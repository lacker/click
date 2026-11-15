//! Scoped rewrites of prepared match payloads. Constructor selection is a
//! separate checking step; this walk preserves arm order and body scopes.
use super::*;

/// Capture reservations include every declaration and every result family.
/// Walk retained algebraic match children directly; exporting each nested
/// prefix would both lose sharing and duplicate the source scan.
pub(super) fn collect_match_carriers(matched: &KernelMatch, variables: &mut CarrierVariables) {
    let mut pending: Vec<_> = matched
        .arguments
        .iter()
        .chain(matched.arms.iter().flat_map(|arm| &arm.bindings))
        .collect();
    let mut export = KernelTermExport::default();
    let mut seen = BTreeSet::new();
    let mut common_seen = BTreeSet::new();
    while let Some(child) = pending.pop() {
        if !common_seen.insert(child.id()) {
            continue;
        }
        if let KernelTermNode::Match(nested) = child.node() {
            if !variables.visit() {
                return;
            }
            if variables.shared_machine_operands.insert(child.id()) {
                pending.extend(
                    nested
                        .arguments
                        .iter()
                        .chain(nested.arms.iter().flat_map(|arm| &arm.bindings)),
                );
            }
        } else if let KernelType::Program(ty) = child.ty()
            && MachineIntegerType::from_program_type(*ty).is_some()
        {
            collect_machine_operand_carriers(MachineOperandView::Shared(child), variables);
        } else if let Ok(argument) = export.argument(child) {
            collect_argument_carriers(&argument, variables, &mut seen);
        }
        if variables.exhausted() {
            return;
        }
    }
}

impl TermRewrite<'_> {
    pub(crate) fn retained_match(
        &mut self,
        matched: &KernelMatch,
    ) -> Result<KernelMatch, RewriteRefusal> {
        let result = self.retained_match_in(matched);
        self.refusal_observed.set(true);
        result
    }

    pub(super) fn retained_match_in(
        &mut self,
        matched: &KernelMatch,
    ) -> Result<KernelMatch, RewriteRefusal> {
        let result = self.rewrite_retained_match_scopes(matched);
        if let Some(refusal) = self.refusal_status() {
            return Err(refusal);
        }
        result.ok_or(RewriteRefusal::UnsupportedScope)
    }

    /// Select only a checked constructor and substitute its fields simultaneously.
    /// None means the existing checker has no reduction, including symbolic inputs.
    pub(crate) fn reduce_retained_match(
        &mut self,
        matched: &KernelMatch,
    ) -> Result<Option<KernelTerm>, RewriteRefusal> {
        let value = self.reduce_retained_match_in(matched);
        self.refusal_observed.set(true);
        match self.refusal_status() {
            Some(refusal) => Err(refusal),
            None => Ok(value),
        }
    }

    pub(super) fn reduce_retained_match_in(&mut self, matched: &KernelMatch) -> Option<KernelTerm> {
        let scrutinee = &matched.arguments[0];
        // Inspect the selected common constructor before the compatibility
        // boundary for typed replacement fields. Symbolic roots have no iota
        // reduction and do not need a native expression tree to say so.
        let native;
        let common_fields;
        let (algebraic_type, variant, fields) = match scrutinee.node() {
            KernelTermNode::Constructor(constructor) => {
                common_fields = constructor.checked_native_fields(&mut self.fold_integer_bridge)?;
                (
                    &constructor.algebraic_type,
                    &constructor.variant,
                    common_fields.as_slice(),
                )
            }
            KernelTermNode::Legacy(value) => {
                let PureFunctionArgument::Algebraic(value) = value.value() else {
                    return None;
                };
                native = value;
                let fields = native.checked_constructor_fields()?;
                let AlgebraicTermNode::Constructor { variant, .. } = &native.node else {
                    return None;
                };
                (&native.algebraic_type, variant, fields)
            }
            _ => return None,
        };
        let index = matched
            .arms
            .iter()
            .position(|arm| arm.variant == *variant)?;
        let schema = algebraic_type
            .variants
            .iter()
            .find(|schema| schema.name == *variant)?;
        let bindings = matched.arms[index]
            .export_bindings(&mut self.fold_integer_bridge)
            .ok()?;
        if bindings.len() != fields.len() {
            return None;
        }
        let (c, integer, algebraic) = match_field_replacements(&bindings, fields, &schema.fields)?;
        let mut rewrite = TermRewrite::for_typed_variables(&c, &integer, &algebraic);
        let value = rewrite.rewrite_retained_match_child(&matched.arguments[index + 1]);
        self.changed |= rewrite.changed;
        rewrite.refusal_observed.set(true);
        self.unsupported_integer_scope |= rewrite.unsupported_integer_scope;
        self.integer_work_exhausted |= rewrite.integer_work_exhausted;
        #[cfg(test)]
        {
            self.visits += rewrite.visits;
        }
        if self.refusal_status().is_some() {
            return None;
        }
        if value.is_some() {
            self.changed = true;
        }
        value
    }

    pub(super) fn rewrite_retained_match_value_in(
        &mut self,
        matched: &KernelMatch,
    ) -> Option<KernelTerm> {
        let matched = match self.retained_match_in(matched) {
            Ok(matched) => matched,
            Err(_) => {
                if self.refusal_status().is_none() {
                    self.unsupported_integer_scope = true;
                }
                return None;
            }
        };
        let reduced = self.reduce_retained_match_in(&matched);
        if self.refusal_status().is_some() {
            return None;
        }
        Some(reduced.unwrap_or_else(|| matched.into_term()))
    }

    fn reserve_retained_match_variables(&mut self, matched: &KernelMatch) -> Option<()> {
        self.ensure_replacement_carriers();
        if self.source_variables_reserved {
            return Some(());
        }
        let mut variables = self.new_carrier_variables();
        collect_match_carriers(matched, &mut variables);
        self.reserve_source_variables(variables);
        (!self.checked_work_exhausted()).then_some(())
    }

    fn rewrite_retained_match_child(&mut self, child: &KernelTerm) -> Option<KernelTerm> {
        if matches!(child.ty(), KernelType::Algebraic(_))
            && let KernelTermNode::Match(matched) = child.node()
        {
            self.visit();
            if self.checked_work_exhausted() {
                return None;
            }
            let key = (
                child.id(),
                self.scope_id,
                self.source_disabled,
                self.integer_shadowed,
                self.resolve_registered_loads,
            );
            let memo = self
                .shared_machine_cache
                .get_or_insert_with(Default::default)
                .clone();
            if let Some(value) = memo.borrow().get(&key).cloned() {
                return Some(value);
            }
            let value = if let Some((from, to)) = self.algebraic
                && !self.source_disabled
                && self.retained_algebraic_source_matches(child, from)?
            {
                self.changed = true;
                let replacement = self.rewrite_algebraic_replacement(to);
                KernelTermImport::default().argument(&PureFunctionArgument::Algebraic(replacement))
            } else {
                self.rewrite_retained_match_value_in(matched)?
            };
            if self.refusal_status().is_some() {
                return None;
            }
            memo.borrow_mut().insert(key, value.clone());
            return Some(value);
        }
        if let KernelType::Program(ty) = child.ty()
            && MachineIntegerType::from_program_type(*ty).is_some()
        {
            return self.shared_machine_operand(child);
        }
        let argument = self.fold_integer_bridge.argument(child).ok()?;
        let rewritten = self.argument(&argument);
        if self.refusal_status().is_some() {
            return None;
        }
        // Variable descriptors have no field payload to transport. Other
        // algebraic values may carry pointer evidence that value equality
        // deliberately ignores, so retain the rewritten payload in that case.
        if let (PureFunctionArgument::Algebraic(before), PureFunctionArgument::Algebraic(after)) =
            (&argument, &rewritten)
            && matches!((&before.node, &after.node), (AlgebraicTermNode::Variable(a), AlgebraicTermNode::Variable(b)) if a == b)
            && before.algebraic_type == after.algebraic_type
        {
            return Some(child.clone());
        }
        Some(KernelTermImport::default().argument(&rewritten))
    }

    /// Exact native source equality over common constructor and match children.
    /// Native leaves retain AlgebraicTerm's pointer-evidence-insensitive value
    /// equality; arm declarations and order retain the same exact semantics.
    fn retained_algebraic_source_matches(
        &mut self,
        root: &KernelTerm,
        source: &AlgebraicTerm,
    ) -> Option<bool> {
        let mut pending = vec![(root, source)];
        while let Some((root, source)) = pending.pop() {
            self.visit();
            if self.checked_work_exhausted() {
                return None;
            }
            if root.ty() != &KernelType::Algebraic(source.algebraic_type.clone()) {
                return Some(false);
            }
            match (root.node(), &source.node) {
                (KernelTermNode::Variable(left), AlgebraicTermNode::Variable(right)) => {
                    if left != right {
                        return Some(false);
                    }
                }
                (KernelTermNode::Constructor(_), AlgebraicTermNode::Constructor { .. }) => {
                    let source = KernelTermImport::default().algebraic(source);
                    if !root.algebraic_syntax_equal_while(&source, || {
                        self.visit();
                        !self.checked_work_exhausted()
                    })? {
                        return Some(false);
                    }
                }
                (KernelTermNode::Legacy(value), _) => {
                    if !matches!(value.value(), PureFunctionArgument::Algebraic(value) if value == source)
                    {
                        return Some(false);
                    }
                }
                (KernelTermNode::Match(matched), AlgebraicTermNode::Match { scrutinee, arms }) => {
                    if matched.arms.len() != arms.len() {
                        return Some(false);
                    }
                    pending.push((&matched.arguments[0], scrutinee));
                    for ((arm, body), source) in
                        matched.arms.iter().zip(&matched.arguments[1..]).zip(arms)
                    {
                        self.visit();
                        if self.checked_work_exhausted() {
                            return None;
                        }
                        if arm.variant != source.variant
                            || arm.bindings.len() != source.bindings.len()
                            || arm.export_bindings(&mut self.fold_integer_bridge).ok()?
                                != source.bindings
                        {
                            return Some(false);
                        }
                        pending.push((body, &source.body));
                    }
                }
                _ => return Some(false),
            }
        }
        Some(true)
    }

    fn rewrite_retained_match_scopes(&mut self, matched: &KernelMatch) -> Option<KernelMatch> {
        self.reserve_retained_match_variables(matched)?;
        let scrutinee = self.rewrite_retained_match_child(&matched.arguments[0])?;
        let mut arms = Vec::with_capacity(matched.arms.len());
        let mut import = KernelTermImport::default();
        for (arm, body) in matched.arms.iter().zip(&matched.arguments[1..]) {
            let saved_scope_id = self.scope_id;
            let saved_shadowed = self.integer_shadowed;
            let mut changes = Vec::new();
            let result = (|| {
                let original = arm.export_bindings(&mut self.fold_integer_bridge).ok()?;
                let mut bindings = original.clone();
                if !self.rewrite_match_bindings(&mut bindings, &mut changes) {
                    return None;
                }
                let body = if self.conditions.is_some() {
                    body.clone()
                } else {
                    self.rewrite_retained_match_child(body)?
                };
                let mut retained = arm.clone();
                for ((child, before), after) in
                    retained.bindings.iter_mut().zip(&original).zip(&bindings)
                {
                    if before != after {
                        *child = import.match_field(after);
                    }
                }
                Some((retained, body))
            })();
            self.restore_scope(&changes, saved_scope_id, saved_shadowed);
            arms.push(result?);
            if self.checked_work_exhausted() {
                return None;
            }
        }
        KernelMatch::new(matched.result_type.clone(), scrutinee, arms).ok()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn retained_algebraic_children_keep_exact_replacement_and_iota_opacity() {
        let leaf = KernelMatch::test_scrutinee(vec![]);
        let native = AlgebraicTerm {
            algebraic_type: leaf.algebraic_type.clone(),
            node: AlgebraicTermNode::Match {
                scrutinee: Box::new(leaf.clone()),
                arms: vec![AlgebraicResultMatchArm {
                    variant: "Arm".into(),
                    bindings: vec![],
                    binding_names: Default::default(),
                    body: leaf.clone(),
                }],
            },
        };
        let inner = KernelMatch::import_algebraic(&mut KernelTermImport::default(), &native)
            .unwrap()
            .into_term();
        let outer = KernelMatch::new(
            KernelType::Algebraic(leaf.algebraic_type.clone()),
            inner.clone(),
            vec![(
                KernelMatchArm {
                    variant: "Arm".into(),
                    bindings: vec![],
                    binding_names: Default::default(),
                },
                inner,
            )],
        )
        .unwrap();
        let mut replacement = leaf;
        replacement.node = AlgebraicTermNode::Variable(Variable(991997));
        let exports = KernelTermExport::algebraic_export_count();
        let mut rewrite = TermRewrite::new(&native, &replacement);
        assert_eq!(rewrite.reduce_retained_match(&outer).unwrap(), None);
        assert_eq!(KernelTermExport::algebraic_export_count(), exports);
        let result = rewrite.retained_match(&outer).unwrap();
        for child in &result.arguments {
            assert_eq!(
                child.ty(),
                &KernelType::Algebraic(replacement.algebraic_type.clone())
            );
            assert!(matches!(
                child.node(),
                KernelTermNode::Variable(variable) if *variable == Variable(991997)
            ));
            assert_eq!(
                KernelTermExport::default().argument(child),
                Ok(PureFunctionArgument::Algebraic(replacement.clone()))
            );
        }
        assert_eq!(KernelTermExport::algebraic_export_count(), exports);
    }

    #[test]
    fn common_numeric_match_reduction_agrees_with_native_checked_fields() {
        for format in [MachineIntegerType::Int32, MachineIntegerType::UInt64] {
            let ty = format.program_type();
            let binding = AlgebraicValue::Program(if format == MachineIntegerType::Int32 {
                ProgramValue::Int32(MachineTerm::Variable(Variable(7)))
            } else {
                ProgramValue::UInt64(MachineTerm::Variable(Variable(7)))
            });
            let mut scrutinee = KernelMatch::test_scrutinee(vec![AlgebraicValueType::Program(ty)]);
            scrutinee.node = AlgebraicTermNode::Constructor {
                variant: "Arm".into(),
                fields: vec![AlgebraicValue::Program(
                    if format == MachineIntegerType::Int32 {
                        ProgramValue::Int32(MachineTerm::Variable(Variable(8)))
                    } else {
                        ProgramValue::UInt64(MachineTerm::Variable(Variable(8)))
                    },
                )],
            };
            let native = MachineTerm::AlgebraicMatch {
                scrutinee: Box::new(scrutinee.clone()),
                arms: vec![AlgebraicBitvectorMatchArm {
                    variant: "Arm".into(),
                    bindings: vec![binding],
                    binding_names: Default::default(),
                    body: MachineTerm::Variable(Variable(7)),
                }],
            };
            let common =
                KernelMatch::import_machine(&mut KernelTermImport::default(), format, &native)
                    .unwrap();
            let result = TermRewrite::empty()
                .reduce_retained_match(&common)
                .unwrap()
                .unwrap();
            assert_eq!(
                KernelTermExport::machine(&result).unwrap(),
                MachineTerm::Variable(Variable(8))
            );
        }
        let mut scrutinee = KernelMatch::test_scrutinee(vec![AlgebraicValueType::Integer]);
        scrutinee.node = AlgebraicTermNode::Constructor {
            variant: "Arm".into(),
            fields: vec![AlgebraicValue::Integer(IntegerTerm::Variable(Variable(8)))],
        };
        let native = IntegerTerm::AlgebraicMatch {
            scrutinee: Box::new(scrutinee),
            arms: vec![AlgebraicIntegerMatchArm {
                variant: "Arm".into(),
                bindings: vec![AlgebraicValue::Integer(IntegerTerm::Variable(Variable(7)))],
                binding_names: Default::default(),
                body: IntegerTerm::Variable(Variable(7)).into(),
            }],
        };
        let common =
            KernelMatch::import_integer(&mut KernelTermImport::default(), &native).unwrap();
        let result = TermRewrite::empty()
            .reduce_retained_match(&common)
            .unwrap()
            .unwrap();
        assert_eq!(
            KernelTermExport::default()
                .integer(&result)
                .unwrap()
                .as_ref(),
            &IntegerTerm::Variable(Variable(8))
        );
    }

    #[test]
    fn common_match_rewrite_preserves_integer_capture_and_machine_scopes() {
        let native = IntegerTerm::AlgebraicMatch {
            scrutinee: Box::new(KernelMatch::test_scrutinee(vec![
                AlgebraicValueType::Integer,
            ])),
            arms: vec![AlgebraicIntegerMatchArm {
                variant: "Arm".into(),
                binding_names: Default::default(),
                bindings: vec![AlgebraicValue::Integer(IntegerTerm::Variable(Variable(2)))],
                body: IntegerTerm::Add(
                    IntegerTerm::Variable(Variable(1)).into(),
                    IntegerTerm::Variable(Variable(2)).into(),
                )
                .into(),
            }],
        };
        let common =
            KernelMatch::import_integer(&mut KernelTermImport::default(), &native).unwrap();
        let replacement = IntegerTerm::Variable(Variable(2));
        let renamings = BTreeMap::new();
        let mut old =
            TermRewrite::for_integer_variables(Variable(1), &replacement, false, &renamings);
        let expected = old.integer(&native);
        assert_eq!(old.refusal(), None);
        let mut new =
            TermRewrite::for_integer_variables(Variable(1), &replacement, false, &renamings);
        let actual = new.retained_match(&common).unwrap();
        assert_eq!(
            actual
                .export_integer(&mut KernelTermExport::default())
                .unwrap(),
            expected
        );
        assert!(new.scope.integer.is_empty());
        assert!(!new.integer_shadowed);

        let native = MachineTerm::AlgebraicMatch {
            scrutinee: Box::new(KernelMatch::test_scrutinee(vec![
                AlgebraicValueType::Program(ProgramType::Int32),
            ])),
            arms: vec![AlgebraicBitvectorMatchArm {
                variant: "Arm".into(),
                binding_names: Default::default(),
                bindings: vec![AlgebraicValue::Program(ProgramValue::Int32(
                    MachineTerm::Variable(Variable(2)),
                ))],
                body: MachineTerm::Binary {
                    format: MachineIntegerType::Int32,
                    op: MachineBinaryOp::Add,
                    left: Box::new(MachineTerm::Variable(Variable(1))),
                    right: Box::new(MachineTerm::Variable(Variable(2))),
                },
            }],
        };
        let common = KernelMatch::import_machine(
            &mut KernelTermImport::default(),
            MachineIntegerType::Int32,
            &native,
        )
        .unwrap();
        for target in [Variable(1), Variable(2)] {
            let source = MachineTerm::Variable(target);
            let replacement = MachineTerm::Variable(Variable(2));
            let mut old = TermRewrite::for_bits(&source, &replacement);
            let expected = old.bits(&native);
            assert_eq!(old.refusal(), None);
            let mut new = TermRewrite::for_bits(&source, &replacement);
            let exports = KernelTermExport::machine_export_count();
            let actual = new.retained_match(&common).unwrap();
            assert_eq!(KernelTermExport::machine_export_count(), exports);
            assert_eq!(
                actual
                    .export_machine(&mut KernelTermExport::default())
                    .unwrap(),
                expected
            );
            assert!(new.scope.program_values.is_empty());
        }
    }

    #[test]
    fn common_match_pointer_transport_preserves_states_and_avoids_capture() {
        let _session = VerificationSession::enter();
        let memory = intern_memory(Memory::new());
        let source = Variable(3);
        let bound = Variable(2);
        let read = |variable| {
            MachineTerm::MemoryLoad(
                memory.clone(),
                Box::new(Pointer::symbolic(variable)),
                LoadKind::Int32,
            )
        };
        let native = MachineTerm::AlgebraicMatch {
            scrutinee: Box::new(KernelMatch::test_scrutinee(vec![
                AlgebraicValueType::Program(ProgramType::Int32Pointer),
            ])),
            arms: vec![AlgebraicBitvectorMatchArm {
                variant: "Arm".into(),
                binding_names: Default::default(),
                bindings: vec![AlgebraicValue::Program(ProgramValue::typed_pointer(
                    Pointer::symbolic(bound),
                    ProgramType::Int32Pointer,
                ))],
                body: MachineTerm::Binary {
                    format: MachineIntegerType::Int32,
                    op: MachineBinaryOp::Add,
                    left: Box::new(read(source)),
                    right: Box::new(read(bound)),
                },
            }],
        };
        let common = KernelMatch::import_machine(
            &mut KernelTermImport::default(),
            MachineIntegerType::Int32,
            &native,
        )
        .unwrap();
        let replacement = Pointer::symbolic(bound);
        let mut old = TermRewrite::for_pointer_variable(source, &replacement);
        let expected = old.bits(&native);
        assert_eq!(old.refusal(), None);
        let mut new = TermRewrite::for_pointer_variable(source, &replacement);
        let actual = new.retained_match(&common).unwrap();
        assert_eq!(
            actual
                .export_machine(&mut KernelTermExport::default())
                .unwrap(),
            expected
        );
        assert!(new.scope.program_values.is_empty());
    }

    #[test]
    fn retained_algebraic_match_keeps_rewritten_pointer_evidence() {
        use crate::kernel::effective_type::{CAccessClass, CStructClass};
        let class = CAccessClass::Struct(CStructClass::opaque("RetainedPointer"));
        let original = ProgramValue::typed_pointer(
            Pointer::symbolic(Variable(991940)),
            ProgramType::Int32Pointer,
        );
        let replacement = original
            .clone()
            .with_pointer_object_class(Some(class.clone()));
        assert_eq!(
            original, replacement,
            "value equality intentionally omits pointer evidence"
        );
        let key = AlgebraicValueType::Algebraic {
            name: "PointerBox".into(),
            arguments: vec![],
        };
        let variants: std::sync::Arc<[AlgebraicVariantType]> = vec![AlgebraicVariantType {
            name: "Box".into(),
            fields: vec![AlgebraicValueType::Program(ProgramType::Int32Pointer)],
        }]
        .into();
        let ty = AlgebraicType {
            rigid: false,
            name: "PointerBox".into(),
            arguments: vec![],
            variants: variants.clone(),
            schemas: std::sync::Arc::new(AlgebraicSchemas::new(BTreeMap::from([(key, variants)]))),
        };
        let native = AlgebraicTerm {
            algebraic_type: ty.clone(),
            node: AlgebraicTermNode::Match {
                scrutinee: Box::new(KernelMatch::test_scrutinee(vec![])),
                arms: vec![AlgebraicResultMatchArm {
                    variant: "Arm".into(),
                    binding_names: Default::default(),
                    bindings: vec![],
                    body: AlgebraicTerm {
                        algebraic_type: ty,
                        node: AlgebraicTermNode::Constructor {
                            variant: "Box".into(),
                            fields: vec![AlgebraicValue::Program(original.clone())],
                        },
                    },
                }],
            },
        };
        let common =
            KernelMatch::import_algebraic(&mut KernelTermImport::default(), &native).unwrap();
        let (ProgramValue::Pointer(from), ProgramValue::Pointer(to)) = (&original, &replacement)
        else {
            unreachable!()
        };
        let mut rewrite = TermRewrite::for_pointer_value_exact(from, to);
        let result = rewrite.retained_match(&common).unwrap().into_term();
        let result = KernelTermExport::default().algebraic(&result).unwrap();
        let AlgebraicTermNode::Match { arms, .. } = result.node else {
            unreachable!()
        };
        let AlgebraicTermNode::Constructor { fields, .. } = &arms[0].body.node else {
            unreachable!()
        };
        let AlgebraicValue::Program(ProgramValue::Pointer(pointer)) = &fields[0] else {
            unreachable!()
        };
        assert!(pointer.supports_object_class(&class));
    }

    #[test]
    fn common_match_refusal_restores_scope_and_keeps_the_native_refusal() {
        let source = MachineTerm::Binary {
            format: MachineIntegerType::Int32,
            op: MachineBinaryOp::Add,
            left: Box::new(MachineTerm::Variable(Variable(1))),
            right: Box::new(MachineTerm::Variable(Variable(2))),
        };
        let native = MachineTerm::AlgebraicMatch {
            scrutinee: Box::new(KernelMatch::test_scrutinee(vec![
                AlgebraicValueType::Program(ProgramType::Int32),
            ])),
            arms: vec![AlgebraicBitvectorMatchArm {
                variant: "Arm".into(),
                binding_names: Default::default(),
                bindings: vec![AlgebraicValue::Program(ProgramValue::Int32(
                    MachineTerm::Variable(Variable(2)),
                ))],
                body: source.clone(),
            }],
        };
        let common = KernelMatch::import_machine(
            &mut KernelTermImport::default(),
            MachineIntegerType::Int32,
            &native,
        )
        .unwrap();
        let replacement = MachineTerm::constant(7);
        let mut old = TermRewrite::for_bits(&source, &replacement);
        let _ = old.bits(&native);
        let expected = old
            .refusal()
            .expect("composite source under a C binder refuses");
        let mut new = TermRewrite::for_bits(&source, &replacement);
        assert_eq!(new.retained_match(&common), Err(expected));
        assert!(new.scope.program_values.is_empty());
    }
}

#[cfg(test)]
mod scaling_tests {
    include!("../../../scaling_tests/kernel/proof/term_rewrite/retained_matches.rs");
}
