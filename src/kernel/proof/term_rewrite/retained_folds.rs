//! Scoped rewriting of prepared common fold payloads. Integer children retain
//! the existing memoized compatibility boundary until the Integer walker moves.
use super::*;

impl TermRewrite<'_> {
    pub(crate) fn retained_fold(
        &mut self,
        fold: &KernelFold,
    ) -> Result<KernelFold, RewriteRefusal> {
        let result = self.retained_fold_in(fold);
        self.refusal_observed.set(true);
        result
    }

    pub(super) fn retained_fold_in(
        &mut self,
        fold: &KernelFold,
    ) -> Result<KernelFold, RewriteRefusal> {
        let result = if fold.result_type() == &KernelType::Integer {
            self.retained_integer_fold(fold)
        } else {
            self.retained_machine_fold(fold)
        };
        if let Some(refusal) = self.refusal_status() {
            return Err(refusal);
        }
        result.ok_or(RewriteRefusal::UnsupportedScope)
    }

    fn retained_integer_fold(&mut self, fold: &KernelFold) -> Option<KernelFold> {
        if self.integer_exact.is_some()
            || self.pointer_exact.is_some()
            || self.pointer_offset_exact.is_some()
            || (fold.index != KernelFoldIndex::Integer && self.has_composite_bitvector_source())
        {
            self.unsupported_integer_scope = true;
            return None;
        }
        let IntegerTerm::RangeFold {
            index,
            initial,
            body,
            ..
        } = fold
            .integer_compatibility(&mut self.fold_integer_bridge)
            .ok()?
        else {
            unreachable!("Integer fold compatibility shape")
        };
        let rewritten =
            self.rewrite_integer_range_fold(&index, &initial, fold.accumulator, fold.item, &body);
        if self.refusal_status().is_some() {
            return None;
        }
        KernelFold::import_integer(&mut KernelTermImport::default(), &rewritten)
    }

    fn retained_machine_fold(&mut self, fold: &KernelFold) -> Option<KernelFold> {
        self.ensure_replacement_carriers();
        if !self.source_variables_reserved {
            let mut variables = self.new_carrier_variables();
            variables.program_values.insert(fold.accumulator);
            variables.program_values.insert(fold.item);
            for child in &fold.arguments {
                collect_machine_operand_carriers(MachineOperandView::Shared(child), &mut variables);
                if variables.exhausted() {
                    break;
                }
            }
            self.reserve_source_variables(variables);
        }
        if self.checked_work_exhausted() {
            return None;
        }
        // The first three children are outside the body binders.
        let start = self.shared_machine_operand(&fold.arguments[0])?;
        let end = self.shared_machine_operand(&fold.arguments[1])?;
        let initial = self.shared_machine_operand(&fold.arguments[2])?;
        let saved_scope_id = self.scope_id;
        let saved_shadowed = self.integer_shadowed;
        let mut changes = Vec::new();
        let result = (|| {
            let accumulator = self.rewrite_program_binder(fold.accumulator, &mut changes)?;
            let item = self.rewrite_program_binder(fold.item, &mut changes)?;
            let body = if self.conditions.is_some() {
                fold.arguments[3].clone()
            } else {
                self.shared_machine_operand(&fold.arguments[3])?
            };
            Some(KernelFold {
                index: fold.index,
                accumulator,
                item,
                arguments: [start, end, initial, body],
            })
        })();
        self.restore_scope(&changes, saved_scope_id, saved_shadowed);
        result
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn common_machine_fold_rewrite_matches_native_capture_and_scope() {
        let source = MachineTerm::Variable(Variable(31));
        for replacement in [
            MachineTerm::constant(7),
            MachineTerm::Variable(Variable(32)),
        ] {
            let native = MachineTerm::RangeFold {
                start: Box::new(source.clone()),
                end: Box::new(MachineTerm::constant(9)),
                initial: Box::new(MachineTerm::Variable(Variable(32))),
                accumulator: Variable(32),
                item: Variable(33),
                body: Box::new(binary_node!(
                    Int32,
                    Add,
                    Box::new(source.clone()),
                    Box::new(MachineTerm::Variable(Variable(32))),
                )),
            };
            let fold =
                KernelFold::import_machine(&mut KernelTermImport::default(), &native).unwrap();
            let mut old = TermRewrite::for_bits(&source, &replacement);
            let expected = old.bits(&native);
            assert_eq!(old.refusal(), None);
            let mut new = TermRewrite::for_bits(&source, &replacement);
            let actual = new.retained_fold(&fold).unwrap();
            assert_eq!(actual.export_machine().unwrap(), expected);
            assert!(new.scope.program_values.is_empty());
        }
    }

    #[test]
    fn common_fold_pointer_transport_preserves_state_and_condition_scope() {
        let _session = crate::kernel::VerificationSession::enter();
        let memory = Memory::new();
        let source = Variable(55);
        let replacement = Pointer::symbolic(Variable(56));
        let read = MachineTerm::MemoryLoad(
            crate::kernel::intern_memory_ref(&memory),
            Box::new(Pointer::symbolic(source)),
            LoadKind::Int32,
        );
        let native = MachineTerm::RangeFold {
            start: Box::new(MachineTerm::constant(0)),
            end: Box::new(MachineTerm::constant(9)),
            initial: Box::new(read.clone()),
            accumulator: Variable(57),
            item: Variable(58),
            body: Box::new(read),
        };
        let fold = KernelFold::import_machine(&mut KernelTermImport::default(), &native).unwrap();
        let mut old = TermRewrite::for_pointer_variable(source, &replacement);
        let expected = old.bits(&native);
        assert_eq!(old.refusal(), None);
        let mut new = TermRewrite::for_pointer_variable(source, &replacement);
        let result = new.retained_fold(&fold).unwrap();
        assert_eq!(result.export_machine().unwrap(), expected);
        let MachineTerm::RangeFold { body, .. } = expected else {
            unreachable!()
        };
        let MachineTerm::MemoryLoad(retained_state, pointer, _) = *body else {
            unreachable!()
        };
        assert_eq!(retained_state, crate::kernel::intern_memory_ref(&memory));
        assert_eq!(*pointer, replacement);

        let condition = ConditionTerm::Variable(Variable(59));
        let conditional = MachineTerm::If {
            condition: Box::new(condition.clone()),
            then_term: Box::new(MachineTerm::constant(1)),
            else_term: Box::new(MachineTerm::constant(2)),
        };
        let native = MachineTerm::RangeFold {
            start: Box::new(MachineTerm::constant(0)),
            end: Box::new(MachineTerm::constant(9)),
            initial: Box::new(conditional.clone()),
            accumulator: Variable(57),
            item: Variable(58),
            body: Box::new(conditional),
        };
        let fold = KernelFold::import_machine(&mut KernelTermImport::default(), &native).unwrap();
        let conditions = HashMap::from([(condition, true)]);
        let mut old = TermRewrite::for_conditions(&conditions);
        let expected = old.bits(&native);
        assert_eq!(old.refusal(), None);
        let mut new = TermRewrite::for_conditions(&conditions);
        let result = new.retained_fold(&fold).unwrap();
        assert_eq!(result.arguments[3], fold.arguments[3]);
        assert_eq!(result.export_machine().unwrap(), expected);
    }

    #[test]
    fn common_integer_fold_rewrite_matches_native_ranges_capture_and_refusal() {
        for index in [
            KernelFoldIndex::Int32,
            KernelFoldIndex::UInt64,
            KernelFoldIndex::Integer,
        ] {
            let bounds = if index == KernelFoldIndex::Integer {
                [
                    KernelTerm::integer_literal(0.into()),
                    KernelTerm::integer_literal(9.into()),
                ]
            } else {
                let format = if index == KernelFoldIndex::Int32 {
                    MachineIntegerType::Int32
                } else {
                    MachineIntegerType::UInt64
                };
                [0, 9].map(|v| {
                    KernelTerm::retained_machine_operand(
                        format,
                        MachineOperandView::Legacy(&MachineTerm::constant(v)),
                    )
                })
            };
            let variable = KernelTerm::variable(KernelType::Integer, Variable(40));
            let fold = KernelFold::new(
                index,
                Variable(41),
                Variable(42),
                [
                    bounds[0].clone(),
                    bounds[1].clone(),
                    variable.clone(),
                    variable,
                ],
            )
            .unwrap();
            let native = fold
                .export_integer(&mut KernelTermExport::default())
                .unwrap();
            let replacement = IntegerTerm::Variable(Variable(41));
            let renamings = BTreeMap::new();
            let mut old =
                TermRewrite::for_integer_variables(Variable(40), &replacement, false, &renamings);
            let expected = old.integer_shared(&native.clone().into());
            assert_eq!(old.refusal(), None);
            let mut new =
                TermRewrite::for_integer_variables(Variable(40), &replacement, false, &renamings);
            let actual = new.retained_fold(&fold).unwrap();
            assert_eq!(
                actual
                    .export_integer(&mut KernelTermExport::default())
                    .unwrap(),
                expected
            );
            let from: SharedIntegerTerm = IntegerTerm::Variable(Variable(40)).into();
            let to: SharedIntegerTerm = replacement.clone().into();
            let mut refusing = TermRewrite::for_integer_exact(&from, &to);
            assert_eq!(
                refusing.retained_fold(&fold),
                Err(RewriteRefusal::UnsupportedScope)
            );
        }
    }
}

#[cfg(test)]
mod scaling_tests {
    include!("../../../scaling_tests/kernel/proof/term_rewrite/retained_folds.rs");
}
