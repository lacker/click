//! Scoped alpha identities for selected native match leaves. Common parents
//! keep their DAG; only the existing match payload is visited here.
use super::*;
use crate::kernel::proof::term_rewrite::{BindingCarrier, binding_variable};

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub(super) struct Arm {
    variant: String,
    types: Vec<crate::kernel::AlgebraicValueType>,
    body: AlphaMachineKey,
}

pub(super) fn machine<const ALLOW_LOADS: bool>(
    scrutinee: &AlgebraicTerm,
    arms: &[crate::kernel::AlgebraicBitvectorMatchArm],
    bindings: &mut AlphaBindings,
    next_binder: &mut usize,
) -> Option<AlphaBitvectorKey> {
    machine_arms::<ALLOW_LOADS>(
        scrutinee,
        arms.iter().map(|arm| {
            (
                arm.variant.as_str(),
                arm.bindings.as_slice(),
                crate::kernel::MachineOperandView::Old(&arm.body),
            )
        }),
        bindings,
        next_binder,
    )
}

fn machine_arms<'a, const ALLOW_LOADS: bool>(
    scrutinee: &AlgebraicTerm,
    arms: impl ExactSizeIterator<
        Item = (
            &'a str,
            &'a [crate::kernel::AlgebraicValue],
            crate::kernel::MachineOperandView<'a>,
        ),
    >,
    bindings: &mut AlphaBindings,
    next_binder: &mut usize,
) -> Option<AlphaBitvectorKey> {
    let scrutinee =
        alpha_algebraic_key_with_bindings::<ALLOW_LOADS>(scrutinee, bindings, next_binder)?;
    let mut keys = Vec::with_capacity(arms.len());
    for (variant, declarations, body) in arms {
        alpha_work_checkpoint(bindings, 1)?;
        let outer_next = *next_binder;
        let outer_scopes = (bindings.integer_scope, bindings.bitvector_scope);
        let scope = bindings.next_scope_id;
        bindings.next_scope_id = scope.checked_add(1)?;
        bindings.integer_scope = scope;
        bindings.bitvector_scope = scope;
        let mut changes = Vec::with_capacity(declarations.len());
        let result = (|| {
            let mut types = Vec::with_capacity(declarations.len());
            for binding in declarations {
                alpha_work_checkpoint(bindings, 1)?;
                let (carrier, variable) = binding_variable(binding)?;
                let ordinal = *next_binder;
                *next_binder = ordinal.checked_add(1)?;
                let map = match carrier {
                    BindingCarrier::Program => &mut bindings.bitvector,
                    BindingCarrier::Integer => &mut bindings.integer,
                    BindingCarrier::Algebraic => &mut bindings.algebraic,
                };
                changes.push((carrier, variable, map.insert(variable, ordinal)));
                types.push(binding.value_type());
            }
            let body = alpha_machine_key::<ALLOW_LOADS>(body, bindings, next_binder)?;
            Some(Arm {
                variant: variant.into(),
                types,
                body,
            })
        })();
        for (carrier, variable, prior) in changes.into_iter().rev() {
            let map = match carrier {
                BindingCarrier::Program => &mut bindings.bitvector,
                BindingCarrier::Integer => &mut bindings.integer,
                BindingCarrier::Algebraic => &mut bindings.algebraic,
            };
            if let Some(prior) = prior {
                map.insert(variable, prior);
            } else {
                map.remove(&variable);
            }
        }
        (bindings.integer_scope, bindings.bitvector_scope) = outer_scopes;
        *next_binder = outer_next;
        keys.push(result?);
    }
    Some(AlphaBitvectorKey::AlgebraicMatch(Box::new(scrutinee), keys))
}

#[allow(dead_code)] // Activated with common match roots in 6l.
pub(super) fn retained_machine<const ALLOW_LOADS: bool>(
    matched: &crate::kernel::KernelMatch,
    bindings: &mut AlphaBindings,
    next_binder: &mut usize,
) -> Option<AlphaBitvectorKey> {
    let mut export = crate::kernel::KernelTermExport::default();
    let PureFunctionArgument::Algebraic(scrutinee) = export.argument(&matched.arguments[0]).ok()?
    else {
        return None;
    };
    let declarations = matched
        .arms
        .iter()
        .map(|arm| arm.export_bindings(&mut export))
        .collect::<Result<Vec<_>, _>>()
        .ok()?;
    machine_arms::<ALLOW_LOADS>(
        &scrutinee,
        matched
            .arms
            .iter()
            .zip(&declarations)
            .zip(&matched.arguments[1..])
            .map(|((arm, declarations), body)| {
                (
                    arm.variant.as_str(),
                    declarations.as_slice(),
                    crate::kernel::MachineOperandView::Shared(body),
                )
            }),
        bindings,
        next_binder,
    )
}

#[allow(dead_code)] // Activated with common match roots in 6l.
pub(crate) fn retained_alpha_equivalent(
    left: &crate::kernel::KernelMatch,
    right: &crate::kernel::KernelMatch,
) -> Option<bool> {
    if left.result_type != right.result_type {
        return Some(false);
    }
    fn key(matched: &crate::kernel::KernelMatch) -> Option<(AlphaBitvectorKey, usize)> {
        let crate::kernel::KernelType::Program(ty) = matched.result_type else {
            return None;
        };
        crate::kernel::MachineIntegerType::from_program_type(ty)?;
        let mut bindings = fold_keys::bindings();
        let key = retained_machine::<false>(matched, &mut bindings, &mut 0)?;
        Some((key, bindings.work_units))
    }
    let (left, lw) = key(left)?;
    let (right, rw) = key(right)?;
    if crate::instrumentation::deadline_exceeded_with_work(lw.saturating_add(rw)) {
        return None;
    }
    Some(left == right)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::{AlgebraicBitvectorMatchArm, AlgebraicValue, ProgramValue};

    fn selected_match(bound: u64, count: usize) -> OldMachineTerm {
        OldMachineTerm::AlgebraicMatch {
            scrutinee: Box::new(AlgebraicTerm {
                algebraic_type: crate::kernel::AlgebraicType::parameter("Payload".into()),
                node: AlgebraicTermNode::Variable(Variable(900)),
            }),
            arms: (0..count)
                .map(|index| AlgebraicBitvectorMatchArm {
                    variant: format!("Arm{index}"),
                    bindings: vec![AlgebraicValue::Program(ProgramValue::Int32(
                        OldMachineTerm::Variable(Variable(bound)),
                    ))],
                    body: OldMachineTerm::Variable(Variable(bound)),
                    binding_names: Default::default(),
                })
                .collect(),
        }
    }

    fn key(term: &OldMachineTerm) -> Option<AlphaBitvectorKey> {
        alpha_bitvector_key::<false>(term, &mut BTreeMap::new(), &mut 0)
    }

    #[test]
    fn match_operands_have_the_same_stored_and_written_comparison_keys() {
        let _session = crate::kernel::VerificationSession::enter();
        for format in [MachineIntegerType::Int32, MachineIntegerType::UInt64] {
            let source = OldConditionTerm::Compare {
                format,
                relation: CompareRelation::LessThan,
                left: Box::new(selected_match(100, 2)),
                right: Box::new(OldMachineTerm::Variable(Variable(101))),
            };
            let root = crate::kernel::KernelTermImport::default().condition(&source);
            assert_stored_proposition_keys(&root, &memory_erased_condition_key(&source));
        }
    }

    #[test]
    fn match_alpha_keys_preserve_free_variables_and_arm_scope() {
        let left = selected_match(100, 2);
        let right = selected_match(200, 2);
        assert!(key(&left).is_some());
        assert_eq!(key(&left), key(&right));
        let mut different = right.clone();
        let OldMachineTerm::AlgebraicMatch { arms, .. } = &mut different else {
            unreachable!()
        };
        arms[1].body = OldMachineTerm::Variable(Variable(100));
        assert_ne!(key(&left), key(&different));

        // A C binder must not capture an algebraic argument with the same ID.
        let with_free_algebraic = |bound| {
            let mut term = selected_match(bound, 1);
            let OldMachineTerm::AlgebraicMatch { arms, .. } = &mut term else {
                unreachable!()
            };
            arms[0].body = OldMachineTerm::ClickFunctionApplication {
                name: "read".into(),
                arguments: vec![PureFunctionArgument::Algebraic(AlgebraicTerm {
                    algebraic_type: crate::kernel::AlgebraicType::parameter("Other".into()),
                    node: AlgebraicTermNode::Variable(Variable(bound)),
                })],
            };
            term
        };
        assert_ne!(
            key(&with_free_algebraic(100)),
            key(&with_free_algebraic(200))
        );
    }

    #[test]
    fn common_match_alpha_keys_agree_with_native_scopes() {
        use crate::kernel::{KernelMatch, KernelTermImport, MachineIntegerType};
        let left = selected_match(100, 2);
        let mut changed = selected_match(200, 2);
        let OldMachineTerm::AlgebraicMatch { arms, .. } = &mut changed else {
            unreachable!()
        };
        arms[1].body = OldMachineTerm::Variable(Variable(100));
        for right in [selected_match(200, 2), changed] {
            let expected = key(&left).unwrap() == key(&right).unwrap();
            let a = KernelMatch::import_machine(
                &mut KernelTermImport::default(),
                MachineIntegerType::Int32,
                &left,
            )
            .unwrap();
            let b = KernelMatch::import_machine(
                &mut KernelTermImport::default(),
                MachineIntegerType::Int32,
                &right,
            )
            .unwrap();
            assert_eq!(retained_alpha_equivalent(&a, &b), Some(expected));
        }
    }

    mod scaling_tests {
        include!("../../../scaling_tests/kernel/proof/fact_keys/match_keys.rs");
    }
}
