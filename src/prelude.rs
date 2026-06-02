//! Standard definitions layered on top of the kernel.

pub mod list;
mod proof;
mod source;

use crate::{Computation, Name, Theorem, Theory};

pub const REVERSE_ACC: Name = Name(1);
pub const REVERSE: Name = Name(2);
pub const REVERSE_ACC_COMPUTES_TO_LIST: Name = Name(3);
pub const REVERSE_COMPUTES_TO_LIST: Name = Name(4);
pub const REVERSE_NIL_COMPUTES_TO_LIST: Name = Name(6);
pub const APPEND: Name = Name(7);
pub const APPEND_NIL_COMPUTES_TO_LIST: Name = Name(8);
pub const APPEND_COMPUTES_TO_LIST: Name = Name(9);

pub fn theory() -> Theory {
    let mut theory = Theory::new();
    assert!(define_in_theory(&mut theory));
    theory
}

pub fn computation_theory() -> Theory {
    let mut theory = Theory::new();
    assert!(define_computations_in_theory(&mut theory));
    theory
}

pub fn define_in_theory(theory: &mut Theory) -> bool {
    let Ok(module) = list::module() else {
        return false;
    };

    define_module_computations(theory, &module) && define_module_theorems(theory, &module)
}

pub fn define_computations_in_theory(theory: &mut Theory) -> bool {
    let Ok(module) = list::module() else {
        return false;
    };

    define_module_computations(theory, &module)
}

fn define_module_computations(theory: &mut Theory, module: &source::ParsedModule) -> bool {
    module
        .computations
        .iter()
        .all(|(name, computation)| theory.define_computation(*name, computation))
}

pub fn define_theorems_in_theory(theory: &mut Theory) -> bool {
    let Ok(module) = list::module() else {
        return false;
    };

    define_module_theorems(theory, &module)
}

fn define_module_theorems(theory: &mut Theory, module: &source::ParsedModule) -> bool {
    module.theorems.iter().all(|theorem| {
        let Some(proof) = proof::proof_for_theorem(theorem, theory) else {
            return false;
        };

        theory
            .define_theorem_from_proof(theorem.name, proof, theorem.prop.clone())
            .is_some()
    })
}

pub fn reverse_acc_computes_to_list() -> Option<Theorem> {
    list::checked_source_theorem(REVERSE_ACC_COMPUTES_TO_LIST)
}

pub fn reverse_computes_to_list() -> Option<Theorem> {
    list::checked_source_theorem(REVERSE_COMPUTES_TO_LIST)
}

pub fn reverse_nil_computes_to_list() -> Option<Theorem> {
    list::checked_source_theorem(REVERSE_NIL_COMPUTES_TO_LIST)
}

pub fn append_nil_computes_to_list() -> Option<Theorem> {
    list::checked_source_theorem(APPEND_NIL_COMPUTES_TO_LIST)
}

pub fn append_computes_to_list() -> Option<Theorem> {
    list::checked_source_theorem(APPEND_COMPUTES_TO_LIST)
}

pub fn reverse_acc() -> Computation {
    Computation::Ref(REVERSE_ACC)
}

pub fn reverse() -> Computation {
    Computation::Ref(REVERSE)
}

pub fn append() -> Computation {
    Computation::Ref(APPEND)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Step, computes_to_list};

    #[test]
    fn theory_defines_reverse() {
        let theory = theory();

        assert_eq!(
            theory.computation(REVERSE_ACC),
            Some(&list::reverse_acc_definition())
        );
        assert_eq!(
            theory.computation(REVERSE),
            Some(&list::reverse_definition())
        );
        assert_eq!(theory.computation(APPEND), Some(&list::append_definition()));
        assert_eq!(reverse_acc(), Computation::Ref(REVERSE_ACC));
        assert_eq!(reverse(), Computation::Ref(REVERSE));
        assert_eq!(append(), Computation::Ref(APPEND));
        assert_eq!(
            theory.reduce(&reverse_acc()),
            Step::Reduced(list::reverse_acc_definition())
        );
        assert_eq!(
            theory.reduce(&reverse()),
            Step::Reduced(list::reverse_definition())
        );
        assert_eq!(
            theory.reduce(&append()),
            Step::Reduced(list::append_definition())
        );
    }

    #[test]
    fn computation_theory_does_not_define_theorems() {
        let theory = computation_theory();

        assert!(theory.theorem(REVERSE_ACC_COMPUTES_TO_LIST).is_none());
        assert!(theory.theorem(REVERSE_COMPUTES_TO_LIST).is_none());
        assert!(theory.theorem(REVERSE_NIL_COMPUTES_TO_LIST).is_none());
        assert!(theory.theorem(APPEND_NIL_COMPUTES_TO_LIST).is_none());
        assert!(theory.theorem(APPEND_COMPUTES_TO_LIST).is_none());
    }

    #[test]
    fn theorem_definitions_require_computations() {
        let mut theory = Theory::new();

        assert!(!define_theorems_in_theory(&mut theory));
        assert!(theory.theorem(REVERSE_ACC_COMPUTES_TO_LIST).is_none());
        assert!(theory.theorem(REVERSE_COMPUTES_TO_LIST).is_none());
        assert!(theory.theorem(REVERSE_NIL_COMPUTES_TO_LIST).is_none());
        assert!(theory.theorem(APPEND_NIL_COMPUTES_TO_LIST).is_none());
        assert!(theory.theorem(APPEND_COMPUTES_TO_LIST).is_none());
    }

    #[test]
    fn theory_defines_reverse_theorems() {
        let theory = theory();
        let reverse_acc_prop = list::reverse_acc_computes_to_list_source_theorem();
        let reverse_prop = list::reverse_computes_to_list_source_theorem();
        let reverse_nil_prop = list::reverse_nil_computes_to_list_source_theorem();
        let append_nil_prop = list::append_nil_computes_to_list_source_theorem();
        let append_prop = list::append_computes_to_list_source_theorem();

        assert_eq!(
            theory.theorem(REVERSE_ACC_COMPUTES_TO_LIST),
            Some(&reverse_acc_prop)
        );
        assert_eq!(
            theory.theorem(REVERSE_COMPUTES_TO_LIST),
            Some(&reverse_prop)
        );
        assert_eq!(
            theory.theorem(REVERSE_NIL_COMPUTES_TO_LIST),
            Some(&reverse_nil_prop)
        );
        assert_eq!(
            theory.theorem(APPEND_NIL_COMPUTES_TO_LIST),
            Some(&append_nil_prop)
        );
        assert_eq!(theory.theorem(APPEND_COMPUTES_TO_LIST), Some(&append_prop));
        assert_eq!(
            theory
                .known(REVERSE_COMPUTES_TO_LIST)
                .expect("reverse theorem should be defined")
                .prop(),
            &reverse_prop,
        );
        assert_eq!(
            reverse_computes_to_list()
                .expect("reverse theorem source proof should check with dependencies")
                .prop(),
            &reverse_prop,
        );
        assert_eq!(
            reverse_nil_computes_to_list()
                .expect("reverse nil theorem source proof should check with dependencies")
                .prop(),
            &reverse_nil_prop,
        );
        assert_eq!(
            append_nil_computes_to_list()
                .expect("append nil theorem source proof should check with dependencies")
                .prop(),
            &append_nil_prop,
        );
        assert_eq!(
            append_computes_to_list()
                .expect("append theorem source proof should check with dependencies")
                .prop(),
            &append_prop,
        );
    }

    #[test]
    fn prelude_theory_instantiates_named_reverse_theorem() {
        let theory = theory();
        let reverse = theory
            .known(REVERSE_COMPUTES_TO_LIST)
            .expect("reverse theorem should be defined");
        let instantiated = theory
            .forall_list_elim(&reverse, list::nil())
            .expect("known theorem should instantiate in its theory");

        assert_eq!(
            instantiated.prop(),
            &computes_to_list(
                list::reverse_computes_to_list_source_result_symbol(),
                list::reverse_call(list::nil()),
            )
        );
    }
}
