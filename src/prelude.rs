//! Standard definitions layered on top of the kernel.

pub mod list;
mod proof;
mod source;

use crate::{Name, Term, Theorem, Theory};

pub const REVERSE_ACC: Name = Name(1);
pub const REVERSE: Name = Name(2);
pub const REVERSE_ACC_COMPUTES_TO_LIST: Name = Name(3);
pub const REVERSE_COMPUTES_TO_LIST: Name = Name(4);

pub fn theory() -> Theory {
    let mut theory = Theory::new();
    assert!(define_in_theory(&mut theory));
    theory
}

pub fn term_theory() -> Theory {
    let mut theory = Theory::new();
    assert!(define_terms_in_theory(&mut theory));
    theory
}

pub fn define_in_theory(theory: &mut Theory) -> bool {
    let Ok(module) = list::module() else {
        return false;
    };

    define_module_terms(theory, &module) && define_module_theorems(theory, &module)
}

pub fn define_terms_in_theory(theory: &mut Theory) -> bool {
    let Ok(module) = list::module() else {
        return false;
    };

    define_module_terms(theory, &module)
}

fn define_module_terms(theory: &mut Theory, module: &source::ParsedModule) -> bool {
    module
        .terms
        .iter()
        .cloned()
        .all(|(name, term)| theory.define_term(name, &term))
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
    let theory = term_theory();
    reverse_acc_computes_to_list_in_theory(&theory)
}

fn reverse_acc_computes_to_list_in_theory(theory: &Theory) -> Option<Theorem> {
    theory.from_proof(
        list::reverse_acc_computes_to_list_source_proof(),
        list::reverse_acc_computes_to_list_source_theorem(),
    )
}

pub fn reverse_computes_to_list() -> Option<Theorem> {
    let theory = term_theory();
    reverse_computes_to_list_in_theory(&theory)
}

fn reverse_computes_to_list_in_theory(theory: &Theory) -> Option<Theorem> {
    theory.from_proof(
        list::reverse_computes_to_list_source_proof(),
        list::reverse_computes_to_list_source_theorem(),
    )
}

pub fn reverse_acc() -> Term {
    Term::Const(REVERSE_ACC)
}

pub fn reverse() -> Term {
    Term::Const(REVERSE)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Step, computes_to_list};

    #[test]
    fn theory_defines_reverse() {
        let theory = theory();

        assert_eq!(
            theory.term(REVERSE_ACC),
            Some(&list::reverse_acc_definition())
        );
        assert_eq!(theory.term(REVERSE), Some(&list::reverse_definition()));
        assert_eq!(reverse_acc(), Term::Const(REVERSE_ACC));
        assert_eq!(reverse(), Term::Const(REVERSE));
        assert_eq!(
            theory.reduce(&reverse_acc()),
            Step::Reduced(list::reverse_acc_definition())
        );
        assert_eq!(
            theory.reduce(&reverse()),
            Step::Reduced(list::reverse_definition())
        );
    }

    #[test]
    fn term_theory_does_not_define_theorems() {
        let theory = term_theory();

        assert!(theory.theorem(REVERSE_ACC_COMPUTES_TO_LIST).is_none());
        assert!(theory.theorem(REVERSE_COMPUTES_TO_LIST).is_none());
    }

    #[test]
    fn theorem_definitions_require_terms() {
        let mut theory = Theory::new();

        assert!(!define_theorems_in_theory(&mut theory));
        assert!(theory.theorem(REVERSE_ACC_COMPUTES_TO_LIST).is_none());
        assert!(theory.theorem(REVERSE_COMPUTES_TO_LIST).is_none());
    }

    #[test]
    fn theory_defines_reverse_theorems() {
        let theory = theory();
        let reverse_acc_prop = list::reverse_acc_computes_to_list_source_theorem();
        let reverse_prop = list::reverse_computes_to_list_source_theorem();

        assert_eq!(
            theory.theorem(REVERSE_ACC_COMPUTES_TO_LIST),
            Some(&reverse_acc_prop)
        );
        assert_eq!(
            theory.theorem(REVERSE_COMPUTES_TO_LIST),
            Some(&reverse_prop)
        );
        assert_eq!(
            theory
                .known(REVERSE_COMPUTES_TO_LIST)
                .expect("reverse theorem should be defined")
                .prop(),
            &reverse_prop,
        );
    }

    #[test]
    fn prelude_theory_instantiates_named_reverse_theorem() {
        let theory = theory();
        let reverse = theory
            .known(REVERSE_COMPUTES_TO_LIST)
            .expect("reverse theorem should be defined");
        let instantiated = theory
            .forall_elim(&reverse, list::nil())
            .expect("known theorem should instantiate in its theory");
        let conclusion = theory
            .implies_elim(&instantiated, &theory.list_nil())
            .expect("nil is a list, so reverse nil computes to a list");

        assert_eq!(
            conclusion.prop(),
            &computes_to_list(
                list::reverse_computes_to_list_source_result_symbol(),
                list::reverse_call(list::nil()),
            )
        );
    }
}
