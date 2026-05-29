//! Standard definitions layered on top of the kernel.

pub mod list;

use crate::{Environment, Name, Symbol, Term, Theorem};

pub const REVERSE_ACC: Name = Name(1);
pub const REVERSE: Name = Name(2);
pub const REVERSE_ACC_COMPUTES_TO_LIST: Name = Name(3);
pub const REVERSE_COMPUTES_TO_LIST: Name = Name(4);

const REVERSE_ACC_THEOREM_LIST: Symbol = Symbol(2_000);
const REVERSE_ACC_THEOREM_ACC: Symbol = Symbol(2_001);
const REVERSE_ACC_THEOREM_RESULT: Symbol = Symbol(2_002);
const REVERSE_THEOREM_LIST: Symbol = Symbol(2_003);
const REVERSE_THEOREM_RESULT: Symbol = Symbol(2_004);

pub fn environment() -> Environment {
    let mut environment = term_environment();
    assert!(define_theorems(&mut environment));
    environment
}

pub fn term_environment() -> Environment {
    let mut environment = Environment::new();
    assert!(define_terms(&mut environment));
    environment
}

pub fn define(environment: &mut Environment) -> bool {
    define_terms(environment) && define_theorems(environment)
}

pub fn define_terms(environment: &mut Environment) -> bool {
    environment.define_term(REVERSE_ACC, &list::reverse_acc_definition())
        && environment.define_term(REVERSE, &list::reverse_definition())
}

pub fn define_theorems(environment: &mut Environment) -> bool {
    let Some(reverse_acc) = reverse_acc_computes_to_list_in_environment(environment) else {
        return false;
    };
    let Some(reverse) = reverse_computes_to_list_in_environment(environment) else {
        return false;
    };

    environment.define_theorem(REVERSE_ACC_COMPUTES_TO_LIST, &reverse_acc)
        && environment.define_theorem(REVERSE_COMPUTES_TO_LIST, &reverse)
}

pub fn reverse_acc_computes_to_list() -> Option<Theorem> {
    let environment = term_environment();
    reverse_acc_computes_to_list_in_environment(&environment)
}

fn reverse_acc_computes_to_list_in_environment(environment: &Environment) -> Option<Theorem> {
    Theorem::from_proof_in_environment(
        list::reverse_acc_computes_to_list_proof(
            REVERSE_ACC_THEOREM_LIST,
            REVERSE_ACC_THEOREM_ACC,
            REVERSE_ACC_THEOREM_RESULT,
        ),
        list::reverse_acc_computes_to_list_theorem(
            REVERSE_ACC_THEOREM_LIST,
            REVERSE_ACC_THEOREM_ACC,
            REVERSE_ACC_THEOREM_RESULT,
        ),
        environment,
    )
}

pub fn reverse_computes_to_list() -> Option<Theorem> {
    let environment = term_environment();
    reverse_computes_to_list_in_environment(&environment)
}

fn reverse_computes_to_list_in_environment(environment: &Environment) -> Option<Theorem> {
    Theorem::from_proof_in_environment(
        list::reverse_computes_to_list_proof(REVERSE_THEOREM_LIST, REVERSE_THEOREM_RESULT),
        list::reverse_computes_to_list_theorem(REVERSE_THEOREM_LIST, REVERSE_THEOREM_RESULT),
        environment,
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
    use crate::{Proof, Step, Theorem, check_in_environment, step_in_environment};

    #[test]
    fn environment_defines_reverse() {
        let env = environment();

        assert_eq!(env.term(REVERSE_ACC), Some(&list::reverse_acc_definition()));
        assert_eq!(env.term(REVERSE), Some(&list::reverse_definition()));
        assert_eq!(reverse_acc(), Term::Const(REVERSE_ACC));
        assert_eq!(reverse(), Term::Const(REVERSE));
        assert_eq!(
            step_in_environment(&reverse_acc(), &env),
            Step::Reduced(list::reverse_acc_definition())
        );
        assert_eq!(
            step_in_environment(&reverse(), &env),
            Step::Reduced(list::reverse_definition())
        );
    }

    #[test]
    fn term_environment_does_not_define_theorems() {
        let env = term_environment();

        assert!(env.theorem(REVERSE_ACC_COMPUTES_TO_LIST).is_none());
        assert!(env.theorem(REVERSE_COMPUTES_TO_LIST).is_none());
    }

    #[test]
    fn theorem_definitions_require_terms() {
        let mut env = Environment::new();

        assert!(!define_theorems(&mut env));
        assert!(env.theorem(REVERSE_ACC_COMPUTES_TO_LIST).is_none());
        assert!(env.theorem(REVERSE_COMPUTES_TO_LIST).is_none());
    }

    #[test]
    fn environment_defines_reverse_theorems() {
        let env = environment();
        let reverse_acc_prop = list::reverse_acc_computes_to_list_theorem(
            REVERSE_ACC_THEOREM_LIST,
            REVERSE_ACC_THEOREM_ACC,
            REVERSE_ACC_THEOREM_RESULT,
        );
        let reverse_prop =
            list::reverse_computes_to_list_theorem(REVERSE_THEOREM_LIST, REVERSE_THEOREM_RESULT);

        assert_eq!(
            env.theorem(REVERSE_ACC_COMPUTES_TO_LIST),
            Some(&reverse_acc_prop)
        );
        assert_eq!(env.theorem(REVERSE_COMPUTES_TO_LIST), Some(&reverse_prop));
        assert!(check_in_environment(
            &Proof::Known(REVERSE_ACC_COMPUTES_TO_LIST),
            &reverse_acc_prop,
            &env,
        ));
        assert_eq!(
            Theorem::known(&env, REVERSE_COMPUTES_TO_LIST)
                .expect("reverse theorem should be defined")
                .prop(),
            &reverse_prop,
        );
    }
}
