//! Standard definitions layered on top of the kernel.

use crate::{Environment, Name, Term, list_example};

pub const REVERSE_ACC: Name = Name(1);

pub fn environment() -> Environment {
    let mut environment = Environment::new();
    assert!(define(&mut environment));
    environment
}

pub fn define(environment: &mut Environment) -> bool {
    environment.define_term(REVERSE_ACC, &list_example::reverse_acc_definition())
}

pub fn reverse_acc() -> Term {
    Term::Const(REVERSE_ACC)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Step, step_in_environment};

    #[test]
    fn environment_defines_reverse_acc() {
        let env = environment();

        assert_eq!(
            env.term(REVERSE_ACC),
            Some(&list_example::reverse_acc_definition())
        );
        assert_eq!(reverse_acc(), Term::Const(REVERSE_ACC));
        assert_eq!(
            step_in_environment(&reverse_acc(), &env),
            Step::Reduced(list_example::reverse_acc_definition())
        );
    }
}
