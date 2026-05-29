//! Standard definitions layered on top of the kernel.

pub mod list;

use crate::{Environment, Name, Term};

pub const REVERSE_ACC: Name = Name(1);
pub const REVERSE: Name = Name(2);

pub fn environment() -> Environment {
    let mut environment = Environment::new();
    assert!(define(&mut environment));
    environment
}

pub fn define(environment: &mut Environment) -> bool {
    environment.define_term(REVERSE_ACC, &list::reverse_acc_definition())
        && environment.define_term(REVERSE, &list::reverse_definition())
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
    use crate::{Step, step_in_environment};

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
}
