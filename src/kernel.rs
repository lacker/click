use std::collections::HashMap;

pub type Symbol = u64;

pub type Env = HashMap<Symbol, Value>;

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Lambda {
    pub parameter: Symbol,
    pub body: Box<Term>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Term {
    Apply {
        function: Box<Term>,
        argument: Box<Term>,
    },
    Lambda(Lambda),
    Var(Symbol),
    Quote(Symbol),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Closure {
    pub lambda: Lambda,
    pub env: Env,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Value {
    Symbol(Symbol),
    Closure(Closure),
}

pub type EvalResult<T> = Result<T, EvalError>;

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum EvalError {
    UnboundVar(Symbol),
    ApplyNonClosure(Value),
}

pub fn eval(term: &Term, env: &Env) -> EvalResult<Value> {
    match term {
        Term::Apply { function, argument } => match eval(function, env)? {
            Value::Closure(Closure {
                lambda,
                env: mut closure_env,
            }) => {
                let argument = eval(argument, env)?;
                closure_env.insert(lambda.parameter, argument);
                eval(lambda.body.as_ref(), &closure_env)
            }
            value => Err(EvalError::ApplyNonClosure(value)),
        },
        Term::Lambda(lambda) => Ok(Value::Closure(Closure {
            lambda: lambda.clone(),
            env: env.clone(),
        })),
        Term::Var(symbol) => env
            .get(symbol)
            .cloned()
            .ok_or(EvalError::UnboundVar(*symbol)),
        Term::Quote(symbol) => Ok(Value::Symbol(*symbol)),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn lambda(parameter: Symbol, body: Term) -> Term {
        Term::Lambda(Lambda {
            parameter,
            body: Box::new(body),
        })
    }

    fn apply(function: Term, argument: Term) -> Term {
        Term::Apply {
            function: Box::new(function),
            argument: Box::new(argument),
        }
    }

    #[test]
    fn quote_evaluates_to_symbol() {
        assert_eq!(eval(&Term::Quote(7), &Env::new()), Ok(Value::Symbol(7)));
    }

    #[test]
    fn identity_lambda_returns_argument() {
        let term = apply(lambda(1, Term::Var(1)), Term::Quote(2));

        assert_eq!(eval(&term, &Env::new()), Ok(Value::Symbol(2)));
    }

    #[test]
    fn closure_captures_definition_environment() {
        let mut env = Env::new();
        env.insert(1, Value::Symbol(10));

        let closure = eval(&lambda(2, Term::Var(1)), &env).unwrap();

        env.insert(1, Value::Symbol(20));
        env.insert(3, closure);

        let term = apply(Term::Var(3), Term::Quote(0));

        assert_eq!(eval(&term, &env), Ok(Value::Symbol(10)));
    }

    #[test]
    fn unbound_variable_is_an_error() {
        assert_eq!(
            eval(&Term::Var(1), &Env::new()),
            Err(EvalError::UnboundVar(1))
        );
    }
}
