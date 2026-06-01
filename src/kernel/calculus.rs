use std::collections::HashSet;

#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct Name(pub u64);

#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct Symbol(pub u64);

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Lambda {
    pub parameter: Symbol,
    pub body: Box<Term>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ListCase {
    pub list: Box<Term>,
    pub nil: Box<Term>,
    pub cons: Symbol,
    pub cons_case: Box<Term>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Computation {
    Apply {
        function: Box<Term>,
        argument: Box<Term>,
    },
    Lambda(Lambda),
    Nil,
    Cons {
        head: Box<Term>,
        tail: Box<Term>,
    },
    Head(Box<Term>),
    Tail(Box<Term>),
    ListCase(ListCase),
    Const(Name),
    Error(Box<Term>),
    Diverge,
    Var(Symbol),
    Quote(Symbol),
}

pub use Computation as Term;

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Value {
    Lambda(Lambda),
    Nil,
    Cons { head: Box<Value>, tail: Box<Value> },
    Quote(Symbol),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Effect {
    Error(Box<Computation>),
    Diverge,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Outcome {
    Value(Value),
    Effect(Effect),
}

impl Computation {
    pub fn as_value(&self) -> Option<Value> {
        match self {
            Self::Lambda(lambda) => Some(Value::Lambda(lambda.clone())),
            Self::Nil => Some(Value::Nil),
            Self::Cons { head, tail } => Some(Value::Cons {
                head: Box::new(head.as_value()?),
                tail: Box::new(tail.as_value()?),
            }),
            Self::Quote(symbol) => Some(Value::Quote(*symbol)),
            _ => None,
        }
    }

    pub fn as_effect(&self) -> Option<Effect> {
        match self {
            Self::Error(payload) => Some(Effect::Error(payload.clone())),
            Self::Diverge => Some(Effect::Diverge),
            _ => None,
        }
    }

    pub fn as_outcome(&self) -> Option<Outcome> {
        if let Some(value) = self.as_value() {
            return Some(Outcome::Value(value));
        }

        self.as_effect().map(Outcome::Effect)
    }
}

impl Value {
    pub fn into_computation(self) -> Computation {
        match self {
            Self::Lambda(lambda) => Computation::Lambda(lambda),
            Self::Nil => Computation::Nil,
            Self::Cons { head, tail } => Computation::Cons {
                head: Box::new(head.into_computation()),
                tail: Box::new(tail.into_computation()),
            },
            Self::Quote(symbol) => Computation::Quote(symbol),
        }
    }
}

impl Effect {
    pub fn into_computation(self) -> Computation {
        match self {
            Self::Error(payload) => Computation::Error(payload),
            Self::Diverge => Computation::Diverge,
        }
    }
}

impl Outcome {
    pub fn into_computation(self) -> Computation {
        match self {
            Self::Value(value) => value.into_computation(),
            Self::Effect(effect) => effect.into_computation(),
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Step {
    Reduced(Term),
    Normal,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Prop {
    Equal(Term, Term),
    IsValue(Term),
    IsList(Term),
    Implies(Box<Prop>, Box<Prop>),
    ForAll { variable: Symbol, body: Box<Prop> },
    Exists { variable: Symbol, body: Box<Prop> },
    And(Box<Prop>, Box<Prop>),
    Or(Box<Prop>, Box<Prop>),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Proof {
    Known(Name),
    Assume(Symbol),
    Refl(Term),
    Symm(Box<Proof>),
    Trans(Box<Proof>, Box<Proof>),
    Step(Term),
    Steps(Vec<Term>),
    Rewrite {
        equality: Box<Proof>,
        proof: Box<Proof>,
        variable: Symbol,
        template: Prop,
    },
    Beta {
        lambda: Lambda,
        argument: Term,
    },
    ValueLambda(Lambda),
    ValueQuote(Symbol),
    ValueNil,
    ValueCons {
        head: Term,
        tail: Term,
        head_is_value: Box<Proof>,
        tail_is_value: Box<Proof>,
    },
    ListNil,
    ListCons {
        head: Term,
        tail: Term,
        head_is_value: Box<Proof>,
        tail_is_list: Box<Proof>,
    },
    ListInduction {
        variable: Symbol,
        property: Prop,
        base: Box<Proof>,
        head: Symbol,
        tail: Symbol,
        head_is_value_assumption: Symbol,
        tail_is_list_assumption: Symbol,
        induction_hypothesis_assumption: Symbol,
        step: Box<Proof>,
    },
    ImpliesIntro {
        assumption: Symbol,
        premise: Prop,
        proof: Box<Proof>,
    },
    ImpliesElim {
        implication: Box<Proof>,
        premise: Box<Proof>,
    },
    ForAllIntro {
        variable: Symbol,
        proof: Box<Proof>,
    },
    ForAllElim {
        forall: Box<Proof>,
        argument: Term,
    },
    ExistsIntro {
        variable: Symbol,
        body: Prop,
        witness: Term,
        proof: Box<Proof>,
    },
    ExistsElim {
        existential: Box<Proof>,
        witness: Symbol,
        assumption: Symbol,
        proof: Box<Proof>,
    },
    AndIntro(Box<Proof>, Box<Proof>),
    AndElimLeft(Box<Proof>),
    AndElimRight(Box<Proof>),
    OrIntroLeft {
        proof: Box<Proof>,
        right: Prop,
    },
    OrIntroRight {
        left: Prop,
        proof: Box<Proof>,
    },
    OrElim {
        disjunction: Box<Proof>,
        left_assumption: Symbol,
        left_proof: Box<Proof>,
        right_assumption: Symbol,
        right_proof: Box<Proof>,
    },
}

pub fn equal(left: Term, right: Term) -> Prop {
    Prop::Equal(left, right)
}

pub fn is_value(term: Term) -> Prop {
    Prop::IsValue(term)
}

pub fn is_list(term: Term) -> Prop {
    Prop::IsList(term)
}

pub fn implies(premise: Prop, conclusion: Prop) -> Prop {
    Prop::Implies(Box::new(premise), Box::new(conclusion))
}

pub fn forall(variable: Symbol, body: Prop) -> Prop {
    Prop::ForAll {
        variable,
        body: Box::new(body),
    }
}

pub fn exists(variable: Symbol, body: Prop) -> Prop {
    Prop::Exists {
        variable,
        body: Box::new(body),
    }
}

pub fn and(left: Prop, right: Prop) -> Prop {
    Prop::And(Box::new(left), Box::new(right))
}

pub fn or(left: Prop, right: Prop) -> Prop {
    Prop::Or(Box::new(left), Box::new(right))
}

pub fn computes_to(term: Term, value: Term) -> Prop {
    equal(term, value)
}

/// `variable` names the existential result and should be fresh for `term`.
pub fn terminates(variable: Symbol, term: Term) -> Prop {
    exists(
        variable,
        and(
            computes_to(term, Term::Var(variable)),
            is_value(Term::Var(variable)),
        ),
    )
}

/// `variable` names the existential list value and should be fresh for `term`.
pub fn computes_to_list(variable: Symbol, term: Term) -> Prop {
    exists(
        variable,
        and(
            computes_to(term, Term::Var(variable)),
            is_list(Term::Var(variable)),
        ),
    )
}

/// `variable` names the existential error payload and should be fresh for `term`.
pub fn errors(variable: Symbol, term: Term) -> Prop {
    exists(
        variable,
        computes_to(term, Term::Error(Box::new(Term::Var(variable)))),
    )
}

pub fn diverges(term: Term) -> Prop {
    computes_to(term, Term::Diverge)
}

pub fn substitute(term: &Term, variable: Symbol, replacement: &Term) -> Term {
    match term {
        Term::Apply { function, argument } => Term::Apply {
            function: Box::new(substitute(function, variable, replacement)),
            argument: Box::new(substitute(argument, variable, replacement)),
        },
        Term::Lambda(lambda) => {
            if lambda.parameter == variable {
                return term.clone();
            }

            if free_symbols(replacement).contains(&lambda.parameter) {
                let fresh = fresh_symbol(term, replacement, variable);
                let body = rename_bound_var(lambda.body.as_ref(), lambda.parameter, fresh);
                return Term::Lambda(Lambda {
                    parameter: fresh,
                    body: Box::new(substitute(&body, variable, replacement)),
                });
            }

            Term::Lambda(Lambda {
                parameter: lambda.parameter,
                body: Box::new(substitute(lambda.body.as_ref(), variable, replacement)),
            })
        }
        Term::Nil => Term::Nil,
        Term::Cons { head, tail } => Term::Cons {
            head: Box::new(substitute(head, variable, replacement)),
            tail: Box::new(substitute(tail, variable, replacement)),
        },
        Term::Head(term) => Term::Head(Box::new(substitute(term, variable, replacement))),
        Term::Tail(term) => Term::Tail(Box::new(substitute(term, variable, replacement))),
        Term::ListCase(list_case) => {
            Term::ListCase(substitute_list_case(list_case, variable, replacement))
        }
        Term::Error(error) => Term::Error(Box::new(substitute(error, variable, replacement))),
        Term::Const(_) | Term::Diverge | Term::Var(_) | Term::Quote(_) => {
            if term == &Term::Var(variable) {
                replacement.clone()
            } else {
                term.clone()
            }
        }
    }
}

fn substitute_list_case(list_case: &ListCase, variable: Symbol, replacement: &Term) -> ListCase {
    let list = Box::new(substitute(list_case.list.as_ref(), variable, replacement));
    let nil = Box::new(substitute(list_case.nil.as_ref(), variable, replacement));

    if list_case.cons == variable {
        return ListCase {
            list,
            nil,
            cons: list_case.cons,
            cons_case: list_case.cons_case.clone(),
        };
    }

    let mut cons = list_case.cons;
    let mut cons_case = list_case.cons_case.as_ref().clone();

    if free_symbols(replacement).contains(&cons) {
        let fresh = fresh_symbol(&Term::ListCase(list_case.clone()), replacement, variable);
        cons_case = rename_bound_var(&cons_case, cons, fresh);
        cons = fresh;
    }

    ListCase {
        list,
        nil,
        cons,
        cons_case: Box::new(substitute(&cons_case, variable, replacement)),
    }
}

pub fn free_symbols(term: &Term) -> HashSet<Symbol> {
    let mut symbols = HashSet::new();
    add_free_symbols(term, &mut symbols);
    symbols
}

pub(super) fn add_free_symbols(term: &Term, symbols: &mut HashSet<Symbol>) {
    match term {
        Term::Apply { function, argument } => {
            add_free_symbols(function, symbols);
            add_free_symbols(argument, symbols);
        }
        Term::Lambda(lambda) => {
            let mut body_symbols = HashSet::new();
            add_free_symbols(lambda.body.as_ref(), &mut body_symbols);
            body_symbols.remove(&lambda.parameter);
            symbols.extend(body_symbols);
        }
        Term::Nil => {}
        Term::Cons { head, tail } => {
            add_free_symbols(head, symbols);
            add_free_symbols(tail, symbols);
        }
        Term::Head(term) | Term::Tail(term) => {
            add_free_symbols(term, symbols);
        }
        Term::ListCase(list_case) => {
            add_free_symbols(list_case.list.as_ref(), symbols);
            add_free_symbols(list_case.nil.as_ref(), symbols);

            let mut cons_case_symbols = HashSet::new();
            add_free_symbols(list_case.cons_case.as_ref(), &mut cons_case_symbols);
            cons_case_symbols.remove(&list_case.cons);
            symbols.extend(cons_case_symbols);
        }
        Term::Error(error) => {
            add_free_symbols(error, symbols);
        }
        Term::Const(_) | Term::Diverge => {}
        Term::Var(symbol) => {
            symbols.insert(*symbol);
        }
        Term::Quote(_) => {}
    }
}

pub(super) fn rename_bound_var(term: &Term, old: Symbol, new: Symbol) -> Term {
    match term {
        Term::Apply { function, argument } => Term::Apply {
            function: Box::new(rename_bound_var(function, old, new)),
            argument: Box::new(rename_bound_var(argument, old, new)),
        },
        Term::Lambda(lambda) if lambda.parameter == old => Term::Lambda(lambda.clone()),
        Term::Lambda(lambda) => Term::Lambda(Lambda {
            parameter: lambda.parameter,
            body: Box::new(rename_bound_var(lambda.body.as_ref(), old, new)),
        }),
        Term::Nil => Term::Nil,
        Term::Cons { head, tail } => Term::Cons {
            head: Box::new(rename_bound_var(head, old, new)),
            tail: Box::new(rename_bound_var(tail, old, new)),
        },
        Term::Head(term) => Term::Head(Box::new(rename_bound_var(term, old, new))),
        Term::Tail(term) => Term::Tail(Box::new(rename_bound_var(term, old, new))),
        Term::ListCase(list_case) => Term::ListCase(ListCase {
            list: Box::new(rename_bound_var(list_case.list.as_ref(), old, new)),
            nil: Box::new(rename_bound_var(list_case.nil.as_ref(), old, new)),
            cons: list_case.cons,
            cons_case: if list_case.cons == old {
                list_case.cons_case.clone()
            } else {
                Box::new(rename_bound_var(list_case.cons_case.as_ref(), old, new))
            },
        }),
        Term::Error(error) => Term::Error(Box::new(rename_bound_var(error, old, new))),
        Term::Const(_) | Term::Diverge => term.clone(),
        Term::Var(symbol) if *symbol == old => Term::Var(new),
        Term::Var(_) | Term::Quote(_) => term.clone(),
    }
}

pub(super) fn fresh_symbol(term: &Term, replacement: &Term, variable: Symbol) -> Symbol {
    let mut symbols = HashSet::new();
    add_all_symbols(term, &mut symbols);
    add_all_symbols(replacement, &mut symbols);
    symbols.insert(variable);

    let mut symbol = Symbol(0);
    while symbols.contains(&symbol) {
        symbol = Symbol(symbol.0 + 1);
    }
    symbol
}

pub(super) fn add_all_symbols(term: &Term, symbols: &mut HashSet<Symbol>) {
    match term {
        Term::Apply { function, argument } => {
            add_all_symbols(function, symbols);
            add_all_symbols(argument, symbols);
        }
        Term::Lambda(lambda) => {
            symbols.insert(lambda.parameter);
            add_all_symbols(lambda.body.as_ref(), symbols);
        }
        Term::Nil => {}
        Term::Cons { head, tail } => {
            add_all_symbols(head, symbols);
            add_all_symbols(tail, symbols);
        }
        Term::Head(term) | Term::Tail(term) => {
            add_all_symbols(term, symbols);
        }
        Term::ListCase(list_case) => {
            add_all_symbols(list_case.list.as_ref(), symbols);
            add_all_symbols(list_case.nil.as_ref(), symbols);
            symbols.insert(list_case.cons);
            add_all_symbols(list_case.cons_case.as_ref(), symbols);
        }
        Term::Error(error) => {
            add_all_symbols(error, symbols);
        }
        Term::Const(_) | Term::Diverge => {}
        Term::Var(symbol) | Term::Quote(symbol) => {
            symbols.insert(*symbol);
        }
    }
}
