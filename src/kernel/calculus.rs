use std::collections::HashSet;

#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct Name(pub u64);

#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct Symbol(pub u64);

#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct ErrorName(pub u64);

pub const RUNTIME_ERROR: ErrorName = ErrorName(0);

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Lambda {
    pub parameter: Symbol,
    pub body: Box<Computation>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ListCase {
    pub list: Box<Computation>,
    pub nil: Box<Computation>,
    pub cons: Symbol,
    pub cons_case: Box<Computation>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Computation {
    Apply {
        function: Box<Computation>,
        argument: Box<Computation>,
    },
    Lambda(Lambda),
    Nil,
    Cons {
        head: Box<Computation>,
        tail: Box<Computation>,
    },
    Head(Box<Computation>),
    Tail(Box<Computation>),
    ListCase(ListCase),
    Ref(Name),
    Error(ErrorName),
    Diverge,
    Var(Symbol),
    Quote(Symbol),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Value {
    Lambda(Lambda),
    List(ListValue),
    Quote(Symbol),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ListValue {
    Nil,
    Cons {
        head: Box<Value>,
        tail: Box<ListValue>,
    },
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Effect {
    Error(ErrorName),
    Diverge,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Outcome {
    Value(Value),
    Effect(Effect),
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Sort {
    Computation,
    Value,
    List,
    Effect,
    Outcome,
}

impl Computation {
    pub fn as_list_value(&self) -> Option<ListValue> {
        match self {
            Self::Nil => Some(ListValue::Nil),
            Self::Cons { head, tail } => Some(ListValue::Cons {
                head: Box::new(head.as_value()?),
                tail: Box::new(tail.as_list_value()?),
            }),
            _ => None,
        }
    }

    pub fn as_value(&self) -> Option<Value> {
        match self {
            Self::Lambda(lambda) => Some(Value::Lambda(lambda.clone())),
            Self::Nil | Self::Cons { .. } => self.as_list_value().map(Value::List),
            Self::Quote(symbol) => Some(Value::Quote(*symbol)),
            _ => None,
        }
    }

    pub fn as_effect(&self) -> Option<Effect> {
        match self {
            Self::Error(name) => Some(Effect::Error(*name)),
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
    pub fn lambda(lambda: Lambda) -> Self {
        Self::Lambda(lambda)
    }

    pub fn list(list: ListValue) -> Self {
        Self::List(list)
    }

    pub fn nil() -> Self {
        Self::list(ListValue::Nil)
    }

    pub fn cons(head: Self, tail: ListValue) -> Self {
        Self::list(ListValue::cons(head, tail))
    }

    pub fn quote(symbol: Symbol) -> Self {
        Self::Quote(symbol)
    }

    pub fn into_computation(self) -> Computation {
        match self {
            Self::Lambda(lambda) => Computation::Lambda(lambda),
            Self::List(list) => list.into_computation(),
            Self::Quote(symbol) => Computation::Quote(symbol),
        }
    }
}

impl ListValue {
    pub fn nil() -> Self {
        Self::Nil
    }

    pub fn cons(head: Value, tail: Self) -> Self {
        Self::Cons {
            head: Box::new(head),
            tail: Box::new(tail),
        }
    }

    pub fn into_computation(self) -> Computation {
        match self {
            Self::Nil => Computation::Nil,
            Self::Cons { head, tail } => Computation::Cons {
                head: Box::new(head.into_computation()),
                tail: Box::new(tail.into_computation()),
            },
        }
    }
}

impl Effect {
    pub fn error(name: ErrorName) -> Self {
        Self::Error(name)
    }

    pub fn diverge() -> Self {
        Self::Diverge
    }

    pub fn into_computation(self) -> Computation {
        match self {
            Self::Error(name) => Computation::Error(name),
            Self::Diverge => Computation::Diverge,
        }
    }
}

impl Outcome {
    pub fn value(value: Value) -> Self {
        Self::Value(value)
    }

    pub fn effect(effect: Effect) -> Self {
        Self::Effect(effect)
    }

    pub fn into_computation(self) -> Computation {
        match self {
            Self::Value(value) => value.into_computation(),
            Self::Effect(effect) => effect.into_computation(),
        }
    }
}

impl From<Value> for Computation {
    fn from(value: Value) -> Self {
        value.into_computation()
    }
}

impl From<ListValue> for Computation {
    fn from(list: ListValue) -> Self {
        list.into_computation()
    }
}

impl From<ListValue> for Value {
    fn from(list: ListValue) -> Self {
        Self::List(list)
    }
}

impl From<Effect> for Computation {
    fn from(effect: Effect) -> Self {
        effect.into_computation()
    }
}

impl From<Outcome> for Computation {
    fn from(outcome: Outcome) -> Self {
        outcome.into_computation()
    }
}

impl From<Value> for Outcome {
    fn from(value: Value) -> Self {
        Self::Value(value)
    }
}

impl From<Effect> for Outcome {
    fn from(effect: Effect) -> Self {
        Self::Effect(effect)
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Step {
    Reduced(Computation),
    Normal,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Prop {
    Equal(Computation, Computation),
    Implies(Box<Prop>, Box<Prop>),
    ForAll {
        variable: Symbol,
        sort: Sort,
        body: Box<Prop>,
    },
    Exists {
        variable: Symbol,
        sort: Sort,
        body: Box<Prop>,
    },
    And(Box<Prop>, Box<Prop>),
    Or(Box<Prop>, Box<Prop>),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Proof {
    Known(Name),
    Assume(Symbol),
    Refl(Computation),
    Symm(Box<Proof>),
    Trans(Box<Proof>, Box<Proof>),
    Step(Computation),
    Steps(Vec<Computation>),
    Rewrite {
        equality: Box<Proof>,
        proof: Box<Proof>,
        variable: Symbol,
        template: Prop,
    },
    ListInduction {
        variable: Symbol,
        property: Prop,
        base: Box<Proof>,
        head: Symbol,
        tail: Symbol,
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
        sort: Sort,
        proof: Box<Proof>,
    },
    ForAllElim {
        forall: Box<Proof>,
        argument: Computation,
    },
    ExistsIntro {
        variable: Symbol,
        sort: Sort,
        body: Prop,
        witness: Computation,
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

pub fn equal(left: Computation, right: Computation) -> Prop {
    Prop::Equal(left, right)
}

pub fn implies(premise: Prop, conclusion: Prop) -> Prop {
    Prop::Implies(Box::new(premise), Box::new(conclusion))
}

pub fn forall(variable: Symbol, body: Prop) -> Prop {
    forall_sort(variable, Sort::Computation, body)
}

pub fn forall_sort(variable: Symbol, sort: Sort, body: Prop) -> Prop {
    Prop::ForAll {
        variable,
        sort,
        body: Box::new(body),
    }
}

pub fn exists(variable: Symbol, body: Prop) -> Prop {
    exists_sort(variable, Sort::Computation, body)
}

pub fn exists_sort(variable: Symbol, sort: Sort, body: Prop) -> Prop {
    Prop::Exists {
        variable,
        sort,
        body: Box::new(body),
    }
}

pub fn exists_value(variable: Symbol, body: Prop) -> Prop {
    exists_sort(variable, Sort::Value, body)
}

pub fn and(left: Prop, right: Prop) -> Prop {
    Prop::And(Box::new(left), Box::new(right))
}

pub fn or(left: Prop, right: Prop) -> Prop {
    Prop::Or(Box::new(left), Box::new(right))
}

pub fn computes_to(computation: Computation, target: Computation) -> Prop {
    equal(computation, target)
}

pub fn computes_to_value(computation: Computation, value: Value) -> Prop {
    computes_to(computation, value.into())
}

pub fn computes_to_effect(computation: Computation, effect: Effect) -> Prop {
    computes_to(computation, effect.into())
}

pub fn computes_to_outcome(computation: Computation, outcome: impl Into<Outcome>) -> Prop {
    computes_to(computation, outcome.into().into())
}

/// `variable` names the existential result and should be fresh for `computation`.
pub fn terminates(variable: Symbol, computation: Computation) -> Prop {
    exists_value(
        variable,
        computes_to(computation, Computation::Var(variable)),
    )
}

/// `variable` names the existential list value and should be fresh for `computation`.
pub fn computes_to_list(variable: Symbol, computation: Computation) -> Prop {
    exists_sort(
        variable,
        Sort::List,
        computes_to(computation, Computation::Var(variable)),
    )
}

pub fn errors_with(computation: Computation, error: ErrorName) -> Prop {
    computes_to_effect(computation, Effect::error(error))
}

pub fn diverges(computation: Computation) -> Prop {
    computes_to_effect(computation, Effect::diverge())
}

pub fn substitute(
    computation: &Computation,
    variable: Symbol,
    replacement: &Computation,
) -> Computation {
    match computation {
        Computation::Apply { function, argument } => Computation::Apply {
            function: Box::new(substitute(function, variable, replacement)),
            argument: Box::new(substitute(argument, variable, replacement)),
        },
        Computation::Lambda(lambda) => {
            if lambda.parameter == variable {
                return computation.clone();
            }

            if free_symbols(replacement).contains(&lambda.parameter) {
                let fresh = fresh_symbol(computation, replacement, variable);
                let body = rename_bound_var(lambda.body.as_ref(), lambda.parameter, fresh);
                return Computation::Lambda(Lambda {
                    parameter: fresh,
                    body: Box::new(substitute(&body, variable, replacement)),
                });
            }

            Computation::Lambda(Lambda {
                parameter: lambda.parameter,
                body: Box::new(substitute(lambda.body.as_ref(), variable, replacement)),
            })
        }
        Computation::Nil => Computation::Nil,
        Computation::Cons { head, tail } => Computation::Cons {
            head: Box::new(substitute(head, variable, replacement)),
            tail: Box::new(substitute(tail, variable, replacement)),
        },
        Computation::Head(computation) => {
            Computation::Head(Box::new(substitute(computation, variable, replacement)))
        }
        Computation::Tail(computation) => {
            Computation::Tail(Box::new(substitute(computation, variable, replacement)))
        }
        Computation::ListCase(list_case) => {
            Computation::ListCase(substitute_list_case(list_case, variable, replacement))
        }
        Computation::Error(error) => Computation::Error(*error),
        Computation::Ref(_)
        | Computation::Diverge
        | Computation::Var(_)
        | Computation::Quote(_) => {
            if computation == &Computation::Var(variable) {
                replacement.clone()
            } else {
                computation.clone()
            }
        }
    }
}

fn substitute_list_case(
    list_case: &ListCase,
    variable: Symbol,
    replacement: &Computation,
) -> ListCase {
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
        let fresh = fresh_symbol(
            &Computation::ListCase(list_case.clone()),
            replacement,
            variable,
        );
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

pub fn free_symbols(computation: &Computation) -> HashSet<Symbol> {
    let mut symbols = HashSet::new();
    add_free_symbols(computation, &mut symbols);
    symbols
}

pub(super) fn add_free_symbols(computation: &Computation, symbols: &mut HashSet<Symbol>) {
    match computation {
        Computation::Apply { function, argument } => {
            add_free_symbols(function, symbols);
            add_free_symbols(argument, symbols);
        }
        Computation::Lambda(lambda) => {
            let mut body_symbols = HashSet::new();
            add_free_symbols(lambda.body.as_ref(), &mut body_symbols);
            body_symbols.remove(&lambda.parameter);
            symbols.extend(body_symbols);
        }
        Computation::Nil => {}
        Computation::Cons { head, tail } => {
            add_free_symbols(head, symbols);
            add_free_symbols(tail, symbols);
        }
        Computation::Head(computation) | Computation::Tail(computation) => {
            add_free_symbols(computation, symbols);
        }
        Computation::ListCase(list_case) => {
            add_free_symbols(list_case.list.as_ref(), symbols);
            add_free_symbols(list_case.nil.as_ref(), symbols);

            let mut cons_case_symbols = HashSet::new();
            add_free_symbols(list_case.cons_case.as_ref(), &mut cons_case_symbols);
            cons_case_symbols.remove(&list_case.cons);
            symbols.extend(cons_case_symbols);
        }
        Computation::Error(_) | Computation::Ref(_) | Computation::Diverge => {}
        Computation::Var(symbol) => {
            symbols.insert(*symbol);
        }
        Computation::Quote(_) => {}
    }
}

pub(super) fn rename_bound_var(computation: &Computation, old: Symbol, new: Symbol) -> Computation {
    match computation {
        Computation::Apply { function, argument } => Computation::Apply {
            function: Box::new(rename_bound_var(function, old, new)),
            argument: Box::new(rename_bound_var(argument, old, new)),
        },
        Computation::Lambda(lambda) if lambda.parameter == old => {
            Computation::Lambda(lambda.clone())
        }
        Computation::Lambda(lambda) => Computation::Lambda(Lambda {
            parameter: lambda.parameter,
            body: Box::new(rename_bound_var(lambda.body.as_ref(), old, new)),
        }),
        Computation::Nil => Computation::Nil,
        Computation::Cons { head, tail } => Computation::Cons {
            head: Box::new(rename_bound_var(head, old, new)),
            tail: Box::new(rename_bound_var(tail, old, new)),
        },
        Computation::Head(computation) => {
            Computation::Head(Box::new(rename_bound_var(computation, old, new)))
        }
        Computation::Tail(computation) => {
            Computation::Tail(Box::new(rename_bound_var(computation, old, new)))
        }
        Computation::ListCase(list_case) => Computation::ListCase(ListCase {
            list: Box::new(rename_bound_var(list_case.list.as_ref(), old, new)),
            nil: Box::new(rename_bound_var(list_case.nil.as_ref(), old, new)),
            cons: list_case.cons,
            cons_case: if list_case.cons == old {
                list_case.cons_case.clone()
            } else {
                Box::new(rename_bound_var(list_case.cons_case.as_ref(), old, new))
            },
        }),
        Computation::Error(error) => Computation::Error(*error),
        Computation::Ref(_) | Computation::Diverge => computation.clone(),
        Computation::Var(symbol) if *symbol == old => Computation::Var(new),
        Computation::Var(_) | Computation::Quote(_) => computation.clone(),
    }
}

pub(super) fn fresh_symbol(
    computation: &Computation,
    replacement: &Computation,
    variable: Symbol,
) -> Symbol {
    let mut symbols = HashSet::new();
    add_all_symbols(computation, &mut symbols);
    add_all_symbols(replacement, &mut symbols);
    symbols.insert(variable);

    let mut symbol = Symbol(0);
    while symbols.contains(&symbol) {
        symbol = Symbol(symbol.0 + 1);
    }
    symbol
}

pub(super) fn add_all_symbols(computation: &Computation, symbols: &mut HashSet<Symbol>) {
    match computation {
        Computation::Apply { function, argument } => {
            add_all_symbols(function, symbols);
            add_all_symbols(argument, symbols);
        }
        Computation::Lambda(lambda) => {
            symbols.insert(lambda.parameter);
            add_all_symbols(lambda.body.as_ref(), symbols);
        }
        Computation::Nil => {}
        Computation::Cons { head, tail } => {
            add_all_symbols(head, symbols);
            add_all_symbols(tail, symbols);
        }
        Computation::Head(computation) | Computation::Tail(computation) => {
            add_all_symbols(computation, symbols);
        }
        Computation::ListCase(list_case) => {
            add_all_symbols(list_case.list.as_ref(), symbols);
            add_all_symbols(list_case.nil.as_ref(), symbols);
            symbols.insert(list_case.cons);
            add_all_symbols(list_case.cons_case.as_ref(), symbols);
        }
        Computation::Error(_) | Computation::Ref(_) | Computation::Diverge => {}
        Computation::Var(symbol) | Computation::Quote(symbol) => {
            symbols.insert(*symbol);
        }
    }
}
