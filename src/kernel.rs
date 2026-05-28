use std::collections::{HashMap, HashSet};

pub mod list_example;

pub type Symbol = u64;
pub type Context = HashMap<Symbol, Prop>;

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
pub enum Term {
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
    Error(Box<Term>),
    Diverge,
    Var(Symbol),
    Quote(Symbol),
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
    ReverseAccumulates { list: Term, acc: Term, result: Term },
    Implies(Box<Prop>, Box<Prop>),
    ForAll { variable: Symbol, body: Box<Prop> },
    Exists { variable: Symbol, body: Box<Prop> },
    And(Box<Prop>, Box<Prop>),
    Or(Box<Prop>, Box<Prop>),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Proof {
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
    ReverseAccNil {
        acc: Term,
    },
    ReverseAccCons {
        head: Term,
        tail: Term,
        acc: Term,
        result: Term,
        head_is_value: Box<Proof>,
        tail_reverse_acc: Box<Proof>,
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

pub fn reverse_accumulates(list: Term, acc: Term, result: Term) -> Prop {
    Prop::ReverseAccumulates { list, acc, result }
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

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Theorem {
    prop: Prop,
    proof: Proof,
}

impl Theorem {
    pub fn from_proof(proof: Proof, prop: Prop) -> Option<Self> {
        check(&proof, &prop).then_some(Self { prop, proof })
    }

    fn from_closed_proof(proof: Proof) -> Option<Self> {
        let prop = proven_prop(&proof, &Context::new())?;
        Some(Self { prop, proof })
    }

    pub fn prop(&self) -> &Prop {
        &self.prop
    }

    pub fn proof(&self) -> &Proof {
        &self.proof
    }

    pub fn into_proof(self) -> Proof {
        self.proof
    }

    pub fn refl(term: Term) -> Self {
        Self {
            prop: equal(term.clone(), term.clone()),
            proof: Proof::Refl(term),
        }
    }

    pub fn symm(theorem: &Self) -> Option<Self> {
        Self::from_closed_proof(Proof::Symm(Box::new(theorem.proof.clone())))
    }

    pub fn trans(first: &Self, second: &Self) -> Option<Self> {
        Self::from_closed_proof(Proof::Trans(
            Box::new(first.proof.clone()),
            Box::new(second.proof.clone()),
        ))
    }

    pub fn step(term: Term) -> Option<Self> {
        Self::from_closed_proof(Proof::Step(term))
    }

    pub fn steps(terms: Vec<Term>) -> Option<Self> {
        Self::from_closed_proof(Proof::Steps(terms))
    }

    pub fn rewrite(
        equality: &Self,
        theorem: &Self,
        variable: Symbol,
        template: Prop,
    ) -> Option<Self> {
        Self::from_closed_proof(Proof::Rewrite {
            equality: Box::new(equality.proof.clone()),
            proof: Box::new(theorem.proof.clone()),
            variable,
            template,
        })
    }

    pub fn beta(lambda: Lambda, argument: Term) -> Option<Self> {
        Self::from_closed_proof(Proof::Beta { lambda, argument })
    }

    pub fn value_lambda(lambda: Lambda) -> Self {
        Self::from_closed_proof(Proof::ValueLambda(lambda))
            .expect("value lambda theorem should be valid")
    }

    pub fn value_quote(symbol: Symbol) -> Self {
        Self::from_closed_proof(Proof::ValueQuote(symbol))
            .expect("value quote theorem should be valid")
    }

    pub fn value_nil() -> Self {
        Self::from_closed_proof(Proof::ValueNil).expect("value nil theorem should be valid")
    }

    pub fn value_cons(
        head: Term,
        tail: Term,
        head_is_value: &Self,
        tail_is_value: &Self,
    ) -> Option<Self> {
        Self::from_closed_proof(Proof::ValueCons {
            head,
            tail,
            head_is_value: Box::new(head_is_value.proof.clone()),
            tail_is_value: Box::new(tail_is_value.proof.clone()),
        })
    }

    pub fn list_nil() -> Self {
        Self::from_closed_proof(Proof::ListNil).expect("list nil theorem should be valid")
    }

    pub fn list_cons(
        head: Term,
        tail: Term,
        head_is_value: &Self,
        tail_is_list: &Self,
    ) -> Option<Self> {
        Self::from_closed_proof(Proof::ListCons {
            head,
            tail,
            head_is_value: Box::new(head_is_value.proof.clone()),
            tail_is_list: Box::new(tail_is_list.proof.clone()),
        })
    }

    pub fn reverse_acc_nil(acc: Term) -> Self {
        Self::from_closed_proof(Proof::ReverseAccNil { acc })
            .expect("reverse accumulator nil theorem should be valid")
    }

    pub fn reverse_acc_cons(
        head: Term,
        tail: Term,
        acc: Term,
        result: Term,
        head_is_value: &Self,
        tail_reverse_acc: &Self,
    ) -> Option<Self> {
        Self::from_closed_proof(Proof::ReverseAccCons {
            head,
            tail,
            acc,
            result,
            head_is_value: Box::new(head_is_value.proof.clone()),
            tail_reverse_acc: Box::new(tail_reverse_acc.proof.clone()),
        })
    }

    pub fn implies_elim(implication: &Self, premise: &Self) -> Option<Self> {
        Self::from_closed_proof(Proof::ImpliesElim {
            implication: Box::new(implication.proof.clone()),
            premise: Box::new(premise.proof.clone()),
        })
    }

    pub fn forall_elim(forall: &Self, argument: Term) -> Option<Self> {
        Self::from_closed_proof(Proof::ForAllElim {
            forall: Box::new(forall.proof.clone()),
            argument,
        })
    }

    pub fn exists_intro(variable: Symbol, body: Prop, witness: Term, proof: &Self) -> Option<Self> {
        Self::from_closed_proof(Proof::ExistsIntro {
            variable,
            body,
            witness,
            proof: Box::new(proof.proof.clone()),
        })
    }

    pub fn and_intro(left: &Self, right: &Self) -> Self {
        Self::from_closed_proof(Proof::AndIntro(
            Box::new(left.proof.clone()),
            Box::new(right.proof.clone()),
        ))
        .expect("and intro over closed theorems should be valid")
    }

    pub fn and_elim_left(theorem: &Self) -> Option<Self> {
        Self::from_closed_proof(Proof::AndElimLeft(Box::new(theorem.proof.clone())))
    }

    pub fn and_elim_right(theorem: &Self) -> Option<Self> {
        Self::from_closed_proof(Proof::AndElimRight(Box::new(theorem.proof.clone())))
    }

    pub fn or_intro_left(theorem: &Self, right: Prop) -> Self {
        Self::from_closed_proof(Proof::OrIntroLeft {
            proof: Box::new(theorem.proof.clone()),
            right,
        })
        .expect("or intro left over a closed theorem should be valid")
    }

    pub fn or_intro_right(left: Prop, theorem: &Self) -> Self {
        Self::from_closed_proof(Proof::OrIntroRight {
            left,
            proof: Box::new(theorem.proof.clone()),
        })
        .expect("or intro right over a closed theorem should be valid")
    }
}

pub fn check(proof: &Proof, prop: &Prop) -> bool {
    check_in_context(proof, prop, &Context::new())
}

pub fn check_in_context(proof: &Proof, prop: &Prop, context: &Context) -> bool {
    proven_prop(proof, context).as_ref() == Some(prop)
}

fn proven_prop(proof: &Proof, context: &Context) -> Option<Prop> {
    match proof {
        Proof::Assume(symbol) => context.get(symbol).cloned(),
        Proof::Refl(term) => Some(Prop::Equal(term.clone(), term.clone())),
        Proof::Symm(proof) => match proven_prop(proof, context)? {
            Prop::Equal(left, right) => Some(Prop::Equal(right, left)),
            _ => None,
        },
        Proof::Trans(first, second) => {
            match (proven_prop(first, context)?, proven_prop(second, context)?) {
                (Prop::Equal(left, middle), Prop::Equal(second_middle, right))
                    if middle == second_middle =>
                {
                    Some(Prop::Equal(left, right))
                }
                _ => None,
            }
        }
        Proof::Step(term) => match step(term) {
            Step::Reduced(reduced) => Some(Prop::Equal(term.clone(), reduced)),
            Step::Normal => None,
        },
        Proof::Steps(terms) => proven_steps(terms),
        Proof::Rewrite {
            equality,
            proof,
            variable,
            template,
        } => {
            let Prop::Equal(left, right) = proven_prop(equality, context)? else {
                return None;
            };

            let left_instance = substitute_prop(template, *variable, &left);
            if proven_prop(proof, context)? != left_instance {
                return None;
            }

            Some(substitute_prop(template, *variable, &right))
        }
        Proof::Beta { lambda, argument } => {
            if !argument_is_ready_for_beta(argument) {
                return None;
            }

            let applied = Term::Apply {
                function: Box::new(Term::Lambda(lambda.clone())),
                argument: Box::new(argument.clone()),
            };
            let reduced = substitute(lambda.body.as_ref(), lambda.parameter, argument);
            Some(Prop::Equal(applied, reduced))
        }
        Proof::ValueLambda(lambda) => Some(Prop::IsValue(Term::Lambda(lambda.clone()))),
        Proof::ValueQuote(symbol) => Some(Prop::IsValue(Term::Quote(*symbol))),
        Proof::ValueNil => Some(Prop::IsValue(Term::Nil)),
        Proof::ValueCons {
            head,
            tail,
            head_is_value,
            tail_is_value,
        } => match (
            proven_prop(head_is_value, context)?,
            proven_prop(tail_is_value, context)?,
        ) {
            (Prop::IsValue(proven_head), Prop::IsValue(proven_tail))
                if proven_head == *head && proven_tail == *tail =>
            {
                Some(Prop::IsValue(Term::Cons {
                    head: Box::new(head.clone()),
                    tail: Box::new(tail.clone()),
                }))
            }
            _ => None,
        },
        Proof::ListNil => Some(Prop::IsList(Term::Nil)),
        Proof::ListCons {
            head,
            tail,
            head_is_value,
            tail_is_list,
        } => match (
            proven_prop(head_is_value, context)?,
            proven_prop(tail_is_list, context)?,
        ) {
            (Prop::IsValue(proven_head), Prop::IsList(proven_tail))
                if proven_head == *head && proven_tail == *tail =>
            {
                Some(Prop::IsList(Term::Cons {
                    head: Box::new(head.clone()),
                    tail: Box::new(tail.clone()),
                }))
            }
            _ => None,
        },
        Proof::ReverseAccNil { acc } => Some(Prop::ReverseAccumulates {
            list: Term::Nil,
            acc: acc.clone(),
            result: acc.clone(),
        }),
        Proof::ReverseAccCons {
            head,
            tail,
            acc,
            result,
            head_is_value,
            tail_reverse_acc,
        } => match (
            proven_prop(head_is_value, context)?,
            proven_prop(tail_reverse_acc, context)?,
        ) {
            (
                Prop::IsValue(proven_head),
                Prop::ReverseAccumulates {
                    list: proven_tail,
                    acc: proven_acc,
                    result: proven_result,
                },
            ) if proven_head == *head
                && proven_tail == *tail
                && proven_acc == cons_term(head.clone(), acc.clone())
                && proven_result == *result =>
            {
                Some(Prop::ReverseAccumulates {
                    list: cons_term(head.clone(), tail.clone()),
                    acc: acc.clone(),
                    result: result.clone(),
                })
            }
            _ => None,
        },
        Proof::ListInduction {
            variable,
            property,
            base,
            head,
            tail,
            head_is_value_assumption,
            tail_is_list_assumption,
            induction_hypothesis_assumption,
            step,
        } => {
            let symbols = ListInductionSymbols {
                variable: *variable,
                head: *head,
                tail: *tail,
                head_is_value_assumption: *head_is_value_assumption,
                tail_is_list_assumption: *tail_is_list_assumption,
                induction_hypothesis_assumption: *induction_hypothesis_assumption,
            };

            prove_list_induction(context, symbols, property, base, step)
        }
        Proof::ImpliesIntro {
            assumption,
            premise,
            proof,
        } => {
            let mut context = context.clone();
            context.insert(*assumption, premise.clone());
            let conclusion = proven_prop(proof, &context)?;
            Some(Prop::Implies(
                Box::new(premise.clone()),
                Box::new(conclusion),
            ))
        }
        Proof::ImpliesElim {
            implication,
            premise,
        } => {
            let premise = proven_prop(premise, context)?;
            match proven_prop(implication, context)? {
                Prop::Implies(expected_premise, conclusion)
                    if expected_premise.as_ref() == &premise =>
                {
                    Some(*conclusion)
                }
                _ => None,
            }
        }
        Proof::ForAllIntro { variable, proof } => {
            if context_mentions_symbol(context, *variable) {
                return None;
            }
            let body = proven_prop(proof, context)?;
            Some(Prop::ForAll {
                variable: *variable,
                body: Box::new(body),
            })
        }
        Proof::ForAllElim { forall, argument } => match proven_prop(forall, context)? {
            Prop::ForAll { variable, body } => Some(substitute_prop(&body, variable, argument)),
            _ => None,
        },
        Proof::ExistsIntro {
            variable,
            body,
            witness,
            proof,
        } => {
            let witness_body = substitute_prop(body, *variable, witness);
            if proven_prop(proof, context)? == witness_body {
                Some(Prop::Exists {
                    variable: *variable,
                    body: Box::new(body.clone()),
                })
            } else {
                None
            }
        }
        Proof::ExistsElim {
            existential,
            witness,
            assumption,
            proof,
        } => match proven_prop(existential, context)? {
            Prop::Exists { variable, body } => {
                let existential = Prop::Exists {
                    variable,
                    body: body.clone(),
                };
                if prop_mentions_symbol(&existential, *witness)
                    || context_mentions_symbol(context, *witness)
                {
                    return None;
                }

                let witness_prop = substitute_prop(&body, variable, &Term::Var(*witness));
                let mut context = context.clone();
                context.insert(*assumption, witness_prop);
                let conclusion = proven_prop(proof, &context)?;

                if prop_mentions_symbol(&conclusion, *witness) {
                    None
                } else {
                    Some(conclusion)
                }
            }
            _ => None,
        },
        Proof::AndIntro(left, right) => Some(Prop::And(
            Box::new(proven_prop(left, context)?),
            Box::new(proven_prop(right, context)?),
        )),
        Proof::AndElimLeft(proof) => match proven_prop(proof, context)? {
            Prop::And(left, _) => Some(*left),
            _ => None,
        },
        Proof::AndElimRight(proof) => match proven_prop(proof, context)? {
            Prop::And(_, right) => Some(*right),
            _ => None,
        },
        Proof::OrIntroLeft { proof, right } => Some(Prop::Or(
            Box::new(proven_prop(proof, context)?),
            Box::new(right.clone()),
        )),
        Proof::OrIntroRight { left, proof } => Some(Prop::Or(
            Box::new(left.clone()),
            Box::new(proven_prop(proof, context)?),
        )),
        Proof::OrElim {
            disjunction,
            left_assumption,
            left_proof,
            right_assumption,
            right_proof,
        } => match proven_prop(disjunction, context)? {
            Prop::Or(left, right) => {
                let mut left_context = context.clone();
                left_context.insert(*left_assumption, *left);
                let left_conclusion = proven_prop(left_proof, &left_context)?;

                let mut right_context = context.clone();
                right_context.insert(*right_assumption, *right);
                let right_conclusion = proven_prop(right_proof, &right_context)?;

                if left_conclusion == right_conclusion {
                    Some(left_conclusion)
                } else {
                    None
                }
            }
            _ => None,
        },
    }
}

fn proven_steps(terms: &[Term]) -> Option<Prop> {
    let (first, rest) = terms.split_first()?;
    let mut previous = first;

    for next in rest {
        match step(previous) {
            Step::Reduced(reduced) if &reduced == next => previous = next,
            _ => return None,
        }
    }

    Some(Prop::Equal(first.clone(), previous.clone()))
}

fn cons_term(head: Term, tail: Term) -> Term {
    Term::Cons {
        head: Box::new(head),
        tail: Box::new(tail),
    }
}

#[derive(Clone, Copy)]
struct ListInductionSymbols {
    variable: Symbol,
    head: Symbol,
    tail: Symbol,
    head_is_value_assumption: Symbol,
    tail_is_list_assumption: Symbol,
    induction_hypothesis_assumption: Symbol,
}

fn prove_list_induction(
    context: &Context,
    symbols: ListInductionSymbols,
    property: &Prop,
    base: &Proof,
    step: &Proof,
) -> Option<Prop> {
    if !list_induction_symbols_are_fresh(context, symbols, property) {
        return None;
    }

    let ListInductionSymbols {
        variable,
        head,
        tail,
        head_is_value_assumption,
        tail_is_list_assumption,
        induction_hypothesis_assumption,
    } = symbols;

    let base_prop = substitute_prop(property, variable, &Term::Nil);
    if proven_prop(base, context)? != base_prop {
        return None;
    }

    let tail_var = Term::Var(tail);
    let step_prop = substitute_prop(
        property,
        variable,
        &Term::Cons {
            head: Box::new(Term::Var(head)),
            tail: Box::new(tail_var.clone()),
        },
    );
    let mut step_context = context.clone();
    step_context.insert(head_is_value_assumption, Prop::IsValue(Term::Var(head)));
    step_context.insert(tail_is_list_assumption, Prop::IsList(tail_var.clone()));
    step_context.insert(
        induction_hypothesis_assumption,
        substitute_prop(property, variable, &tail_var),
    );

    if proven_prop(step, &step_context)? != step_prop {
        return None;
    }

    let variable_term = Term::Var(variable);
    Some(Prop::ForAll {
        variable,
        body: Box::new(Prop::Implies(
            Box::new(Prop::IsList(variable_term.clone())),
            Box::new(substitute_prop(property, variable, &variable_term)),
        )),
    })
}

fn list_induction_symbols_are_fresh(
    context: &Context,
    symbols: ListInductionSymbols,
    property: &Prop,
) -> bool {
    let ListInductionSymbols {
        variable,
        head,
        tail,
        head_is_value_assumption,
        tail_is_list_assumption,
        induction_hypothesis_assumption,
    } = symbols;

    if head == tail || head == variable || tail == variable {
        return false;
    }

    let assumption_symbols = [
        head_is_value_assumption,
        tail_is_list_assumption,
        induction_hypothesis_assumption,
    ];
    let mut seen_assumption_symbols = HashSet::new();
    if assumption_symbols.into_iter().any(|assumption| {
        !seen_assumption_symbols.insert(assumption) || context.contains_key(&assumption)
    }) {
        return false;
    }

    !context_mentions_symbol(context, variable)
        && !context_mentions_symbol(context, head)
        && !context_mentions_symbol(context, tail)
        && !prop_mentions_symbol(property, head)
        && !prop_mentions_symbol(property, tail)
}

pub fn substitute_prop(prop: &Prop, variable: Symbol, replacement: &Term) -> Prop {
    match prop {
        Prop::Equal(left, right) => Prop::Equal(
            substitute(left, variable, replacement),
            substitute(right, variable, replacement),
        ),
        Prop::IsValue(term) => Prop::IsValue(substitute(term, variable, replacement)),
        Prop::IsList(term) => Prop::IsList(substitute(term, variable, replacement)),
        Prop::ReverseAccumulates { list, acc, result } => Prop::ReverseAccumulates {
            list: substitute(list, variable, replacement),
            acc: substitute(acc, variable, replacement),
            result: substitute(result, variable, replacement),
        },
        Prop::Implies(premise, conclusion) => Prop::Implies(
            Box::new(substitute_prop(premise, variable, replacement)),
            Box::new(substitute_prop(conclusion, variable, replacement)),
        ),
        Prop::ForAll {
            variable: binder,
            body,
        } => substitute_quantified_prop(true, *binder, body, variable, replacement),
        Prop::Exists {
            variable: binder,
            body,
        } => substitute_quantified_prop(false, *binder, body, variable, replacement),
        Prop::And(left, right) => Prop::And(
            Box::new(substitute_prop(left, variable, replacement)),
            Box::new(substitute_prop(right, variable, replacement)),
        ),
        Prop::Or(left, right) => Prop::Or(
            Box::new(substitute_prop(left, variable, replacement)),
            Box::new(substitute_prop(right, variable, replacement)),
        ),
    }
}

fn substitute_quantified_prop(
    forall: bool,
    binder: Symbol,
    body: &Prop,
    variable: Symbol,
    replacement: &Term,
) -> Prop {
    if binder == variable {
        return quantified_prop(forall, binder, body.clone());
    }

    if free_symbols(replacement).contains(&binder) {
        let fresh = fresh_symbol_for_prop(body, replacement, variable);
        let body = rename_bound_var_prop(body, binder, fresh);
        return quantified_prop(forall, fresh, substitute_prop(&body, variable, replacement));
    }

    quantified_prop(forall, binder, substitute_prop(body, variable, replacement))
}

fn quantified_prop(forall: bool, variable: Symbol, body: Prop) -> Prop {
    if forall {
        Prop::ForAll {
            variable,
            body: Box::new(body),
        }
    } else {
        Prop::Exists {
            variable,
            body: Box::new(body),
        }
    }
}

pub fn free_symbols_prop(prop: &Prop) -> HashSet<Symbol> {
    let mut symbols = HashSet::new();
    add_free_symbols_prop(prop, &mut symbols);
    symbols
}

fn add_free_symbols_prop(prop: &Prop, symbols: &mut HashSet<Symbol>) {
    match prop {
        Prop::Equal(left, right) => {
            add_free_symbols(left, symbols);
            add_free_symbols(right, symbols);
        }
        Prop::IsValue(term) => {
            add_free_symbols(term, symbols);
        }
        Prop::IsList(term) => {
            add_free_symbols(term, symbols);
        }
        Prop::ReverseAccumulates { list, acc, result } => {
            add_free_symbols(list, symbols);
            add_free_symbols(acc, symbols);
            add_free_symbols(result, symbols);
        }
        Prop::Implies(premise, conclusion)
        | Prop::And(premise, conclusion)
        | Prop::Or(premise, conclusion) => {
            add_free_symbols_prop(premise, symbols);
            add_free_symbols_prop(conclusion, symbols);
        }
        Prop::ForAll { variable, body } | Prop::Exists { variable, body } => {
            let mut body_symbols = HashSet::new();
            add_free_symbols_prop(body, &mut body_symbols);
            body_symbols.remove(variable);
            symbols.extend(body_symbols);
        }
    }
}

fn rename_bound_var_prop(prop: &Prop, old: Symbol, new: Symbol) -> Prop {
    match prop {
        Prop::Equal(left, right) => Prop::Equal(
            rename_bound_var(left, old, new),
            rename_bound_var(right, old, new),
        ),
        Prop::IsValue(term) => Prop::IsValue(rename_bound_var(term, old, new)),
        Prop::IsList(term) => Prop::IsList(rename_bound_var(term, old, new)),
        Prop::ReverseAccumulates { list, acc, result } => Prop::ReverseAccumulates {
            list: rename_bound_var(list, old, new),
            acc: rename_bound_var(acc, old, new),
            result: rename_bound_var(result, old, new),
        },
        Prop::Implies(premise, conclusion) => Prop::Implies(
            Box::new(rename_bound_var_prop(premise, old, new)),
            Box::new(rename_bound_var_prop(conclusion, old, new)),
        ),
        Prop::ForAll { variable, .. } if *variable == old => prop.clone(),
        Prop::ForAll { variable, body } => Prop::ForAll {
            variable: *variable,
            body: Box::new(rename_bound_var_prop(body, old, new)),
        },
        Prop::Exists { variable, .. } if *variable == old => prop.clone(),
        Prop::Exists { variable, body } => Prop::Exists {
            variable: *variable,
            body: Box::new(rename_bound_var_prop(body, old, new)),
        },
        Prop::And(left, right) => Prop::And(
            Box::new(rename_bound_var_prop(left, old, new)),
            Box::new(rename_bound_var_prop(right, old, new)),
        ),
        Prop::Or(left, right) => Prop::Or(
            Box::new(rename_bound_var_prop(left, old, new)),
            Box::new(rename_bound_var_prop(right, old, new)),
        ),
    }
}

fn fresh_symbol_for_prop(prop: &Prop, replacement: &Term, variable: Symbol) -> Symbol {
    let mut symbols = HashSet::new();
    add_all_symbols_prop(prop, &mut symbols);
    add_all_symbols(replacement, &mut symbols);
    symbols.insert(variable);

    let mut symbol = 0;
    while symbols.contains(&symbol) {
        symbol += 1;
    }
    symbol
}

fn add_all_symbols_prop(prop: &Prop, symbols: &mut HashSet<Symbol>) {
    match prop {
        Prop::Equal(left, right) => {
            add_all_symbols(left, symbols);
            add_all_symbols(right, symbols);
        }
        Prop::IsValue(term) => {
            add_all_symbols(term, symbols);
        }
        Prop::IsList(term) => {
            add_all_symbols(term, symbols);
        }
        Prop::ReverseAccumulates { list, acc, result } => {
            add_all_symbols(list, symbols);
            add_all_symbols(acc, symbols);
            add_all_symbols(result, symbols);
        }
        Prop::Implies(premise, conclusion)
        | Prop::And(premise, conclusion)
        | Prop::Or(premise, conclusion) => {
            add_all_symbols_prop(premise, symbols);
            add_all_symbols_prop(conclusion, symbols);
        }
        Prop::ForAll { variable, body } | Prop::Exists { variable, body } => {
            symbols.insert(*variable);
            add_all_symbols_prop(body, symbols);
        }
    }
}

fn prop_mentions_symbol(prop: &Prop, symbol: Symbol) -> bool {
    free_symbols_prop(prop).contains(&symbol)
}

fn context_mentions_symbol(context: &Context, symbol: Symbol) -> bool {
    context
        .values()
        .any(|prop| prop_mentions_symbol(prop, symbol))
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
        Term::Diverge | Term::Var(_) | Term::Quote(_) => {
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

pub fn step(term: &Term) -> Step {
    match term {
        Term::Apply { function, argument } => step_apply(function, argument),
        Term::Lambda(_) => Step::Normal,
        Term::Nil => Step::Normal,
        Term::Cons { head, tail } => step_cons(head, tail),
        Term::Head(term) => step_head(term),
        Term::Tail(term) => step_tail(term),
        Term::ListCase(list_case) => step_list_case(list_case),
        Term::Error(_) | Term::Diverge => Step::Normal,
        Term::Var(_) | Term::Quote(_) => Step::Normal,
    }
}

fn step_apply(function: &Term, argument: &Term) -> Step {
    match function {
        Term::Lambda(lambda) => step_lambda_application(lambda, argument),
        Term::Error(_) | Term::Diverge => Step::Reduced(function.clone()),
        _ => match step(function) {
            Step::Reduced(function) => Step::Reduced(Term::Apply {
                function: Box::new(function),
                argument: Box::new(argument.clone()),
            }),
            Step::Normal if is_known_non_callable(function) => {
                Step::Reduced(runtime_error(function.clone()))
            }
            Step::Normal => step_neutral_application(function, argument),
        },
    }
}

fn step_lambda_application(lambda: &Lambda, argument: &Term) -> Step {
    match step(argument) {
        Step::Reduced(argument) => Step::Reduced(Term::Apply {
            function: Box::new(Term::Lambda(lambda.clone())),
            argument: Box::new(argument),
        }),
        Step::Normal if is_effect(argument) => Step::Reduced(argument.clone()),
        Step::Normal => Step::Reduced(substitute(lambda.body.as_ref(), lambda.parameter, argument)),
    }
}

fn step_neutral_application(function: &Term, argument: &Term) -> Step {
    match step(argument) {
        Step::Reduced(argument) => Step::Reduced(Term::Apply {
            function: Box::new(function.clone()),
            argument: Box::new(argument),
        }),
        Step::Normal if is_effect(argument) => Step::Reduced(argument.clone()),
        Step::Normal => Step::Normal,
    }
}

fn argument_is_ready_for_beta(argument: &Term) -> bool {
    match step(argument) {
        Step::Reduced(_) => false,
        Step::Normal => !is_effect(argument),
    }
}

fn is_effect(term: &Term) -> bool {
    matches!(term, Term::Error(_) | Term::Diverge)
}

pub fn term_is_value(term: &Term) -> bool {
    match term {
        Term::Lambda(_) | Term::Nil | Term::Quote(_) => true,
        Term::Cons { head, tail } => term_is_value(head) && term_is_value(tail),
        _ => false,
    }
}

fn is_known_non_callable(term: &Term) -> bool {
    matches!(term, Term::Quote(_) | Term::Nil | Term::Cons { .. })
}

fn runtime_error(payload: Term) -> Term {
    Term::Error(Box::new(payload))
}

fn step_cons(head: &Term, tail: &Term) -> Step {
    match step(head) {
        Step::Reduced(head) => Step::Reduced(Term::Cons {
            head: Box::new(head),
            tail: Box::new(tail.clone()),
        }),
        Step::Normal if is_effect(head) => Step::Reduced(head.clone()),
        Step::Normal => match step(tail) {
            Step::Reduced(tail) => Step::Reduced(Term::Cons {
                head: Box::new(head.clone()),
                tail: Box::new(tail),
            }),
            Step::Normal if is_effect(tail) => Step::Reduced(tail.clone()),
            Step::Normal => Step::Normal,
        },
    }
}

fn step_head(term: &Term) -> Step {
    match step(term) {
        Step::Reduced(term) => Step::Reduced(Term::Head(Box::new(term))),
        Step::Normal => match term {
            Term::Cons { head, .. } => Step::Reduced(head.as_ref().clone()),
            Term::Error(_) | Term::Diverge => Step::Reduced(term.clone()),
            Term::Var(_)
            | Term::Apply { .. }
            | Term::Head(_)
            | Term::Tail(_)
            | Term::ListCase(_) => Step::Normal,
            Term::Nil | Term::Quote(_) | Term::Lambda(_) => {
                Step::Reduced(runtime_error(term.clone()))
            }
        },
    }
}

fn step_tail(term: &Term) -> Step {
    match step(term) {
        Step::Reduced(term) => Step::Reduced(Term::Tail(Box::new(term))),
        Step::Normal => match term {
            Term::Cons { tail, .. } => Step::Reduced(tail.as_ref().clone()),
            Term::Error(_) | Term::Diverge => Step::Reduced(term.clone()),
            Term::Var(_)
            | Term::Apply { .. }
            | Term::Head(_)
            | Term::Tail(_)
            | Term::ListCase(_) => Step::Normal,
            Term::Nil | Term::Quote(_) | Term::Lambda(_) => {
                Step::Reduced(runtime_error(term.clone()))
            }
        },
    }
}

fn step_list_case(list_case: &ListCase) -> Step {
    match step(list_case.list.as_ref()) {
        Step::Reduced(list) => Step::Reduced(Term::ListCase(ListCase {
            list: Box::new(list),
            nil: list_case.nil.clone(),
            cons: list_case.cons,
            cons_case: list_case.cons_case.clone(),
        })),
        Step::Normal => match list_case.list.as_ref() {
            Term::Nil => Step::Reduced(list_case.nil.as_ref().clone()),
            Term::Cons { .. } => Step::Reduced(substitute(
                list_case.cons_case.as_ref(),
                list_case.cons,
                list_case.list.as_ref(),
            )),
            Term::Error(_) | Term::Diverge => Step::Reduced(list_case.list.as_ref().clone()),
            Term::Var(_)
            | Term::Apply { .. }
            | Term::Head(_)
            | Term::Tail(_)
            | Term::ListCase(_) => Step::Normal,
            Term::Quote(_) | Term::Lambda(_) => {
                Step::Reduced(runtime_error(list_case.list.as_ref().clone()))
            }
        },
    }
}

pub fn normal_form(term: &Term) -> Term {
    let mut term = term.clone();
    loop {
        match step(&term) {
            Step::Reduced(next) => term = next,
            Step::Normal => return term,
        }
    }
}

pub fn free_symbols(term: &Term) -> HashSet<Symbol> {
    let mut symbols = HashSet::new();
    add_free_symbols(term, &mut symbols);
    symbols
}

fn add_free_symbols(term: &Term, symbols: &mut HashSet<Symbol>) {
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
        Term::Diverge => {}
        Term::Var(symbol) => {
            symbols.insert(*symbol);
        }
        Term::Quote(_) => {}
    }
}

fn rename_bound_var(term: &Term, old: Symbol, new: Symbol) -> Term {
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
        Term::Diverge => term.clone(),
        Term::Var(symbol) if *symbol == old => Term::Var(new),
        Term::Var(_) | Term::Quote(_) => term.clone(),
    }
}

fn fresh_symbol(term: &Term, replacement: &Term, variable: Symbol) -> Symbol {
    let mut symbols = HashSet::new();
    add_all_symbols(term, &mut symbols);
    add_all_symbols(replacement, &mut symbols);
    symbols.insert(variable);

    let mut symbol = 0;
    while symbols.contains(&symbol) {
        symbol += 1;
    }
    symbol
}

fn add_all_symbols(term: &Term, symbols: &mut HashSet<Symbol>) {
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
        Term::Diverge => {}
        Term::Var(symbol) | Term::Quote(symbol) => {
            symbols.insert(*symbol);
        }
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

    fn cons(head: Term, tail: Term) -> Term {
        Term::Cons {
            head: Box::new(head),
            tail: Box::new(tail),
        }
    }

    fn head(term: Term) -> Term {
        Term::Head(Box::new(term))
    }

    fn tail(term: Term) -> Term {
        Term::Tail(Box::new(term))
    }

    fn list_case(list: Term, nil: Term, cons_var: Symbol, cons_case: Term) -> Term {
        Term::ListCase(ListCase {
            list: Box::new(list),
            nil: Box::new(nil),
            cons: cons_var,
            cons_case: Box::new(cons_case),
        })
    }

    fn error(error: Term) -> Term {
        Term::Error(Box::new(error))
    }

    #[test]
    fn step_beta_reduces_after_argument_is_ready() {
        let term = apply(lambda(1, Term::Var(1)), Term::Quote(2));

        assert_eq!(step(&term), Step::Reduced(Term::Quote(2)));
    }

    #[test]
    fn application_reduces_argument_before_beta() {
        let term = apply(
            lambda(1, Term::Quote(9)),
            apply(lambda(2, Term::Var(2)), Term::Quote(3)),
        );

        assert_eq!(
            step(&term),
            Step::Reduced(apply(lambda(1, Term::Quote(9)), Term::Quote(3)))
        );
        assert_eq!(normal_form(&term), Term::Quote(9));
    }

    #[test]
    fn lambda_is_a_value_without_evaluating_body() {
        let term = lambda(1, apply(lambda(2, Term::Var(2)), Term::Var(1)));

        assert_eq!(step(&term), Step::Normal);
    }

    #[test]
    fn is_value_distinguishes_values_from_pending_computations() {
        assert!(term_is_value(&Term::Nil));
        assert!(term_is_value(&Term::Quote(1)));
        assert!(term_is_value(&lambda(1, Term::Var(1))));
        assert!(term_is_value(&cons(Term::Quote(1), Term::Nil)));

        assert!(!term_is_value(&apply(Term::Var(1), Term::Quote(2))));
        assert!(!term_is_value(&Term::Diverge));
        assert!(!term_is_value(&error(Term::Quote(1))));
        assert!(!term_is_value(&Term::Var(1)));
        assert_eq!(step(&Term::Var(1)), Step::Normal);
    }

    #[test]
    fn application_propagates_effects() {
        let thrown = error(Term::Quote(1));

        assert_eq!(
            normal_form(&apply(thrown.clone(), Term::Quote(2))),
            thrown.clone()
        );
        assert_eq!(
            normal_form(&apply(lambda(1, Term::Quote(2)), thrown.clone())),
            thrown
        );
        assert_eq!(
            normal_form(&apply(lambda(1, Term::Quote(2)), Term::Diverge)),
            Term::Diverge
        );
    }

    #[test]
    fn apply_known_non_callable_reduces_to_error() {
        let term = apply(Term::Nil, Term::Quote(2));

        assert_eq!(step(&term), Step::Reduced(error(Term::Nil)));
    }

    #[test]
    fn cons_evaluates_head_then_tail_and_propagates_effects() {
        let term = cons(
            apply(lambda(1, Term::Var(1)), Term::Quote(2)),
            error(Term::Quote(3)),
        );

        assert_eq!(
            step(&term),
            Step::Reduced(cons(Term::Quote(2), error(Term::Quote(3))))
        );
        assert_eq!(normal_form(&term), error(Term::Quote(3)));
    }

    #[test]
    fn head_and_tail_destructure_cons() {
        let term = cons(Term::Quote(1), Term::Quote(2));

        assert_eq!(step(&head(term.clone())), Step::Reduced(Term::Quote(1)));
        assert_eq!(step(&tail(term)), Step::Reduced(Term::Quote(2)));
    }

    #[test]
    fn head_and_tail_open_terms_are_neutral() {
        assert_eq!(step(&head(Term::Var(1))), Step::Normal);
        assert_eq!(step(&tail(Term::Var(1))), Step::Normal);
    }

    #[test]
    fn head_and_tail_known_non_cons_reduce_to_error() {
        assert_eq!(step(&head(Term::Nil)), Step::Reduced(error(Term::Nil)));
        assert_eq!(step(&tail(Term::Nil)), Step::Reduced(error(Term::Nil)));
    }

    #[test]
    fn list_case_reduces_nil_and_cons() {
        let cons_value = cons(Term::Quote(1), Term::Nil);
        let cons_case = head(Term::Var(9));

        assert_eq!(
            step(&list_case(Term::Nil, Term::Quote(0), 9, cons_case.clone())),
            Step::Reduced(Term::Quote(0))
        );
        assert_eq!(
            normal_form(&list_case(cons_value, Term::Quote(0), 9, cons_case)),
            Term::Quote(1)
        );
    }

    #[test]
    fn list_case_open_term_is_neutral_and_known_non_list_reduces_to_error() {
        assert_eq!(
            step(&list_case(Term::Var(1), Term::Quote(0), 9, Term::Quote(1))),
            Step::Normal
        );
        assert_eq!(
            step(&list_case(
                Term::Quote(1),
                Term::Quote(0),
                9,
                Term::Quote(1)
            )),
            Step::Reduced(error(Term::Quote(1)))
        );
    }

    #[test]
    fn substitution_descends_into_cons_and_destructors() {
        let term = cons(head(Term::Var(1)), tail(Term::Var(2)));

        assert_eq!(
            substitute(&term, 1, &Term::Quote(3)),
            cons(head(Term::Quote(3)), tail(Term::Var(2)))
        );
    }

    #[test]
    fn substitution_avoids_lambda_capture() {
        let term = lambda(2, Term::Var(1));

        assert_eq!(substitute(&term, 1, &Term::Var(2)), lambda(0, Term::Var(2)));
    }

    #[test]
    fn substitution_avoids_list_case_capture() {
        let term = list_case(Term::Var(1), Term::Quote(0), 2, Term::Var(3));

        assert_eq!(
            substitute(&term, 3, &Term::Var(2)),
            list_case(Term::Var(1), Term::Quote(0), 4, Term::Var(2))
        );
    }

    #[test]
    fn free_symbols_ignore_list_case_cons_binder() {
        assert_eq!(
            free_symbols(&list_case(
                Term::Var(1),
                Term::Var(2),
                3,
                apply(Term::Var(3), Term::Var(4))
            )),
            HashSet::from([1, 2, 4])
        );
    }

    #[test]
    fn step_proof_proves_one_step_reduction() {
        let term = head(cons(Term::Quote(1), Term::Nil));

        assert!(check(
            &Proof::Step(term.clone()),
            &equal(term, Term::Quote(1))
        ));
    }

    #[test]
    fn steps_proof_proves_multi_step_reduction() {
        let start = apply(
            lambda(1, Term::Quote(9)),
            apply(lambda(2, Term::Var(2)), Term::Quote(3)),
        );
        let middle = apply(lambda(1, Term::Quote(9)), Term::Quote(3));
        let end = Term::Quote(9);

        assert!(check(
            &Proof::Steps(vec![start.clone(), middle, end.clone()]),
            &equal(start, end)
        ));
    }

    #[test]
    fn theorem_from_proof_checks_closed_proofs() {
        let valid = Theorem::from_proof(
            Proof::Refl(Term::Quote(1)),
            equal(Term::Quote(1), Term::Quote(1)),
        );
        let invalid = Theorem::from_proof(
            Proof::Refl(Term::Quote(1)),
            equal(Term::Quote(1), Term::Quote(2)),
        );

        assert!(valid.is_some());
        assert!(invalid.is_none());
        assert!(
            Theorem::from_proof(Proof::Assume(7), equal(Term::Quote(1), Term::Quote(1))).is_none()
        );
    }

    #[test]
    fn theorem_equality_rules_build_checked_theorems() {
        let start = apply(lambda(1, Term::Var(1)), Term::Quote(2));
        let step = Theorem::step(start.clone()).expect("term should step");
        let refl = Theorem::refl(Term::Quote(2));
        let trans = Theorem::trans(&step, &refl).expect("equalities should chain");
        let symm = Theorem::symm(&step).expect("step equality should be symmetric");

        assert_eq!(step.prop(), &equal(start.clone(), Term::Quote(2)));
        assert_eq!(trans.prop(), &equal(start.clone(), Term::Quote(2)));
        assert_eq!(symm.prop(), &equal(Term::Quote(2), start));
        assert!(Theorem::step(Term::Quote(2)).is_none());
    }

    #[test]
    fn theorem_rewrite_moves_props_across_equality() {
        let term = apply(lambda(1, Term::Var(1)), Term::Nil);
        let step = Theorem::step(term.clone()).expect("term should step");
        let nil_to_term = Theorem::symm(&step).expect("step should be symmetric");
        let theorem = Theorem::rewrite(
            &nil_to_term,
            &Theorem::list_nil(),
            99,
            is_list(Term::Var(99)),
        )
        .expect("rewrite should prove listness before evaluation");

        assert_eq!(theorem.prop(), &is_list(term));
    }

    #[test]
    fn theorem_value_and_list_rules_build_checked_theorems() {
        let head = Term::Quote(1);
        let tail = Term::Nil;
        let head_value = Theorem::value_quote(1);
        let tail_value = Theorem::value_nil();
        let tail_list = Theorem::list_nil();
        let list = cons(head.clone(), tail.clone());
        let value = Theorem::value_cons(head.clone(), tail.clone(), &head_value, &tail_value)
            .expect("cons of values is a value");
        let list_theorem = Theorem::list_cons(head.clone(), tail.clone(), &head_value, &tail_list)
            .expect("cons with value head and list tail is a list");

        assert_eq!(value.prop(), &is_value(list.clone()));
        assert_eq!(list_theorem.prop(), &is_list(list));
        assert!(Theorem::list_cons(Term::Diverge, tail, &head_value, &tail_list).is_none());
    }

    #[test]
    fn reverse_accumulator_rules_build_checked_theorems() {
        let head = Term::Quote(1);
        let acc = Term::Nil;
        let result = cons(head.clone(), acc.clone());
        let head_value = Theorem::value_quote(1);
        let tail_relation = Theorem::reverse_acc_nil(result.clone());
        let relation = Theorem::reverse_acc_cons(
            head.clone(),
            Term::Nil,
            acc.clone(),
            result.clone(),
            &head_value,
            &tail_relation,
        )
        .expect("reverse accumulator cons rule should apply");

        assert_eq!(
            relation.prop(),
            &reverse_accumulates(cons(head.clone(), Term::Nil), acc, result)
        );
        assert!(
            Theorem::reverse_acc_cons(
                Term::Diverge,
                Term::Nil,
                Term::Nil,
                cons(head, Term::Nil),
                &head_value,
                &tail_relation,
            )
            .is_none()
        );
    }

    #[test]
    fn theorem_first_order_rules_build_checked_theorems() {
        let prop = equal(Term::Quote(1), Term::Quote(1));
        let implication = Theorem::from_proof(
            Proof::ImpliesIntro {
                assumption: 7,
                premise: prop.clone(),
                proof: Box::new(Proof::Assume(7)),
            },
            implies(prop.clone(), prop.clone()),
        )
        .expect("identity implication should check");
        let conclusion = Theorem::implies_elim(&implication, &Theorem::refl(Term::Quote(1)))
            .expect("modus ponens should apply");
        let universal = Theorem::from_proof(
            Proof::ForAllIntro {
                variable: 1,
                proof: Box::new(Proof::Refl(Term::Var(1))),
            },
            forall(1, equal(Term::Var(1), Term::Var(1))),
        )
        .expect("forall intro should check");
        let instance = Theorem::forall_elim(&universal, Term::Quote(2))
            .expect("forall theorem should instantiate");

        assert_eq!(conclusion.prop(), &prop);
        assert_eq!(instance.prop(), &equal(Term::Quote(2), Term::Quote(2)));
    }

    #[test]
    fn rewrite_uses_equality_inside_template() {
        let start = head(cons(Term::Quote(1), Term::Nil));
        let end = Term::Quote(1);
        let template = equal(
            cons(Term::Var(99), Term::Nil),
            cons(Term::Var(99), Term::Nil),
        );
        let left_instance = substitute_prop(&template, 99, &start);
        let right_instance = substitute_prop(&template, 99, &end);
        let proof = Proof::Rewrite {
            equality: Box::new(Proof::Step(start)),
            proof: Box::new(Proof::Refl(match left_instance.clone() {
                Prop::Equal(left, _) => left,
                _ => unreachable!(),
            })),
            variable: 99,
            template,
        };

        assert!(check(&proof, &right_instance));
    }

    #[test]
    fn beta_proof_rejects_reducible_arguments() {
        let lam = Lambda {
            parameter: 1,
            body: Box::new(Term::Quote(9)),
        };
        let argument = apply(lambda(2, Term::Var(2)), Term::Quote(3));

        assert!(!check(
            &Proof::Beta {
                lambda: lam.clone(),
                argument: argument.clone()
            },
            &Prop::Equal(apply(Term::Lambda(lam), argument), Term::Quote(9))
        ));
    }

    #[test]
    fn value_intro_rules_prove_concrete_values() {
        let lambda = Lambda {
            parameter: 1,
            body: Box::new(Term::Var(1)),
        };
        let list = cons(Term::Quote(1), Term::Nil);
        let proof = Proof::ValueCons {
            head: Term::Quote(1),
            tail: Term::Nil,
            head_is_value: Box::new(Proof::ValueQuote(1)),
            tail_is_value: Box::new(Proof::ValueNil),
        };

        assert!(check(
            &Proof::ValueLambda(lambda.clone()),
            &is_value(Term::Lambda(lambda))
        ));
        assert!(check(&Proof::ValueQuote(1), &is_value(Term::Quote(1))));
        assert!(check(&Proof::ValueNil, &is_value(Term::Nil)));
        assert!(check(&proof, &is_value(list)));
    }

    #[test]
    fn value_cons_requires_matching_value_proofs() {
        let proof = Proof::ValueCons {
            head: Term::Diverge,
            tail: Term::Nil,
            head_is_value: Box::new(Proof::ValueQuote(1)),
            tail_is_value: Box::new(Proof::ValueNil),
        };

        assert!(!check(&proof, &is_value(cons(Term::Diverge, Term::Nil))));
    }

    #[test]
    fn list_intro_rules_prove_concrete_lists() {
        let list = cons(Term::Quote(1), cons(Term::Quote(2), Term::Nil));
        let proof = Proof::ListCons {
            head: Term::Quote(1),
            tail: cons(Term::Quote(2), Term::Nil),
            head_is_value: Box::new(Proof::ValueQuote(1)),
            tail_is_list: Box::new(Proof::ListCons {
                head: Term::Quote(2),
                tail: Term::Nil,
                head_is_value: Box::new(Proof::ValueQuote(2)),
                tail_is_list: Box::new(Proof::ListNil),
            }),
        };

        assert!(check(&Proof::ListNil, &is_list(Term::Nil)));
        assert!(check(&proof, &is_list(list)));
    }

    #[test]
    fn list_cons_requires_tail_list_proof_for_the_same_tail() {
        let proof = Proof::ListCons {
            head: Term::Quote(1),
            tail: cons(Term::Quote(2), Term::Nil),
            head_is_value: Box::new(Proof::ValueQuote(1)),
            tail_is_list: Box::new(Proof::ListNil),
        };

        assert!(!check(
            &proof,
            &is_list(cons(Term::Quote(1), cons(Term::Quote(2), Term::Nil)))
        ));
    }

    #[test]
    fn list_cons_requires_head_value_proof_for_the_same_head() {
        let proof = Proof::ListCons {
            head: Term::Diverge,
            tail: Term::Nil,
            head_is_value: Box::new(Proof::ValueQuote(1)),
            tail_is_list: Box::new(Proof::ListNil),
        };

        assert!(!check(&proof, &is_list(cons(Term::Diverge, Term::Nil))));
    }

    #[test]
    fn is_list_can_be_rewritten_back_across_evaluation() {
        let term = apply(lambda(1, Term::Var(1)), Term::Nil);
        let proof = Proof::Rewrite {
            equality: Box::new(Proof::Symm(Box::new(Proof::Step(term.clone())))),
            proof: Box::new(Proof::ListNil),
            variable: 99,
            template: is_list(Term::Var(99)),
        };

        assert!(check(&proof, &is_list(term)));
    }

    #[test]
    fn list_induction_proves_every_list_is_a_value() {
        let variable = 1;
        let head = 2;
        let tail = 3;
        let head_is_value_assumption = 4;
        let tail_is_list_assumption = 5;
        let induction_hypothesis_assumption = 6;
        let property = is_value(Term::Var(variable));
        let proof = Proof::ListInduction {
            variable,
            property: property.clone(),
            base: Box::new(Proof::ValueNil),
            head,
            tail,
            head_is_value_assumption,
            tail_is_list_assumption,
            induction_hypothesis_assumption,
            step: Box::new(Proof::ValueCons {
                head: Term::Var(head),
                tail: Term::Var(tail),
                head_is_value: Box::new(Proof::Assume(head_is_value_assumption)),
                tail_is_value: Box::new(Proof::Assume(induction_hypothesis_assumption)),
            }),
        };
        let expected = forall(
            variable,
            implies(is_list(Term::Var(variable)), is_value(Term::Var(variable))),
        );

        assert!(check(&proof, &expected));
    }

    #[test]
    fn list_induction_rejects_stale_step_variables() {
        let variable = 1;
        let head = 2;
        let tail = 3;
        let head_is_value_assumption = 4;
        let tail_is_list_assumption = 5;
        let induction_hypothesis_assumption = 6;
        let property = is_list(Term::Var(variable));
        let proof = Proof::ListInduction {
            variable,
            property,
            base: Box::new(Proof::ListNil),
            head,
            tail,
            head_is_value_assumption,
            tail_is_list_assumption,
            induction_hypothesis_assumption,
            step: Box::new(Proof::Assume(tail_is_list_assumption)),
        };
        let expected = forall(
            variable,
            implies(is_list(Term::Var(variable)), is_list(Term::Var(variable))),
        );

        assert!(!check(&proof, &expected));
    }

    #[test]
    fn assume_uses_context() {
        let prop = equal(Term::Quote(1), Term::Quote(1));
        let mut context = Context::new();
        context.insert(7, prop.clone());

        assert!(check_in_context(&Proof::Assume(7), &prop, &context));
        assert!(!check(&Proof::Assume(7), &prop));
    }

    #[test]
    fn implies_intro_and_elim_work() {
        let prop = equal(Term::Quote(1), Term::Quote(1));
        let proof = Proof::ImpliesElim {
            implication: Box::new(Proof::ImpliesIntro {
                assumption: 7,
                premise: prop.clone(),
                proof: Box::new(Proof::Assume(7)),
            }),
            premise: Box::new(Proof::Refl(Term::Quote(1))),
        };

        assert!(check(&proof, &prop));
    }

    #[test]
    fn forall_intro_and_elim_work() {
        let proof = Proof::ForAllElim {
            forall: Box::new(Proof::ForAllIntro {
                variable: 1,
                proof: Box::new(Proof::Refl(Term::Var(1))),
            }),
            argument: Term::Quote(2),
        };

        assert!(check(&proof, &equal(Term::Quote(2), Term::Quote(2))));
    }

    #[test]
    fn exists_intro_and_elim_work() {
        let body = equal(Term::Var(1), Term::Var(1));
        let conclusion = equal(Term::Quote(0), Term::Quote(0));
        let proof = Proof::ExistsElim {
            existential: Box::new(Proof::ExistsIntro {
                variable: 1,
                body,
                witness: Term::Quote(2),
                proof: Box::new(Proof::Refl(Term::Quote(2))),
            }),
            witness: 9,
            assumption: 7,
            proof: Box::new(Proof::Refl(Term::Quote(0))),
        };

        assert!(check(&proof, &conclusion));
    }

    #[test]
    fn and_or_rules_work() {
        let left = equal(Term::Quote(1), Term::Quote(1));
        let right = equal(Term::Quote(2), Term::Quote(2));
        let and_proof = Proof::AndIntro(
            Box::new(Proof::Refl(Term::Quote(1))),
            Box::new(Proof::Refl(Term::Quote(2))),
        );

        assert!(check(
            &Proof::AndElimLeft(Box::new(and_proof.clone())),
            &left
        ));
        assert!(check(&Proof::AndElimRight(Box::new(and_proof)), &right));

        let or_proof = Proof::OrElim {
            disjunction: Box::new(Proof::OrIntroLeft {
                proof: Box::new(Proof::Refl(Term::Quote(1))),
                right: left.clone(),
            }),
            left_assumption: 7,
            left_proof: Box::new(Proof::Assume(7)),
            right_assumption: 8,
            right_proof: Box::new(Proof::Assume(8)),
        };

        assert!(check(&or_proof, &left));
    }

    #[test]
    fn substitute_prop_avoids_quantifier_capture() {
        let prop = forall(2, equal(Term::Var(1), Term::Var(2)));

        assert_eq!(
            substitute_prop(&prop, 1, &Term::Var(2)),
            forall(0, equal(Term::Var(2), Term::Var(0)))
        );
    }

    #[test]
    fn exists_intro_uses_witness() {
        let body = equal(Term::Var(1), Term::Var(1));
        let proof = Proof::ExistsIntro {
            variable: 1,
            body: body.clone(),
            witness: Term::Quote(2),
            proof: Box::new(Proof::Refl(Term::Quote(2))),
        };

        assert!(check(&proof, &exists(1, body)));
    }

    #[test]
    fn prop_helpers_construct_expected_shapes() {
        let prop = equal(Term::Quote(1), Term::Quote(1));
        let term = apply(lambda(1, Term::Var(1)), Term::Quote(2));

        assert_eq!(
            implies(prop.clone(), prop.clone()),
            Prop::Implies(Box::new(prop.clone()), Box::new(prop))
        );
        assert_eq!(
            terminates(9, term.clone()),
            exists(
                9,
                and(
                    computes_to(term.clone(), Term::Var(9)),
                    is_value(Term::Var(9)),
                ),
            )
        );
        assert_eq!(
            computes_to_list(9, term.clone()),
            exists(
                9,
                and(
                    computes_to(term.clone(), Term::Var(9)),
                    is_list(Term::Var(9))
                ),
            )
        );
        assert_eq!(
            errors(9, term.clone()),
            exists(
                9,
                computes_to(term.clone(), Term::Error(Box::new(Term::Var(9)))),
            )
        );
        assert_eq!(
            reverse_accumulates(term.clone(), Term::Nil, Term::Var(9)),
            Prop::ReverseAccumulates {
                list: term.clone(),
                acc: Term::Nil,
                result: Term::Var(9),
            }
        );
        assert_eq!(diverges(term.clone()), computes_to(term, Term::Diverge));
        assert_eq!(
            or(is_value(Term::Quote(1)), is_list(Term::Nil)),
            Prop::Or(
                Box::new(Prop::IsValue(Term::Quote(1))),
                Box::new(Prop::IsList(Term::Nil))
            )
        );
    }
}
