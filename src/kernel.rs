use std::collections::{HashMap, HashSet};

pub mod prelude;

#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct Name(pub u64);

#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct Symbol(pub u64);

pub type Context = HashMap<Symbol, Prop>;

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Environment {
    terms: HashMap<Name, Term>,
    theorems: HashMap<Name, Prop>,
}

impl Environment {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn theorem(&self, name: Name) -> Option<&Prop> {
        self.theorems.get(&name)
    }

    pub fn term(&self, name: Name) -> Option<&Term> {
        self.terms.get(&name)
    }

    pub(crate) fn define_term(&mut self, name: Name, term: &Term) -> bool {
        if self.terms.contains_key(&name)
            || self.theorems.contains_key(&name)
            || !free_symbols(term).is_empty()
        {
            return false;
        }

        self.terms.insert(name, term.clone());
        true
    }

    pub(crate) fn define_theorem(&mut self, name: Name, theorem: &Theorem) -> bool {
        if self.terms.contains_key(&name) || self.theorems.contains_key(&name) {
            return false;
        }

        self.theorems.insert(name, theorem.prop().clone());
        true
    }
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Theory {
    environment: Environment,
}

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
    Const(Name),
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

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Theorem {
    prop: Prop,
    proof: Proof,
}

impl Theorem {
    pub fn from_proof(proof: Proof, prop: Prop) -> Option<Self> {
        check(&proof, &prop).then_some(Self { prop, proof })
    }

    fn from_proof_in_environment(
        proof: Proof,
        prop: Prop,
        environment: &Environment,
    ) -> Option<Self> {
        check_in_environment(&proof, &prop, environment).then_some(Self { prop, proof })
    }

    fn from_closed_proof(proof: Proof) -> Option<Self> {
        let prop = proven_prop(&proof, &Environment::new(), &Context::new())?;
        Some(Self { prop, proof })
    }

    fn from_closed_proof_in_environment(proof: Proof, environment: &Environment) -> Option<Self> {
        let prop = proven_prop(&proof, environment, &Context::new())?;
        Some(Self { prop, proof })
    }

    pub fn prop(&self) -> &Prop {
        &self.prop
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

impl Theory {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn from_environment(environment: Environment) -> Self {
        Self { environment }
    }

    pub fn environment(&self) -> &Environment {
        &self.environment
    }

    pub fn into_environment(self) -> Environment {
        self.environment
    }

    pub fn theorem(&self, name: Name) -> Option<&Prop> {
        self.environment.theorem(name)
    }

    pub fn term(&self, name: Name) -> Option<&Term> {
        self.environment.term(name)
    }

    pub fn define_term(&mut self, name: Name, term: &Term) -> bool {
        self.environment.define_term(name, term)
    }

    pub fn define_theorem(&mut self, name: Name, theorem: &Theorem) -> bool {
        if !self.check(&theorem.proof, theorem.prop()) {
            return false;
        }

        self.environment.define_theorem(name, theorem)
    }

    pub fn define_theorem_from_proof(
        &mut self,
        name: Name,
        proof: Proof,
        prop: Prop,
    ) -> Option<Theorem> {
        let theorem = self.from_proof(proof, prop)?;
        self.define_theorem(name, &theorem).then_some(theorem)
    }

    pub fn check(&self, proof: &Proof, prop: &Prop) -> bool {
        check_in_environment(proof, prop, &self.environment)
    }

    pub fn check_in_context(&self, proof: &Proof, prop: &Prop, context: &Context) -> bool {
        check_in_environment_and_context(proof, prop, &self.environment, context)
    }

    pub fn from_proof(&self, proof: Proof, prop: Prop) -> Option<Theorem> {
        Theorem::from_proof_in_environment(proof, prop, &self.environment)
    }

    fn from_closed_proof(&self, proof: Proof) -> Option<Theorem> {
        Theorem::from_closed_proof_in_environment(proof, &self.environment)
    }

    pub fn known(&self, name: Name) -> Option<Theorem> {
        self.from_closed_proof(Proof::Known(name))
    }

    pub fn reduce(&self, term: &Term) -> Step {
        step_in_environment(term, &self.environment)
    }

    pub fn normal_form(&self, term: &Term) -> Term {
        normal_form_in_environment(term, &self.environment)
    }

    pub fn refl(&self, term: Term) -> Theorem {
        Theorem::refl(term)
    }

    pub fn symm(&self, theorem: &Theorem) -> Option<Theorem> {
        self.from_closed_proof(Proof::Symm(Box::new(theorem.proof.clone())))
    }

    pub fn trans(&self, first: &Theorem, second: &Theorem) -> Option<Theorem> {
        self.from_closed_proof(Proof::Trans(
            Box::new(first.proof.clone()),
            Box::new(second.proof.clone()),
        ))
    }

    pub fn step(&self, term: Term) -> Option<Theorem> {
        self.from_closed_proof(Proof::Step(term))
    }

    pub fn steps(&self, terms: Vec<Term>) -> Option<Theorem> {
        self.from_closed_proof(Proof::Steps(terms))
    }

    pub fn rewrite(
        &self,
        equality: &Theorem,
        theorem: &Theorem,
        variable: Symbol,
        template: Prop,
    ) -> Option<Theorem> {
        self.from_closed_proof(Proof::Rewrite {
            equality: Box::new(equality.proof.clone()),
            proof: Box::new(theorem.proof.clone()),
            variable,
            template,
        })
    }

    pub fn beta(&self, lambda: Lambda, argument: Term) -> Option<Theorem> {
        self.from_closed_proof(Proof::Beta { lambda, argument })
    }

    pub fn value_lambda(&self, lambda: Lambda) -> Theorem {
        self.from_closed_proof(Proof::ValueLambda(lambda))
            .expect("value lambda theorem should be valid in every theory")
    }

    pub fn value_quote(&self, symbol: Symbol) -> Theorem {
        self.from_closed_proof(Proof::ValueQuote(symbol))
            .expect("value quote theorem should be valid in every theory")
    }

    pub fn value_nil(&self) -> Theorem {
        self.from_closed_proof(Proof::ValueNil)
            .expect("value nil theorem should be valid in every theory")
    }

    pub fn value_cons(
        &self,
        head: Term,
        tail: Term,
        head_is_value: &Theorem,
        tail_is_value: &Theorem,
    ) -> Option<Theorem> {
        self.from_closed_proof(Proof::ValueCons {
            head,
            tail,
            head_is_value: Box::new(head_is_value.proof.clone()),
            tail_is_value: Box::new(tail_is_value.proof.clone()),
        })
    }

    pub fn list_nil(&self) -> Theorem {
        self.from_closed_proof(Proof::ListNil)
            .expect("list nil theorem should be valid in every theory")
    }

    pub fn list_cons(
        &self,
        head: Term,
        tail: Term,
        head_is_value: &Theorem,
        tail_is_list: &Theorem,
    ) -> Option<Theorem> {
        self.from_closed_proof(Proof::ListCons {
            head,
            tail,
            head_is_value: Box::new(head_is_value.proof.clone()),
            tail_is_list: Box::new(tail_is_list.proof.clone()),
        })
    }

    pub fn implies_elim(&self, implication: &Theorem, premise: &Theorem) -> Option<Theorem> {
        self.from_closed_proof(Proof::ImpliesElim {
            implication: Box::new(implication.proof.clone()),
            premise: Box::new(premise.proof.clone()),
        })
    }

    pub fn forall_elim(&self, forall: &Theorem, argument: Term) -> Option<Theorem> {
        self.from_closed_proof(Proof::ForAllElim {
            forall: Box::new(forall.proof.clone()),
            argument,
        })
    }

    pub fn exists_intro(
        &self,
        variable: Symbol,
        body: Prop,
        witness: Term,
        proof: &Theorem,
    ) -> Option<Theorem> {
        self.from_closed_proof(Proof::ExistsIntro {
            variable,
            body,
            witness,
            proof: Box::new(proof.proof.clone()),
        })
    }

    pub fn and_intro(&self, left: &Theorem, right: &Theorem) -> Option<Theorem> {
        self.from_closed_proof(Proof::AndIntro(
            Box::new(left.proof.clone()),
            Box::new(right.proof.clone()),
        ))
    }

    pub fn and_elim_left(&self, theorem: &Theorem) -> Option<Theorem> {
        self.from_closed_proof(Proof::AndElimLeft(Box::new(theorem.proof.clone())))
    }

    pub fn and_elim_right(&self, theorem: &Theorem) -> Option<Theorem> {
        self.from_closed_proof(Proof::AndElimRight(Box::new(theorem.proof.clone())))
    }

    pub fn or_intro_left(&self, theorem: &Theorem, right: Prop) -> Option<Theorem> {
        self.from_closed_proof(Proof::OrIntroLeft {
            proof: Box::new(theorem.proof.clone()),
            right,
        })
    }

    pub fn or_intro_right(&self, left: Prop, theorem: &Theorem) -> Option<Theorem> {
        self.from_closed_proof(Proof::OrIntroRight {
            left,
            proof: Box::new(theorem.proof.clone()),
        })
    }
}

pub fn check(proof: &Proof, prop: &Prop) -> bool {
    check_in_context(proof, prop, &Context::new())
}

pub fn check_in_context(proof: &Proof, prop: &Prop, context: &Context) -> bool {
    check_in_environment_and_context(proof, prop, &Environment::new(), context)
}

pub fn check_in_environment(proof: &Proof, prop: &Prop, environment: &Environment) -> bool {
    check_in_environment_and_context(proof, prop, environment, &Context::new())
}

pub fn check_in_environment_and_context(
    proof: &Proof,
    prop: &Prop,
    environment: &Environment,
    context: &Context,
) -> bool {
    proven_prop(proof, environment, context).as_ref() == Some(prop)
}

fn proven_prop(proof: &Proof, environment: &Environment, context: &Context) -> Option<Prop> {
    match proof {
        Proof::Known(name) => environment.theorem(*name).cloned(),
        Proof::Assume(symbol) => context.get(symbol).cloned(),
        Proof::Refl(term) => Some(Prop::Equal(term.clone(), term.clone())),
        Proof::Symm(proof) => match proven_prop(proof, environment, context)? {
            Prop::Equal(left, right) => Some(Prop::Equal(right, left)),
            _ => None,
        },
        Proof::Trans(first, second) => {
            match (
                proven_prop(first, environment, context)?,
                proven_prop(second, environment, context)?,
            ) {
                (Prop::Equal(left, middle), Prop::Equal(second_middle, right))
                    if middle == second_middle =>
                {
                    Some(Prop::Equal(left, right))
                }
                _ => None,
            }
        }
        Proof::Step(term) => match step_in_environment(term, environment) {
            Step::Reduced(reduced) => Some(Prop::Equal(term.clone(), reduced)),
            Step::Normal => None,
        },
        Proof::Steps(terms) => proven_steps(terms, environment),
        Proof::Rewrite {
            equality,
            proof,
            variable,
            template,
        } => {
            let Prop::Equal(left, right) = proven_prop(equality, environment, context)? else {
                return None;
            };

            let left_instance = substitute_prop(template, *variable, &left);
            if proven_prop(proof, environment, context)? != left_instance {
                return None;
            }

            Some(substitute_prop(template, *variable, &right))
        }
        Proof::Beta { lambda, argument } => {
            if !argument_is_ready_for_beta(argument, environment) {
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
            proven_prop(head_is_value, environment, context)?,
            proven_prop(tail_is_value, environment, context)?,
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
            proven_prop(head_is_value, environment, context)?,
            proven_prop(tail_is_list, environment, context)?,
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

            prove_list_induction(environment, context, symbols, property, base, step)
        }
        Proof::ImpliesIntro {
            assumption,
            premise,
            proof,
        } => {
            let mut context = context.clone();
            context.insert(*assumption, premise.clone());
            let conclusion = proven_prop(proof, environment, &context)?;
            Some(Prop::Implies(
                Box::new(premise.clone()),
                Box::new(conclusion),
            ))
        }
        Proof::ImpliesElim {
            implication,
            premise,
        } => {
            let premise = proven_prop(premise, environment, context)?;
            match proven_prop(implication, environment, context)? {
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
            let body = proven_prop(proof, environment, context)?;
            Some(Prop::ForAll {
                variable: *variable,
                body: Box::new(body),
            })
        }
        Proof::ForAllElim { forall, argument } => {
            match proven_prop(forall, environment, context)? {
                Prop::ForAll { variable, body } => Some(substitute_prop(&body, variable, argument)),
                _ => None,
            }
        }
        Proof::ExistsIntro {
            variable,
            body,
            witness,
            proof,
        } => {
            let witness_body = substitute_prop(body, *variable, witness);
            if proven_prop(proof, environment, context)? == witness_body {
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
        } => match proven_prop(existential, environment, context)? {
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
                let conclusion = proven_prop(proof, environment, &context)?;

                if prop_mentions_symbol(&conclusion, *witness) {
                    None
                } else {
                    Some(conclusion)
                }
            }
            _ => None,
        },
        Proof::AndIntro(left, right) => Some(Prop::And(
            Box::new(proven_prop(left, environment, context)?),
            Box::new(proven_prop(right, environment, context)?),
        )),
        Proof::AndElimLeft(proof) => match proven_prop(proof, environment, context)? {
            Prop::And(left, _) => Some(*left),
            _ => None,
        },
        Proof::AndElimRight(proof) => match proven_prop(proof, environment, context)? {
            Prop::And(_, right) => Some(*right),
            _ => None,
        },
        Proof::OrIntroLeft { proof, right } => Some(Prop::Or(
            Box::new(proven_prop(proof, environment, context)?),
            Box::new(right.clone()),
        )),
        Proof::OrIntroRight { left, proof } => Some(Prop::Or(
            Box::new(left.clone()),
            Box::new(proven_prop(proof, environment, context)?),
        )),
        Proof::OrElim {
            disjunction,
            left_assumption,
            left_proof,
            right_assumption,
            right_proof,
        } => match proven_prop(disjunction, environment, context)? {
            Prop::Or(left, right) => {
                let mut left_context = context.clone();
                left_context.insert(*left_assumption, *left);
                let left_conclusion = proven_prop(left_proof, environment, &left_context)?;

                let mut right_context = context.clone();
                right_context.insert(*right_assumption, *right);
                let right_conclusion = proven_prop(right_proof, environment, &right_context)?;

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

fn proven_steps(terms: &[Term], environment: &Environment) -> Option<Prop> {
    let (first, rest) = terms.split_first()?;
    let mut previous = first;

    for next in rest {
        match step_in_environment(previous, environment) {
            Step::Reduced(reduced) if &reduced == next => previous = next,
            _ => return None,
        }
    }

    Some(Prop::Equal(first.clone(), previous.clone()))
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
    environment: &Environment,
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
    if proven_prop(base, environment, context)? != base_prop {
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

    if proven_prop(step, environment, &step_context)? != step_prop {
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

    let mut symbol = Symbol(0);
    while symbols.contains(&symbol) {
        symbol = Symbol(symbol.0 + 1);
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

pub fn step(term: &Term) -> Step {
    step_in_environment(term, &Environment::new())
}

pub fn step_in_environment(term: &Term, environment: &Environment) -> Step {
    match term {
        Term::Apply { function, argument } => step_apply(function, argument, environment),
        Term::Lambda(_) => Step::Normal,
        Term::Nil => Step::Normal,
        Term::Cons { head, tail } => step_cons(head, tail, environment),
        Term::Head(term) => step_head(term, environment),
        Term::Tail(term) => step_tail(term, environment),
        Term::ListCase(list_case) => step_list_case(list_case, environment),
        Term::Const(name) => match environment.term(*name) {
            Some(term) => Step::Reduced(term.clone()),
            None => Step::Normal,
        },
        Term::Error(_) | Term::Diverge => Step::Normal,
        Term::Var(_) | Term::Quote(_) => Step::Normal,
    }
}

fn step_apply(function: &Term, argument: &Term, environment: &Environment) -> Step {
    match function {
        Term::Lambda(lambda) => step_lambda_application(lambda, argument, environment),
        Term::Error(_) | Term::Diverge => Step::Reduced(function.clone()),
        _ => match step_in_environment(function, environment) {
            Step::Reduced(function) => Step::Reduced(Term::Apply {
                function: Box::new(function),
                argument: Box::new(argument.clone()),
            }),
            Step::Normal if is_known_non_callable(function) => {
                Step::Reduced(runtime_error(function.clone()))
            }
            Step::Normal => step_neutral_application(function, argument, environment),
        },
    }
}

fn step_lambda_application(lambda: &Lambda, argument: &Term, environment: &Environment) -> Step {
    match step_in_environment(argument, environment) {
        Step::Reduced(argument) => Step::Reduced(Term::Apply {
            function: Box::new(Term::Lambda(lambda.clone())),
            argument: Box::new(argument),
        }),
        Step::Normal if is_effect(argument) => Step::Reduced(argument.clone()),
        Step::Normal => Step::Reduced(substitute(lambda.body.as_ref(), lambda.parameter, argument)),
    }
}

fn step_neutral_application(function: &Term, argument: &Term, environment: &Environment) -> Step {
    match step_in_environment(argument, environment) {
        Step::Reduced(argument) => Step::Reduced(Term::Apply {
            function: Box::new(function.clone()),
            argument: Box::new(argument),
        }),
        Step::Normal if is_effect(argument) => Step::Reduced(argument.clone()),
        Step::Normal => Step::Normal,
    }
}

fn argument_is_ready_for_beta(argument: &Term, environment: &Environment) -> bool {
    match step_in_environment(argument, environment) {
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

fn step_cons(head: &Term, tail: &Term, environment: &Environment) -> Step {
    match step_in_environment(head, environment) {
        Step::Reduced(head) => Step::Reduced(Term::Cons {
            head: Box::new(head),
            tail: Box::new(tail.clone()),
        }),
        Step::Normal if is_effect(head) => Step::Reduced(head.clone()),
        Step::Normal => match step_in_environment(tail, environment) {
            Step::Reduced(tail) => Step::Reduced(Term::Cons {
                head: Box::new(head.clone()),
                tail: Box::new(tail),
            }),
            Step::Normal if is_effect(tail) => Step::Reduced(tail.clone()),
            Step::Normal => Step::Normal,
        },
    }
}

fn step_head(term: &Term, environment: &Environment) -> Step {
    match step_in_environment(term, environment) {
        Step::Reduced(term) => Step::Reduced(Term::Head(Box::new(term))),
        Step::Normal => match term {
            Term::Cons { head, .. } => Step::Reduced(head.as_ref().clone()),
            Term::Error(_) | Term::Diverge => Step::Reduced(term.clone()),
            Term::Const(_)
            | Term::Var(_)
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

fn step_tail(term: &Term, environment: &Environment) -> Step {
    match step_in_environment(term, environment) {
        Step::Reduced(term) => Step::Reduced(Term::Tail(Box::new(term))),
        Step::Normal => match term {
            Term::Cons { tail, .. } => Step::Reduced(tail.as_ref().clone()),
            Term::Error(_) | Term::Diverge => Step::Reduced(term.clone()),
            Term::Const(_)
            | Term::Var(_)
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

fn step_list_case(list_case: &ListCase, environment: &Environment) -> Step {
    match step_in_environment(list_case.list.as_ref(), environment) {
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
            Term::Const(_)
            | Term::Var(_)
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
    normal_form_in_environment(term, &Environment::new())
}

pub fn normal_form_in_environment(term: &Term, environment: &Environment) -> Term {
    let mut term = term.clone();
    loop {
        match step_in_environment(&term, environment) {
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
        Term::Const(_) | Term::Diverge => {}
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
        Term::Const(_) | Term::Diverge => term.clone(),
        Term::Var(symbol) if *symbol == old => Term::Var(new),
        Term::Var(_) | Term::Quote(_) => term.clone(),
    }
}

fn fresh_symbol(term: &Term, replacement: &Term, variable: Symbol) -> Symbol {
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
        Term::Const(_) | Term::Diverge => {}
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
        let term = apply(
            lambda(Symbol(1), Term::Var(Symbol(1))),
            Term::Quote(Symbol(2)),
        );

        assert_eq!(step(&term), Step::Reduced(Term::Quote(Symbol(2))));
    }

    #[test]
    fn application_reduces_argument_before_beta() {
        let term = apply(
            lambda(Symbol(1), Term::Quote(Symbol(9))),
            apply(
                lambda(Symbol(2), Term::Var(Symbol(2))),
                Term::Quote(Symbol(3)),
            ),
        );

        assert_eq!(
            step(&term),
            Step::Reduced(apply(
                lambda(Symbol(1), Term::Quote(Symbol(9))),
                Term::Quote(Symbol(3))
            ))
        );
        assert_eq!(normal_form(&term), Term::Quote(Symbol(9)));
    }

    #[test]
    fn lambda_is_a_value_without_evaluating_body() {
        let term = lambda(
            Symbol(1),
            apply(
                lambda(Symbol(2), Term::Var(Symbol(2))),
                Term::Var(Symbol(1)),
            ),
        );

        assert_eq!(step(&term), Step::Normal);
    }

    #[test]
    fn is_value_distinguishes_values_from_pending_computations() {
        assert!(term_is_value(&Term::Nil));
        assert!(term_is_value(&Term::Quote(Symbol(1))));
        assert!(term_is_value(&lambda(Symbol(1), Term::Var(Symbol(1)))));
        assert!(term_is_value(&cons(Term::Quote(Symbol(1)), Term::Nil)));

        assert!(!term_is_value(&apply(
            Term::Var(Symbol(1)),
            Term::Quote(Symbol(2))
        )));
        assert!(!term_is_value(&Term::Diverge));
        assert!(!term_is_value(&error(Term::Quote(Symbol(1)))));
        assert!(!term_is_value(&Term::Var(Symbol(1))));
        assert_eq!(step(&Term::Var(Symbol(1))), Step::Normal);
    }

    #[test]
    fn application_propagates_effects() {
        let thrown = error(Term::Quote(Symbol(1)));

        assert_eq!(
            normal_form(&apply(thrown.clone(), Term::Quote(Symbol(2)))),
            thrown.clone()
        );
        assert_eq!(
            normal_form(&apply(
                lambda(Symbol(1), Term::Quote(Symbol(2))),
                thrown.clone()
            )),
            thrown
        );
        assert_eq!(
            normal_form(&apply(
                lambda(Symbol(1), Term::Quote(Symbol(2))),
                Term::Diverge
            )),
            Term::Diverge
        );
    }

    #[test]
    fn apply_known_non_callable_reduces_to_error() {
        let term = apply(Term::Nil, Term::Quote(Symbol(2)));

        assert_eq!(step(&term), Step::Reduced(error(Term::Nil)));
    }

    #[test]
    fn cons_evaluates_head_then_tail_and_propagates_effects() {
        let term = cons(
            apply(
                lambda(Symbol(1), Term::Var(Symbol(1))),
                Term::Quote(Symbol(2)),
            ),
            error(Term::Quote(Symbol(3))),
        );

        assert_eq!(
            step(&term),
            Step::Reduced(cons(Term::Quote(Symbol(2)), error(Term::Quote(Symbol(3)))))
        );
        assert_eq!(normal_form(&term), error(Term::Quote(Symbol(3))));
    }

    #[test]
    fn head_and_tail_destructure_cons() {
        let term = cons(Term::Quote(Symbol(1)), Term::Quote(Symbol(2)));

        assert_eq!(
            step(&head(term.clone())),
            Step::Reduced(Term::Quote(Symbol(1)))
        );
        assert_eq!(step(&tail(term)), Step::Reduced(Term::Quote(Symbol(2))));
    }

    #[test]
    fn head_and_tail_open_terms_are_neutral() {
        assert_eq!(step(&head(Term::Var(Symbol(1)))), Step::Normal);
        assert_eq!(step(&tail(Term::Var(Symbol(1)))), Step::Normal);
    }

    #[test]
    fn head_and_tail_known_non_cons_reduce_to_error() {
        assert_eq!(step(&head(Term::Nil)), Step::Reduced(error(Term::Nil)));
        assert_eq!(step(&tail(Term::Nil)), Step::Reduced(error(Term::Nil)));
    }

    #[test]
    fn list_case_reduces_nil_and_cons() {
        let cons_value = cons(Term::Quote(Symbol(1)), Term::Nil);
        let cons_case = head(Term::Var(Symbol(9)));

        assert_eq!(
            step(&list_case(
                Term::Nil,
                Term::Quote(Symbol(0)),
                Symbol(9),
                cons_case.clone(),
            )),
            Step::Reduced(Term::Quote(Symbol(0)))
        );
        assert_eq!(
            normal_form(&list_case(
                cons_value,
                Term::Quote(Symbol(0)),
                Symbol(9),
                cons_case,
            )),
            Term::Quote(Symbol(1))
        );
    }

    #[test]
    fn list_case_open_term_is_neutral_and_known_non_list_reduces_to_error() {
        assert_eq!(
            step(&list_case(
                Term::Var(Symbol(1)),
                Term::Quote(Symbol(0)),
                Symbol(9),
                Term::Quote(Symbol(1)),
            )),
            Step::Normal
        );
        assert_eq!(
            step(&list_case(
                Term::Quote(Symbol(1)),
                Term::Quote(Symbol(0)),
                Symbol(9),
                Term::Quote(Symbol(1))
            )),
            Step::Reduced(error(Term::Quote(Symbol(1))))
        );
    }

    #[test]
    fn substitution_descends_into_cons_and_destructors() {
        let term = cons(head(Term::Var(Symbol(1))), tail(Term::Var(Symbol(2))));

        assert_eq!(
            substitute(&term, Symbol(1), &Term::Quote(Symbol(3))),
            cons(head(Term::Quote(Symbol(3))), tail(Term::Var(Symbol(2))))
        );
    }

    #[test]
    fn substitution_avoids_lambda_capture() {
        let term = lambda(Symbol(2), Term::Var(Symbol(1)));

        assert_eq!(
            substitute(&term, Symbol(1), &Term::Var(Symbol(2))),
            lambda(Symbol(0), Term::Var(Symbol(2)))
        );
    }

    #[test]
    fn substitution_avoids_list_case_capture() {
        let term = list_case(
            Term::Var(Symbol(1)),
            Term::Quote(Symbol(0)),
            Symbol(2),
            Term::Var(Symbol(3)),
        );

        assert_eq!(
            substitute(&term, Symbol(3), &Term::Var(Symbol(2))),
            list_case(
                Term::Var(Symbol(1)),
                Term::Quote(Symbol(0)),
                Symbol(4),
                Term::Var(Symbol(2))
            )
        );
    }

    #[test]
    fn free_symbols_ignore_list_case_cons_binder() {
        assert_eq!(
            free_symbols(&list_case(
                Term::Var(Symbol(1)),
                Term::Var(Symbol(2)),
                Symbol(3),
                apply(Term::Var(Symbol(3)), Term::Var(Symbol(4)))
            )),
            HashSet::from([Symbol(1), Symbol(2), Symbol(4)])
        );
    }

    #[test]
    fn step_proof_proves_one_step_reduction() {
        let term = head(cons(Term::Quote(Symbol(1)), Term::Nil));

        assert!(check(
            &Proof::Step(term.clone()),
            &equal(term, Term::Quote(Symbol(1)))
        ));
    }

    #[test]
    fn steps_proof_proves_multi_step_reduction() {
        let start = apply(
            lambda(Symbol(1), Term::Quote(Symbol(9))),
            apply(
                lambda(Symbol(2), Term::Var(Symbol(2))),
                Term::Quote(Symbol(3)),
            ),
        );
        let middle = apply(
            lambda(Symbol(1), Term::Quote(Symbol(9))),
            Term::Quote(Symbol(3)),
        );
        let end = Term::Quote(Symbol(9));

        assert!(check(
            &Proof::Steps(vec![start.clone(), middle, end.clone()]),
            &equal(start, end)
        ));
    }

    #[test]
    fn theorem_from_proof_checks_closed_proofs() {
        let valid = Theorem::from_proof(
            Proof::Refl(Term::Quote(Symbol(1))),
            equal(Term::Quote(Symbol(1)), Term::Quote(Symbol(1))),
        );
        let invalid = Theorem::from_proof(
            Proof::Refl(Term::Quote(Symbol(1))),
            equal(Term::Quote(Symbol(1)), Term::Quote(Symbol(2))),
        );

        assert!(valid.is_some());
        assert!(invalid.is_none());
        assert!(
            Theorem::from_proof(
                Proof::Assume(Symbol(7)),
                equal(Term::Quote(Symbol(1)), Term::Quote(Symbol(1)))
            )
            .is_none()
        );
    }

    #[test]
    fn theory_known_proofs_cite_named_theorems() {
        let name = Name(42);
        let theorem = Theorem::refl(Term::Quote(Symbol(1)));
        let replacement = Theorem::refl(Term::Quote(Symbol(2)));
        let mut theory = Theory::new();

        assert!(theory.define_theorem(name, &theorem));
        assert!(!theory.define_theorem(name, &replacement));
        assert_eq!(theory.theorem(name), Some(theorem.prop()));
        assert!(theory.check(&Proof::Known(name), theorem.prop()));
        assert!(!check(&Proof::Known(name), theorem.prop()));

        let known = theory.known(name).expect("known theorem should check");
        assert_eq!(known.prop(), theorem.prop());
    }

    #[test]
    fn theory_defines_closed_terms() {
        let name = Name(4);
        let term = Term::Quote(Symbol(1));
        let replacement = Term::Quote(Symbol(2));
        let theorem = Theorem::refl(Term::Nil);
        let mut theory = Theory::new();

        assert!(theory.define_term(name, &term));
        assert_eq!(theory.term(name), Some(&term));
        assert!(!theory.define_term(name, &replacement));
        assert!(!theory.define_theorem(name, &theorem));
        assert!(!theory.define_term(Name(5), &Term::Var(Symbol(1))));

        assert!(theory.define_theorem(Name(6), &theorem));
        assert!(!theory.define_term(Name(6), &Term::Nil));
    }

    #[test]
    fn term_definitions_unfold_during_evaluation() {
        let id = Name(8);
        let id_term = lambda(Symbol(1), Term::Var(Symbol(1)));
        let argument = Term::Quote(Symbol(2));
        let call = apply(Term::Const(id), argument.clone());
        let mut theory = Theory::new();

        assert_eq!(step(&Term::Const(id)), Step::Normal);
        assert_eq!(
            step(&apply(Term::Const(Name(9)), argument.clone())),
            Step::Normal
        );

        assert!(theory.define_term(id, &id_term));
        assert_eq!(
            theory.reduce(&Term::Const(id)),
            Step::Reduced(id_term.clone())
        );
        assert_eq!(theory.normal_form(&call), argument.clone());
        assert_eq!(normal_form(&call), call);
    }

    #[test]
    fn step_proofs_use_environment_term_definitions() {
        let name = Name(11);
        let term = Term::Const(name);
        let value = Term::Quote(Symbol(7));
        let mut theory = Theory::new();

        assert!(theory.define_term(name, &value));
        assert!(theory.check(
            &Proof::Step(term.clone()),
            &equal(term.clone(), value.clone())
        ));
        assert!(!check(
            &Proof::Step(term.clone()),
            &equal(term.clone(), value.clone())
        ));

        let theorem = theory
            .step(term.clone())
            .expect("defined constant should step");
        assert_eq!(theorem.prop(), &equal(term, value));
    }

    #[test]
    fn raw_checker_known_proofs_compose_with_rules() {
        let start = head(cons(Term::Quote(Symbol(1)), Term::Nil));
        let end = Term::Quote(Symbol(1));
        let step = Theorem::step(start.clone()).expect("term should step");
        let mut environment = Environment::new();

        assert!(environment.define_theorem(Name(7), &step));
        assert!(check_in_environment(
            &Proof::Symm(Box::new(Proof::Known(Name(7)))),
            &equal(end, start),
            &environment,
        ));
    }

    #[test]
    fn theory_combinators_use_their_environment() {
        let start = head(cons(Term::Quote(Symbol(1)), Term::Nil));
        let end = Term::Quote(Symbol(1));
        let step = Theorem::step(start.clone()).expect("term should step");
        let mut theory = Theory::new();

        assert!(theory.define_theorem(Name(7), &step));
        let known = theory.known(Name(7)).expect("known theorem should check");

        assert!(Theorem::symm(&known).is_none());
        assert_eq!(
            theory
                .symm(&known)
                .expect("known theorem should compose")
                .prop(),
            &equal(end, start)
        );
    }

    #[test]
    fn theorem_equality_rules_build_checked_theorems() {
        let start = apply(
            lambda(Symbol(1), Term::Var(Symbol(1))),
            Term::Quote(Symbol(2)),
        );
        let step = Theorem::step(start.clone()).expect("term should step");
        let refl = Theorem::refl(Term::Quote(Symbol(2)));
        let trans = Theorem::trans(&step, &refl).expect("equalities should chain");
        let symm = Theorem::symm(&step).expect("step equality should be symmetric");

        assert_eq!(step.prop(), &equal(start.clone(), Term::Quote(Symbol(2))));
        assert_eq!(trans.prop(), &equal(start.clone(), Term::Quote(Symbol(2))));
        assert_eq!(symm.prop(), &equal(Term::Quote(Symbol(2)), start));
        assert!(Theorem::step(Term::Quote(Symbol(2))).is_none());
    }

    #[test]
    fn theorem_rewrite_moves_props_across_equality() {
        let term = apply(lambda(Symbol(1), Term::Var(Symbol(1))), Term::Nil);
        let step = Theorem::step(term.clone()).expect("term should step");
        let nil_to_term = Theorem::symm(&step).expect("step should be symmetric");
        let theorem = Theorem::rewrite(
            &nil_to_term,
            &Theorem::list_nil(),
            Symbol(99),
            is_list(Term::Var(Symbol(99))),
        )
        .expect("rewrite should prove listness before evaluation");

        assert_eq!(theorem.prop(), &is_list(term));
    }

    #[test]
    fn theorem_value_and_list_rules_build_checked_theorems() {
        let head = Term::Quote(Symbol(1));
        let tail = Term::Nil;
        let head_value = Theorem::value_quote(Symbol(1));
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
    fn theorem_first_order_rules_build_checked_theorems() {
        let prop = equal(Term::Quote(Symbol(1)), Term::Quote(Symbol(1)));
        let implication = Theorem::from_proof(
            Proof::ImpliesIntro {
                assumption: Symbol(7),
                premise: prop.clone(),
                proof: Box::new(Proof::Assume(Symbol(7))),
            },
            implies(prop.clone(), prop.clone()),
        )
        .expect("identity implication should check");
        let conclusion =
            Theorem::implies_elim(&implication, &Theorem::refl(Term::Quote(Symbol(1))))
                .expect("modus ponens should apply");
        let universal = Theorem::from_proof(
            Proof::ForAllIntro {
                variable: Symbol(1),
                proof: Box::new(Proof::Refl(Term::Var(Symbol(1)))),
            },
            forall(Symbol(1), equal(Term::Var(Symbol(1)), Term::Var(Symbol(1)))),
        )
        .expect("forall intro should check");
        let instance = Theorem::forall_elim(&universal, Term::Quote(Symbol(2)))
            .expect("forall theorem should instantiate");

        assert_eq!(conclusion.prop(), &prop);
        assert_eq!(
            instance.prop(),
            &equal(Term::Quote(Symbol(2)), Term::Quote(Symbol(2)))
        );
    }

    #[test]
    fn rewrite_uses_equality_inside_template() {
        let start = head(cons(Term::Quote(Symbol(1)), Term::Nil));
        let end = Term::Quote(Symbol(1));
        let template = equal(
            cons(Term::Var(Symbol(99)), Term::Nil),
            cons(Term::Var(Symbol(99)), Term::Nil),
        );
        let left_instance = substitute_prop(&template, Symbol(99), &start);
        let right_instance = substitute_prop(&template, Symbol(99), &end);
        let proof = Proof::Rewrite {
            equality: Box::new(Proof::Step(start)),
            proof: Box::new(Proof::Refl(match left_instance.clone() {
                Prop::Equal(left, _) => left,
                _ => unreachable!(),
            })),
            variable: Symbol(99),
            template,
        };

        assert!(check(&proof, &right_instance));
    }

    #[test]
    fn beta_proof_rejects_reducible_arguments() {
        let lam = Lambda {
            parameter: Symbol(1),
            body: Box::new(Term::Quote(Symbol(9))),
        };
        let argument = apply(
            lambda(Symbol(2), Term::Var(Symbol(2))),
            Term::Quote(Symbol(3)),
        );

        assert!(!check(
            &Proof::Beta {
                lambda: lam.clone(),
                argument: argument.clone()
            },
            &Prop::Equal(apply(Term::Lambda(lam), argument), Term::Quote(Symbol(9)))
        ));
    }

    #[test]
    fn value_intro_rules_prove_concrete_values() {
        let lambda = Lambda {
            parameter: Symbol(1),
            body: Box::new(Term::Var(Symbol(1))),
        };
        let list = cons(Term::Quote(Symbol(1)), Term::Nil);
        let proof = Proof::ValueCons {
            head: Term::Quote(Symbol(1)),
            tail: Term::Nil,
            head_is_value: Box::new(Proof::ValueQuote(Symbol(1))),
            tail_is_value: Box::new(Proof::ValueNil),
        };

        assert!(check(
            &Proof::ValueLambda(lambda.clone()),
            &is_value(Term::Lambda(lambda))
        ));
        assert!(check(
            &Proof::ValueQuote(Symbol(1)),
            &is_value(Term::Quote(Symbol(1)))
        ));
        assert!(check(&Proof::ValueNil, &is_value(Term::Nil)));
        assert!(check(&proof, &is_value(list)));
    }

    #[test]
    fn value_cons_requires_matching_value_proofs() {
        let proof = Proof::ValueCons {
            head: Term::Diverge,
            tail: Term::Nil,
            head_is_value: Box::new(Proof::ValueQuote(Symbol(1))),
            tail_is_value: Box::new(Proof::ValueNil),
        };

        assert!(!check(&proof, &is_value(cons(Term::Diverge, Term::Nil))));
    }

    #[test]
    fn list_intro_rules_prove_concrete_lists() {
        let list = cons(
            Term::Quote(Symbol(1)),
            cons(Term::Quote(Symbol(2)), Term::Nil),
        );
        let proof = Proof::ListCons {
            head: Term::Quote(Symbol(1)),
            tail: cons(Term::Quote(Symbol(2)), Term::Nil),
            head_is_value: Box::new(Proof::ValueQuote(Symbol(1))),
            tail_is_list: Box::new(Proof::ListCons {
                head: Term::Quote(Symbol(2)),
                tail: Term::Nil,
                head_is_value: Box::new(Proof::ValueQuote(Symbol(2))),
                tail_is_list: Box::new(Proof::ListNil),
            }),
        };

        assert!(check(&Proof::ListNil, &is_list(Term::Nil)));
        assert!(check(&proof, &is_list(list)));
    }

    #[test]
    fn list_cons_requires_tail_list_proof_for_the_same_tail() {
        let proof = Proof::ListCons {
            head: Term::Quote(Symbol(1)),
            tail: cons(Term::Quote(Symbol(2)), Term::Nil),
            head_is_value: Box::new(Proof::ValueQuote(Symbol(1))),
            tail_is_list: Box::new(Proof::ListNil),
        };

        assert!(!check(
            &proof,
            &is_list(cons(
                Term::Quote(Symbol(1)),
                cons(Term::Quote(Symbol(2)), Term::Nil)
            ))
        ));
    }

    #[test]
    fn list_cons_requires_head_value_proof_for_the_same_head() {
        let proof = Proof::ListCons {
            head: Term::Diverge,
            tail: Term::Nil,
            head_is_value: Box::new(Proof::ValueQuote(Symbol(1))),
            tail_is_list: Box::new(Proof::ListNil),
        };

        assert!(!check(&proof, &is_list(cons(Term::Diverge, Term::Nil))));
    }

    #[test]
    fn is_list_can_be_rewritten_back_across_evaluation() {
        let term = apply(lambda(Symbol(1), Term::Var(Symbol(1))), Term::Nil);
        let proof = Proof::Rewrite {
            equality: Box::new(Proof::Symm(Box::new(Proof::Step(term.clone())))),
            proof: Box::new(Proof::ListNil),
            variable: Symbol(99),
            template: is_list(Term::Var(Symbol(99))),
        };

        assert!(check(&proof, &is_list(term)));
    }

    #[test]
    fn list_induction_proves_every_list_is_a_value() {
        let variable = Symbol(1);
        let head = Symbol(2);
        let tail = Symbol(3);
        let head_is_value_assumption = Symbol(4);
        let tail_is_list_assumption = Symbol(5);
        let induction_hypothesis_assumption = Symbol(6);
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
        let variable = Symbol(1);
        let head = Symbol(2);
        let tail = Symbol(3);
        let head_is_value_assumption = Symbol(4);
        let tail_is_list_assumption = Symbol(5);
        let induction_hypothesis_assumption = Symbol(6);
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
        let prop = equal(Term::Quote(Symbol(1)), Term::Quote(Symbol(1)));
        let mut context = Context::new();
        context.insert(Symbol(7), prop.clone());

        assert!(check_in_context(&Proof::Assume(Symbol(7)), &prop, &context));
        assert!(!check(&Proof::Assume(Symbol(7)), &prop));
    }

    #[test]
    fn implies_intro_and_elim_work() {
        let prop = equal(Term::Quote(Symbol(1)), Term::Quote(Symbol(1)));
        let proof = Proof::ImpliesElim {
            implication: Box::new(Proof::ImpliesIntro {
                assumption: Symbol(7),
                premise: prop.clone(),
                proof: Box::new(Proof::Assume(Symbol(7))),
            }),
            premise: Box::new(Proof::Refl(Term::Quote(Symbol(1)))),
        };

        assert!(check(&proof, &prop));
    }

    #[test]
    fn forall_intro_and_elim_work() {
        let proof = Proof::ForAllElim {
            forall: Box::new(Proof::ForAllIntro {
                variable: Symbol(1),
                proof: Box::new(Proof::Refl(Term::Var(Symbol(1)))),
            }),
            argument: Term::Quote(Symbol(2)),
        };

        assert!(check(
            &proof,
            &equal(Term::Quote(Symbol(2)), Term::Quote(Symbol(2)))
        ));
    }

    #[test]
    fn exists_intro_and_elim_work() {
        let body = equal(Term::Var(Symbol(1)), Term::Var(Symbol(1)));
        let conclusion = equal(Term::Quote(Symbol(0)), Term::Quote(Symbol(0)));
        let proof = Proof::ExistsElim {
            existential: Box::new(Proof::ExistsIntro {
                variable: Symbol(1),
                body,
                witness: Term::Quote(Symbol(2)),
                proof: Box::new(Proof::Refl(Term::Quote(Symbol(2)))),
            }),
            witness: Symbol(9),
            assumption: Symbol(7),
            proof: Box::new(Proof::Refl(Term::Quote(Symbol(0)))),
        };

        assert!(check(&proof, &conclusion));
    }

    #[test]
    fn and_or_rules_work() {
        let left = equal(Term::Quote(Symbol(1)), Term::Quote(Symbol(1)));
        let right = equal(Term::Quote(Symbol(2)), Term::Quote(Symbol(2)));
        let and_proof = Proof::AndIntro(
            Box::new(Proof::Refl(Term::Quote(Symbol(1)))),
            Box::new(Proof::Refl(Term::Quote(Symbol(2)))),
        );

        assert!(check(
            &Proof::AndElimLeft(Box::new(and_proof.clone())),
            &left
        ));
        assert!(check(&Proof::AndElimRight(Box::new(and_proof)), &right));

        let or_proof = Proof::OrElim {
            disjunction: Box::new(Proof::OrIntroLeft {
                proof: Box::new(Proof::Refl(Term::Quote(Symbol(1)))),
                right: left.clone(),
            }),
            left_assumption: Symbol(7),
            left_proof: Box::new(Proof::Assume(Symbol(7))),
            right_assumption: Symbol(8),
            right_proof: Box::new(Proof::Assume(Symbol(8))),
        };

        assert!(check(&or_proof, &left));
    }

    #[test]
    fn substitute_prop_avoids_quantifier_capture() {
        let prop = forall(Symbol(2), equal(Term::Var(Symbol(1)), Term::Var(Symbol(2))));

        assert_eq!(
            substitute_prop(&prop, Symbol(1), &Term::Var(Symbol(2))),
            forall(Symbol(0), equal(Term::Var(Symbol(2)), Term::Var(Symbol(0))))
        );
    }

    #[test]
    fn exists_intro_uses_witness() {
        let body = equal(Term::Var(Symbol(1)), Term::Var(Symbol(1)));
        let proof = Proof::ExistsIntro {
            variable: Symbol(1),
            body: body.clone(),
            witness: Term::Quote(Symbol(2)),
            proof: Box::new(Proof::Refl(Term::Quote(Symbol(2)))),
        };

        assert!(check(&proof, &exists(Symbol(1), body)));
    }

    #[test]
    fn prop_helpers_construct_expected_shapes() {
        let prop = equal(Term::Quote(Symbol(1)), Term::Quote(Symbol(1)));
        let term = apply(
            lambda(Symbol(1), Term::Var(Symbol(1))),
            Term::Quote(Symbol(2)),
        );

        assert_eq!(
            implies(prop.clone(), prop.clone()),
            Prop::Implies(Box::new(prop.clone()), Box::new(prop))
        );
        assert_eq!(
            terminates(Symbol(9), term.clone()),
            exists(
                Symbol(9),
                and(
                    computes_to(term.clone(), Term::Var(Symbol(9))),
                    is_value(Term::Var(Symbol(9))),
                ),
            )
        );
        assert_eq!(
            computes_to_list(Symbol(9), term.clone()),
            exists(
                Symbol(9),
                and(
                    computes_to(term.clone(), Term::Var(Symbol(9))),
                    is_list(Term::Var(Symbol(9)))
                ),
            )
        );
        assert_eq!(
            errors(Symbol(9), term.clone()),
            exists(
                Symbol(9),
                computes_to(term.clone(), Term::Error(Box::new(Term::Var(Symbol(9))))),
            )
        );
        assert_eq!(diverges(term.clone()), computes_to(term, Term::Diverge));
        assert_eq!(
            or(is_value(Term::Quote(Symbol(1))), is_list(Term::Nil)),
            Prop::Or(
                Box::new(Prop::IsValue(Term::Quote(Symbol(1)))),
                Box::new(Prop::IsList(Term::Nil))
            )
        );
    }
}
