use std::collections::HashMap;

use super::{
    calculus::*,
    check::{check, check_in_bindings, check_in_bindings_and_context, proven_prop},
    eval::{normal_form_in_bindings, normal_outcome_in_bindings, step_in_bindings},
};

pub type Context = HashMap<Symbol, Prop>;

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub(crate) struct Bindings {
    computations: HashMap<Name, Computation>,
    theorems: HashMap<Name, Prop>,
}

impl Bindings {
    pub(crate) fn new() -> Self {
        Self::default()
    }

    pub(crate) fn theorem(&self, name: Name) -> Option<&Prop> {
        self.theorems.get(&name)
    }

    pub(crate) fn computation(&self, name: Name) -> Option<&Computation> {
        self.computations.get(&name)
    }

    pub(crate) fn define_computation(&mut self, name: Name, computation: &Computation) -> bool {
        if self.computations.contains_key(&name)
            || self.theorems.contains_key(&name)
            || !free_symbols(computation).is_empty()
        {
            return false;
        }

        self.computations.insert(name, computation.clone());
        true
    }

    pub(crate) fn define_theorem(&mut self, name: Name, theorem: &Theorem) -> bool {
        if self.computations.contains_key(&name) || self.theorems.contains_key(&name) {
            return false;
        }

        self.theorems.insert(name, theorem.prop().clone());
        true
    }
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Theory {
    bindings: Bindings,
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

    fn from_proof_in_bindings(proof: Proof, prop: Prop, bindings: &Bindings) -> Option<Self> {
        check_in_bindings(&proof, &prop, bindings).then_some(Self { prop, proof })
    }

    fn from_closed_proof(proof: Proof) -> Option<Self> {
        let prop = proven_prop(&proof, &Bindings::new(), &Context::new())?;
        Some(Self { prop, proof })
    }

    fn from_closed_proof_in_bindings(proof: Proof, bindings: &Bindings) -> Option<Self> {
        let prop = proven_prop(&proof, bindings, &Context::new())?;
        Some(Self { prop, proof })
    }

    pub fn prop(&self) -> &Prop {
        &self.prop
    }

    pub fn refl(computation: Computation) -> Self {
        Self {
            prop: equal(computation.clone(), computation.clone()),
            proof: Proof::Refl(computation),
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

    pub fn step(computation: Computation) -> Option<Self> {
        Self::from_closed_proof(Proof::Step(computation))
    }

    pub fn steps(computations: Vec<Computation>) -> Option<Self> {
        Self::from_closed_proof(Proof::Steps(computations))
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

    pub fn beta(lambda: Lambda, argument: Computation) -> Option<Self> {
        Self::from_closed_proof(Proof::Beta { lambda, argument })
    }

    pub fn value(value: Value) -> Self {
        Self::from_closed_proof(Proof::Value(value)).expect("value theorem should be valid")
    }

    pub fn value_lambda(lambda: Lambda) -> Self {
        Self::value(Value::lambda(lambda))
    }

    pub fn value_quote(symbol: Symbol) -> Self {
        Self::value(Value::quote(symbol))
    }

    pub fn value_nil() -> Self {
        Self::value(Value::nil())
    }

    pub fn value_cons(
        head: Computation,
        tail: Computation,
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
        head: Computation,
        tail: Computation,
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

    pub fn forall_elim(forall: &Self, argument: Computation) -> Option<Self> {
        Self::from_closed_proof(Proof::ForAllElim {
            forall: Box::new(forall.proof.clone()),
            argument,
        })
    }

    pub fn exists_intro(
        variable: Symbol,
        body: Prop,
        witness: Computation,
        proof: &Self,
    ) -> Option<Self> {
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

    pub fn theorem(&self, name: Name) -> Option<&Prop> {
        self.bindings.theorem(name)
    }

    pub fn computation(&self, name: Name) -> Option<&Computation> {
        self.bindings.computation(name)
    }

    pub fn define_computation(&mut self, name: Name, computation: &Computation) -> bool {
        self.bindings.define_computation(name, computation)
    }

    pub fn define_theorem(&mut self, name: Name, theorem: &Theorem) -> bool {
        if !self.check(&theorem.proof, theorem.prop()) {
            return false;
        }

        self.bindings.define_theorem(name, theorem)
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
        check_in_bindings(proof, prop, &self.bindings)
    }

    pub fn check_in_context(&self, proof: &Proof, prop: &Prop, context: &Context) -> bool {
        check_in_bindings_and_context(proof, prop, &self.bindings, context)
    }

    pub fn from_proof(&self, proof: Proof, prop: Prop) -> Option<Theorem> {
        Theorem::from_proof_in_bindings(proof, prop, &self.bindings)
    }

    fn theorem_from_closed_proof(&self, proof: Proof) -> Option<Theorem> {
        Theorem::from_closed_proof_in_bindings(proof, &self.bindings)
    }

    pub fn known(&self, name: Name) -> Option<Theorem> {
        self.theorem_from_closed_proof(Proof::Known(name))
    }

    pub fn reduce(&self, computation: &Computation) -> Step {
        step_in_bindings(computation, &self.bindings)
    }

    pub fn normal_form(&self, computation: &Computation) -> Computation {
        normal_form_in_bindings(computation, &self.bindings)
    }

    pub fn normal_outcome(&self, computation: &Computation) -> Option<Outcome> {
        normal_outcome_in_bindings(computation, &self.bindings)
    }

    pub fn refl(&self, computation: Computation) -> Theorem {
        Theorem::refl(computation)
    }

    pub fn symm(&self, theorem: &Theorem) -> Option<Theorem> {
        self.theorem_from_closed_proof(Proof::Symm(Box::new(theorem.proof.clone())))
    }

    pub fn trans(&self, first: &Theorem, second: &Theorem) -> Option<Theorem> {
        self.theorem_from_closed_proof(Proof::Trans(
            Box::new(first.proof.clone()),
            Box::new(second.proof.clone()),
        ))
    }

    pub fn step(&self, computation: Computation) -> Option<Theorem> {
        self.theorem_from_closed_proof(Proof::Step(computation))
    }

    pub fn steps(&self, computations: Vec<Computation>) -> Option<Theorem> {
        self.theorem_from_closed_proof(Proof::Steps(computations))
    }

    pub fn rewrite(
        &self,
        equality: &Theorem,
        theorem: &Theorem,
        variable: Symbol,
        template: Prop,
    ) -> Option<Theorem> {
        self.theorem_from_closed_proof(Proof::Rewrite {
            equality: Box::new(equality.proof.clone()),
            proof: Box::new(theorem.proof.clone()),
            variable,
            template,
        })
    }

    pub fn beta(&self, lambda: Lambda, argument: Computation) -> Option<Theorem> {
        self.theorem_from_closed_proof(Proof::Beta { lambda, argument })
    }

    pub fn value(&self, value: Value) -> Theorem {
        self.theorem_from_closed_proof(Proof::Value(value))
            .expect("value theorem should be valid in every theory")
    }

    pub fn value_lambda(&self, lambda: Lambda) -> Theorem {
        self.value(Value::lambda(lambda))
    }

    pub fn value_quote(&self, symbol: Symbol) -> Theorem {
        self.value(Value::quote(symbol))
    }

    pub fn value_nil(&self) -> Theorem {
        self.value(Value::nil())
    }

    pub fn value_cons(
        &self,
        head: Computation,
        tail: Computation,
        head_is_value: &Theorem,
        tail_is_value: &Theorem,
    ) -> Option<Theorem> {
        self.theorem_from_closed_proof(Proof::ValueCons {
            head,
            tail,
            head_is_value: Box::new(head_is_value.proof.clone()),
            tail_is_value: Box::new(tail_is_value.proof.clone()),
        })
    }

    pub fn list_nil(&self) -> Theorem {
        self.theorem_from_closed_proof(Proof::ListNil)
            .expect("list nil theorem should be valid in every theory")
    }

    pub fn list_cons(
        &self,
        head: Computation,
        tail: Computation,
        head_is_value: &Theorem,
        tail_is_list: &Theorem,
    ) -> Option<Theorem> {
        self.theorem_from_closed_proof(Proof::ListCons {
            head,
            tail,
            head_is_value: Box::new(head_is_value.proof.clone()),
            tail_is_list: Box::new(tail_is_list.proof.clone()),
        })
    }

    pub fn implies_elim(&self, implication: &Theorem, premise: &Theorem) -> Option<Theorem> {
        self.theorem_from_closed_proof(Proof::ImpliesElim {
            implication: Box::new(implication.proof.clone()),
            premise: Box::new(premise.proof.clone()),
        })
    }

    pub fn forall_elim(&self, forall: &Theorem, argument: Computation) -> Option<Theorem> {
        self.theorem_from_closed_proof(Proof::ForAllElim {
            forall: Box::new(forall.proof.clone()),
            argument,
        })
    }

    pub fn exists_intro(
        &self,
        variable: Symbol,
        body: Prop,
        witness: Computation,
        proof: &Theorem,
    ) -> Option<Theorem> {
        self.theorem_from_closed_proof(Proof::ExistsIntro {
            variable,
            body,
            witness,
            proof: Box::new(proof.proof.clone()),
        })
    }

    pub fn and_intro(&self, left: &Theorem, right: &Theorem) -> Option<Theorem> {
        self.theorem_from_closed_proof(Proof::AndIntro(
            Box::new(left.proof.clone()),
            Box::new(right.proof.clone()),
        ))
    }

    pub fn and_elim_left(&self, theorem: &Theorem) -> Option<Theorem> {
        self.theorem_from_closed_proof(Proof::AndElimLeft(Box::new(theorem.proof.clone())))
    }

    pub fn and_elim_right(&self, theorem: &Theorem) -> Option<Theorem> {
        self.theorem_from_closed_proof(Proof::AndElimRight(Box::new(theorem.proof.clone())))
    }

    pub fn or_intro_left(&self, theorem: &Theorem, right: Prop) -> Option<Theorem> {
        self.theorem_from_closed_proof(Proof::OrIntroLeft {
            proof: Box::new(theorem.proof.clone()),
            right,
        })
    }

    pub fn or_intro_right(&self, left: Prop, theorem: &Theorem) -> Option<Theorem> {
        self.theorem_from_closed_proof(Proof::OrIntroRight {
            left,
            proof: Box::new(theorem.proof.clone()),
        })
    }
}
