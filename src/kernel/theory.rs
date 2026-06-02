use std::collections::HashMap;

use super::{
    calculus::*,
    check::{check_in_bindings, check_in_bindings_and_context, free_symbols_prop, proven_prop},
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

    pub(crate) fn define_computation_result(
        &mut self,
        name: Name,
        computation: &Computation,
    ) -> Result<(), ComputationDefinitionError> {
        if self.computations.contains_key(&name) {
            return Err(ComputationDefinitionError::ComputationNameAlreadyDefined(
                name,
            ));
        }
        if self.theorems.contains_key(&name) {
            return Err(ComputationDefinitionError::TheoremNameAlreadyDefined(name));
        }

        closed_computation(computation)?;
        self.computations.insert(name, computation.clone());
        Ok(())
    }

    pub(crate) fn define_theorem_result(
        &mut self,
        name: Name,
        theorem: &Theorem,
    ) -> Result<(), TheoremError> {
        if self.computations.contains_key(&name) || self.theorems.contains_key(&name) {
            return Err(TheoremError::NameAlreadyDefined(name));
        }

        closed_prop(theorem.prop())?;
        self.theorems.insert(name, theorem.prop().clone());
        Ok(())
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

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ComputationDefinitionError {
    ComputationNameAlreadyDefined(Name),
    TheoremNameAlreadyDefined(Name),
    OpenComputation(Vec<Symbol>),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum TheoremError {
    InvalidProof,
    NameAlreadyDefined(Name),
    OpenProp(Vec<Symbol>),
}

fn closed_computation(computation: &Computation) -> Result<(), ComputationDefinitionError> {
    let mut symbols = free_symbols(computation).into_iter().collect::<Vec<_>>();
    symbols.sort();

    if symbols.is_empty() {
        Ok(())
    } else {
        Err(ComputationDefinitionError::OpenComputation(symbols))
    }
}

fn closed_prop(prop: &Prop) -> Result<(), TheoremError> {
    let mut symbols = free_symbols_prop(prop).into_iter().collect::<Vec<_>>();
    symbols.sort();

    if symbols.is_empty() {
        Ok(())
    } else {
        Err(TheoremError::OpenProp(symbols))
    }
}

impl Theorem {
    pub fn from_proof_result(proof: Proof, prop: Prop) -> Result<Self, TheoremError> {
        Self::from_proof_in_bindings_result(proof, prop, &Bindings::new())
    }

    pub fn from_proof(proof: Proof, prop: Prop) -> Option<Self> {
        Self::from_proof_result(proof, prop).ok()
    }

    fn from_proof_in_bindings_result(
        proof: Proof,
        prop: Prop,
        bindings: &Bindings,
    ) -> Result<Self, TheoremError> {
        closed_prop(&prop)?;

        if check_in_bindings(&proof, &prop, bindings) {
            Ok(Self { prop, proof })
        } else {
            Err(TheoremError::InvalidProof)
        }
    }

    fn from_proof_without_assumptions(proof: Proof) -> Option<Self> {
        Self::from_proof_without_assumptions_result(proof, &Bindings::new()).ok()
    }

    fn from_proof_without_assumptions_result(
        proof: Proof,
        bindings: &Bindings,
    ) -> Result<Self, TheoremError> {
        let prop =
            proven_prop(&proof, bindings, &Context::new()).ok_or(TheoremError::InvalidProof)?;
        closed_prop(&prop)?;

        Ok(Self { prop, proof })
    }

    pub fn prop(&self) -> &Prop {
        &self.prop
    }

    pub fn refl(computation: Computation) -> Option<Self> {
        Self::from_proof_without_assumptions(Proof::Refl(computation))
    }

    pub fn symm(theorem: &Self) -> Option<Self> {
        Self::from_proof_without_assumptions(Proof::Symm(Box::new(theorem.proof.clone())))
    }

    pub fn trans(first: &Self, second: &Self) -> Option<Self> {
        Self::from_proof_without_assumptions(Proof::Trans(
            Box::new(first.proof.clone()),
            Box::new(second.proof.clone()),
        ))
    }

    pub fn step(computation: Computation) -> Option<Self> {
        Self::from_proof_without_assumptions(Proof::Step(computation))
    }

    pub fn steps(computations: Vec<Computation>) -> Option<Self> {
        Self::from_proof_without_assumptions(Proof::Steps(computations))
    }

    pub fn rewrite(
        equality: &Self,
        theorem: &Self,
        variable: Symbol,
        template: Prop,
    ) -> Option<Self> {
        Self::from_proof_without_assumptions(Proof::Rewrite {
            equality: Box::new(equality.proof.clone()),
            proof: Box::new(theorem.proof.clone()),
            variable,
            template,
        })
    }

    pub fn implies_elim(implication: &Self, premise: &Self) -> Option<Self> {
        Self::from_proof_without_assumptions(Proof::ImpliesElim {
            implication: Box::new(implication.proof.clone()),
            premise: Box::new(premise.proof.clone()),
        })
    }

    pub fn forall_elim(forall: &Self, argument: Computation) -> Option<Self> {
        Self::from_proof_without_assumptions(Proof::ForAllElim {
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
        Self::from_proof_without_assumptions(Proof::ExistsIntro {
            variable,
            guard: None,
            body,
            witness,
            proof: Box::new(proof.proof.clone()),
        })
    }

    pub fn exists_intro_where(
        variable: Symbol,
        guard: Prop,
        body: Prop,
        witness: Computation,
        proof: &Self,
    ) -> Option<Self> {
        Self::from_proof_without_assumptions(Proof::ExistsIntro {
            variable,
            guard: Some(guard),
            body,
            witness,
            proof: Box::new(proof.proof.clone()),
        })
    }

    pub fn and_intro(left: &Self, right: &Self) -> Self {
        Self::from_proof_without_assumptions(Proof::AndIntro(
            Box::new(left.proof.clone()),
            Box::new(right.proof.clone()),
        ))
        .expect("and intro over closed theorems should be valid")
    }

    pub fn and_elim_left(theorem: &Self) -> Option<Self> {
        Self::from_proof_without_assumptions(Proof::AndElimLeft(Box::new(theorem.proof.clone())))
    }

    pub fn and_elim_right(theorem: &Self) -> Option<Self> {
        Self::from_proof_without_assumptions(Proof::AndElimRight(Box::new(theorem.proof.clone())))
    }

    pub fn or_intro_left(theorem: &Self, right: Prop) -> Option<Self> {
        Self::from_proof_without_assumptions(Proof::OrIntroLeft {
            proof: Box::new(theorem.proof.clone()),
            right,
        })
    }

    pub fn or_intro_right(left: Prop, theorem: &Self) -> Option<Self> {
        Self::from_proof_without_assumptions(Proof::OrIntroRight {
            left,
            proof: Box::new(theorem.proof.clone()),
        })
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
        self.define_computation_result(name, computation).is_ok()
    }

    pub fn define_computation_result(
        &mut self,
        name: Name,
        computation: &Computation,
    ) -> Result<(), ComputationDefinitionError> {
        self.bindings.define_computation_result(name, computation)
    }

    pub fn define_theorem(&mut self, name: Name, theorem: &Theorem) -> bool {
        self.define_theorem_result(name, theorem).is_ok()
    }

    pub fn define_theorem_result(
        &mut self,
        name: Name,
        theorem: &Theorem,
    ) -> Result<(), TheoremError> {
        closed_prop(theorem.prop())?;

        if !self.check(&theorem.proof, theorem.prop()) {
            return Err(TheoremError::InvalidProof);
        }

        self.bindings.define_theorem_result(name, theorem)
    }

    pub fn define_theorem_from_proof(
        &mut self,
        name: Name,
        proof: Proof,
        prop: Prop,
    ) -> Option<Theorem> {
        self.define_theorem_from_proof_result(name, proof, prop)
            .ok()
    }

    pub fn define_theorem_from_proof_result(
        &mut self,
        name: Name,
        proof: Proof,
        prop: Prop,
    ) -> Result<Theorem, TheoremError> {
        let theorem = self.from_proof_result(proof, prop)?;
        self.define_theorem_result(name, &theorem)?;
        Ok(theorem)
    }

    pub fn check(&self, proof: &Proof, prop: &Prop) -> bool {
        check_in_bindings(proof, prop, &self.bindings)
    }

    pub fn check_in_context(&self, proof: &Proof, prop: &Prop, context: &Context) -> bool {
        check_in_bindings_and_context(proof, prop, &self.bindings, context)
    }

    pub fn from_proof(&self, proof: Proof, prop: Prop) -> Option<Theorem> {
        self.from_proof_result(proof, prop).ok()
    }

    pub fn from_proof_result(&self, proof: Proof, prop: Prop) -> Result<Theorem, TheoremError> {
        Theorem::from_proof_in_bindings_result(proof, prop, &self.bindings)
    }

    fn theorem_from_proof_without_assumptions(&self, proof: Proof) -> Option<Theorem> {
        Theorem::from_proof_without_assumptions_result(proof, &self.bindings).ok()
    }

    pub fn known(&self, name: Name) -> Option<Theorem> {
        self.theorem_from_proof_without_assumptions(Proof::Known(name))
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

    pub fn refl(&self, computation: Computation) -> Option<Theorem> {
        Theorem::refl(computation)
    }

    pub fn symm(&self, theorem: &Theorem) -> Option<Theorem> {
        self.theorem_from_proof_without_assumptions(Proof::Symm(Box::new(theorem.proof.clone())))
    }

    pub fn trans(&self, first: &Theorem, second: &Theorem) -> Option<Theorem> {
        self.theorem_from_proof_without_assumptions(Proof::Trans(
            Box::new(first.proof.clone()),
            Box::new(second.proof.clone()),
        ))
    }

    pub fn step(&self, computation: Computation) -> Option<Theorem> {
        self.theorem_from_proof_without_assumptions(Proof::Step(computation))
    }

    pub fn steps(&self, computations: Vec<Computation>) -> Option<Theorem> {
        self.theorem_from_proof_without_assumptions(Proof::Steps(computations))
    }

    pub fn rewrite(
        &self,
        equality: &Theorem,
        theorem: &Theorem,
        variable: Symbol,
        template: Prop,
    ) -> Option<Theorem> {
        self.theorem_from_proof_without_assumptions(Proof::Rewrite {
            equality: Box::new(equality.proof.clone()),
            proof: Box::new(theorem.proof.clone()),
            variable,
            template,
        })
    }

    pub fn implies_elim(&self, implication: &Theorem, premise: &Theorem) -> Option<Theorem> {
        self.theorem_from_proof_without_assumptions(Proof::ImpliesElim {
            implication: Box::new(implication.proof.clone()),
            premise: Box::new(premise.proof.clone()),
        })
    }

    pub fn forall_elim(&self, forall: &Theorem, argument: Computation) -> Option<Theorem> {
        self.theorem_from_proof_without_assumptions(Proof::ForAllElim {
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
        self.theorem_from_proof_without_assumptions(Proof::ExistsIntro {
            variable,
            guard: None,
            body,
            witness,
            proof: Box::new(proof.proof.clone()),
        })
    }

    pub fn exists_intro_where(
        &self,
        variable: Symbol,
        guard: Prop,
        body: Prop,
        witness: Computation,
        proof: &Theorem,
    ) -> Option<Theorem> {
        self.theorem_from_proof_without_assumptions(Proof::ExistsIntro {
            variable,
            guard: Some(guard),
            body,
            witness,
            proof: Box::new(proof.proof.clone()),
        })
    }

    pub fn and_intro(&self, left: &Theorem, right: &Theorem) -> Option<Theorem> {
        self.theorem_from_proof_without_assumptions(Proof::AndIntro(
            Box::new(left.proof.clone()),
            Box::new(right.proof.clone()),
        ))
    }

    pub fn and_elim_left(&self, theorem: &Theorem) -> Option<Theorem> {
        self.theorem_from_proof_without_assumptions(Proof::AndElimLeft(Box::new(
            theorem.proof.clone(),
        )))
    }

    pub fn and_elim_right(&self, theorem: &Theorem) -> Option<Theorem> {
        self.theorem_from_proof_without_assumptions(Proof::AndElimRight(Box::new(
            theorem.proof.clone(),
        )))
    }

    pub fn or_intro_left(&self, theorem: &Theorem, right: Prop) -> Option<Theorem> {
        self.theorem_from_proof_without_assumptions(Proof::OrIntroLeft {
            proof: Box::new(theorem.proof.clone()),
            right,
        })
    }

    pub fn or_intro_right(&self, left: Prop, theorem: &Theorem) -> Option<Theorem> {
        self.theorem_from_proof_without_assumptions(Proof::OrIntroRight {
            left,
            proof: Box::new(theorem.proof.clone()),
        })
    }
}
