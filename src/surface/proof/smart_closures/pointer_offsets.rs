//! Bounded scalar-pointer translation through named laws and exact index proofs.
//! Pointer domains come from a selected pointer relation, never address words.
use super::*;
use ContractExpression as E;

#[derive(Clone, Copy, PartialEq, Eq)]
enum Index {
    Signed,
    Unsigned,
}
impl Index {
    fn name(self) -> &'static str {
        match self {
            Self::Signed => "int32",
            Self::Unsigned => "uint64",
        }
    }
    fn zero(self) -> E {
        self.literal(0)
    }
    fn literal(self, value: i64) -> E {
        E::ProgramExpression(ProgramExpression::Value(match self {
            Self::Signed => int32(MachineTerm::constant(value as u32)),
            Self::Unsigned => crate::kernel::uint64(MachineTerm::uint64_constant(value as u64)),
        }))
    }
}
fn add(a: E, b: E) -> E {
    E::Add(Box::new(a), Box::new(b))
}
fn sub(a: E, b: E) -> E {
    E::Subtract(Box::new(a), Box::new(b))
}
fn observe(e: E) -> E {
    super::super::wide_arithmetic::to_integer(&e)
}
fn equality(a: E, b: E) -> ClickProposition {
    ClickProposition::Comparison {
        left: a,
        operator: ComparisonOperator::Equal,
        right: b,
    }
}
fn law(name: &str, arguments: Vec<E>, premises: Vec<ClickProposition>) -> ProofStep {
    ProofStep::ApplyPlannedTheorem {
        application: TheoremApplication {
            name: format!("click::integer::{name}"),
            arguments,
        },
        premises,
    }
}
#[derive(Clone)]
struct Chain {
    original: E,
    base: E,
    indices: Vec<E>,
}
fn chain(expression: &E) -> Option<Chain> {
    let mut base = expression.clone();
    let mut indices = Vec::new();
    loop {
        if indices.len() >= 64 || crate::instrumentation::deadline_exceeded_with_work(1) {
            return None;
        }
        match base {
            E::Add(a, b) => {
                indices.push(*b);
                base = *a;
            }
            E::ProgramExpression(ProgramExpression::Add(a, b)) => {
                indices.push(E::ProgramExpression(*b));
                base = E::ProgramExpression(*a);
            }
            _ => break,
        }
    }
    indices.reverse();
    Some(Chain {
        original: expression.clone(),
        base,
        indices,
    })
}
fn scalar_pointer(value: &ProgramValue) -> bool {
    let ProgramValue::Pointer(p) = value else {
        return false;
    };
    matches!(
        p.program_type(),
        ProgramType::UInt8Pointer
            | ProgramType::Int8Pointer
            | ProgramType::UInt16Pointer
            | ProgramType::Int16Pointer
            | ProgramType::UInt32Pointer
            | ProgramType::Int32Pointer
            | ProgramType::UInt64Pointer
            | ProgramType::Int64Pointer
            | ProgramType::Float32Pointer
            | ProgramType::Float64Pointer
    ) && p.object_class().is_none_or(|class| {
        matches!(
            class,
            crate::kernel::effective_type::CAccessClass::Scalar(_)
        )
    })
}

fn pointee_name(value: &ProgramValue) -> Option<&'static str> {
    let ProgramValue::Pointer(p) = value else {
        return None;
    };
    Some(match p.program_type() {
        ProgramType::UInt8Pointer => "uint8",
        ProgramType::Int8Pointer => "int8",
        ProgramType::UInt16Pointer => "uint16",
        ProgramType::Int16Pointer => "int16",
        ProgramType::UInt32Pointer => "uint32",
        ProgramType::Int32Pointer => "int32",
        ProgramType::UInt64Pointer => "uint64",
        ProgramType::Int64Pointer => "int64",
        ProgramType::Float32Pointer => "float32",
        ProgramType::Float64Pointer => "float64",
        _ => return None,
    })
}
struct Emitter<'a> {
    proof: Proof<'a>,
    pointee: &'static str,
    sources: Vec<ClickProposition>,
    steps: usize,
}
impl<'a> Emitter<'a> {
    fn charge(&mut self) -> Result<(), ClickError> {
        self.steps += 1;
        if self.steps > 4096 || crate::instrumentation::deadline_exceeded_with_work(1) {
            return Err(self
                .proof
                .step_error("pointer translation reached its work or 4096-step bound"));
        }
        Ok(())
    }
    fn apply(&mut self, step: ProofStep) -> Result<(), ClickError> {
        self.charge()?;
        self.proof = self.proof.driver().apply_step(step)?;
        Ok(())
    }
    fn known(&mut self, proposition: ClickProposition) -> Result<(), ClickError> {
        self.apply(super::super::wide_arithmetic::have(
            proposition.clone(),
            vec![ProofStep::Known],
        ))?;
        self.sources.push(proposition);
        Ok(())
    }
    fn arithmetic(&mut self, proposition: ClickProposition) -> Result<(), ClickError> {
        self.charge()?;
        let scope = self.proof.driver().open_have(proposition.clone())?;
        self.proof = if matches!(proposition, ClickProposition::Defined { .. })
            && let Some(closed) =
                attempt::candidate_outcome(scope.driver().try_signed_definedness_bounds(
                    crate::kernel::SignedDefinedWidth::Int32,
                    self.sources.clone(),
                ))?
                .flatten()
        {
            closed.join()?
        } else {
            scope
                .driver()
                .apply_step(ProofStep::ArithmeticUsing(self.sources.clone()))?
                .join()?
        };
        self.sources.push(proposition);
        Ok(())
    }
    fn index_sum(
        &mut self,
        left: E,
        right: E,
        kind: Index,
    ) -> Result<(E, ClickProposition), ClickError> {
        let sum = add(left.clone(), right.clone());
        let guard = match kind {
            Index::Signed => ClickProposition::Defined {
                expression: sum.clone(),
            },
            Index::Unsigned => ClickProposition::Comparison {
                left: add(observe(left.clone()), observe(right.clone())),
                operator: ComparisonOperator::LessEqual,
                right: super::super::surface_synthesis::integer_typed_expression(
                    surface_signed_integer_literal(&BigInt::from(u64::MAX)),
                ),
            },
        };
        self.arithmetic(guard.clone())?;
        self.apply(law(
            &format!("{}_add_to_integer", kind.name()),
            vec![left.clone(), right.clone()],
            vec![guard.clone()],
        ))?;
        self.sources.push(equality(
            observe(sum.clone()),
            add(observe(left), observe(right)),
        ));
        Ok((sum, guard))
    }
    fn prepare_index(&mut self, index: &E, kind: Index, depth: usize) -> Result<(), ClickError> {
        if depth >= 64 {
            return Err(self
                .proof
                .step_error("pointer index source depth bound reached"));
        }
        if let E::Add(a, b) = index {
            self.prepare_index(a, kind, depth + 1)?;
            self.prepare_index(b, kind, depth + 1)?;
            self.index_sum(a.as_ref().clone(), b.as_ref().clone(), kind)?;
        }
        Ok(())
    }
    fn normalize(&mut self, chain: &Chain, kind: Index) -> Result<E, ClickError> {
        let mut indices = Vec::new();
        for index in &chain.indices {
            let value = self.proof.capture_native_argument(index)?;
            let index = match (kind, value) {
                (Index::Signed, ProgramValue::Int32(_))
                | (Index::Unsigned, ProgramValue::UInt64(_)) => index.clone(),
                (Index::Unsigned, ProgramValue::Int32(value))
                    if value.as_const().is_some_and(|n| (n as i32) >= 0) =>
                {
                    kind.literal(i64::from(value.as_const().unwrap()))
                }
                _ => {
                    return Err(self
                        .proof
                        .step_error("unsupported mixed pointer index formats"));
                }
            };
            indices.push(index);
        }
        for index in &indices {
            self.prepare_index(index, kind, 0)?;
        }
        let Some(mut index) = indices.first().cloned() else {
            return Ok(kind.zero());
        };
        for next in &indices[1..] {
            let (sum, guard) = self.index_sum(index.clone(), next.clone(), kind)?;
            self.apply(law(
                &format!("{}_pointer_add_associate_{}", self.pointee, kind.name()),
                vec![chain.base.clone(), index.clone(), next.clone()],
                vec![guard],
            ))?;
            index = sum;
            if self.proof.focused_discharged() {
                return Ok(index);
            }
        }
        self.known(equality(
            chain.original.clone(),
            add(chain.base.clone(), index.clone()),
        ))?;
        Ok(index)
    }
}

impl<'a> crate::kernel::search::ProofSearch<Proof<'a>> {
    /// Ambient discovery selects bounded connected premises; replay keeps the
    /// identical selected-source emitter used by restricted solve.
    pub(in crate::surface::proof) fn try_pointer_translation_closure(
        input: &Proof<'a>,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_pointer_translation_closure");
        let Some(goal) = input.goal() else {
            return Ok(None);
        };
        if !matches!(&goal, condition_source_0 @ Proposition::ConditionIs(
                _,
                true
            ) if matches!(condition_source_0.condition_native(), Some((ConditionTerm::AddressEqual(..)
                    | ConditionTerm::PointerEqual(..)
                    | ConditionTerm::AddressOffsetEqual(..), _))))
        {
            return Ok(None);
        }
        let Some(ClickProposition::Comparison {
            left,
            operator: ComparisonOperator::Equal,
            right,
        }) = input.surface_goal()
        else {
            return Ok(None);
        };
        let (Some(a), Some(b)) = (chain(left), chain(right)) else {
            return Ok(None);
        };
        if ![&a, &b].into_iter().any(|c| {
            c.indices.len() > 1 || c.indices.iter().any(|index| matches!(index, E::Add(..)))
        }) {
            return Ok(None);
        }
        let Some(candidates) =
            crate::kernel::search::proposition_search::arithmetic_connected_premises(
                input.facts().assumptions(),
                goal,
            )
        else {
            return Ok(None);
        };
        if candidates.len() > 64 {
            return Ok(None);
        }
        let Some(pairs) = Self::resolve_solve_premises(input, &candidates, &[]) else {
            return Ok(None);
        };
        let sources = pairs
            .into_iter()
            .map(|(_, surface)| surface)
            .collect::<Vec<_>>();
        Self::try_pointer_translation_using(input, &sources)
    }

    pub(in crate::surface::proof) fn try_pointer_translation_using(
        input: &Proof<'a>,
        sources: &[ClickProposition],
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_pointer_translation_using");
        if !matches!(&input.goal(), Some(condition_source_0 @ Proposition::ConditionIs(
                _,
                true
            )) if matches!(condition_source_0.condition_native(), Some((ConditionTerm::AddressEqual(..)
                    | ConditionTerm::PointerEqual(..)
                    | ConditionTerm::AddressOffsetEqual(..), _))))
        {
            return Ok(None);
        }
        let Some(ClickProposition::Comparison {
            left,
            operator: ComparisonOperator::Equal,
            right,
        }) = input.surface_goal()
        else {
            return Ok(None);
        };
        let (Ok(left_value), Ok(right_value)) = (
            input.capture_native_argument(left),
            input.capture_native_argument(right),
        ) else {
            return Ok(None);
        };
        if !scalar_pointer(&left_value) || !scalar_pointer(&right_value) {
            return Ok(None);
        }
        let (Some(left), Some(right)) = (chain(left), chain(right)) else {
            return Ok(None);
        };
        if let (Some((condition, true)), [a], [b]) = (
            input.goal().and_then(Proposition::condition_native),
            left.indices.as_slice(),
            right.indices.as_slice(),
        ) && crate::kernel::proof::fact_reasoning::pointer_projection_source(condition).is_some()
            && let Some(index) = [a, b].into_iter().find(|index| {
                matches!(
                    input.capture_native_argument(index),
                    Ok(ProgramValue::UInt64(_))
                )
            })
        {
            let bound = ClickProposition::Comparison {
                left: observe(index.clone()),
                operator: ComparisonOperator::LessEqual,
                right: surface_signed_integer_literal(&BigInt::from(i32::MAX)),
            };
            let scope = input.driver().open_have(bound)?;
            if let Some(closed) = scope.driver().try_integer_composition_using(sources)? {
                let proof = closed.join()?.driver().apply_step(ProofStep::Known)?;
                return Ok(proof.focused_discharged().then_some(proof));
            }
        }
        let Some(pointee) = pointee_name(&left_value) else {
            return Ok(None);
        };
        if pointee_name(&right_value) != Some(pointee) {
            return Ok(None);
        }
        let mut relations = Vec::new();
        for source in sources {
            let kernel =
                input.lower_cited_surface_proposition(source, "pointer translation source")?;
            if !input.facts().listed_premise_available(&kernel, &[], false) {
                return Ok(None);
            }
            if let ClickProposition::Comparison {
                left,
                operator: ComparisonOperator::Equal,
                right,
            } = source
                && let (Ok(a), Ok(b)) = (
                    input.capture_native_argument(left),
                    input.capture_native_argument(right),
                )
                && scalar_pointer(&a)
                && scalar_pointer(&b)
                && let (Some(a), Some(b)) = (chain(left), chain(right))
            {
                relations.push((a, b));
            }
        }
        let mut kind = None;
        for c in std::iter::once(&left)
            .chain(std::iter::once(&right))
            .chain(relations.iter().flat_map(|(a, b)| [a, b]))
        {
            for index in &c.indices {
                let next = match input.capture_native_argument(index)? {
                    ProgramValue::Int32(v) if v.as_const().is_some() => None,
                    ProgramValue::Int32(_) => Some(Index::Signed),
                    ProgramValue::UInt64(_) => Some(Index::Unsigned),
                    _ => return Ok(None),
                };
                if let Some(next) = next {
                    if kind.is_some_and(|kind| kind != next) {
                        return Ok(None);
                    }
                    kind = Some(next);
                }
            }
        }
        let kind = kind.unwrap_or(Index::Signed);
        let mut emitter = Emitter {
            proof: input.clone(),
            pointee,
            sources: sources.to_vec(),
            steps: 0,
        };
        let attempt = (|| -> Result<Option<Proof<'a>>, ClickError> {
            let c = emitter.normalize(&left, kind)?;
            if emitter.proof.focused_discharged() {
                return Ok(Some(emitter.proof.clone()));
            }
            let d = emitter.normalize(&right, kind)?;
            if emitter.proof.focused_discharged() {
                return Ok(Some(emitter.proof.clone()));
            }
            let normalized_left = add(left.base.clone(), c.clone());
            let normalized_right = add(right.base.clone(), d.clone());
            if emitter.proof.capture_native_argument(&normalized_left)?
                == emitter.proof.capture_native_argument(&normalized_right)?
            {
                emitter.apply(ProofStep::Known)?;
                return Ok(Some(emitter.proof.clone()));
            }
            if emitter.proof.capture_native_argument(&left.base)?
                == emitter.proof.capture_native_argument(&right.base)?
            {
                relations.push((
                    Chain {
                        original: left.base.clone(),
                        base: left.base.clone(),
                        indices: vec![],
                    },
                    Chain {
                        original: right.base.clone(),
                        base: right.base.clone(),
                        indices: vec![],
                    },
                ));
            }
            for (a, b) in relations {
                for (a, b) in [(a.clone(), b.clone()), (b, a)] {
                    if emitter.proof.capture_native_argument(&a.base)?
                        != emitter.proof.capture_native_argument(&left.base)?
                        || emitter.proof.capture_native_argument(&b.base)?
                            != emitter.proof.capture_native_argument(&right.base)?
                    {
                        continue;
                    }
                    let a = emitter.normalize(&a, kind)?;
                    let b = emitter.normalize(&b, kind)?;
                    let relation = equality(
                        add(left.base.clone(), a.clone()),
                        add(right.base.clone(), b.clone()),
                    );
                    emitter.known(relation.clone())?;
                    let delta = equality(
                        sub(observe(c.clone()), observe(a.clone())),
                        sub(observe(d.clone()), observe(b.clone())),
                    );
                    emitter.arithmetic(delta.clone())?;
                    let mut premises = vec![relation, delta];
                    premises.extend(emitter.sources.clone());
                    emitter.apply(law(
                        &format!("{}_pointer_translate_{}", emitter.pointee, kind.name()),
                        vec![
                            left.base.clone(),
                            right.base.clone(),
                            a,
                            b,
                            c.clone(),
                            d.clone(),
                        ],
                        premises,
                    ))?;
                    if !emitter.proof.focused_discharged() {
                        emitter.apply(ProofStep::Known)?;
                    }
                    return Ok(Some(emitter.proof.clone()));
                }
            }
            Ok(None)
        })();
        attempt::candidate_outcome(attempt).map(Option::flatten)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::surface::{
        expand_c_claim_source_by_label, verify_c_sources, without_implicit_solve,
    };
    fn replay(source: &str) {
        let expanded = expand_c_claim_source_by_label(source, &[], "translated.ensures_0")
            .unwrap_or_else(|e| panic!("{}\n{source}", e.message()));
        assert!(!expanded.contains("normalize("), "{source}\n{expanded}");
        assert!(!expanded.contains("solve("), "{expanded}");
        without_implicit_solve(|| verify_c_sources(&expanded, &[]))
            .unwrap_or_else(|e| panic!("{}\n{expanded}", e.message()));
    }
    #[test]
    #[cfg(not(feature = "fast-gate"))]
    #[ignore = "nightly: scalar pointer offset laws and strict expansion replay"]
    fn pointer_offsets_expand_without_normalize() {
        let mut failures = Vec::new();
        for ty in [
            "uint8",
            "int8",
            "uint16",
            "int16",
            "uint32",
            "int32",
            "uint64",
            "int64",
            "float",
            "double",
            "const uint8",
        ] {
            for (index, bounds) in [
                ("int32", "0<=i;i<=100;0<=j;j<=100;"),
                ("uint64", "i<=100u64;j<=100u64;"),
            ] {
                let requires = bounds
                    .split(';')
                    .filter(|p| !p.is_empty())
                    .map(|p| format!("requires {p};"))
                    .collect::<String>();
                let source = format!(
                    "theorem translated(p: {ty}*,i:{index},j:{index}) {{ {requires} ensures (p+i)+j==p+(i+j) by {{close() using {{{bounds}}};}} }}"
                );
                if std::panic::catch_unwind(|| replay(&source)).is_err() {
                    failures.push(source);
                }
            }
        }
        for (parameters, bounds, goal) in [
            ("p:int32*,q:int32*", "p==q+3;", "p+1==q+4"),
            (
                "p:int32*,q:int32*,i:int32,j:int32,k:int32",
                "p+i==q+j;0<=i;i<=100;0<=j;j<=100;0<=k;k<=10;",
                "p+(i+k)==q+(j+k)",
            ),
            (
                "p:uint8*,i:int32,j:int32",
                "0<=i;i<=100;0<=j;j<=100;",
                "(p+i)+j==(p+j)+i",
            ),
            (
                "p:int32*,q:int32*,i:uint64,j:uint64,k:uint64",
                "p+i==q+j;i<=100u64;j<=100u64;k<=10u64;",
                "p+(i+k)==q+(j+k)",
            ),
            (
                "p:int32*,q:int32*,n:uint64,k:uint64",
                "p==q+(n-k);to_integer(n-k)<18446744073709551615;",
                "p+1==q+((n-k)+1u64)",
            ),
        ] {
            let requires = bounds
                .split(';')
                .filter(|p| !p.is_empty())
                .map(|p| format!("requires {p};"))
                .collect::<String>();
            for tactic in [format!("close() using {{{bounds}}};"), "close();".into()] {
                let source = format!(
                    "theorem translated({parameters}) {{ {requires} ensures {goal} by {{ {tactic} }} }}"
                );
                if std::panic::catch_unwind(|| replay(&source)).is_err() {
                    failures.push(source);
                }
            }
        }
        assert!(failures.is_empty(), "{}", failures.join("\n"));
    }
    #[test]
    #[cfg(not(feature = "fast-gate"))]
    #[ignore = "nightly: pointer translation missing-premise and overflow controls"]
    fn pointer_offsets_do_not_borrow_relations_or_allow_wrapping() {
        for source in [
            "theorem bad(p:int32*,q:int32*) {requires p==q+3;ensures p+1==q+4 by {close() using {};}}",
            "theorem bad(p:int32*,q:int32*) {requires p==q+3;ensures p+1==q+5 by {close() using {p==q+3;};}}",
            "theorem bad(p:int32*,i:uint64) {requires i==18446744073709551615u64;ensures (p+i)+1u64==p+(i+1u64) by {close() using {i==18446744073709551615u64;};}}",
            "theorem bad(p:int32*,q:int32*) {requires address(p)==address(q);ensures p+1==q+2 by {close() using {address(p)==address(q);};}}",
        ] {
            crate::surface::parse(source).unwrap();
            assert!(verify_c_sources(source, &[]).is_err(), "{source}");
        }
    }
    #[derive(Clone, Debug, PartialEq, Eq)]
    enum Value {
        Number(BigInt),
        Pointer(u8, u8, BigInt),
    }
    fn model(e: &E, values: &BTreeMap<String, Value>, width: u32) -> Value {
        match e {
            E::Binding(name)
            | E::ProgramExpression(ProgramExpression::Variable(
                crate::kernel::BindingName::Named(name),
            )) => values[name].clone(),
            E::IntegerContext(e) => model(e, values, width),
            E::Call { name, arguments } if name == "to_integer" => {
                model(&arguments[0], values, width)
            }
            E::Add(a, b) => match (model(a, values, width), model(b, values, width)) {
                (Value::Pointer(block, domain, a), Value::Number(b)) => {
                    Value::Pointer(block, domain, a + b * width)
                }
                (Value::Number(a), Value::Number(b)) => Value::Number(a + b),
                other => panic!("unexpected pointer law add: {other:?}"),
            },
            E::Subtract(a, b) => match (model(a, values, width), model(b, values, width)) {
                (Value::Number(a), Value::Number(b)) => Value::Number(a - b),
                _ => panic!("unexpected pointer law subtraction"),
            },
            _ => panic!("unexpected pointer law expression: {e:?}"),
        }
    }
    #[test]
    #[cfg(not(feature = "fast-gate"))]
    #[ignore = "nightly: parsed pointer translation axioms against exact coordinate models"]
    fn pointer_translation_axioms_match_independent_coordinate_models() {
        let library = crate::surface::standard_library_theorem_definitions().unwrap();
        for (name, samples) in [
            (
                "pointer_translate_int32",
                vec![
                    BigInt::from(i32::MIN),
                    (-1).into(),
                    0.into(),
                    1.into(),
                    BigInt::from(i32::MAX),
                ],
            ),
            (
                "pointer_translate_uint64",
                vec![
                    0.into(),
                    1.into(),
                    2.into(),
                    BigInt::from(1u64 << 63),
                    BigInt::from(u64::MAX),
                ],
            ),
        ] {
            for law in library
                .iter()
                .filter(|law| law.name().ends_with(&format!("_{name}")))
            {
                let mut applicable = 0;
                for width in [1, 2, 4, 8, 24] {
                    for a in &samples {
                        for b in &samples {
                            for c in &samples {
                                for d in &samples {
                                    for perturb in [0, 1] {
                                        for block in [0, 1] {
                                            for domain in [0, 1] {
                                                for full in [false, true] {
                                                    let origin: BigInt =
                                                        (BigInt::one() << 80usize) + 17;
                                                    let mut values = BTreeMap::from([
                                                        (
                                                            "p".into(),
                                                            Value::Pointer(0, 0, origin.clone()),
                                                        ),
                                                        (
                                                            "q".into(),
                                                            Value::Pointer(
                                                                block,
                                                                domain,
                                                                origin + (a - b) * width + perturb,
                                                            ),
                                                        ),
                                                    ]);
                                                    for (n, v) in
                                                        [("a", a), ("b", b), ("c", c), ("d", d)]
                                                    {
                                                        values.insert(
                                                            n.into(),
                                                            Value::Number(v.clone()),
                                                        );
                                                    }
                                                    let holds = |p: &ClickProposition| {
                                                        let ClickProposition::Comparison {
                                                            left,
                                                            operator: ComparisonOperator::Equal,
                                                            right,
                                                        } = p
                                                        else {
                                                            panic!(
                                                                "unexpected pointer axiom proposition"
                                                            )
                                                        };
                                                        match (
                                                            model(left, &values, width),
                                                            model(right, &values, width),
                                                        ) {
                                                            (
                                                                Value::Pointer(a, ad, x),
                                                                Value::Pointer(b, bd, y),
                                                            ) => {
                                                                a == b
                                                                    && (!full || ad == bd)
                                                                    && x == y
                                                            }
                                                            (a, b) => a == b,
                                                        }
                                                    };
                                                    if law.requires().iter().all(|r| {
                                                        let Requirement::Proposition(p) = r else {
                                                            panic!("pointer axiom resource premise")
                                                        };
                                                        holds(p)
                                                    }) {
                                                        applicable += 1;
                                                        for ensure in law.ensures() {
                                                            let Ensure::Proposition(p) =
                                                                ensure.ensure()
                                                            else {
                                                                panic!(
                                                                    "pointer axiom resource conclusion"
                                                                )
                                                            };
                                                            assert!(holds(p), "{name} {values:?}");
                                                        }
                                                    }
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
                assert!(applicable > 10, "pointer oracle must not be vacuous");
            }
        }
    }
}
