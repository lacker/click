//! Exact interface identity modulo lexical parameter names. This is not
//! behavioral refinement: it neither executes nor proves implications.
use super::*;

pub(super) fn same_interface(contract: &CFunctionContract, function: &CFunction) -> bool {
    // Proof binders are introduced by the named contract's explicit
    // application syntax and are checked by the binder judgment.  The
    // ordinary one-call refinement relation compares the shared behavioral
    // interface after that separate check, just as the previous template
    // comparison did.
    let mut normalized_contract = normalize(contract.interface());
    normalized_contract.proof_parameters = Default::default();
    let normalized_function = normalize(function.contract_interface());
    normalized_contract.exactly_matches(&normalized_function)
}

/// Native place requirements are a separate refinement obligation. Byte
/// resource containment and access-mode variance cannot erase them.
pub(super) fn same_native_record_obligations(
    left: &CFunctionContractInterface,
    right: &CFunctionContractInterface,
) -> bool {
    if normalize(left).native_span_expression_inputs
        != normalize(right).native_span_expression_inputs
        || left.native_span_inputs() != right.native_span_inputs()
        || !crate::kernel::functions::typed_access_policy_refinement_compatible(left, right)
        || left.parameters().len() != right.parameters().len()
        || left
            .parameters()
            .iter()
            .zip(right.parameters())
            .any(|(left, right)| left.is_native_pointer_input() != right.is_native_pointer_input())
    {
        return false;
    }
    #[derive(Clone, Eq, PartialEq, Ord, PartialOrd)]
    enum NativeRequirement {
        Record(CNativeRecordPlaceRequirement),
        Span(CNativeSpanRequirement),
        Storage(
            CExpression,
            CExpression,
            CExpression,
            u32,
            CType,
            Option<u32>,
        ),
    }
    type Key = (
        String,
        CResourceSnapshot,
        Option<SpecProposition>,
        NativeRequirement,
    );
    fn add(
        keys: &mut BTreeSet<Key>,
        scope: &str,
        specs: &[CResourceSpec],
        names: &mut Names,
        outer_guard: Option<&SpecProposition>,
    ) {
        for spec in specs {
            if spec.native_record_places().is_empty()
                && spec.native_span_requirements().is_empty()
                && spec.declared_storage_type().is_none()
            {
                continue;
            }
            let mut guard = match (outer_guard, spec.guard()) {
                (Some(outer), Some(inner)) => Some(SpecProposition::And(
                    Box::new(outer.clone()),
                    Box::new(inner.clone()),
                )),
                (Some(guard), None) | (None, Some(guard)) => Some(guard.clone()),
                (None, None) => None,
            };
            if let Some(guard) = &mut guard {
                names.proposition(guard);
            }
            if let Some(storage_type) = spec.declared_storage_type()
                && let Some(segment) = spec.memory_segment()
            {
                let mut base = segment.base.clone();
                let mut start = segment.start.clone();
                let mut end = segment.end.clone();
                names.c(&mut base);
                names.c(&mut start);
                names.c(&mut end);
                keys.insert((
                    scope.to_string(),
                    spec.snapshot(),
                    guard.clone(),
                    NativeRequirement::Storage(
                        base,
                        start,
                        end,
                        segment.element_width,
                        storage_type,
                        spec.declared_storage_count(),
                    ),
                ));
            }
            for place in spec.native_record_places() {
                let mut place = place.clone();
                names.c(&mut place.carrier);
                if let Some(count) = &mut place.prefix_count {
                    names.c(count);
                }
                keys.insert((
                    scope.to_string(),
                    spec.snapshot(),
                    guard.clone(),
                    NativeRequirement::Record(place),
                ));
            }
            for span in spec.native_span_requirements() {
                let mut span = span.clone();
                names.c(&mut span.carrier);
                names.c(&mut span.count);
                keys.insert((
                    scope.to_string(),
                    spec.snapshot(),
                    guard.clone(),
                    NativeRequirement::Span(span),
                ));
            }
        }
    }
    fn keys(interface: &CFunctionContractInterface) -> BTreeSet<Key> {
        let mut keys = BTreeSet::new();
        let mut names = Names::default();
        for parameter in interface.parameters() {
            let mut name = parameter.name().to_string();
            names.bind(&mut name);
        }
        add(
            &mut keys,
            "requires",
            interface.resource_requires(),
            &mut names,
            None,
        );
        add(
            &mut keys,
            "ensures",
            interface.resource_ensures(),
            &mut names,
            None,
        );
        let declared = interface
            .resource_requires()
            .iter()
            .chain(interface.resource_ensures())
            .filter_map(CResourceSpec::declared_name)
            .collect::<BTreeSet<_>>();
        for name in declared {
            let definitions = interface.composite_resource_definitions();
            let Ok(index) = definitions.binary_search_by(|definition| {
                crate::instrumentation::record_deterministic_work(1);
                definition.name().cmp(name)
            }) else {
                continue;
            };
            let definition = &definitions[index];
            let mut names = Names::default();
            for parameter in definition.parameters().iter().chain(definition.witnesses()) {
                let mut name = parameter.name().to_string();
                names.bind(&mut name);
            }
            add(
                &mut keys,
                name,
                definition.contains(),
                &mut names,
                definition.condition(),
            );
            if let Some(body) = &definition.matched {
                for arm in &body.arms {
                    let mut arm_names = names.clone();
                    for binding in &arm.bindings {
                        let mut name = binding.clone();
                        arm_names.bind(&mut name);
                    }
                    add(
                        &mut keys,
                        &format!("{name}:field{}:{}", body.field_index, arm.variant),
                        &arm.contains,
                        &mut arm_names,
                        definition.condition(),
                    );
                }
            }
        }
        keys
    }
    keys(left) == keys(right)
}

fn normalize(interface: &CFunctionContractInterface) -> CFunctionContractInterface {
    let mut interface = interface.clone();
    let mut names = Names::default();
    for parameter in &mut interface.parameters {
        names.bind(&mut parameter.name);
    }
    interface.native_span_expression_inputs = interface
        .native_span_expression_inputs
        .iter()
        .map(|span| {
            let mut span = span.clone();
            names.c(&mut span.carrier);
            names.c(&mut span.count);
            span
        })
        .collect();
    for proposition in interface
        .contract_requires
        .iter_mut()
        .chain(&mut interface.contract_ensures)
        .chain(&mut interface.exceptional_ensures)
    {
        names.proposition(proposition);
    }
    for resource in interface
        .resource_requires
        .iter_mut()
        .chain(&mut interface.resource_ensures)
    {
        names.resource_spec(resource);
    }
    for segment in &mut interface.contract_mutable {
        names.segment(segment);
    }
    // The declared `decreases` measure reads the same parameters the clauses
    // read, so it is renamed with them; two declarations that differ only in
    // what they call a parameter stay one interface.
    for measure in &mut interface.recursion_measure {
        match measure {
            CRankingComponent::CExpression(expression) => names.c(expression),
            // The declared spelling is what a diagnostic prints, not part of
            // the interface, exactly as a resource binder's spelling is not.
            // Erase it so two declarations that differ only in what they call
            // a parameter stay one interface.
            CRankingComponent::Pure { source, expression } => {
                source.clear();
                names.expression(expression);
            }
            CRankingComponent::PureInteger { source, expression } => {
                source.clear();
                names.integer(expression);
            }
        }
    }
    interface
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn standalone_span_geometry_is_an_exact_alpha_normalized_interface_obligation() {
        let requirement = |name: &str| CNativeSpanRequirement {
            carrier: c_variable(name),
            count: c_int32_literal(1),
            element_type: CType::UInt32,
            access_policy: CTypedAccessPolicy::NativeObjectOnly,
        };
        let function = |name: &str| {
            c_function(
                CType::Void,
                "span",
                vec![c_parameter(name, CType::UInt32Pointer)],
                c_skip(),
            )
            .with_native_span_expression_inputs(vec![requirement(name)])
        };
        let left = function("left");
        let right = function("right");
        assert!(same_native_record_obligations(
            left.contract_interface(),
            right.contract_interface()
        ));
        let absent = right.clone().with_native_span_expression_inputs(Vec::new());
        assert!(!same_native_record_obligations(
            left.contract_interface(),
            absent.contract_interface()
        ));
        assert!(
            !left
                .contract_interface()
                .exactly_matches(absent.contract_interface())
        );
    }

    #[test]
    fn typed_source_policy_survives_lexical_interface_normalization() {
        let function = |name: &str, policy| {
            c_function(
                CType::Void,
                "policy",
                vec![c_parameter(name, CType::Int32Pointer)],
                CStatement::Skip,
            )
            .with_typed_access_policy(policy)
        };
        let native = function("p", CTypedAccessPolicy::NativeObjectOnly);
        let contract = CFunctionContract::new("Native", native.clone()).unwrap();
        assert!(same_interface(
            &contract,
            &function("renamed", CTypedAccessPolicy::NativeObjectOnly)
        ));
        let c = function("renamed", CTypedAccessPolicy::CAllocatedAccessAllowed);
        assert!(!same_interface(&contract, &c));
        assert!(!same_native_record_obligations(
            native.contract_interface(),
            c.contract_interface()
        ));
    }

    #[test]
    fn native_pointer_enrollment_is_retained_by_interface_identity_and_refinement() {
        use std::hash::{Hash, Hasher};
        let function = |name: &str, enrolled| {
            c_function(
                CType::Void,
                "native_input",
                vec![c_parameter(name, CType::Int32Pointer).with_native_pointer_input(enrolled)],
                CStatement::Skip,
            )
        };
        let legacy = function("p", false);
        let enrolled = function("q", true);
        assert!(!legacy.parameters()[0].is_native_pointer_input());
        assert!(enrolled.parameters()[0].is_native_pointer_input());
        let target = CFunctionContract::new("Native", enrolled.clone()).unwrap();
        assert!(same_interface(&target, &function("renamed", true)));
        assert!(!same_interface(&target, &legacy));
        assert!(!same_native_record_obligations(
            legacy.contract_interface(),
            enrolled.contract_interface()
        ));
        assert!(
            !legacy
                .contract_interface()
                .has_compatible_signature_and_composite_vocabulary(enrolled.contract_interface())
        );
        let parameter = &legacy.parameters()[0];
        let mut actual = std::collections::hash_map::DefaultHasher::new();
        parameter.hash(&mut actual);
        let mut original = std::collections::hash_map::DefaultHasher::new();
        parameter.name.hash(&mut original);
        parameter.c_type.hash(&mut original);
        parameter.aggregate_layout.hash(&mut original);
        parameter.volatile.hash(&mut original);
        parameter.pointee_volatile.hash(&mut original);
        parameter.constant.hash(&mut original);
        parameter.pointee_constant.hash(&mut original);
        assert_eq!(actual.finish(), original.finish());
    }

    fn interface(parameter: &str, local: &str, body: &str) -> CFunction {
        c_function(
            CType::Void,
            "interface",
            vec![c_parameter(parameter, CType::Int32)],
            CStatement::Skip,
        )
        .with_contract(
            vec![],
            vec![SpecProposition::Comparison {
                left: SpecExpression::Let {
                    name: local.to_string(),
                    value: Box::new(SpecExpression::CExpression(c_variable(parameter))),
                    body: Box::new(SpecExpression::CExpression(c_variable(body))),
                },
                operator: CComparisonOperator::Equal,
                right: SpecExpression::CExpression(c_variable(parameter)),
            }],
            vec![],
            vec![],
            true,
        )
    }

    #[test]
    fn lexical_identity_retains_resource_guards_across_parameter_renaming() {
        let interface = |parameter: &str, guard_value| {
            let spec = CResourceSpec::owned_memory(CMemorySegment::new(
                c_variable(parameter),
                c_int32_literal(0),
                c_int32_literal(1),
            ))
            .with_guard(SpecProposition::Comparison {
                left: SpecExpression::Value(int32(guard_value)),
                operator: CComparisonOperator::Equal,
                right: SpecExpression::Value(int32(1)),
            });
            c_function(
                CType::Void,
                "guarded",
                vec![c_parameter(parameter, CType::Int32Pointer)],
                CStatement::Skip,
            )
            .with_resource_summary(vec![spec.clone()], vec![spec])
        };
        let target = CFunctionContract::new("Guarded", interface("p", 1)).unwrap();
        assert!(same_interface(&target, &interface("q", 1)));
        assert!(!same_interface(&target, &interface("q", 0)));
    }

    #[test]
    fn lexical_identity_preserves_shadowing_and_free_names() {
        let target = CFunctionContract::new("Target", interface("x", "x", "x")).unwrap();
        assert!(same_interface(&target, &interface("p", "q", "q")));
        assert!(!same_interface(&target, &interface("p", "q", "p")));
        assert!(!same_interface(&target, &interface("p", "q", "bound:1")));
        let free = CFunctionContract::new("Free", interface("p", "q", "global")).unwrap();
        assert!(same_interface(&free, &interface("x", "y", "global")));
        assert!(!same_interface(&free, &interface("x", "y", "different")));
    }

    #[test]
    fn integer_conversions_preserve_lexical_interface_identity() {
        let interface = |parameter: &str, referenced: &str| {
            let observation =
                SpecIntegerExpression::FromMachine(Box::new(SpecExpression::IntegerToMachine {
                    value: Box::new(SpecIntegerExpression::FromMachine(Box::new(
                        SpecExpression::CExpression(c_variable(referenced)),
                    ))),
                    destination: MachineIntegerType::Int32,
                }));
            c_function(
                CType::Void,
                "interface",
                vec![c_parameter(parameter, CType::Int32)],
                CStatement::Skip,
            )
            .with_contract(
                vec![],
                vec![SpecProposition::IntegerComparison {
                    left: observation,
                    operator: IntegerComparisonOperator::Equal,
                    right: SpecIntegerExpression::Term(IntegerTerm::constant_i64(0)),
                }],
                vec![],
                vec![],
                true,
            )
        };
        let target = CFunctionContract::new("Target", interface("x", "x")).unwrap();
        assert!(same_interface(&target, &interface("y", "y")));
        assert!(!same_interface(&target, &interface("y", "x")));
    }

    #[test]
    fn interface_visits_scale_with_explicit_specification_nodes() {
        for size in [1, 16, 64, 256] {
            let mut names = Names::default();
            for index in 0..size {
                names.bind(&mut format!("argument{index}"));
            }
            for index in 0..size {
                let mut proposition = SpecProposition::Comparison {
                    left: SpecExpression::CountedResourceCount {
                        name: "Token".into(),
                        arguments: vec![Some(SpecExpression::CExpression(c_variable(format!(
                            "argument{index}"
                        ))))],
                    },
                    operator: CComparisonOperator::Equal,
                    right: SpecExpression::Value(int32(1)),
                };
                names.proposition(&mut proposition);
            }
            assert_eq!(names.visits, 5 * size);
        }
    }

    #[test]
    fn lexical_identity_preserves_resource_projection_identity_and_snapshot() {
        let interface = |identity, at_entry| {
            c_function(CType::Void, "interface", vec![], CStatement::Skip).with_contract(
                vec![],
                vec![SpecProposition::Comparison {
                    left: SpecExpression::ResourceField {
                        projection: ResourceFieldProjection {
                            identity: Variable(identity),
                            children: vec![],
                            field_index: 0,
                            at_entry,
                        },
                        c_type: CType::Int32,
                    },
                    operator: CComparisonOperator::Equal,
                    right: SpecExpression::Value(CValue::Int32(Bitvector32Term::Constant(0))),
                }],
                vec![],
                vec![],
                true,
            )
        };
        let target = CFunctionContract::new("Target", interface(1, false)).unwrap();
        assert!(same_interface(&target, &interface(1, false)));
        assert!(!same_interface(&target, &interface(2, false)));
        assert!(!same_interface(&target, &interface(1, true)));
    }
}

#[derive(Clone, Default)]
struct Names {
    bindings: BTreeMap<String, Vec<String>>,
    next: usize,
    #[cfg(test)]
    visits: usize,
}

impl Names {
    fn visit(&mut self) {
        #[cfg(test)]
        {
            self.visits += 1;
        }
    }
    fn reference(&self, name: &mut String) {
        *name = self
            .bindings
            .get(name)
            .and_then(|stack| stack.last())
            .cloned()
            .unwrap_or_else(|| format!("free:{name}"));
    }
    fn bind(&mut self, name: &mut String) -> String {
        let original = name.clone();
        *name = format!("bound:{}", self.next);
        self.next += 1;
        self.bindings
            .entry(original.clone())
            .or_default()
            .push(name.clone());
        original
    }
    fn unbind(&mut self, name: String) {
        let stack = self.bindings.get_mut(&name).unwrap();
        stack.pop();
        if stack.is_empty() {
            self.bindings.remove(&name);
        }
    }
    fn c(&mut self, expression: &mut CExpression) {
        self.visit();
        use CExpression::*;
        match expression {
            Variable(name) => self.reference(name),
            Value(_) | FunctionAddress(_) => {}
            Cast { expression, .. }
            | FloatClassification { expression, .. }
            | PointerOffsetBytes {
                pointer: expression,
                ..
            }
            | PointerAligned {
                pointer: expression,
                ..
            }
            | TypedLoad {
                pointer: expression,
                ..
            }
            | MemberAddress {
                object: expression, ..
            }
            | FloatNegate(expression)
            | AddressOf(expression)
            | CheckedObjectAddress(expression)
            | Not(expression)
            | BitwiseNot(expression)
            | Load(expression) => self.c(expression),
            Conditional {
                condition,
                then_branch,
                else_branch,
            } => {
                self.c(condition);
                self.c(then_branch);
                self.c(else_branch);
            }
            ArrayRowAddress {
                array: a, index: b, ..
            }
            | RecordPointerOffset {
                pointer: a,
                index: b,
                ..
            }
            | LessThan(a, b)
            | LessEqual(a, b)
            | GreaterThan(a, b)
            | GreaterEqual(a, b)
            | Equal(a, b)
            | NotEqual(a, b)
            | And(a, b)
            | Or(a, b)
            | Add(a, b)
            | Subtract(a, b)
            | Multiply(a, b)
            | Divide(a, b)
            | Remainder(a, b)
            | ShiftLeft(a, b)
            | ShiftRight(a, b)
            | BitwiseAnd(a, b)
            | BitwiseOr(a, b)
            | BitwiseXor(a, b)
            | Index(a, b) => {
                self.c(a);
                self.c(b);
            }
        }
    }
    fn integer(&mut self, expression: &mut SpecIntegerExpression) {
        self.visit();
        match expression {
            SpecIntegerExpression::Term(_) | SpecIntegerExpression::ResourceField(_) => {}
            SpecIntegerExpression::PureFunctionApplication { arguments, .. } => {
                for argument in arguments {
                    self.argument(argument);
                }
            }
            SpecIntegerExpression::AlgebraicMatch { scrutinee, arms } => {
                self.algebraic(scrutinee);
                for arm in arms {
                    self.integer(&mut arm.body);
                }
            }
            SpecIntegerExpression::FromMachine(machine) => self.expression(machine),
            SpecIntegerExpression::Negate(inner) => self.integer(inner),
            crate::kernel::binary_spec_integer_expression!(left, right) => {
                self.integer(left);
                self.integer(right);
            }
            SpecIntegerExpression::RangeFold {
                index,
                initial,
                body,
                ..
            } => {
                match index {
                    SpecIntegerRangeFoldIndex::Int32 { start, end }
                    | SpecIntegerRangeFoldIndex::UInt64 { start, end } => {
                        self.expression(start);
                        self.expression(end);
                    }
                    SpecIntegerRangeFoldIndex::Integer { start, end } => {
                        self.integer(start);
                        self.integer(end);
                    }
                }
                self.integer(initial);
                self.integer(body);
            }
        }
    }
    fn expression(&mut self, expression: &mut SpecExpression) {
        self.visit();
        use SpecExpression::*;
        match expression {
            // Instance identities are not lexical C parameter names.
            Value(_) | ResourceField { .. } => {}
            IntegerToMachine { value, .. } => self.integer(value),
            CExpression(e) => self.c(e),
            AggregateFieldValue {
                parameter, pointer, ..
            } => {
                self.reference(parameter);
                self.expression(pointer);
            }
            CountedResourceCount { arguments, .. } => {
                for e in arguments.iter_mut().flatten() {
                    self.expression(e);
                }
            }
            Add(a, b)
            | Subtract(a, b)
            | Multiply(a, b)
            | Divide(a, b)
            | Remainder(a, b)
            | ShiftLeft(a, b)
            | ShiftRight(a, b)
            | BitwiseAnd(a, b)
            | BitwiseOr(a, b)
            | BitwiseXor(a, b) => {
                self.expression(a);
                self.expression(b);
            }
            BitwiseNot(e) | Cast(e, _) | LoopEntrySnapshot(e) | MemoryLoad { pointer: e, .. } => {
                self.expression(e)
            }
            PointerOffset {
                pointer, elements, ..
            } => {
                self.expression(pointer);
                self.expression(elements);
            }
            If {
                condition,
                then_branch,
                else_branch,
            } => {
                self.proposition(condition);
                self.expression(then_branch);
                self.expression(else_branch);
            }
            Let { name, value, body } => {
                self.expression(value);
                let original = self.bind(name);
                self.expression(body);
                self.unbind(original);
            }
            RangeFold {
                start,
                end,
                initial,
                accumulator,
                item,
                body,
            } => {
                self.expression(start);
                self.expression(end);
                self.expression(initial);
                let a = self.bind(accumulator);
                let b = self.bind(item);
                self.expression(body);
                self.unbind(b);
                self.unbind(a);
            }
            PureFunctionApplication { arguments, .. } => {
                for a in arguments {
                    self.argument(a);
                }
            }
            AlgebraicMatch { scrutinee, arms } => {
                self.algebraic(scrutinee);
                for arm in arms {
                    let bound: Vec<_> = arm.bindings.iter_mut().map(|n| self.bind(n)).collect();
                    self.expression(&mut arm.body);
                    for n in bound.into_iter().rev() {
                        self.unbind(n);
                    }
                }
            }
        }
    }
    fn algebraic(&mut self, expression: &mut SpecAlgebraicExpression) {
        use SpecAlgebraicExpressionNode::*;
        match &mut expression.node {
            Variable(_) | ResourceField(_) => {}
            Binding(name) => self.reference(name),
            Constructor { fields, .. } => {
                for field in fields {
                    match field {
                        SpecAlgebraicValue::C(e) => self.expression(e),
                        SpecAlgebraicValue::Integer(_) => {}
                        SpecAlgebraicValue::Algebraic(e) => self.algebraic(e),
                    }
                }
            }
            PureFunctionApplication { arguments, .. } => {
                for a in arguments {
                    self.argument(a);
                }
            }
            Match { scrutinee, arms } => {
                self.algebraic(scrutinee);
                for arm in arms {
                    let bound: Vec<_> = arm.bindings.iter_mut().map(|n| self.bind(n)).collect();
                    self.algebraic(&mut arm.body);
                    for n in bound.into_iter().rev() {
                        self.unbind(n);
                    }
                }
            }
        }
    }
    fn argument(&mut self, argument: &mut SpecPureFunctionArgument) {
        match argument {
            SpecPureFunctionArgument::Value(e)
            | SpecPureFunctionArgument::ArrayRef { pointer: e, .. } => self.expression(e),
            SpecPureFunctionArgument::Integer(_) => {}
            SpecPureFunctionArgument::Algebraic(e) => self.algebraic(e),
        }
    }
    fn sequence(&mut self, sequence: &mut SpecSequenceExpression) {
        match sequence {
            SpecSequenceExpression::Literal(es) => {
                for e in es {
                    self.expression(e);
                }
            }
            SpecSequenceExpression::Concat(a, b) => {
                self.sequence(a);
                self.sequence(b);
            }
        }
    }
    fn resource(&mut self, resource: &mut SpecResource) {
        match resource {
            SpecResource::Memory {
                base, start, end, ..
            } => {
                self.expression(base);
                self.expression(start);
                self.expression(end);
            }
            SpecResource::Composite { arguments, .. } | SpecResource::Token { arguments, .. } => {
                for e in arguments {
                    self.expression(e);
                }
            }
        }
    }
    fn proposition(&mut self, proposition: &mut SpecProposition) {
        self.visit();
        use SpecProposition::*;
        match proposition {
            IntegerComparison { left, right, .. } => {
                self.integer(left);
                self.integer(right);
            }
            AlgebraicComparison { left, right, .. } => {
                self.algebraic(left);
                self.algebraic(right);
            }
            SequenceComparison { left, right, .. } => {
                self.sequence(left);
                self.sequence(right);
            }
            SequenceMembership { element, sequence } => {
                self.expression(element);
                self.sequence(sequence);
            }
            Comparison { left, right, .. } => {
                self.expression(left);
                self.expression(right);
            }
            Defined(e) | FloatClassification { expression: e, .. } => self.expression(e),
            ValidPlace { pointer, range, .. } => {
                self.expression(pointer);
                if let Some((start, end)) = range {
                    self.expression(start);
                    self.expression(end);
                }
            }
            And(a, b) | Or(a, b) | Implies(a, b) => {
                self.proposition(a);
                self.proposition(b);
            }
            Not(p) => self.proposition(p),
            ForAllMachineInteger { name, body, .. }
            | ExistsMachineInteger { name, body, .. }
            | ForAllInt32 { name, body, .. }
            | ForAllInteger { name, body, .. }
            | ForAllAlgebraic { name, body, .. }
            | ExistsInt32 { name, body, .. }
            | ExistsInteger { name, body, .. }
            | ExistsAlgebraic { name, body, .. }
            | ForAllPointer { name, body, .. }
            | ExistsPointer { name, body, .. } => {
                let original = self.bind(name);
                self.proposition(body);
                self.unbind(original);
            }
            Predicate { arguments, .. } => {
                for a in arguments {
                    match a {
                        SpecPredicateArgument::Value(e)
                        | SpecPredicateArgument::ArrayRef { pointer: e, .. } => self.expression(e),
                    }
                }
            }
            ResourceSeparate { left, right } => {
                self.resource(left);
                self.resource(right);
            }
            ResourceContains { parent, child } => {
                self.resource(parent);
                self.resource(child);
            }
            MemoryInitialized { base, .. } => self.expression(base),
            MemoryLoadable {
                base, start, end, ..
            } => {
                self.expression(base);
                self.expression(start);
                self.expression(end);
            }
        }
    }
    fn segment(&mut self, segment: &mut CMemorySegment) {
        self.c(&mut segment.base);
        self.c(&mut segment.start);
        self.c(&mut segment.end);
        if let Some(guard) = &mut segment.guard {
            self.proposition(guard);
        }
    }
    fn resource_spec(&mut self, resource: &mut CResourceSpec) {
        let mut term = resource.term().clone();
        self.resource_term(&mut term);
        let quantity = match resource.quantity() {
            CResourceQuantity::One => CResourceQuantity::One,
            CResourceQuantity::Count(quantity) => {
                let mut quantity = quantity.clone();
                self.c(&mut quantity);
                CResourceQuantity::Count(quantity)
            }
        };
        let native_record_places = resource
            .native_record_places()
            .iter()
            .map(|place| {
                let mut place = place.clone();
                self.c(&mut place.carrier);
                if let Some(count) = &mut place.prefix_count {
                    self.c(count);
                }
                place
            })
            .collect();
        let native_span_requirements = resource
            .native_span_requirements()
            .iter()
            .map(|span| {
                let mut span = span.clone();
                self.c(&mut span.carrier);
                self.c(&mut span.count);
                span
            })
            .collect();
        let mut guard = resource.guard().cloned();
        if let Some(guard) = &mut guard {
            self.proposition(guard);
        }
        let quantity_snapshot = resource.quantity_snapshot();
        let declared_storage_observation = resource.declared_storage_observation();
        *resource = CResourceSpec::new(
            term,
            resource.access(),
            quantity,
            resource.role(),
            resource.snapshot(),
        )
        .expect("interface identity normalization preserves resource validity")
        .with_declared_storage_observation(declared_storage_observation)
        .with_native_record_places(native_record_places)
        .with_native_span_requirements(native_span_requirements)
        .with_quantity_snapshot(quantity_snapshot);
        if let Some(guard) = guard {
            *resource = resource.clone().with_guard(guard);
        }
    }

    fn resource_term(&mut self, resource: &mut CResourceTerm) {
        match resource {
            // A binder's spelling is a name, not part of the interface: the
            // identity beside it is the semantic key, exactly as a parameter's
            // type rather than its name is. Erase it so two declarations that
            // differ only in what they call an instance stay one interface.
            CResourceTerm::Instance {
                binder, resource, ..
            } => {
                binder.clear();
                self.resource_term(resource);
            }
            CResourceTerm::PopulationAuthority { protected, .. } => {
                self.resource_spec(&mut protected.resource)
            }
            CResourceTerm::MutexGuard { mutex, .. } | CResourceTerm::MutexLive { mutex, .. } => {
                self.c(mutex)
            }
            CResourceTerm::MutexUse {
                mutex, protected, ..
            } => {
                self.c(mutex);
                if let Some(p) = protected {
                    self.resource_spec(&mut p.resource);
                }
            }
            CResourceTerm::Publication { flag, payload, .. } => {
                self.c(flag);
                self.resource_spec(&mut payload.resource);
            }
            CResourceTerm::Memory(s) => self.segment(s),
            CResourceTerm::Composite { arguments, .. } | CResourceTerm::Token { arguments, .. } => {
                for e in arguments {
                    self.c(e);
                }
            }
            CResourceTerm::Iterated(spec) => {
                for e in spec.expressions_mut() {
                    self.c(e);
                }
            }
        }
    }
}
