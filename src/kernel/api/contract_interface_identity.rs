//! Exact interface identity modulo lexical parameter names. This is not
//! behavioral refinement: it neither executes nor proves implications.
use super::*;

pub(super) fn same_interface(contract: &FunctionContract, function: &ProgramFunction) -> bool {
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

fn normalize(interface: &FunctionContractInterface) -> FunctionContractInterface {
    let mut interface = interface.clone();
    let mut names = Names::default();
    for parameter in &mut interface.parameters {
        names.bind(&mut parameter.name);
    }
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
            RankingComponent::ProgramExpression(expression) => names.c(expression),
            // The declared spelling is what a diagnostic prints, not part of
            // the interface, exactly as a resource binder's spelling is not.
            // Erase it so two declarations that differ only in what they call
            // a parameter stay one interface.
            RankingComponent::Pure { source, expression } => {
                source.clear();
                names.expression(expression);
            }
            RankingComponent::PureInteger { source, expression } => {
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

    fn interface(parameter: &str, local: &str, body: &str) -> ProgramFunction {
        program_function(
            ProgramType::Void,
            "interface",
            vec![program_parameter(parameter, ProgramType::Int32)],
            ProgramStatement::Skip,
        )
        .with_contract(
            vec![],
            vec![SpecProposition::Comparison {
                left: SpecExpression::Let {
                    name: local.to_string(),
                    value: Box::new(SpecExpression::ProgramExpression(
                        crate::kernel::program_expression::variable(parameter),
                    )),
                    body: Box::new(SpecExpression::ProgramExpression(
                        crate::kernel::program_expression::variable(body),
                    )),
                },
                operator: ComparisonOperator::Equal,
                right: SpecExpression::ProgramExpression(
                    crate::kernel::program_expression::variable(parameter),
                ),
            }],
            vec![],
            vec![],
            true,
        )
    }

    #[test]
    fn lexical_identity_preserves_shadowing_and_free_names() {
        let target = FunctionContract::new("Target", interface("x", "x", "x")).unwrap();
        assert!(same_interface(&target, &interface("p", "q", "q")));
        assert!(!same_interface(&target, &interface("p", "q", "p")));
        assert!(!same_interface(&target, &interface("p", "q", "bound:1")));
        let free = FunctionContract::new("Free", interface("p", "q", "global")).unwrap();
        assert!(same_interface(&free, &interface("x", "y", "global")));
        assert!(!same_interface(&free, &interface("x", "y", "different")));
    }

    #[test]
    fn integer_conversions_preserve_lexical_interface_identity() {
        let interface = |parameter: &str, referenced: &str| {
            let observation =
                SpecIntegerExpression::FromMachine(Box::new(SpecExpression::IntegerToMachine {
                    value: Box::new(SpecIntegerExpression::FromMachine(Box::new(
                        SpecExpression::ProgramExpression(
                            crate::kernel::program_expression::variable(referenced),
                        ),
                    ))),
                    destination: MachineIntegerType::Int32,
                }));
            program_function(
                ProgramType::Void,
                "interface",
                vec![program_parameter(parameter, ProgramType::Int32)],
                ProgramStatement::Skip,
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
        let target = FunctionContract::new("Target", interface("x", "x")).unwrap();
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
                        arguments: vec![Some(SpecExpression::ProgramExpression(
                            crate::kernel::program_expression::variable(format!("argument{index}")),
                        ))],
                    },
                    operator: ComparisonOperator::Equal,
                    right: SpecExpression::Value(int32(1)),
                };
                names.proposition(&mut proposition);
            }
            assert_eq!(names.visits, 5 * size);
        }
    }

    #[test]
    fn lexical_identity_preserves_resource_projection_identity_and_state() {
        let interface = |identity, at_entry| {
            program_function(
                ProgramType::Void,
                "interface",
                vec![],
                ProgramStatement::Skip,
            )
            .with_contract(
                vec![],
                vec![SpecProposition::Comparison {
                    left: SpecExpression::ResourceField {
                        projection: ResourceFieldProjection {
                            identity: Variable(identity),
                            children: vec![],
                            field_index: 0,
                            at_entry,
                        },
                        program_type: ProgramType::Int32,
                    },
                    operator: ComparisonOperator::Equal,
                    right: SpecExpression::Value(ProgramValue::Int32(MachineTerm::constant(0))),
                }],
                vec![],
                vec![],
                true,
            )
        };
        let target = FunctionContract::new("Target", interface(1, false)).unwrap();
        assert!(same_interface(&target, &interface(1, false)));
        assert!(!same_interface(&target, &interface(2, false)));
        assert!(!same_interface(&target, &interface(1, true)));
    }
}

#[derive(Default)]
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
    fn c(&mut self, expression: &mut ProgramExpression) {
        self.visit();
        use ProgramExpression::*;
        match expression {
            Variable(name) => self.reference(name),
            Value(_) | FunctionAddress(_) | StepResult { .. } => {}
            Cast { expression, .. }
            | FloatClassification { expression, .. }
            | PointerOffsetBytes {
                pointer: expression,
                ..
            }
            | Subobject {
                pointer: expression,
                ..
            }
            | TypedLoad {
                pointer: expression,
                ..
            }
            | FloatNegate(expression)
            | EnumField {
                value: expression, ..
            }
            | EnumIs {
                value: expression, ..
            }
            | AddressOf(expression)
            | CheckedObjectAddress(expression)
            | Not(expression)
            | BitwiseNot(expression)
            | Load(expression) => self.c(expression),
            EnumConstruct { fields, .. } => {
                for field in fields {
                    self.c(field);
                }
            }
            Ternary {
                condition,
                then_branch,
                else_branch,
            } => {
                self.c(condition);
                self.c(then_branch);
                self.c(else_branch);
            }
            LessThan(a, b)
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
            | RustShiftLeft(a, b)
            | RustShiftRight(a, b)
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
            SpecIntegerExpression::If {
                condition,
                then_branch,
                else_branch,
            } => {
                self.proposition(condition);
                self.integer(then_branch);
                self.integer(else_branch);
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
            ProgramExpression(e) => self.c(e),
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
            | RustShiftLeft(a, b)
            | RustShiftRight(a, b)
            | ShiftRight(a, b)
            | BitwiseAnd(a, b)
            | BitwiseOr(a, b)
            | BitwiseXor(a, b) => {
                self.expression(a);
                self.expression(b);
            }
            Subobject { pointer: e, .. }
            | BitwiseNot(e)
            | NarrowArithmetic(e, _)
            | Cast(e, _)
            | PointerCoercion(e, _)
            | LoopEntryState(e)
            | MemoryLoad { pointer: e, .. } => self.expression(e),
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
            Requires { requirement, value } => {
                self.proposition(requirement);
                self.expression(value);
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
            ProgramValue(value) => self.expression(value),
            Constructor { fields, .. } => {
                for field in fields {
                    match field {
                        SpecAlgebraicValue::Program(e) => self.expression(e),
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
            If {
                condition,
                then_branch,
                else_branch,
            } => {
                self.proposition(condition);
                self.algebraic(then_branch);
                self.algebraic(else_branch);
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
            SpecPureFunctionArgument::ObjectPointer { argument, .. } => self.argument(argument),
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
            SpecResource::Star(a, b) => {
                self.resource(a);
                self.resource(b);
            }
            SpecResource::Instance { .. } | SpecResource::Value(_) => {}
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
            ResourceViewable { resource, .. } => self.resource(resource),
            ChangesOnly { resources, .. } => {
                for r in resources {
                    self.resource(r);
                }
            }

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
            MemoryLoadable {
                base, start, end, ..
            } => {
                self.expression(base);
                self.expression(start);
                self.expression(end);
            }
        }
    }
    fn segment(&mut self, segment: &mut MemorySegment) {
        self.c(&mut segment.base);
        self.c(&mut segment.start);
        self.c(&mut segment.end);
        if let Some(guard) = &mut segment.guard {
            self.proposition(guard);
        }
    }
    fn resource_spec(&mut self, resource: &mut ResourceSpec) {
        let mut term = resource.term().clone();
        self.resource_term(&mut term);
        let quantity = match resource.quantity() {
            ResourceQuantity::One => ResourceQuantity::One,
            ResourceQuantity::Count(quantity) => {
                let mut quantity = quantity.clone();
                self.c(&mut quantity);
                ResourceQuantity::Count(quantity)
            }
        };
        *resource = ResourceSpec::new(
            term,
            resource.access(),
            quantity,
            resource.role(),
            resource.state_source(),
        )
        .expect("interface identity normalization preserves resource validity");
    }

    fn resource_term(&mut self, resource: &mut ResourceTerm) {
        match resource {
            // A binder's spelling is a name, not part of the interface: the
            // identity beside it is the semantic key, exactly as a parameter's
            // type rather than its name is. Erase it so two declarations that
            // differ only in what they call an instance stay one interface.
            ResourceTerm::Instance {
                binder, resource, ..
            } => {
                binder.clear();
                self.resource_term(resource);
            }
            ResourceTerm::PopulationAuthority { protected, .. } => {
                self.resource_spec(&mut protected.resource)
            }
            ResourceTerm::MutexGuard { mutex, .. } | ResourceTerm::MutexLive { mutex, .. } => {
                self.c(mutex)
            }
            ResourceTerm::MutexUse {
                mutex, protected, ..
            } => {
                self.c(mutex);
                if let Some(p) = protected {
                    self.resource_spec(&mut p.resource);
                }
            }
            ResourceTerm::Publication { flag, payload, .. } => {
                self.c(flag);
                self.resource_spec(&mut payload.resource);
            }
            ResourceTerm::Memory(s) => self.segment(s),
            ResourceTerm::Composite { arguments, .. } | ResourceTerm::Token { arguments, .. } => {
                for e in arguments {
                    self.c(e);
                }
            }
            ResourceTerm::Iterated(spec) => {
                for e in spec.expressions_mut() {
                    self.c(e);
                }
            }
        }
    }
}
