//! Exact interface identity modulo lexical parameter names. This is not
//! behavioral refinement: it neither executes nor proves implications.
use super::*;

pub(super) fn same_interface(contract: &CFunctionContract, function: &CFunction) -> bool {
    let normalized =
        CFunctionContract::new(contract.name(), normalize(contract.template())).unwrap();
    normalized.exactly_matches(&normalize(function))
}

fn normalize(function: &CFunction) -> CFunction {
    let mut function = function.clone();
    let mut names = Names::default();
    for parameter in &mut function.parameters {
        names.bind(&mut parameter.name);
    }
    for proposition in function
        .contract_requires
        .iter_mut()
        .chain(&mut function.contract_ensures)
    {
        names.proposition(proposition);
    }
    for resource in function
        .resource_requires
        .iter_mut()
        .chain(&mut function.resource_ensures)
    {
        names.resource_spec(resource);
    }
    for segment in &mut function.contract_mutable {
        names.segment(segment);
    }
    function
}

#[cfg(test)]
mod tests {
    use super::*;

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
            | TypedLoad {
                pointer: expression,
                ..
            }
            | FloatNegate(expression)
            | AddressOf(expression)
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
            SpecIntegerExpression::Add(left, right)
            | SpecIntegerExpression::Subtract(left, right)
            | SpecIntegerExpression::Multiply(left, right) => {
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
                    SpecIntegerRangeFoldIndex::Int32 { start, end } => {
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
            And(a, b) | Or(a, b) | Implies(a, b) => {
                self.proposition(a);
                self.proposition(b);
            }
            Not(p) => self.proposition(p),
            ForAllInt32 { name, body, .. }
            | ForAllInteger { name, body, .. }
            | ExistsInt32 { name, body, .. }
            | ExistsInteger { name, body, .. }
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
    fn segment(&mut self, segment: &mut CMemorySegment) {
        self.c(&mut segment.base);
        self.c(&mut segment.start);
        self.c(&mut segment.end);
        if let Some(guard) = &mut segment.guard {
            self.proposition(guard);
        }
    }
    fn resource_spec(&mut self, resource: &mut CResourceSpec) {
        match resource {
            CResourceSpec::Instance { resource, .. } => self.resource_spec(resource),
            CResourceSpec::ViewMemory(s) | CResourceSpec::OwnMemory(s) => self.segment(s),
            CResourceSpec::Quantified { quantity, resource } => {
                self.c(quantity);
                self.resource_spec(resource);
            }
            CResourceSpec::Composite { arguments, .. } | CResourceSpec::Token { arguments, .. } => {
                for e in arguments {
                    self.c(e);
                }
            }
        }
    }
}
