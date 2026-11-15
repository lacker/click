//! Declaration-only nominal requirements. This never examines a C body or proof.
use super::*;
use crate::kernel::spec::walk::{SpecNode, Visit, WalkBudget, walk_spec};
use crate::kernel::{bits32_constant, uint64_constant};

type Origins = Option<Arc<Origin>>;
enum Origin {
    Parameter(usize),
    Join(Vec<Arc<Origin>>),
}
fn join(origins: impl IntoIterator<Item = Origins>) -> Origins {
    let mut nodes: Vec<_> = origins.into_iter().flatten().collect();
    match nodes.len() {
        0 => None,
        1 => nodes.pop(),
        _ => Some(Arc::new(Origin::Join(nodes))),
    }
}
struct Analysis<'a> {
    bindings: BTreeMap<&'a str, Origins>,
    origins: BTreeMap<usize, Origins>,
    required: ObjectTypeRequirements,
    demanded: BTreeSet<(usize, effective_type::CAccessClass)>,
    variants: BTreeMap<usize, BTreeMap<&'a str, &'a [AlgebraicValueType]>>,
}

pub(in crate::kernel) fn declared_requirements(
    interface: &FunctionContractInterface,
) -> ObjectTypeRequirements {
    let mut analysis = Analysis::new(interface);
    for proposition in interface
        .contract_requires()
        .iter()
        .chain(interface.contract_ensures())
        .chain(interface.exceptional_ensures())
    {
        analysis.visit(SpecNode::Proposition(proposition));
    }
    analysis.required
}

impl<'a> Analysis<'a> {
    fn new(interface: &'a FunctionContractInterface) -> Self {
        Self {
            bindings: interface
                .parameters()
                .iter()
                .chain(interface.value_parameters())
                .enumerate()
                .map(|(index, p)| (p.name(), Some(Arc::new(Origin::Parameter(index)))))
                .collect(),
            origins: BTreeMap::new(),
            required: Default::default(),
            demanded: Default::default(),
            variants: Default::default(),
        }
    }

    fn fields(&mut self, ty: &'a AlgebraicType, name: &str) -> Option<&'a [AlgebraicValueType]> {
        self.variants
            .entry(ty.variants.as_ptr() as usize)
            .or_insert_with(|| {
                ty.variants
                    .iter()
                    .map(|variant| {
                        crate::instrumentation::record_deterministic_work(1);
                        (variant.name.as_str(), variant.fields.as_slice())
                    })
                    .collect()
            })
            .get(name)
            .copied()
    }

    fn program_origins(&self, value: &ProgramExpression) -> Origins {
        match value {
            ProgramExpression::Variable(name) => self
                .bindings
                .get(name.as_str())
                .cloned()
                .unwrap_or_default(),
            ProgramExpression::Cast { expression, .. } => self.program_origins(expression),
            _ => None,
        }
    }
    fn argument_origins(&mut self, argument: &'a SpecPureFunctionArgument) -> Origins {
        match argument {
            SpecPureFunctionArgument::Value(value)
            | SpecPureFunctionArgument::ArrayRef { pointer: value, .. } => self.origins(value),
            SpecPureFunctionArgument::ObjectPointer { argument, .. } => {
                self.argument_origins(argument)
            }
            _ => None,
        }
    }
    fn origins(&mut self, value: &'a SpecExpression) -> Origins {
        let key = value as *const SpecExpression as usize;
        if let Some(origins) = self.origins.get(&key) {
            return origins.clone();
        }
        crate::instrumentation::record_deterministic_work(1);
        let result = match value {
            SpecExpression::ProgramExpression(value) => self.program_origins(value),
            SpecExpression::Cast(value, _) | SpecExpression::LoopEntryState(value) => {
                self.origins(value)
            }
            SpecExpression::PointerOffset { pointer, .. } => self.origins(pointer),
            crate::kernel::binary_spec_expression!(left, right) => {
                join([self.origins(left), self.origins(right)])
            }
            SpecExpression::If {
                then_branch,
                else_branch,
                ..
            } => join([self.origins(then_branch), self.origins(else_branch)]),
            SpecExpression::Let { name, value, body } => {
                let origins = self.origins(value);
                let old = self.bindings.insert(name, origins);
                let result = self.origins(body);
                self.restore(name, old);
                result
            }
            SpecExpression::PureFunctionApplication {
                arguments,
                pointer_result: Some(result),
                ..
            } => {
                let mut origins = Vec::new();
                for index in &result.arguments {
                    if let Some(argument) = arguments.get(*index) {
                        origins.push(self.argument_origins(argument));
                    }
                }
                join(origins)
            }
            _ => None,
        };
        self.origins.insert(key, result.clone());
        result
    }
    fn require(&mut self, value: &'a SpecExpression, class: &effective_type::CAccessClass) {
        let mut pending: Vec<_> = self.origins(value).into_iter().collect();
        while let Some(origin) = pending.pop() {
            if !self
                .demanded
                .insert((Arc::as_ptr(&origin) as usize, class.clone()))
            {
                continue;
            }
            crate::instrumentation::record_deterministic_work(1);
            match origin.as_ref() {
                Origin::Parameter(index) => {
                    self.required.insert(*index, class.clone());
                }
                Origin::Join(children) => pending.extend(children.iter().cloned()),
            }
        }
    }

    fn restore(&mut self, name: &'a str, old: Option<Origins>) {
        match old {
            Some(value) => {
                self.bindings.insert(name, value);
            }
            None => {
                self.bindings.remove(name);
            }
        }
    }
    fn scoped(&mut self, names: impl Iterator<Item = &'a String>, body: SpecNode<'a>) {
        let previous: Vec<_> = names
            .map(|name| (name.as_str(), self.bindings.insert(name, None)))
            .collect();
        self.visit(body);
        for (name, old) in previous {
            self.restore(name, old);
        }
    }
    fn visit(&mut self, root: SpecNode<'a>) {
        walk_spec::<()>(root, WalkBudget::Unmetered, |node| {
            crate::instrumentation::record_deterministic_work(1);
            match node {
                SpecNode::Algebraic(expression) => match &expression.node {
                    SpecAlgebraicExpressionNode::Constructor { variant, fields } => {
                        if let Some(schema) = self.fields(&expression.algebraic_type, variant) {
                            for (field, ty) in fields.iter().zip(schema) {
                                if let (
                                    SpecAlgebraicValue::Program(value),
                                    AlgebraicValueType::ObjectPointer(_, class),
                                ) = (field, ty)
                                {
                                    self.require(value, class);
                                }
                            }
                        }
                    }
                    SpecAlgebraicExpressionNode::Match { scrutinee, arms } => {
                        self.visit(SpecNode::Algebraic(scrutinee));
                        for arm in arms {
                            self.scoped(arm.bindings.iter(), SpecNode::Algebraic(&arm.body));
                        }
                        return Visit::Skip;
                    }
                    _ => {}
                },
                SpecNode::Argument(SpecPureFunctionArgument::ObjectPointer {
                    argument,
                    object_class,
                }) => {
                    let value = match argument.as_ref() {
                        SpecPureFunctionArgument::Value(value)
                        | SpecPureFunctionArgument::ArrayRef { pointer: value, .. } => Some(value),
                        _ => None,
                    };
                    if let Some(value) = value {
                        self.require(value, object_class);
                    }
                }
                SpecNode::Expression(SpecExpression::Let { name, value, body }) => {
                    self.visit(SpecNode::Expression(value));
                    let origin = self.origins(value);
                    let old = self.bindings.insert(name, origin);
                    self.visit(SpecNode::Expression(body));
                    self.restore(name, old);
                    return Visit::Skip;
                }
                SpecNode::Expression(SpecExpression::AlgebraicMatch { scrutinee, arms }) => {
                    self.visit(SpecNode::Algebraic(scrutinee));
                    for arm in arms {
                        self.scoped(arm.bindings.iter(), SpecNode::Expression(&arm.body));
                    }
                    return Visit::Skip;
                }
                SpecNode::Proposition(
                    SpecProposition::ForAllPointer { name, body, .. }
                    | SpecProposition::ExistsPointer { name, body, .. }
                    | SpecProposition::ForAllInt32 { name, body, .. }
                    | SpecProposition::ExistsInt32 { name, body, .. }
                    | SpecProposition::ForAllMachineInteger { name, body, .. }
                    | SpecProposition::ExistsMachineInteger { name, body, .. }
                    | SpecProposition::ForAllInteger { name, body, .. }
                    | SpecProposition::ExistsInteger { name, body, .. }
                    | SpecProposition::ForAllAlgebraic { name, body, .. }
                    | SpecProposition::ExistsAlgebraic { name, body, .. },
                ) => {
                    self.scoped(std::iter::once(name), SpecNode::Proposition(body));
                    return Visit::Skip;
                }
                _ => {}
            }
            Visit::Descend
        });
    }
}

/// A nullable class entailed by an eager typed use of the result. Only
/// unconditional clauses and the exact nonnull-result guard cover every
/// possible nonnull return. Other guards and branching expressions supply none.
pub(in crate::kernel) fn declared_return_class(
    interface: &FunctionContractInterface,
) -> Option<effective_type::CAccessClass> {
    if !interface.return_type().is_pointer() {
        return None;
    }
    let mut analysis = Analysis::new(interface);
    let mut pending: Vec<_> = interface.contract_ensures().iter().collect();
    while let Some(clause) = pending.pop() {
        crate::instrumentation::record_deterministic_work(1);
        let class = match clause {
            SpecProposition::And(a, b) => {
                pending.extend([a.as_ref(), b.as_ref()]);
                None
            }
            SpecProposition::Implies(guard, body) if result_nonnull(guard) => {
                pending.push(body);
                None
            }
            SpecProposition::Comparison { left, right, .. } => {
                result_expression_class(left).or_else(|| result_expression_class(right))
            }
            SpecProposition::Defined(value) => result_expression_class(value),
            SpecProposition::AlgebraicComparison { left, right, .. } => analysis
                .result_model_class(left)
                .or_else(|| analysis.result_model_class(right)),
            _ => None,
        };
        if class.is_some() {
            return class;
        }
    }
    None
}
fn direct_result(value: &SpecExpression) -> bool {
    matches!(value, SpecExpression::ProgramExpression(ProgramExpression::Variable(name)) if name == C_CONTRACT_RESULT_NAME)
}
fn zero(value: &SpecExpression) -> bool {
    match value {
        SpecExpression::Value(value)
        | SpecExpression::ProgramExpression(ProgramExpression::Value(value)) => match value {
            ProgramValue::Pointer(p) => p.is_null(),
            ProgramValue::Int32(bits32_constant!(0))
            | ProgramValue::UInt32(bits32_constant!(0))
            | ProgramValue::UInt64(uint64_constant!(0)) => true,
            _ => false,
        },
        SpecExpression::Cast(value, _) => zero(value),
        _ => false,
    }
}
fn result_nonnull(proposition: &SpecProposition) -> bool {
    matches!(proposition, SpecProposition::Comparison { left, operator: ComparisonOperator::NotEqual, right }
        if (direct_result(left) && zero(right)) || (zero(left) && direct_result(right)))
}
fn result_arguments_class(
    arguments: &[SpecPureFunctionArgument],
) -> Option<effective_type::CAccessClass> {
    arguments.iter().find_map(|argument| {
        crate::instrumentation::record_deterministic_work(1);
        let SpecPureFunctionArgument::ObjectPointer {
            argument,
            object_class,
        } = argument
        else {
            return None;
        };
        let value = match argument.as_ref() {
            SpecPureFunctionArgument::Value(value)
            | SpecPureFunctionArgument::ArrayRef { pointer: value, .. } => value,
            _ => return None,
        };
        direct_result(value).then(|| object_class.clone())
    })
}
fn result_expression_class(value: &SpecExpression) -> Option<effective_type::CAccessClass> {
    if let SpecExpression::PureFunctionApplication { arguments, .. } = value {
        result_arguments_class(arguments)
    } else {
        None
    }
}
impl<'a> Analysis<'a> {
    fn result_model_class(
        &mut self,
        value: &'a SpecAlgebraicExpression,
    ) -> Option<effective_type::CAccessClass> {
        match &value.node {
            SpecAlgebraicExpressionNode::Constructor { variant, fields } => {
                let schema = self.fields(&value.algebraic_type, variant)?;
                fields.iter().zip(schema).find_map(|(field, ty)| {
                    crate::instrumentation::record_deterministic_work(1);
                    let (
                        SpecAlgebraicValue::Program(value),
                        AlgebraicValueType::ObjectPointer(_, class),
                    ) = (field, ty)
                    else {
                        return None;
                    };
                    direct_result(value).then(|| class.clone())
                })
            }
            SpecAlgebraicExpressionNode::PureFunctionApplication { arguments, .. } => {
                result_arguments_class(arguments)
            }
            _ => None,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::effective_type::{CAccessClass, CStructClass};
    fn class() -> CAccessClass {
        CAccessClass::Struct(CStructClass::opaque("node"))
    }
    fn variable(name: &str) -> SpecExpression {
        SpecExpression::ProgramExpression(ProgramExpression::Variable(name.to_string()))
    }
    fn typed(value: SpecExpression) -> SpecExpression {
        SpecExpression::PureFunctionApplication {
            name: "typed".to_string(),
            result_type: ProgramType::Int32,
            pointer_result: None,
            result_object_class: None,
            projection: None,
            arguments: vec![SpecPureFunctionArgument::ObjectPointer {
                argument: Box::new(SpecPureFunctionArgument::Value(value)),
                object_class: class(),
            }],
        }
    }
    fn interface(proposition: SpecProposition) -> FunctionContractInterface {
        let mut interface = FunctionContractInterface::new(
            ProgramType::Void,
            vec![
                ProgramParameter::new("p", ProgramType::Int32Pointer),
                ProgramParameter::new("q", ProgramType::Int32Pointer),
            ],
        );
        interface.contract_ensures = vec![proposition];
        interface.object_type_requirements = declared_requirements(&interface);
        interface
    }
    #[test]
    fn declarations_select_only_used_formals_and_respect_lexical_aliases() {
        let spec = SpecProposition::Defined(SpecExpression::Let {
            name: "p".to_string(),
            value: Box::new(variable("q")),
            body: Box::new(typed(variable("p"))),
        });
        assert_eq!(
            declared_requirements(&interface(spec)),
            ObjectTypeRequirements::unit(1, class())
        );
    }
    #[test]
    fn quantified_names_do_not_strengthen_same_named_program_inputs() {
        let spec = SpecProposition::ForAllPointer {
            name: "p".to_string(),
            variable: Variable(501),
            program_type: ProgramType::Int32Pointer,
            body: Box::new(SpecProposition::Defined(typed(variable("p")))),
        };
        assert!(declared_requirements(&interface(spec)).is_empty());
    }
    #[test]
    fn address_only_declarations_need_no_positive_type_assumption() {
        assert!(
            declared_requirements(&interface(SpecProposition::Comparison {
                left: variable("p"),
                operator: ComparisonOperator::Equal,
                right: variable("p"),
            }))
            .is_empty()
        );
    }
    #[test]
    fn captured_value_types_are_checked_after_interface_parameter_partitioning() {
        let interface = interface(SpecProposition::Defined(typed(variable("p"))))
            .with_leading_value_parameters(1)
            .unwrap();
        assert_eq!(
            interface.object_type_requirements(),
            &ObjectTypeRequirements::unit(1, class())
        );
        let mut normal = vec![ProgramValue::typed_pointer(
            Pointer::symbolic(Variable(700)),
            ProgramType::Int32Pointer,
        )];
        assert!(
            check_requirements(
                "f",
                interface.parameters(),
                interface.object_type_requirements(),
                &mut normal,
                &Memory::new(),
                &PureFactContext::new()
            )
            .is_none()
        );
        let mut captured = vec![ProgramValue::typed_pointer(
            Pointer::symbolic(Variable(701)),
            ProgramType::Int32Pointer,
        )];
        assert!(
            check_value_requirements(
                "f",
                &interface,
                &mut captured,
                &Memory::new(),
                &PureFactContext::new()
            )
            .is_some()
        );
        captured[0] = captured[0].clone().with_pointer_object_class(Some(class()));
        assert!(
            check_value_requirements(
                "f",
                &interface,
                &mut captured,
                &Memory::new(),
                &PureFactContext::new()
            )
            .is_none()
        );
    }

    fn returning(clause: SpecProposition) -> FunctionContractInterface {
        let mut interface = FunctionContractInterface::new(ProgramType::Int32Pointer, vec![]);
        interface.contract_ensures = vec![clause];
        interface
    }
    fn return_check() -> SpecProposition {
        SpecProposition::Defined(typed(variable(C_CONTRACT_RESULT_NAME)))
    }
    fn return_guard(operator: ComparisonOperator) -> SpecProposition {
        SpecProposition::Comparison {
            left: variable(C_CONTRACT_RESULT_NAME),
            operator,
            right: SpecExpression::Value(ProgramValue::Int32(MachineTerm::constant(0))),
        }
    }
    #[test]
    fn only_eager_or_nonnull_guarded_uses_guarantee_the_return_class() {
        assert_eq!(
            declared_return_class(&returning(return_check())),
            Some(class())
        );
        assert_eq!(
            declared_return_class(&returning(SpecProposition::Implies(
                Box::new(return_guard(ComparisonOperator::NotEqual)),
                Box::new(return_check())
            ))),
            Some(class())
        );
        for guard in [
            return_guard(ComparisonOperator::Equal),
            SpecProposition::Defined(variable("flag")),
        ] {
            assert_eq!(
                declared_return_class(&returning(SpecProposition::Implies(
                    Box::new(guard),
                    Box::new(return_check())
                ))),
                None
            );
        }
        assert_eq!(
            declared_return_class(&returning(SpecProposition::Or(
                Box::new(return_check()),
                Box::new(return_check())
            ))),
            None
        );
        let branched = SpecExpression::If {
            condition: Box::new(SpecProposition::Defined(variable("flag"))),
            then_branch: Box::new(typed(variable(C_CONTRACT_RESULT_NAME))),
            else_branch: Box::new(variable("other")),
        };
        assert_eq!(
            declared_return_class(&returning(SpecProposition::Defined(branched))),
            None
        );
        let mut address_only = FunctionContractInterface::new(ProgramType::Int32Pointer, vec![]);
        address_only.return_pointee_class = Some(class());
        assert_eq!(declared_return_class(&address_only), None);
    }
    #[cfg(test)]
    mod scaling_tests {
        include!("../../scaling_tests/kernel/object_types/contract_requirements_tests.rs");
    }
}
