//! Generated spec trees for the oracle tests of spec-tree walks.

use super::*;

/// A deterministic generator of mixed spec trees for oracle tests.
///
/// Leaves include C names that the generated binders also bind (`n`, `v`,
/// `acc`, `i`), variables, and resource fields. A quantifier's variable is
/// fresh and occurs only inside its body, as lowering allocates it.
pub(in crate::kernel) struct Gen {
    state: u64,
    binders: Vec<Variable>,
    next_binder: u64,
}

impl Gen {
    pub(in crate::kernel) fn new(seed: u64) -> Self {
        Gen {
            state: seed,
            binders: Vec::new(),
            next_binder: 900_500,
        }
    }

    pub(in crate::kernel) fn pick(&mut self, n: u64) -> u64 {
        self.state ^= self.state << 13;
        self.state ^= self.state >> 7;
        self.state ^= self.state << 17;
        self.state % n
    }

    /// A free variable, or a quantifier variable in scope.
    fn variable(&mut self) -> Variable {
        let in_scope = self.binders.len() as u64;
        match self.pick(3 + in_scope) {
            choice @ 0..3 => Variable(900_100 + choice),
            choice => self.binders[(choice - 3) as usize],
        }
    }

    fn projection(&mut self) -> ResourceFieldProjection {
        ResourceFieldProjection {
            identity: Variable(900_200 + self.pick(2)),
            children: vec![],
            field_index: 0,
            at_entry: false,
        }
    }

    fn quantified(&mut self, depth: u32) -> (Variable, Box<SpecProposition>) {
        let variable = Variable(self.next_binder);
        self.next_binder += 1;
        self.binders.push(variable);
        let body = Box::new(self.prop(depth));
        self.binders.pop();
        (variable, body)
    }

    fn ty(&self) -> AlgebraicType {
        let variants: std::sync::Arc<[AlgebraicVariantType]> = vec![
            AlgebraicVariantType {
                name: "One".into(),
                fields: vec![AlgebraicValueType::Integer],
            },
            AlgebraicVariantType {
                name: "Two".into(),
                fields: vec![],
            },
        ]
        .into();
        AlgebraicType {
            rigid: false,
            name: "Choice".into(),
            arguments: vec![],
            variants: variants.clone(),
            schemas: std::sync::Arc::new(AlgebraicSchemas::new(BTreeMap::from([(
                AlgebraicValueType::Algebraic {
                    name: "Choice".into(),
                    arguments: vec![],
                },
                variants,
            )]))),
        }
    }

    fn memory(&mut self) -> SpecMemory {
        match self.pick(4) {
            0 => SpecMemory::Current,
            1 => SpecMemory::FunctionEntry,
            2 => SpecMemory::LoopEntry,
            _ => SpecMemory::Fixed(CMemory::new()),
        }
    }

    fn c(&mut self) -> CExpression {
        const NAMES: [&str; 6] = ["x", "x", "n", "v", "acc", "i"];
        match self.pick(4) {
            0 => CExpression::Variable(NAMES[self.pick(6) as usize].into()),
            1 => CExpression::Value(CValue::Int32(Bitvector32Term::Constant(1))),
            2 => CExpression::Value(CValue::Int32(Bitvector32Term::Variable(self.variable()))),
            _ => CExpression::Load(Box::new(CExpression::Variable("p".into()))),
        }
    }

    fn expr_leaf(&mut self) -> SpecExpression {
        match self.pick(5) {
            0 => SpecExpression::Value(CValue::Int32(Bitvector32Term::Constant(7))),
            1 => SpecExpression::Value(CValue::Int32(Bitvector32Term::Variable(self.variable()))),
            2 => SpecExpression::ResourceField {
                projection: self.projection(),
                c_type: CType::Int32,
            },
            _ => SpecExpression::CExpression(self.c()),
        }
    }

    /// A load address: often a constant offset from the parameter `x`.
    fn pointer(&mut self, depth: u32) -> SpecExpression {
        let parameter = SpecExpression::CExpression(CExpression::Variable("x".into()));
        match self.pick(3) {
            0 => parameter,
            1 => SpecExpression::PointerOffset {
                pointer: Box::new(parameter),
                elements: Box::new(SpecExpression::Value(CValue::Int32(
                    Bitvector32Term::Constant(2),
                ))),
                byte_width: 4,
            },
            _ => self.expr(depth),
        }
    }

    pub(in crate::kernel) fn expr(&mut self, depth: u32) -> SpecExpression {
        if depth == 0 {
            return self.expr_leaf();
        }
        let d = depth - 1;
        match self.pick(19) {
            0 => self.expr_leaf(),
            1 => SpecExpression::CExpression(self.c()),
            2 => SpecExpression::IntegerToMachine {
                value: Box::new(self.int(d)),
                destination: MachineIntegerType::Int32,
            },
            3 => SpecExpression::Add(Box::new(self.expr(d)), Box::new(self.expr(d))),
            4 => SpecExpression::BitwiseNot(Box::new(self.expr(d))),
            5 => SpecExpression::Cast(Box::new(self.expr(d)), CType::Int32),
            6 => SpecExpression::LoopEntrySnapshot(Box::new(self.expr(d))),
            7 => SpecExpression::If {
                condition: Box::new(self.prop(d)),
                then_branch: Box::new(self.expr(d)),
                else_branch: Box::new(self.expr(d)),
            },
            8 => SpecExpression::RangeFold {
                start: Box::new(self.expr(d)),
                end: Box::new(self.expr(d)),
                initial: Box::new(self.expr(d)),
                accumulator: "acc".into(),
                item: "i".into(),
                body: Box::new(self.expr(d)),
            },
            9 => SpecExpression::Let {
                name: "v".into(),
                value: Box::new(self.expr(d)),
                body: Box::new(self.expr(d)),
            },
            10 => SpecExpression::PureFunctionApplication {
                name: "f".into(),
                arguments: vec![self.arg(d), self.arg(d)],
                result_type: CType::Int32,
            },
            11 => SpecExpression::PointerOffset {
                pointer: Box::new(self.expr(d)),
                elements: Box::new(self.expr(d)),
                byte_width: 4,
            },
            12 => SpecExpression::MemoryLoad {
                memory: self.memory(),
                pointer: Box::new(self.pointer(d)),
                value_type: CType::Int32,
            },
            13 => SpecExpression::AggregateFieldValue {
                parameter: "s".into(),
                pointer: Box::new(self.pointer(d)),
                value_type: CType::Int32,
            },
            14 => SpecExpression::CountedResourceCount {
                name: "member".into(),
                arguments: vec![Some(self.expr(d)), None],
            },
            15 => SpecExpression::AlgebraicMatch {
                scrutinee: Box::new(self.alg(d)),
                arms: vec![
                    SpecAlgebraicMatchArm {
                        variant: "Two".into(),
                        bindings: vec![],
                        binding_types: vec![],
                        body: self.expr(d),
                    },
                    SpecAlgebraicMatchArm {
                        variant: "One".into(),
                        bindings: vec!["n".into()],
                        binding_types: vec![AlgebraicValueType::Integer],
                        body: self.expr(d),
                    },
                ],
            },
            16 => SpecExpression::Multiply(Box::new(self.expr(d)), Box::new(self.expr(d))),
            17 => SpecExpression::ShiftRight(Box::new(self.expr(d)), Box::new(self.expr(d))),
            _ => SpecExpression::BitwiseXor(Box::new(self.expr(d)), Box::new(self.expr(d))),
        }
    }

    pub(in crate::kernel) fn int(&mut self, depth: u32) -> SpecIntegerExpression {
        if depth == 0 || self.pick(8) == 0 {
            return match self.pick(3) {
                0 => SpecIntegerExpression::Term(IntegerTerm::constant_i64(3)),
                1 => SpecIntegerExpression::Term(IntegerTerm::var(self.variable())),
                _ => SpecIntegerExpression::ResourceField(self.projection()),
            };
        }
        let d = depth - 1;
        match self.pick(10) {
            0 => SpecIntegerExpression::AlgebraicMatch {
                scrutinee: Box::new(self.alg(d)),
                arms: vec![SpecIntegerMatchArm {
                    variant: "One".into(),
                    bindings: vec!["n".into()],
                    binding_types: vec![AlgebraicValueType::Integer],
                    binding_variables: vec![Some(Variable(900_011))],
                    body: Box::new(self.int(d)),
                }],
            },
            1 => SpecIntegerExpression::FromMachine(Box::new(self.expr(d))),
            2 => SpecIntegerExpression::Negate(Box::new(self.int(d))),
            3 => SpecIntegerExpression::Add(Box::new(self.int(d)), Box::new(self.int(d))),
            4 => SpecIntegerExpression::TruncatingQuotient(
                Box::new(self.int(d)),
                Box::new(self.int(d)),
            ),
            5 => SpecIntegerExpression::PureFunctionApplication {
                name: "g".into(),
                arguments: vec![self.arg(d)],
            },
            6 => SpecIntegerExpression::RangeFold {
                index: match self.pick(2) {
                    0 => SpecIntegerRangeFoldIndex::Int32 {
                        start: Box::new(self.expr(d)),
                        end: Box::new(self.expr(d)),
                    },
                    _ => SpecIntegerRangeFoldIndex::Integer {
                        start: Box::new(self.int(d)),
                        end: Box::new(self.int(d)),
                    },
                },
                initial: Box::new(self.int(d)),
                accumulator: Variable(900_001),
                item: Variable(900_002),
                body: Box::new(self.int(d)),
            },
            7 => SpecIntegerExpression::Multiply(Box::new(self.int(d)), Box::new(self.int(d))),
            8 => SpecIntegerExpression::Subtract(Box::new(self.int(d)), Box::new(self.int(d))),
            _ => SpecIntegerExpression::TruncatingRemainder(
                Box::new(self.int(d)),
                Box::new(self.int(d)),
            ),
        }
    }

    pub(in crate::kernel) fn alg(&mut self, depth: u32) -> SpecAlgebraicExpression {
        let algebraic_type = self.ty();
        let node = if depth == 0 {
            match self.pick(2) {
                0 => SpecAlgebraicExpressionNode::Variable(Variable(900_010)),
                _ => SpecAlgebraicExpressionNode::Binding("b".into()),
            }
        } else if self.pick(8) == 0 {
            SpecAlgebraicExpressionNode::ResourceField(self.projection())
        } else {
            let d = depth - 1;
            match self.pick(6) {
                0 => SpecAlgebraicExpressionNode::Variable(Variable(900_010)),
                1 => SpecAlgebraicExpressionNode::Constructor {
                    variant: "One".into(),
                    fields: vec![match self.pick(3) {
                        0 => SpecAlgebraicValue::C(self.expr(d)),
                        1 => SpecAlgebraicValue::Integer(self.int(d)),
                        _ => SpecAlgebraicValue::Algebraic(self.alg(d)),
                    }],
                },
                2 | 3 => {
                    let full = self.pick(2) == 0;
                    let mut arms = vec![SpecAlgebraicResultMatchArm {
                        variant: "Two".into(),
                        bindings: vec![],
                        binding_types: vec![],
                        binding_variables: vec![],
                        body: Box::new(self.alg(d)),
                    }];
                    if full {
                        arms.push(SpecAlgebraicResultMatchArm {
                            variant: "One".into(),
                            bindings: vec!["n".into()],
                            binding_types: vec![AlgebraicValueType::Integer],
                            binding_variables: vec![Some(Variable(900_011))],
                            body: Box::new(self.alg(d)),
                        });
                    }
                    SpecAlgebraicExpressionNode::Match {
                        scrutinee: Box::new(self.alg(d)),
                        arms,
                    }
                }
                4 => SpecAlgebraicExpressionNode::PureFunctionApplication {
                    name: if self.pick(3) == 0 {
                        "to_nat".into()
                    } else {
                        "h".into()
                    },
                    arguments: vec![self.arg(d)],
                },
                _ => SpecAlgebraicExpressionNode::Binding("b".into()),
            }
        };
        SpecAlgebraicExpression {
            algebraic_type,
            node,
        }
    }

    pub(in crate::kernel) fn arg(&mut self, depth: u32) -> SpecPureFunctionArgument {
        match self.pick(4) {
            0 => SpecPureFunctionArgument::Value(self.expr(depth)),
            1 => SpecPureFunctionArgument::Integer(self.int(depth)),
            2 => SpecPureFunctionArgument::Algebraic(self.alg(depth)),
            _ => SpecPureFunctionArgument::ArrayRef {
                memory: self.memory(),
                pointer: self.expr(depth),
                element_type: CType::Int32,
            },
        }
    }

    pub(in crate::kernel) fn seq(&mut self, depth: u32) -> SpecSequenceExpression {
        if depth == 0 || self.pick(2) == 0 {
            SpecSequenceExpression::Literal(vec![self.expr(depth), self.expr(depth)])
        } else {
            SpecSequenceExpression::Concat(
                Box::new(self.seq(depth - 1)),
                Box::new(self.seq(depth - 1)),
            )
        }
    }

    pub(in crate::kernel) fn resource(&mut self, depth: u32) -> SpecResource {
        match self.pick(2) {
            0 => SpecResource::Memory {
                base: self.expr(depth),
                start: self.expr(depth),
                end: self.expr(depth),
                element_width: 4,
            },
            _ => SpecResource::Token {
                name: "t".into(),
                arguments: vec![self.expr(depth)],
            },
        }
    }

    pub(in crate::kernel) fn prop(&mut self, depth: u32) -> SpecProposition {
        let d = depth.saturating_sub(1);
        let choice = if depth == 0 {
            self.pick(2)
        } else {
            self.pick(17)
        };
        match choice {
            0 => SpecProposition::Comparison {
                left: self.expr(d),
                operator: CComparisonOperator::LessThan,
                right: self.expr(d),
            },
            1 => SpecProposition::Defined(self.expr(d)),
            2 => SpecProposition::IntegerComparison {
                left: self.int(d),
                operator: IntegerComparisonOperator::LessEqual,
                right: self.int(d),
            },
            3 => SpecProposition::AlgebraicComparison {
                left: self.alg(d),
                equal: true,
                right: self.alg(d),
            },
            4 => SpecProposition::SequenceMembership {
                element: self.expr(d),
                sequence: self.seq(d),
            },
            5 => SpecProposition::SequenceComparison {
                left: self.seq(d),
                equal: false,
                right: self.seq(d),
            },
            6 => SpecProposition::And(Box::new(self.prop(d)), Box::new(self.prop(d))),
            7 => SpecProposition::Implies(Box::new(self.prop(d)), Box::new(self.prop(d))),
            8 => SpecProposition::Not(Box::new(self.prop(d))),
            9 => {
                let (variable, body) = self.quantified(d);
                SpecProposition::ForAllInt32 {
                    name: "k".into(),
                    variable,
                    body,
                }
            }
            10 => {
                let (variable, body) = self.quantified(d);
                SpecProposition::ExistsInteger {
                    name: "z".into(),
                    variable,
                    body,
                }
            }
            11 => SpecProposition::Predicate {
                name: "pred".into(),
                arguments: vec![
                    SpecPredicateArgument::Value(self.expr(d)),
                    SpecPredicateArgument::ArrayRef {
                        memory: self.memory(),
                        pointer: self.expr(d),
                    },
                ],
                resource_state_dependent: self.pick(2) == 0,
            },
            12 => SpecProposition::ResourceSeparate {
                left: self.resource(d),
                right: self.resource(d),
            },
            13 => SpecProposition::MemoryLoadable {
                memory: self.memory(),
                base: self.expr(d),
                start: self.expr(d),
                end: self.expr(d),
                element_width: 4,
            },
            14 => SpecProposition::FloatClassification {
                expression: self.expr(d),
                classification: CFloatClassification::Finite,
            },
            15 => SpecProposition::Or(Box::new(self.prop(d)), Box::new(self.prop(d))),
            _ => SpecProposition::ResourceContains {
                parent: self.resource(d),
                child: self.resource(d),
            },
        }
    }
}
