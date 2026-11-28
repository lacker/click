//! Logical Bool operands of machine conversions. Import/export preserves the
//! written comparison format, even when fact equality identifies formats.
use super::*;
mod call;
mod comparison;
mod complete_pointer;
mod composition;
mod overflow;
mod storage;
pub use complete_pointer::KernelPointerEquality;
mod pointer_comparison;

/// Borrow a Boolean root or an exact native compatibility payload. Inspecting
/// this view never exports children, consults facts, or selects a branch.
#[derive(Clone, Copy)]
pub(crate) enum BooleanOperandView<'a> {
    Shared(&'a KernelTerm),
    Native(&'a OldConditionTerm),
}

impl<'a> BooleanOperandView<'a> {
    /// Visit dependency-bearing Boolean leaves, sharing a common connective
    /// once. Call arguments and native opaque leaves keep the reader's rules.
    pub(crate) fn for_each_dependency_leaf(self, mut visit: impl FnMut(Self)) {
        let mut pending = vec![self];
        let mut seen = std::collections::HashSet::new();
        while let Some(view) = pending.pop() {
            if let Self::Shared(root) = view
                && !seen.insert(root.id())
            {
                continue;
            }
            crate::instrumentation::record_deterministic_work(1);
            if let Some(children) = view.conditional() {
                pending.extend(children.into_iter().rev());
            } else if let Some(children) = view.equality() {
                pending.extend(children.into_iter().rev());
            } else {
                visit(view);
            }
        }
    }

    /// Exact native Boolean identity, without exporting connective trees or
    /// primitive comparison operands. Load authority is never consulted here.
    pub(crate) fn syntax_equal(self, other: Self) -> bool {
        self.syntax_equal_by(other, |a, b| {
            crate::kernel::machine_operand_syntax_cmp(a, b).is_eq()
        })
    }

    /// The callback supplies exact native machine syntax equality. Callers
    /// outside the machine correspondence traversal may reuse its syntax memo;
    /// callers inside it use the non-reentrant reader above.
    pub(crate) fn syntax_equal_by(
        self,
        other: Self,
        mut machine_equal: impl FnMut(MachineOperandView<'a>, MachineOperandView<'a>) -> bool,
    ) -> bool {
        use crate::kernel::machine_integer::comparison::{FactOperand, fact_operand_identity};
        let mut pending = vec![(self, other)];
        let mut seen = std::collections::HashSet::new();
        while let Some((left, right)) = pending.pop() {
            crate::instrumentation::record_deterministic_work(1);
            if let (Self::Shared(a), Self::Shared(b)) = (left, right)
                && (a == b || !seen.insert((a.id(), b.id())))
            {
                continue;
            }
            if let (Some(a), Some(b)) = (left.native_leaf(), right.native_leaf()) {
                if a != b {
                    return false;
                }
                continue;
            }
            match (left.conditional(), right.conditional()) {
                (Some(a), Some(b)) => {
                    pending.extend(a.into_iter().zip(b));
                    continue;
                }
                (None, None) => {}
                _ => return false,
            }
            match (left.equality(), right.equality()) {
                (Some(a), Some(b)) => {
                    pending.extend(a.into_iter().zip(b));
                    continue;
                }
                (None, None) => {}
                _ => return false,
            }
            match (left.comparison(), right.comparison()) {
                (Some((af, ar, a)), Some((bf, br, b))) => {
                    if ar != br {
                        return false;
                    }
                    let (af, a) = fact_operand_identity(af, ar, a);
                    let (bf, b) = fact_operand_identity(bf, br, b);
                    if af != bf {
                        return false;
                    }
                    for (a, b) in a.into_iter().zip(b) {
                        let equal = match (a, b) {
                            (FactOperand::Value(a), FactOperand::Value(b)) => a == b,
                            (FactOperand::Term(a), FactOperand::Term(b)) => machine_equal(a, b),
                            _ => false,
                        };
                        if !equal {
                            return false;
                        }
                    }
                    continue;
                }
                (None, None) => {}
                _ => return false,
            }
            match (left.float_comparison(), right.float_comparison()) {
                (Some((af, ao, a)), Some((bf, bo, b))) => {
                    if af != bf || ao != bo || !a.into_iter().zip(b).all(|(a, b)| a.syntax_equal(b))
                    {
                        return false;
                    }
                    continue;
                }
                (None, None) => {}
                _ => return false,
            }
            match (left.float_classification(), right.float_classification()) {
                (Some((af, ac, a)), Some((bf, bc, b))) => {
                    if af != bf || ac != bc || !a.syntax_equal(b) {
                        return false;
                    }
                    continue;
                }
                (None, None) => {}
                _ => return false,
            }
            match (left.algebraic_equality(), right.algebraic_equality()) {
                (Some(a), Some(b)) => {
                    if !a.iter().zip(&b).all(|(a, b)| a.algebraic_syntax_equal(b)) {
                        return false;
                    }
                    continue;
                }
                (None, None) => {}
                _ => return false,
            }
            match (left.overflow(), right.overflow()) {
                (Some((af, ao, a)), Some((bf, bo, b))) => {
                    if af != bf
                        || ao != bo
                        || !a.into_iter().zip(b).all(|(a, b)| machine_equal(a, b))
                    {
                        return false;
                    }
                    continue;
                }
                (None, None) => {}
                _ => return false,
            }
            match (left.pointer_offsets(), right.pointer_offsets()) {
                (Some(a), Some(b)) => {
                    if !a.iter().zip(&b).all(|(a, b)| a.syntax_equal(b)) {
                        return false;
                    }
                    continue;
                }
                (None, None) => {}
                _ => return false,
            }
            match (left.pointer_values(), right.pointer_values()) {
                (Some(a), Some(b)) => {
                    if !a.iter().zip(&b).all(|(a, b)| a.condition_syntax_equal(b)) {
                        return false;
                    }
                    continue;
                }
                (None, None) => {}
                _ => return false,
            }
            match (left.pointer_addresses(), right.pointer_addresses()) {
                (Some(a), Some(b)) => {
                    if !a.iter().zip(&b).all(|(a, b)| a.syntax_equal(b)) {
                        return false;
                    }
                    continue;
                }
                (None, None) => {}
                _ => return false,
            }
            if left.identity_leaf() != right.identity_leaf() {
                return false;
            }
        }
        true
    }

    /// Keep numeric call arguments as typed handles for semantic identity.
    /// Other leaves already have exact native payloads or shared Integer
    /// bridges; no enclosing Boolean connective reaches this boundary.
    pub(crate) fn identity_leaf(self) -> std::borrow::Cow<'a, OldConditionTerm> {
        if let Self::Shared(root) = self
            && let Some(call) = root.old_boolean_call()
        {
            return std::borrow::Cow::Borrowed(call);
        }
        self.native()
    }

    pub(crate) fn algebraic_equality(self) -> Option<[KernelTerm; 2]> {
        if let Self::Shared(root) = self
            && let KernelTermNode::AlgebraicEqual { arguments } = root.node()
        {
            return Some(arguments.clone());
        }
        let OldConditionTerm::AlgebraicEqual(a, b) = self.native_leaf()? else {
            return None;
        };
        Some([
            KernelTermImport::default().algebraic(a),
            KernelTermImport::default().algebraic(b),
        ])
    }

    /// Borrow the written operands for keys that compare algebraic term syntax.
    pub(crate) fn written_algebraic_equality(self) -> Option<[&'a AlgebraicTerm; 2]> {
        let native = match self {
            Self::Native(condition) => condition,
            Self::Shared(root) => {
                let KernelTermNode::AlgebraicEqual {
                    arguments: [left, right],
                } = root.node()
                else {
                    return None;
                };
                let Some(condition) = root.cached_condition_output() else {
                    return Some([
                        left.algebraic_native_term()?,
                        right.algebraic_native_term()?,
                    ]);
                };
                condition
            }
        };
        match native {
            OldConditionTerm::AlgebraicEqual(left, right) => Some([left, right]),
            _ => None,
        }
    }

    pub(crate) fn native_leaf(self) -> Option<&'a OldConditionTerm> {
        match self {
            Self::Native(value) => Some(value),
            Self::Shared(_) => None,
        }
    }

    /// Explicit compatibility boundary for callers that still need a native
    /// condition. Borrow existing leaves; only common compound roots export.
    pub(crate) fn native(self) -> std::borrow::Cow<'a, OldConditionTerm> {
        if let Self::Shared(root) = self
            && let Some(value) = root.cached_condition_output()
        {
            return std::borrow::Cow::Borrowed(value);
        }
        if let Some(value) = self.native_leaf() {
            return std::borrow::Cow::Borrowed(value);
        }
        let Self::Shared(root) = self else {
            unreachable!()
        };
        std::borrow::Cow::Owned(KernelTermExport::condition(root).expect("Boolean operand"))
    }

    pub(crate) fn pointer_values(self) -> Option<[SharedPointer; 2]> {
        if let Self::Shared(root) = self
            && let KernelTermNode::PointerEqual(pair) = root.node()
        {
            return Some(pair.arguments().clone());
        }
        let OldConditionTerm::PointerEqual(a, b) = self.native_leaf()? else {
            return None;
        };
        Some([a.shared().clone(), b.shared().clone()])
    }

    pub(crate) fn pointer_addresses(self) -> Option<[SharedAddress; 2]> {
        if let Self::Shared(root) = self
            && let KernelTermNode::AddressEqual { arguments, .. } = root.node()
        {
            return Some(arguments.clone());
        }
        let OldConditionTerm::AddressEqual(a, b) = self.native_leaf()? else {
            return None;
        };
        Some([a.shared().clone(), b.shared().clone()])
    }

    pub(crate) fn pointer_offsets(self) -> Option<[SharedAddressOffset; 2]> {
        if let Self::Shared(root) = self
            && let KernelTermNode::AddressOffsetEqual { arguments } = root.node()
        {
            return Some(arguments.clone());
        }
        let OldConditionTerm::AddressOffsetEqual(a, b) = self.native_leaf()? else {
            return None;
        };
        Some([a.shared().clone(), b.shared().clone()])
    }

    pub(crate) fn constant(self) -> Option<bool> {
        match self {
            Self::Shared(root) if matches!(root.node(), KernelTermNode::BoolLiteral(_)) => {
                let KernelTermNode::BoolLiteral(value) = root.node() else {
                    unreachable!()
                };
                Some(*value)
            }
            _ => match self.native_leaf()? {
                OldConditionTerm::Constant(value) => Some(*value),
                _ => None,
            },
        }
    }

    pub(crate) fn variable(self) -> Option<&'a Variable> {
        match self {
            Self::Shared(root) => match root.node() {
                KernelTermNode::Variable(variable) => Some(variable),
                _ => None,
            },
            Self::Native(OldConditionTerm::Variable(variable)) => Some(variable),
            _ => None,
        }
    }

    pub(crate) fn conditional(self) -> Option<[Self; 3]> {
        match self {
            Self::Shared(root) => match root.node() {
                KernelTermNode::BoolIf { arguments } => {
                    Some(arguments.each_ref().map(Self::Shared))
                }
                _ => None,
            },
            Self::Native(OldConditionTerm::BoolIf {
                condition,
                then_condition,
                else_condition,
            }) => Some([
                Self::Native(condition),
                Self::Native(then_condition),
                Self::Native(else_condition),
            ]),
            _ => None,
        }
    }

    pub(crate) fn equality(self) -> Option<[Self; 2]> {
        match self {
            Self::Shared(root) => match root.node() {
                KernelTermNode::BoolEqual { arguments } => {
                    Some(arguments.each_ref().map(Self::Shared))
                }
                _ => None,
            },
            Self::Native(OldConditionTerm::BoolEqual(left, right)) => {
                Some([Self::Native(left), Self::Native(right)])
            }
            _ => None,
        }
    }

    pub(crate) fn is_integer_comparison(self) -> bool {
        match self {
            Self::Shared(root) if matches!(root.node(), KernelTermNode::IntegerCompare { .. }) => {
                true
            }
            _ => self.native_leaf().is_some_and(|value| {
                matches!(value, crate::kernel::integer_comparison_condition!(_, _))
            }),
        }
    }

    pub(crate) fn is_bool_value_form(self) -> bool {
        match self {
            Self::Shared(root)
                if matches!(
                    root.node(),
                    KernelTermNode::BoolIf { .. }
                        | KernelTermNode::BoolEqual { .. }
                        | KernelTermNode::Call { .. }
                ) =>
            {
                true
            }
            _ => self
                .native_leaf()
                .is_some_and(OldConditionTerm::is_bool_value_form),
        }
    }

    pub(crate) fn machine_arguments(
        self,
    ) -> Option<(MachineIntegerType, [MachineOperandView<'a>; 2])> {
        self.comparison()
            .map(|(format, _, arguments)| (format, arguments))
            .or_else(|| {
                self.overflow()
                    .map(|(format, _, arguments)| (format, arguments))
            })
    }
    pub(crate) fn overflow(
        self,
    ) -> Option<(
        MachineIntegerType,
        OverflowOperation,
        [MachineOperandView<'a>; 2],
    )> {
        match self {
            Self::Shared(root) => match root.node() {
                KernelTermNode::BoolOverflow {
                    format,
                    operation,
                    arguments,
                } => Some((
                    *format,
                    *operation,
                    arguments.each_ref().map(MachineOperandView::Shared),
                )),
                _ => None,
            },
            Self::Native(OldConditionTerm::Overflows {
                format,
                op,
                left,
                right,
            }) => Some((
                *format,
                *op,
                [
                    MachineOperandView::Old(left),
                    MachineOperandView::Old(right),
                ],
            )),
            _ => None,
        }
    }

    pub(crate) fn comparison(
        self,
    ) -> Option<(
        MachineIntegerType,
        CompareRelation,
        [MachineOperandView<'a>; 2],
    )> {
        match self {
            Self::Shared(root) => match root.node() {
                KernelTermNode::BoolCompare {
                    format,
                    relation,
                    arguments,
                } => Some((
                    *format,
                    *relation,
                    arguments.each_ref().map(MachineOperandView::Shared),
                )),
                _ => None,
            },
            Self::Native(OldConditionTerm::Compare {
                format,
                relation,
                left,
                right,
            }) => Some((
                *format,
                *relation,
                [
                    MachineOperandView::Old(left),
                    MachineOperandView::Old(right),
                ],
            )),
            _ => None,
        }
    }
}

impl KernelTerm {
    pub(crate) fn integer_comparison(
        operator: IntegerComparisonOperator,
        arguments: [Self; 2],
    ) -> Result<Self, &'static str> {
        if arguments
            .iter()
            .any(|argument| argument.ty() != &KernelType::Integer)
        {
            return Err("Integer comparison requires Integer operands");
        }
        Ok(Self::intern(
            KernelType::Bool,
            KernelTermNode::IntegerCompare {
                operator,
                arguments,
            },
        ))
    }

    pub(crate) fn boolean_if_raw(arguments: [Self; 3]) -> Self {
        Self::intern(KernelType::Bool, KernelTermNode::BoolIf { arguments })
    }

    pub(crate) fn boolean_equal_raw(arguments: [Self; 2]) -> Self {
        Self::intern(KernelType::Bool, KernelTermNode::BoolEqual { arguments })
    }

    /// Structural Boolean reconstruction. The callback owns each selected
    /// atom's existing rewrite and binder rules; connectives are never folded.
    /// A query-local memo prevents shared Boolean prefixes becoming trees.
    pub(crate) fn map_boolean_leaves<E>(
        &self,
        leaf: impl FnMut(&Self) -> Result<Self, E>,
    ) -> Result<Self, E> {
        self.map_boolean_with_connectives(leaf, |original, children| {
            let node = match original.node() {
                KernelTermNode::BoolIf { .. } => KernelTermNode::BoolIf {
                    arguments: [
                        children[0].clone(),
                        children[1].clone(),
                        children[2].clone(),
                    ],
                },
                KernelTermNode::BoolEqual { .. } => KernelTermNode::BoolEqual {
                    arguments: [children[0].clone(), children[1].clone()],
                },
                _ => unreachable!(),
            };
            Ok(Self::intern(KernelType::Bool, node))
        })
    }

    pub(crate) fn map_boolean_with_connectives<E>(
        &self,
        leaf: impl FnMut(&Self) -> Result<Self, E>,
        connective: impl FnMut(&Self, &[Self]) -> Result<Self, E>,
    ) -> Result<Self, E> {
        self.map_boolean_with_connectives_cached(|_| None, leaf, connective)
    }

    /// The caller's active-scope memo can stop at an already rewritten common
    /// prefix. The per-call memo still shares all newly visited connectives.
    pub(crate) fn map_boolean_with_connectives_cached<E>(
        &self,
        mut cached: impl FnMut(&Self) -> Option<Self>,
        mut leaf: impl FnMut(&Self) -> Result<Self, E>,
        mut connective: impl FnMut(&Self, &[Self]) -> Result<Self, E>,
    ) -> Result<Self, E> {
        let mut rewritten = HashMap::<u64, Self>::new();
        let mut pending = vec![(self, false)];
        while let Some((term, finish)) = pending.pop() {
            if rewritten.contains_key(&term.id()) {
                continue;
            }
            if let Some(result) = cached(term) {
                rewritten.insert(term.id(), result);
                continue;
            }
            crate::instrumentation::record_deterministic_work(1);
            let children: &[Self] = match term.node() {
                KernelTermNode::BoolIf { arguments } => arguments,
                KernelTermNode::BoolEqual { arguments } => arguments,
                _ => {
                    rewritten.insert(term.id(), leaf(term)?);
                    continue;
                }
            };
            if !finish {
                pending.push((term, true));
                pending.extend(children.iter().rev().map(|child| (child, false)));
                continue;
            }
            let children: Vec<_> = children
                .iter()
                .map(|child| rewritten[&child.id()].clone())
                .collect();
            let result = connective(term, &children)?;
            rewritten.insert(term.id(), result);
        }
        Ok(rewritten
            .remove(&self.id())
            .expect("rewritten Boolean root"))
    }
}

impl KernelTermImport {
    pub(crate) fn condition(&mut self, condition: &OldConditionTerm) -> KernelTerm {
        use KernelTermNode as Node;
        use OldConditionTerm as Old;
        crate::instrumentation::record_deterministic_work(1);
        let node = match condition {
            Old::Overflows {
                format,
                op,
                left,
                right,
            } => Node::BoolOverflow {
                format: *format,
                operation: *op,
                arguments: [self.machine(*format, left), self.machine(*format, right)],
            },
            Old::PointerEqual(a, b) => {
                return KernelTerm::pointer_equal_raw([a.shared().clone(), b.shared().clone()]);
            }
            Old::AddressEqual(a, b) => {
                return KernelTerm::address_equal_raw([a.shared().clone(), b.shared().clone()]);
            }
            Old::AddressOffsetEqual(a, b) => {
                return KernelTerm::address_offset_equal_raw([
                    a.shared().clone(),
                    b.shared().clone(),
                ]);
            }
            Old::Constant(value) => Node::BoolLiteral(*value),
            Old::Variable(variable) => Node::Variable(*variable),
            Old::Compare {
                format,
                relation,
                left,
                right,
            } => Node::BoolCompare {
                format: *format,
                relation: *relation,
                arguments: [self.machine(*format, left), self.machine(*format, right)],
            },
            Old::IntegerLessThan(left, right)
            | Old::IntegerLessEqual(left, right)
            | Old::IntegerGreaterThan(left, right)
            | Old::IntegerGreaterEqual(left, right)
            | Old::IntegerEqual(left, right)
            | Old::IntegerNotEqual(left, right) => {
                use IntegerComparisonOperator as Op;
                let operator = match condition {
                    Old::IntegerLessThan(..) => Op::LessThan,
                    Old::IntegerLessEqual(..) => Op::LessEqual,
                    Old::IntegerGreaterThan(..) => Op::GreaterThan,
                    Old::IntegerGreaterEqual(..) => Op::GreaterEqual,
                    Old::IntegerEqual(..) => Op::Equal,
                    Old::IntegerNotEqual(..) => Op::NotEqual,
                    _ => unreachable!(),
                };
                Node::IntegerCompare {
                    operator,
                    arguments: [self.integer(left), self.integer(right)],
                }
            }
            Old::Float32(value) => return self.float_condition(KernelFloatType::Float32, value),
            Old::Float64(value) => return self.float_condition(KernelFloatType::Float64, value),
            Old::AlgebraicEqual(left, right) => Node::AlgebraicEqual {
                arguments: [self.algebraic(left), self.algebraic(right)],
            },
            Old::BoolEqual(left, right) => Node::BoolEqual {
                arguments: [self.condition(left), self.condition(right)],
            },
            Old::BoolIf {
                condition,
                then_condition,
                else_condition,
            } => Node::BoolIf {
                arguments: [
                    self.condition(condition),
                    self.condition(then_condition),
                    self.condition(else_condition),
                ],
            },
            Old::BoolApplication(application) => return self.boolean_call(application),
        };
        KernelTerm::intern(KernelType::Bool, node)
    }
}

impl KernelTermExport {
    pub(crate) fn condition(term: &KernelTerm) -> Result<OldConditionTerm, &'static str> {
        use KernelTermNode as Node;
        use OldConditionTerm as Old;
        if term.ty() != &KernelType::Bool {
            return Err("expected Bool kernel term");
        }
        crate::instrumentation::record_deterministic_work(1);
        Ok(match term.node() {
            Node::BoolOverflow {
                format,
                operation,
                arguments,
            } => Old::Overflows {
                format: *format,
                op: *operation,
                left: Box::new(Self::machine(&arguments[0])?),
                right: Box::new(Self::machine(&arguments[1])?),
            },
            Node::PointerEqual(pair) => {
                let [a, b] = pair.arguments();
                Old::PointerEqual(Box::new(a.export()?), Box::new(b.export()?))
            }
            Node::AddressEqual {
                arguments: [a, b], ..
            } => Old::AddressEqual(Box::new(a.export()?), Box::new(b.export()?)),
            Node::AddressOffsetEqual { arguments: [a, b] } => Old::AddressOffsetEqual(
                Box::new(AddressOffset::try_from_shared(a.clone())?),
                Box::new(AddressOffset::try_from_shared(b.clone())?),
            ),
            Node::BoolLiteral(value) => Old::Constant(*value),
            Node::Variable(variable) => Old::Variable(*variable),
            Node::BoolCompare {
                format,
                relation,
                arguments,
            } => Old::Compare {
                format: *format,
                relation: *relation,
                left: Box::new(Self::condition_machine_operand(&arguments[0])?),
                right: Box::new(Self::condition_machine_operand(&arguments[1])?),
            },
            Node::IntegerCompare {
                operator,
                arguments,
            } => {
                use IntegerComparisonOperator as Op;
                let mut export = Self::default();
                let left = export.integer(&arguments[0])?;
                let right = export.integer(&arguments[1])?;
                match operator {
                    Op::LessThan => Old::IntegerLessThan(left, right),
                    Op::LessEqual => Old::IntegerLessEqual(left, right),
                    Op::GreaterThan => Old::IntegerGreaterThan(left, right),
                    Op::GreaterEqual => Old::IntegerGreaterEqual(left, right),
                    Op::Equal => Old::IntegerEqual(left, right),
                    Op::NotEqual => Old::IntegerNotEqual(left, right),
                }
            }
            Node::FloatCompare { .. } | Node::FloatClassify { .. } => Self::float_condition(term)?,
            Node::AlgebraicEqual { arguments } => Old::AlgebraicEqual(
                Box::new(Self::default().algebraic(&arguments[0])?),
                Box::new(Self::default().algebraic(&arguments[1])?),
            ),
            Node::BoolEqual { arguments } => Old::BoolEqual(
                Box::new(Self::condition(&arguments[0])?),
                Box::new(Self::condition(&arguments[1])?),
            ),
            Node::BoolIf { arguments } => Old::BoolIf {
                condition: Box::new(Self::condition(&arguments[0])?),
                then_condition: Box::new(Self::condition(&arguments[1])?),
                else_condition: Box::new(Self::condition(&arguments[2])?),
            },
            Node::Call { name, arguments } => Old::BoolApplication(SharedPureApplication::intern(
                name.clone(),
                arguments
                    .iter()
                    .map(|arg| Self::default().argument(arg))
                    .collect::<Result<Vec<_>, _>>()?,
            )),
            _ => return Err("expected Bool kernel node"),
        })
    }

    pub(in crate::kernel) fn condition_machine_operand(
        term: &KernelTerm,
    ) -> Result<OldMachineTerm, &'static str> {
        // Fixed-size atoms have their exact written form already. Only a
        // compound guard operand needs the remaining Boolean export boundary.
        match term.node() {
            KernelTermNode::Variable(variable) => Ok(OldMachineTerm::Variable(*variable)),
            KernelTermNode::MachineLiteral(value) => Ok(value.old_term()),
            KernelTermNode::MemoryLoad { .. } => {
                Ok(term.machine_read_leaf().expect("read descriptor").clone())
            }
            _ => Self::machine(term),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn boolean_identity_matches_native_formats_and_composites() {
        let _session = crate::kernel::VerificationSession::enter();
        let mut cases = vec![
            OldConditionTerm::Constant(false),
            OldConditionTerm::Variable(Variable(964_095)),
        ];
        for format in crate::kernel::machine_integer::FORMATS {
            for relation in [
                CompareRelation::Equal,
                CompareRelation::LessThan,
                CompareRelation::GreaterEqual,
            ] {
                cases.push(OldConditionTerm::Compare {
                    format,
                    relation,
                    left: Box::new(OldMachineTerm::Variable(Variable(964_096))),
                    right: Box::new(OldMachineTerm::machine_constant(
                        MachineIntegerConstant::from_signed(format.format(), 1).unwrap(),
                    )),
                });
            }
        }
        for source in cases.clone() {
            cases.push(OldConditionTerm::BoolEqual(
                Box::new(source.clone()),
                Box::new(source),
            ));
        }
        let common: Vec<_> = cases
            .iter()
            .map(|source| KernelTermImport::default().condition(source))
            .collect();
        for (i, a) in cases.iter().enumerate() {
            for (j, b) in cases.iter().enumerate() {
                let expected = a == b;
                let shared_a = BooleanOperandView::Shared(&common[i]);
                let shared_b = BooleanOperandView::Shared(&common[j]);
                assert_eq!(
                    shared_a.syntax_equal(shared_b),
                    expected,
                    "{a:?} versus {b:?}"
                );
                assert_eq!(
                    shared_a.syntax_equal(BooleanOperandView::Native(b)),
                    expected
                );
                assert_eq!(
                    BooleanOperandView::Native(a).syntax_equal(shared_b),
                    expected
                );
            }
        }
    }

    #[test]
    fn common_boolean_substitution_keeps_unfolded_connectives_and_scoped_folds() {
        use crate::kernel::reasoning::substitute_bitvector_variable_in_common_condition;
        let _session = crate::kernel::VerificationSession::enter();
        let free = Variable(971_001);
        let accumulator = Variable(971_002);
        let fold = OldMachineTerm::RangeFold {
            start: Box::new(OldMachineTerm::constant(0)),
            end: Box::new(OldMachineTerm::Variable(free)),
            initial: Box::new(OldMachineTerm::Variable(accumulator)),
            accumulator,
            item: Variable(971_003),
            body: Box::new(OldMachineTerm::add(
                OldMachineTerm::Variable(free),
                OldMachineTerm::Variable(accumulator),
            )),
        };
        let source = OldConditionTerm::BoolIf {
            condition: Box::new(OldConditionTerm::Variable(free)),
            then_condition: Box::new(OldConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::LessThan,
                left: Box::new(fold.clone()),
                right: Box::new(OldMachineTerm::Variable(Variable(971_004))),
            }),
            else_condition: Box::new(OldConditionTerm::Constant(false)),
        };
        let root = KernelTermImport::default().condition(&source);
        let replacement = OldMachineTerm::Variable(accumulator);
        let expected =
            crate::kernel::reasoning::substitute_bitvector_variable(&fold, free, &replacement);
        let actual =
            substitute_bitvector_variable_in_common_condition(&root, free, &replacement).unwrap();
        let [_, then_branch, _] = BooleanOperandView::Shared(&actual).conditional().unwrap();
        let (_, _, operands) = then_branch.comparison().unwrap();
        let MachineOperandView::Shared(left) = operands[0] else {
            panic!("common comparison child")
        };
        let actual_fold = KernelTermExport::machine(left).unwrap();
        assert_eq!(
            crate::kernel::proof::fact_keys::bitvector_folds_alpha_equivalent(
                &actual_fold,
                &expected
            ),
            Some(true)
        );
        assert!(matches!(actual.node(), KernelTermNode::BoolIf { .. }));
    }

    #[test]
    fn common_boolean_pointer_substitution_keeps_native_folding_policy() {
        let _session = crate::kernel::VerificationSession::enter();
        let from = Variable(971_020);
        let pointer = Address::null();
        let atom = OldConditionTerm::Compare {
            format: MachineIntegerType::Int64,
            relation: CompareRelation::Equal,
            left: Box::new(OldMachineTerm::IntegerAddress(
                Box::new(Address::symbolic(from)),
                crate::kernel::AddressObjectClass::NONE,
            )),
            right: Box::new(OldMachineTerm::uint64_constant(0)),
        };
        let sources = [
            OldConditionTerm::BoolEqual(Box::new(atom.clone()), Box::new(atom.clone())),
            OldConditionTerm::BoolIf {
                condition: Box::new(atom),
                then_condition: Box::new(OldConditionTerm::Constant(true)),
                else_condition: Box::new(OldConditionTerm::Constant(false)),
            },
            OldConditionTerm::BoolIf {
                condition: Box::new(OldConditionTerm::Constant(true)),
                then_condition: Box::new(OldConditionTerm::Variable(Variable(971_021))),
                else_condition: Box::new(OldConditionTerm::Constant(false)),
            },
        ];
        for source in sources {
            let expected = crate::kernel::proof::term_rewrite::TermRewrite::for_pointer_variable(
                from, &pointer,
            )
            .condition(&source);
            let root = KernelTermImport::default().condition(&source);
            let actual = crate::kernel::reasoning::substitute_pointer_variable_in_common_condition(
                &root, from, &pointer,
            )
            .unwrap();
            let actual = KernelTermExport::condition(&actual).unwrap();
            assert_eq!(format!("{actual:?}"), format!("{expected:?}"));
        }
    }

    #[test]
    fn common_boolean_pointer_substitution_preserves_read_state() {
        let from = Variable(971_010);
        let memory = crate::kernel::intern_memory(SymbolicMemory::new());
        let source = OldConditionTerm::BoolEqual(
            Box::new(OldConditionTerm::boolean_cell_read(
                crate::kernel::ProgramPoint::at(&memory.clone()),
                Address::symbolic(from),
            )),
            Box::new(OldConditionTerm::Constant(true)),
        );
        let root = KernelTermImport::default().condition(&source);
        let pointer = Address::symbolic(Variable(971_011));
        let actual = crate::kernel::reasoning::substitute_pointer_variable_in_common_condition(
            &root, from, &pointer,
        )
        .unwrap();
        let restored = KernelTermExport::condition(&actual).unwrap();
        assert_eq!(
            restored,
            OldConditionTerm::BoolEqual(
                Box::new(OldConditionTerm::boolean_cell_read(
                    crate::kernel::ProgramPoint::at(&memory),
                    pointer
                )),
                Box::new(OldConditionTerm::Constant(true)),
            )
        );
    }

    #[test]
    fn boolean_views_keep_written_comparison_and_shared_children() {
        let source = OldConditionTerm::BoolIf {
            condition: Box::new(OldConditionTerm::Compare {
                format: MachineIntegerType::UInt32,
                relation: CompareRelation::Equal,
                left: Box::new(OldMachineTerm::Variable(Variable(964_090))),
                right: Box::new(OldMachineTerm::constant(1)),
            }),
            then_condition: Box::new(OldConditionTerm::Constant(true)),
            else_condition: Box::new(OldConditionTerm::BoolEqual(
                Box::new(OldConditionTerm::Constant(false)),
                Box::new(OldConditionTerm::Constant(true)),
            )),
        };
        let common = KernelTermImport::default().condition(&source);
        for view in [
            BooleanOperandView::Native(&source),
            BooleanOperandView::Shared(&common),
        ] {
            let [guard, yes, no] = view.conditional().unwrap();
            let (format, relation, operands) = guard.comparison().unwrap();
            assert_eq!(format, MachineIntegerType::UInt32);
            assert_eq!(relation, CompareRelation::Equal);
            assert_eq!(operands[0].variable(), Some(&Variable(964_090)));
            assert_eq!(yes.constant(), Some(true));
            let [left, right] = no.equality().unwrap();
            assert_eq!(left.constant(), Some(false));
            assert_eq!(right.constant(), Some(true));
            assert_eq!(view.native().as_ref(), &source);
        }
        let [guard, _, _] = BooleanOperandView::Shared(&common).conditional().unwrap();
        assert!(matches!(
            guard.comparison().unwrap().2[0],
            MachineOperandView::Shared(_)
        ));
    }

    #[test]
    fn integer_comparisons_preserve_all_operators_and_order_after_source_drop() {
        use IntegerComparisonOperator as Op;
        type Constructor = fn(SharedIntegerTerm, SharedIntegerTerm) -> OldConditionTerm;
        let constructors: [(Op, Constructor); 6] = [
            (Op::LessThan, OldConditionTerm::IntegerLessThan),
            (Op::LessEqual, OldConditionTerm::IntegerLessEqual),
            (Op::GreaterThan, OldConditionTerm::IntegerGreaterThan),
            (Op::GreaterEqual, OldConditionTerm::IntegerGreaterEqual),
            (Op::Equal, OldConditionTerm::IntegerEqual),
            (Op::NotEqual, OldConditionTerm::IntegerNotEqual),
        ];
        let mut distinct = std::collections::HashSet::new();
        for (operator, constructor) in constructors {
            let left: SharedIntegerTerm = IntegerTerm::Add(
                IntegerTerm::Variable(Variable(964_001)).into(),
                IntegerTerm::constant_i64(1).into(),
            )
            .into();
            let right: SharedIntegerTerm = IntegerTerm::constant_i64(0).into();
            let source = constructor(left, right);
            let term = KernelTermImport::default().condition(&source);
            assert_eq!(term.ty(), &KernelType::Bool);
            assert!(
                matches!(term.node(), KernelTermNode::IntegerCompare { operator: actual, .. } if *actual == operator)
            );
            assert_eq!(term.children().len(), 2);
            assert!(
                term.children()
                    .iter()
                    .all(|child| child.ty() == &KernelType::Integer)
            );
            assert!(matches!(
                term.children()[0].node(),
                KernelTermNode::IntegerOperation { .. }
            ));
            assert!(matches!(
                term.children()[1].node(),
                KernelTermNode::IntegerLiteral(_)
            ));
            assert!(distinct.insert(term.clone()));
            let stored = StoredConditionTerm::from(source.clone());
            assert_eq!(stored.root(), Some(&term));
            assert_eq!(stored.old_form(), &source);
            drop(source);
            drop(stored);
            let restored = KernelTermExport::condition(&term).unwrap();
            // Reconstructed old objects may have new allocation IDs; the
            // common operator and ordered operands must retain their identity.
            assert_eq!(KernelTermImport::default().condition(&restored), term);
        }
    }

    #[test]
    fn boolean_bridge_preserves_structure_and_comparison_format() {
        let comparison = |format| OldConditionTerm::Compare {
            format,
            relation: CompareRelation::Equal,
            left: Box::new(OldMachineTerm::Variable(Variable(961_001))),
            right: Box::new(OldMachineTerm::constant(0)),
        };
        let signed = comparison(MachineIntegerType::Int32);
        let unsigned = comparison(MachineIntegerType::UInt32);
        // Fact equality deliberately identifies these. Term identity must not.
        assert_eq!(signed, unsigned);
        assert_ne!(
            KernelTermImport::default().condition(&signed),
            KernelTermImport::default().condition(&unsigned)
        );
        for condition in [
            signed,
            unsigned,
            OldConditionTerm::Constant(false),
            OldConditionTerm::Variable(Variable(961_002)),
            OldConditionTerm::BoolEqual(
                Box::new(OldConditionTerm::Constant(true)),
                Box::new(OldConditionTerm::Constant(true)),
            ),
            OldConditionTerm::BoolIf {
                condition: Box::new(OldConditionTerm::Constant(false)),
                then_condition: Box::new(OldConditionTerm::Constant(true)),
                else_condition: Box::new(OldConditionTerm::Constant(false)),
            },
            OldConditionTerm::BoolApplication(SharedPureApplication::intern(
                "predicate".into(),
                vec![PureFunctionArgument::Value(ProgramValue::Int32(
                    OldMachineTerm::Variable(Variable(961_003)),
                ))],
            )),
            OldConditionTerm::IntegerEqual(
                IntegerTerm::constant_i64(1).into(),
                IntegerTerm::constant_i64(2).into(),
            ),
        ] {
            for destination in [
                MachineIntegerType::Int8,
                MachineIntegerType::Int32,
                MachineIntegerType::UInt64,
                MachineIntegerType::UInt128,
            ] {
                let source = PureFunctionArgument::Value(super::super::machine::wrap_exact(
                    destination,
                    OldMachineTerm::BoolCast {
                        to: destination,
                        value: Box::new(condition.clone()),
                    },
                ));
                let term = KernelTermImport::default().argument(&source);
                assert!(matches!(term.node(), KernelTermNode::BoolCast { .. }));
                assert_eq!(term.children()[0].ty(), &KernelType::Bool);
                let restored = KernelTermExport::default().argument(&term).unwrap();
                // Debug retains the comparison format that equality omits.
                assert_eq!(format!("{restored:?}"), format!("{source:?}"));
            }
        }
    }
}
