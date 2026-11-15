//! Congruence signatures, not function evaluation or predicate search.
//! Curried application nodes have shallow keys and indexed parent uses. A late
//! operand merge therefore updates precisely the applications depending on it.
use super::*;
use crate::kernel::MachineBinaryOp;
use crate::kernel::MachineIntegerType;
use crate::kernel::machine_integer::representation;
use crate::kernel::{
    BitvectorUnaryOp as U, CarrierWidth as W, ConditionTerm as C, MachineTerm as T, ProgramType,
    ProgramValue, PureFunctionArgument as A, SharedPureApplication,
};
use crate::kernel::{CompareRelation, OverflowOperation};
use crate::kernel::{MachineCastSpelling, cast_op};
use crate::kernel::{binary_term, unary_term};
use crate::kernel::{bits32_constant, int64_constant, uint64_constant};

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(super) enum ArgumentTag {
    Value(ProgramType),
    Array((u32, u32), ProgramType),
    Algebraic,
    DesignationRead((u32, u32)),
    PointerExtentRead((u32, u32)),
    PointerRootExtent,
    PointerSubobjectExtent,
    PointerCallDesignation,
    PointerCallExtent,
    Integer,
}

/// The head an interned call gets: a pointer function's value, its
/// identity, or a `-> Bool` function's application.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(in crate::kernel::equality_graph) enum CallHead {
    Pointer,
    PointerIdentity,
    Bool,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(in crate::kernel::equality_graph) enum ConditionKind {
    Int32Eq,
    Int32Lt,
    Int32Le,
    Int32Gt,
    Int32Ge,
    Int32AddOverflow,
    UInt64Eq,
    Int64Lt,
    Int64Le,
    Int64Gt,
    Int64Ge,
    UInt64Lt,
    UInt64Le,
    UInt64Gt,
    UInt64Ge,
    PointerEq,
    PointerValueEq,
    OffsetEq,
    AlgebraicEq,
    IntegerEq,
    IntegerNe,
    IntegerLt,
    IntegerLe,
    IntegerGt,
    IntegerGe,
    UInt32Lt,
    UInt32Le,
    UInt32Gt,
    UInt32Ge,
    /// The logical equality of two `Bool` values (rule L-Eq).
    BoolEq,
    /// A fact about a `Bool` value that is not a comparison: an
    /// application, a conditional or a read. Its truth is the annotation of
    /// the value's class, which can also arrive through an L-Eq merge.
    BoolValue,
}

/// Shared classification for registration and the opaque-atom lookup fast path.
/// An expression with indexed operands must never be queried as an opaque atom.
pub(in crate::kernel::equality_graph) fn has_machine_operands(term: &T) -> bool {
    term.as_binary().is_some_and(|(op, _, _)| !op.is_float())
        || term
            .as_unary()
            .is_some_and(|(op, _)| !matches!(op, U::Float32Negate | U::Float64Negate))
        || matches!(
            term,
            T::ClickFunctionApplication { .. } | T::IntegerToMachine { .. } | T::MemoryLoad(..)
        )
        || matches!(term, T::Variable(variable) if crate::kernel::is_load_variable(variable))
}

/// A local wrapping identity used only by the comparison graph. Literal
/// matching examines two operation roots and leaves their source terms intact.
fn add_sub_cancel_operand(term: &T) -> Option<&T> {
    let T::Binary {
        format,
        op,
        left,
        right,
    } = term
    else {
        return None;
    };
    if !matches!(format.format().bits(), 32 | 64) {
        return None;
    }
    let T::Binary {
        format: inner_format,
        op: inner_op,
        left: base,
        right: added,
    } = left.as_ref()
    else {
        return None;
    };
    (format == inner_format
        && matches!(
            (op, inner_op),
            (MachineBinaryOp::Add, MachineBinaryOp::Subtract)
                | (MachineBinaryOp::Subtract, MachineBinaryOp::Add)
        )
        && matches!(
            added.as_ref(),
            bits32_constant!(_) | int64_constant!(_) | uint64_constant!(_)
        )
        && added == right)
        .then_some(base.as_ref())
}

impl TermClasses {
    /// Walk mixed-width machine applications once. In particular, a nested
    /// pure call does not recursively canonicalize every enclosing subtree.
    pub(super) fn intern_machine(&mut self, term: &T, wide: bool) -> u64 {
        self.intern_typed_machine(term, if wide { W::Bits64 } else { W::Bits32 })
    }

    pub(super) fn intern_typed_machine(&mut self, term: &T, width: W) -> u64 {
        self.intern_expression(Some((term, width)), None, None, None, None)
    }

    /// Admits `left == right` between two native values of `width`.
    #[cfg(test)]
    pub(in crate::kernel::equality_graph) fn add_typed_equality(
        &mut self,
        width: W,
        left: &T,
        right: &T,
    ) -> bool {
        let left = self.intern_typed_machine(left, width);
        let right = self.intern_typed_machine(right, width);
        left != right && self.close(vec![(left, right)])
    }

    /// Whether two native values of `width` are one class.
    #[cfg(test)]
    pub(in crate::kernel::equality_graph) fn are_typed_equal(
        &mut self,
        width: W,
        left: &T,
        right: &T,
    ) -> bool {
        let left = self.intern_typed_machine(left, width);
        let right = self.intern_typed_machine(right, width);
        self.root(left) == self.root(right)
    }

    pub(super) fn intern_algebraic(&mut self, term: &crate::kernel::AlgebraicTerm) -> u64 {
        self.intern_expression(None, Some(term), None, None, None)
    }

    pub(super) fn intern_integer(&mut self, term: &crate::kernel::IntegerTerm) -> u64 {
        self.intern_expression(None, None, Some(term), None, None)
    }

    pub(in crate::kernel::equality_graph) fn add_integer_equality(
        &mut self,
        left: &crate::kernel::IntegerTerm,
        right: &crate::kernel::IntegerTerm,
    ) -> bool {
        let a = self.intern_integer(left);
        let b = self.intern_integer(right);
        self.register_pending_loads();
        self.close(vec![(a, b)])
    }

    /// Read an admitted observation through its carrier without exporting it.
    /// The caller retains the original Integer source for restriction/replay.
    pub(in crate::kernel::equality_graph) fn admit_observation_comparison(
        &mut self,
        view: &crate::kernel::machine_integer::comparison::NativeComparisonView<'_>,
    ) -> bool {
        let mut next = Some(view.clone());
        let mut changed = false;
        while let Some(view) = next {
            next = view.cancelled_equality();
            changed = self.admit_observation_comparison_leaf(&view) || changed;
        }
        changed
    }

    fn admit_observation_comparison_leaf(
        &mut self,
        view: &crate::kernel::machine_integer::comparison::NativeComparisonView<'_>,
    ) -> bool {
        use crate::kernel::machine_integer::Relation;
        if matches!(view.relation, Relation::Less | Relation::LessEqual)
            && let Some(widened) = view.widened()
        {
            return self.admit_observation_comparison(&widened);
        }
        let operands = view
            .operands
            .each_ref()
            .map(|operand| operand.operand_view());
        let (relation, truth) = match view.relation {
            Relation::Equal => (CompareRelation::Equal, true),
            Relation::NotEqual => (CompareRelation::Equal, false),
            Relation::Less => (CompareRelation::LessThan, true),
            Relation::LessEqual => (CompareRelation::LessEqual, true),
        };
        let format =
            if relation == CompareRelation::Equal && view.format == MachineIntegerType::UInt64 {
                MachineIntegerType::Int64
            } else {
                view.format
            };
        if relation == CompareRelation::Equal && truth {
            let width = Self::machine_comparison_width(format, relation, operands);
            let [left, right] = operands.map(|operand| match operand {
                crate::kernel::MachineOperandView::Shared(term) => {
                    self.intern_shared_machine(term, width)
                }
                crate::kernel::MachineOperandView::Legacy(term) => {
                    self.intern_typed_machine(term, width)
                }
            });
            self.register_pending_loads();
            self.close(vec![(left, right)])
        } else {
            self.admit_machine_comparison(format, relation, operands, truth)
        }
    }

    /// Equality of Integers implies equality of their 32-bit residues.
    /// Visit only the rule's bounded Integer skeleton; machine observations
    /// register their existing shared graph, never a boxed expansion.
    pub(in crate::kernel::equality_graph) fn add_modular_integer_equality(
        &mut self,
        left: &crate::kernel::IntegerTerm,
        right: &crate::kernel::IntegerTerm,
    ) -> bool {
        let (mut remaining, mut observed) = (64, false);
        let mut pending = Vec::new();
        let Some(left) =
            self.modular_integer_word32(left, &mut remaining, &mut observed, &mut pending)
        else {
            return false;
        };
        let Some(right) =
            self.modular_integer_word32(right, &mut remaining, &mut observed, &mut pending)
        else {
            return false;
        };
        if !observed {
            return false;
        }
        self.register_pending_loads();
        pending.push((left, right));
        self.close(pending)
    }

    fn modular_integer_word32(
        &mut self,
        term: &crate::kernel::IntegerTerm,
        remaining: &mut usize,
        observed: &mut bool,
        pending: &mut Vec<(u64, u64)>,
    ) -> Option<u64> {
        use crate::kernel::machine_integer::Operation;
        use crate::kernel::{IntegerTerm as I, MachineOperandView as V};
        use num_traits::ToPrimitive;
        crate::instrumentation::record_deterministic_work(1);
        *remaining = remaining.checked_sub(1)?;
        Some(match term {
            I::Machine(machine) if machine.ty().format().bits() == 32 => {
                *observed = true;
                match machine.operand_view() {
                    V::Shared(term) => self.intern_shared_machine(term, W::Bits32),
                    V::Legacy(term) => self.intern_int32(term),
                }
            }
            I::Constant(value) => {
                let modulus = num_bigint::BigInt::from(1u64 << 32);
                let residue = ((value % &modulus) + &modulus) % &modulus;
                self.intern_int32(&T::constant(residue.to_u32()?))
            }
            I::Negate(inner) => {
                let inner = self.modular_integer_word32(inner, remaining, observed, pending)?;
                let zero = self.intern_int32(&T::constant(0));
                self.modular_word_operation(MachineBinaryOp::Subtract, zero, inner, pending)
            }
            _ => {
                let (operation, left, right) = Operation::of_exact(term)?;
                let left = self.modular_integer_word32(left, remaining, observed, pending)?;
                let right = self.modular_integer_word32(right, remaining, observed, pending)?;
                let op = match operation {
                    Operation::Add => MachineBinaryOp::Add,
                    Operation::Subtract => MachineBinaryOp::Subtract,
                    Operation::Multiply => MachineBinaryOp::Multiply,
                };
                self.modular_word_operation(op, left, right, pending)
            }
        })
    }

    /// The old residue map used folded word constructors. Preserve those
    /// identities in checking, using indexed graph nodes rather than exporting
    /// operands. Cancellation follows one smaller operation at a time and memoizes
    /// every visited pair, including shared prefixes across admissions.
    fn modular_word_operation(
        &mut self,
        op: MachineBinaryOp,
        mut left: u64,
        mut right: u64,
        pending: &mut Vec<(u64, u64)>,
    ) -> u64 {
        use crate::kernel::BitvectorBinaryOp as B;
        use MachineBinaryOp::{Add, Multiply, Subtract};
        let mut visited = Vec::new();
        let result = loop {
            crate::instrumentation::record_deterministic_work(1);
            let key = (op, left, right);
            // Keep the structural operation connected to its folded result.
            // These are checking equalities, never replacement stored terms.
            let raw = self.intern_node(if op == Add {
                Node::Int32Add(left, right)
            } else {
                Node::Int32Binary(
                    Int32Binary::Other(B::Machine(MachineIntegerType::Int32, op)),
                    left,
                    right,
                )
            });
            if let Some(&known) = self.modular_word_operations.get(&key) {
                pending.push((raw, known));
                break known;
            }
            visited.push((key, raw));
            let constant = |id| {
                self.int32_constants
                    .get(&self.root(id))
                    .copied()
                    .map(|v| v as u32)
            };
            let (a, b) = (constant(left), constant(right));
            if let (Some(a), Some(b)) = (a, b) {
                let bits = match op {
                    Add => a.wrapping_add(b),
                    Subtract => a.wrapping_sub(b),
                    Multiply => a.wrapping_mul(b),
                    _ => unreachable!(),
                };
                break self.intern_int32(&T::constant(bits));
            }
            let addition = |id| match self.applications.get(&id) {
                Some(Application::Int32Add(a, b)) => Some((*a, *b)),
                _ => None,
            };
            let subtraction = |id| match self.applications.get(&id) {
                Some(Application::Int32Binary(
                    Int32Binary::Other(B::Machine(MachineIntegerType::Int32, Subtract)),
                    a,
                    b,
                )) => Some((*a, *b)),
                _ => None,
            };
            match op {
                Add => {
                    if b == Some(0) {
                        break left;
                    }
                    if a == Some(0) {
                        break right;
                    }
                    if let Some((base, removed)) = subtraction(right) {
                        if removed == left {
                            break base;
                        }
                    }
                    if let Some((base, removed)) = subtraction(left) {
                        if removed == right {
                            break base;
                        }
                    }
                    let mut cancelled = None;
                    for (negation, sum) in [(left, right), (right, left)] {
                        if let (Some((zero, removed)), Some((a, b))) =
                            (subtraction(negation), addition(sum))
                        {
                            if constant(zero) == Some(0) {
                                if removed == a {
                                    cancelled = Some(b);
                                }
                                if removed == b {
                                    cancelled = Some(a);
                                }
                            }
                        }
                    }
                    if let Some(id) = cancelled {
                        break id;
                    }
                }
                Subtract => {
                    if b == Some(0) {
                        break left;
                    }
                    if left == right {
                        break self.intern_int32(&T::constant(0));
                    }
                    let (l, r) = (addition(left), addition(right));
                    if let (Some((a, b)), Some((c, d))) = (l, r) {
                        let next = if a == c {
                            Some((b, d))
                        } else if a == d {
                            Some((b, c))
                        } else if b == c {
                            Some((a, d))
                        } else if b == d {
                            Some((a, c))
                        } else {
                            None
                        };
                        if let Some((a, b)) = next {
                            left = a;
                            right = b;
                            continue;
                        }
                    }
                    if let Some((a, b)) = l {
                        if a == right {
                            break b;
                        }
                        if b == right {
                            break a;
                        }
                    }
                    if let Some((a, b)) = r {
                        let remaining = if a == left {
                            Some(b)
                        } else if b == left {
                            Some(a)
                        } else {
                            None
                        };
                        if let Some(remaining) = remaining {
                            left = self.intern_int32(&T::constant(0));
                            right = remaining;
                            continue;
                        }
                    }
                }
                Multiply => {
                    if a == Some(0) || b == Some(0) {
                        break self.intern_int32(&T::constant(0));
                    }
                    if a == Some(1) {
                        break right;
                    }
                    if b == Some(1) {
                        break left;
                    }
                }
                _ => unreachable!(),
            }
            break self.intern_node(if op == Add {
                Node::Int32Add(left, right)
            } else {
                Node::Int32Binary(
                    Int32Binary::Other(B::Machine(MachineIntegerType::Int32, op)),
                    left,
                    right,
                )
            });
        };
        for (key, raw) in visited {
            self.modular_word_operations.insert(key, result);
            pending.push((raw, result));
        }
        result
    }

    pub(in crate::kernel::equality_graph) fn are_integer_equal(
        &mut self,
        left: &crate::kernel::IntegerTerm,
        right: &crate::kernel::IntegerTerm,
    ) -> bool {
        let a = self.intern_integer(left);
        let b = self.intern_integer(right);
        self.register_pending_loads();
        self.root(a) == self.root(b)
    }

    pub(super) fn intern_pointer_call(&mut self, application: &SharedPureApplication) -> u64 {
        self.intern_expression(
            None,
            None,
            None,
            None,
            Some((application, CallHead::Pointer)),
        )
    }

    pub(super) fn intern_pointer_call_identity(
        &mut self,
        application: &SharedPureApplication,
    ) -> u64 {
        self.intern_expression(
            None,
            None,
            None,
            None,
            Some((application, CallHead::PointerIdentity)),
        )
    }

    /// The class of a `-> Bool` pure function's application: its head and
    /// argument classes, so applications to equal arguments are congruent.
    pub(super) fn intern_bool_call(&mut self, application: &SharedPureApplication) -> u64 {
        self.intern_expression(None, None, None, None, Some((application, CallHead::Bool)))
    }

    fn intern_expression(
        &mut self,
        machine: Option<(&T, W)>,
        algebraic: Option<&crate::kernel::AlgebraicTerm>,
        integer: Option<&crate::kernel::IntegerTerm>,
        value: Option<&ProgramValue>,
        pointer_call: Option<(&SharedPureApplication, CallHead)>,
    ) -> u64 {
        enum Binary {
            Int32Add,
            Int32(Int32Binary),
            UInt64(UInt64Binary),
        }
        enum Work<'a> {
            PointerCall(&'a SharedPureApplication, CallHead),
            Algebraic(&'a crate::kernel::AlgebraicTerm),
            Integer(&'a crate::kernel::IntegerTerm),
            RememberInteger(crate::kernel::SharedIntegerTerm),
            Field(&'a crate::kernel::AlgebraicValue),
            Machine(&'a T, W),
            RetainedMachine(&'a crate::kernel::SharedMachineIntegerTerm, W),
            OpaqueCount(&'a T),
            Argument(&'a A),
            Value(&'a ProgramValue),
            Wrap(ArgumentTag),
            Call(u64, usize),
            /// Exact observation followed by conversion back to its own type.
            /// Keep both written application nodes and join their word value.
            ObservationRoundTrip(crate::kernel::MachineIntegerType),
            Binary(Binary),
            Unary(Int32Unary, bool),
            /// A conversion into an 8- or 16-bit format, whose operand's
            /// class is on the value stack: the cast node, joined with its
            /// rule-K7 word.
            NarrowCast {
                source: MachineIntegerType,
                destination: MachineIntegerType,
                inverse: bool,
            },
        }
        let mut pending = if let Some(value) = value {
            vec![Work::Value(value)]
        } else if let Some((term, width)) = machine {
            vec![Work::Machine(term, width)]
        } else if let Some(term) = integer {
            vec![Work::Integer(term)]
        } else if let Some((call, identity)) = pointer_call {
            vec![Work::PointerCall(call, identity)]
        } else {
            vec![Work::Algebraic(algebraic.expect("expression"))]
        };
        // Shared Integer children form a DAG: process each selected node once,
        // including when a source uses the same large child twice.
        let mut integer_values = std::collections::BTreeMap::new();
        let mut values = Vec::new();
        while let Some(work) = pending.pop() {
            // Preserve existing scalar work accounting; new argument/call
            // nodes are charged once each, like the old wide traversal.
            if !matches!(
                &work,
                Work::Machine(_, W::Bits32) | Work::Binary(Binary::Int32Add | Binary::Int32(_))
            ) {
                crate::instrumentation::record_deterministic_work(1);
            }
            let scalar_source = match &work {
                Work::Machine(term, W::Bits32) if matches!(term, T::If { .. }) => Some(*term),
                _ => None,
            };
            let node = match work {
                Work::PointerCall(application, identity) => {
                    let symbol =
                        SharedPureApplication::intern(application.name().to_owned(), vec![]);
                    let arity = application.arguments().len();
                    let head = self.intern_node(match identity {
                        CallHead::PointerIdentity => Node::PointerFunctionValue(symbol, arity),
                        CallHead::Pointer => Node::PointerFunction(symbol, arity),
                        CallHead::Bool => Node::BoolFunction(symbol, arity),
                    });
                    pending.push(Work::Call(head, application.arguments().len()));
                    pending.extend(application.arguments().iter().rev().map(Work::Argument));
                    continue;
                }
                Work::OpaqueCount(term) => {
                    values
                        .push(self.opaque_argument(&A::Value(ProgramValue::UInt64(term.clone()))));
                    continue;
                }
                Work::RememberInteger(term) => {
                    // Register literal identities as equalities, retaining the
                    // original operation node and its source spelling.
                    use crate::kernel::IntegerTerm as I;
                    let value = *values.last().expect("Integer value");
                    let zero = |t: &crate::kernel::SharedIntegerTerm| matches!(t.as_ref(), I::Constant(n) if n == &0.into());
                    let one = |t: &crate::kernel::SharedIntegerTerm| matches!(t.as_ref(), I::Constant(n) if n == &1.into());
                    let equivalent = match term.as_ref() {
                        I::Add(a, b) if zero(b) => Some(a),
                        I::Add(a, b) if zero(a) => Some(b),
                        I::Subtract(a, b) if zero(b) => Some(a),
                        I::Multiply(a, b) if zero(a) || one(b) => Some(a),
                        I::Multiply(a, b) if zero(b) || one(a) => Some(b),
                        _ => None,
                    };
                    if let Some(other) = equivalent.and_then(|child| integer_values.get(child)) {
                        self.close(vec![(value, *other)]);
                    }
                    integer_values.insert(term, value);
                    continue;
                }
                Work::Integer(term) => {
                    use crate::kernel::IntegerTerm as I;
                    let shared = crate::kernel::SharedIntegerTerm::intern(term.clone());
                    if let Some(value) = integer_values.get(&shared) {
                        values.push(*value);
                        continue;
                    }
                    pending.push(Work::RememberInteger(shared.clone()));
                    let binary = match term {
                        I::Add(a, b) => Some((IntegerOperation::Add, a, b)),
                        I::Subtract(a, b) => Some((IntegerOperation::Subtract, a, b)),
                        I::Multiply(a, b) => Some((IntegerOperation::Multiply, a, b)),
                        I::TruncatingQuotient(a, b) => Some((IntegerOperation::Quotient, a, b)),
                        I::TruncatingRemainder(a, b) => Some((IntegerOperation::Remainder, a, b)),
                        _ => None,
                    };
                    if let Some((op, a, b)) = binary {
                        let head = self.intern_node(Node::IntegerOperation(op));
                        pending.push(Work::Call(head, 2));
                        pending.push(Work::Integer(b));
                        pending.push(Work::Integer(a));
                        continue;
                    }
                    match term {
                        I::Constant(value) => {
                            use crate::kernel::{MachineIntegerConstant, MachineIntegerType as M};
                            let literal = self.intern_node(Node::IntegerAtom(shared));
                            // Literal observations are folded by Integer constructors.
                            // Install their bounded typed spellings so a late machine
                            // equality reaches that same canonical Integer literal.
                            for ty in [
                                M::Int8,
                                M::UInt8,
                                M::Int16,
                                M::UInt16,
                                M::Int32,
                                M::UInt32,
                                M::Int64,
                                M::UInt64,
                                M::Int128,
                                M::UInt128,
                            ] {
                                let Some(bits) =
                                    MachineIntegerConstant::from_integer(ty.format(), value)
                                        .and_then(|constant| ty.constant_term(constant))
                                else {
                                    continue;
                                };
                                let operand =
                                    self.intern_typed_machine(&bits, W::of_machine_type(ty));
                                let head = self.intern_node(Node::IntegerOperation(
                                    IntegerOperation::Observe(ty),
                                ));
                                let observed = self.intern_node(Node::Apply(head, operand));
                                self.close(vec![(literal, observed)]);
                            }
                            values.push(literal);
                            continue;
                        }
                        I::Machine(value) => {
                            let head = self.intern_node(Node::IntegerOperation(
                                IntegerOperation::Observe(value.ty()),
                            ));
                            let width = W::of_machine_type(value.ty());
                            if let Some(term) = value.shared_operand() {
                                let operand = self.intern_shared_machine(term, width);
                                values.push(self.intern_node(Node::Apply(head, operand)));
                            } else {
                                pending.push(Work::Call(head, 1));
                                pending.push(Work::Machine(value.value(), width));
                            }
                            continue;
                        }
                        I::Negate(value) => {
                            let head =
                                self.intern_node(Node::IntegerOperation(IntegerOperation::Negate));
                            pending.push(Work::Call(head, 1));
                            pending.push(Work::Integer(value));
                            continue;
                        }
                        I::PureFunctionApplication(application) => {
                            let symbol = SharedPureApplication::intern(
                                application.name().to_owned(),
                                vec![],
                            );
                            let head = self.intern_node(Node::IntegerFunction(
                                symbol,
                                application.arguments().len(),
                            ));
                            pending.push(Work::Call(head, application.arguments().len()));
                            pending
                                .extend(application.arguments().iter().rev().map(Work::Argument));
                            continue;
                        }
                        I::RangeFold {
                            index,
                            initial,
                            accumulator,
                            item,
                            body,
                        } => {
                            // Keep the bound body opaque and exact. Endpoints
                            // and initial value are outside its binding scope,
                            // so ordinary congruence applies to those children.
                            let head = self.intern_node(Node::IntegerFold(
                                index.machine_item_type(),
                                *accumulator,
                                *item,
                                body.clone(),
                            ));
                            pending.push(Work::Call(head, 3));
                            pending.push(Work::Integer(initial));
                            match index {
                                crate::kernel::IntegerRangeFoldIndex::Int32 { start, end } => {
                                    pending.push(Work::RetainedMachine(
                                        end.machine_operand(),
                                        W::Bits32,
                                    ));
                                    pending.push(Work::RetainedMachine(
                                        start.machine_operand(),
                                        W::Bits32,
                                    ));
                                }
                                crate::kernel::IntegerRangeFoldIndex::UInt64 { start, end } => {
                                    pending.push(Work::RetainedMachine(
                                        end.machine_operand(),
                                        W::Bits64,
                                    ));
                                    pending.push(Work::RetainedMachine(
                                        start.machine_operand(),
                                        W::Bits64,
                                    ));
                                }
                                crate::kernel::IntegerRangeFoldIndex::Integer { start, end } => {
                                    pending.push(Work::Integer(end));
                                    pending.push(Work::Integer(start));
                                }
                            }
                            continue;
                        }
                        // Other binder-bearing terms retain their complete,
                        // shallow interned identity.
                        _ => Node::IntegerAtom(shared),
                    }
                }
                Work::Algebraic(term) => {
                    use crate::kernel::AlgebraicTermNode as N;
                    let ty = self.algebraic_type_token(&term.algebraic_type);
                    match &term.node {
                        N::Variable(variable) => Node::AlgebraicVariable(ty, *variable),
                        N::Constructor { variant, fields } => {
                            let head = self.intern_node(Node::AlgebraicConstructor(
                                ty,
                                variant.clone(),
                                fields.len(),
                            ));
                            pending.push(Work::Call(head, fields.len()));
                            pending.extend(fields.iter().rev().map(Work::Field));
                            continue;
                        }
                        N::PureFunctionApplication { name, arguments } => {
                            let head = self.intern_node(Node::AlgebraicFunction(
                                ty,
                                name.clone(),
                                arguments.len(),
                            ));
                            pending.push(Work::Call(head, arguments.len()));
                            pending.extend(arguments.iter().rev().map(Work::Argument));
                            continue;
                        }
                        N::MemoryLoad { memory, pointer } => {
                            let head = self.intern_node(Node::AlgebraicMemoryRead(
                                ty.clone(),
                                memory.read_identity(),
                            ));
                            let address = self.numeric_address(pointer);
                            let node = Node::Apply(head, address);
                            let read = self.intern_node(node.clone());
                            // A projection's selected-cell equation is producer
                            // metadata. Consult its exact key, without walking
                            // the memory history or choosing a term from facts.
                            if let Some(source) =
                                crate::kernel::prelude::canonical_load_projection_source(
                                    memory, pointer,
                                )
                            {
                                let source_head = self.intern_node(Node::AlgebraicMemoryRead(
                                    ty.clone(),
                                    source.read_identity(),
                                ));
                                let source_read =
                                    self.intern_node(Node::Apply(source_head, address));
                                self.close(vec![(read, source_read)]);
                            }
                            if let Some(origin) = crate::kernel::prelude::value_load_origin(
                                memory,
                                pointer,
                                crate::kernel::ABSTRACT_VALUE_WIDTH,
                            ) {
                                let origin_head = self.intern_node(Node::AlgebraicMemoryRead(
                                    ty,
                                    origin.read_identity(),
                                ));
                                let origin_read =
                                    self.intern_node(Node::Apply(origin_head, address));
                                self.close(vec![(read, origin_read)]);
                            }
                            node
                        }
                        // Match binds payload variables. Do not equate bodies
                        // by a signature that would forget their binding scope.
                        // A conditional is an atom by its whole identity, as a
                        // scalar conditional is.
                        N::Match { .. } | N::If { .. } => {
                            values.push(self.opaque_argument(&A::Algebraic(term.clone())));
                            continue;
                        }
                    }
                }
                Work::Field(field) => {
                    use crate::kernel::AlgebraicValue as V;
                    match field {
                        // A value of an abstract type is its algebraic term,
                        // so a field holding one is congruent with a field
                        // holding an equal one.
                        V::Program(ProgramValue::Parameter(term)) => {
                            pending.push(Work::Algebraic(term))
                        }
                        V::Program(value) => pending.push(Work::Value(value)),
                        V::Algebraic(term) => pending.push(Work::Algebraic(term)),
                        V::Integer(term) => {
                            pending.push(Work::Wrap(ArgumentTag::Integer));
                            pending.push(Work::Integer(term));
                        }
                    }
                    continue;
                }
                Work::RetainedMachine(term, width) => {
                    if let Some(root) = term.shared_operand() {
                        values.push(self.intern_shared_machine(root, width));
                    } else {
                        pending.push(Work::Machine(term.value(), width));
                    }
                    continue;
                }
                Work::Machine(term, width) => {
                    let wide = width == W::Bits64;
                    // Structural arithmetic stays intact in logical terms.
                    // Register its total word identities only for comparison.
                    if wide
                        && let T::Binary {
                            format,
                            op,
                            left,
                            right,
                        } = term
                        && matches!(
                            format,
                            MachineIntegerType::Int64 | MachineIntegerType::UInt64
                        )
                    {
                        let zero = |t: &T| matches!(t, int64_constant!(0) | uint64_constant!(0));
                        let one = |t: &T| matches!(t, int64_constant!(1) | uint64_constant!(1));
                        let identity = match op {
                            MachineBinaryOp::Add if zero(left) => Some(right.as_ref()),
                            MachineBinaryOp::Add | MachineBinaryOp::Subtract if zero(right) => {
                                Some(left.as_ref())
                            }
                            MachineBinaryOp::Multiply if zero(left) || one(right) => {
                                Some(left.as_ref())
                            }
                            MachineBinaryOp::Multiply if zero(right) || one(left) => {
                                Some(right.as_ref())
                            }
                            _ => None,
                        };
                        if let Some(base) = identity {
                            pending.push(Work::Machine(base, width));
                            continue;
                        }
                        if *op == MachineBinaryOp::Subtract && left == right {
                            let zero = if *format == MachineIntegerType::Int64 {
                                T::int64_constant(0)
                            } else {
                                T::uint64_constant(0)
                            };
                            values.push(self.intern_typed_machine(&zero, width));
                            continue;
                        }
                    }
                    if let Some(base) = add_sub_cancel_operand(term) {
                        pending.push(Work::Machine(base, width));
                        continue;
                    }

                    let binary = if wide {
                        uint64_binary(term).map(|(op, a, b)| (Binary::UInt64(op), a, b))
                    } else if width == W::Bits32 {
                        // The e-graph reads a 32-bit sign-free operator as
                        // the word operator it computes, at either format:
                        // its operands are of that format, and σ, a node of
                        // its own, relates the two (R0, R-dist).
                        match term {
                            binary_term!(Bits32, Add, a, b) => {
                                Some((Binary::Int32Add, a.as_ref(), b.as_ref()))
                            }
                            binary_term!(UInt32, Divide, a, b) => Some((
                                Binary::Int32(Int32Binary::UnsignedDivide),
                                a.as_ref(),
                                b.as_ref(),
                            )),
                            binary_term!(UInt32, Remainder, a, b) => Some((
                                Binary::Int32(Int32Binary::UnsignedRemainder),
                                a.as_ref(),
                                b.as_ref(),
                            )),
                            binary_term!(Bits32, BitwiseXor, a, b) => Some((
                                Binary::Int32(Int32Binary::BitwiseXor),
                                a.as_ref(),
                                b.as_ref(),
                            )),
                            _ => term
                                .as_binary()
                                .filter(|(op, _, _)| op.is_bitvector32())
                                .map(|(op, a, b)| {
                                    (Binary::Int32(Int32Binary::Other(word_operator(op))), a, b)
                                }),
                        }
                    } else {
                        None
                    };
                    // A conversion into a narrow format: its node, of its
                    // own width, whose 32-bit widening has its operand's
                    // masked word (rule K7').
                    if let T::Cast {
                        spelling: MachineCastSpelling::Generic,
                        value,
                        from: source,
                        to: destination,
                    } = term
                        && width == W::of_machine_type(*destination)
                        && representation::narrow_carrier_mask(*destination).is_some()
                        && source.format().bits() <= 64
                    {
                        pending.push(Work::NarrowCast {
                            source: *source,
                            destination: *destination,
                            inverse: constants::signed_byte_load_operand(term).is_some(),
                        });
                        pending.push(Work::Machine(value, W::of_machine_type(*source)));
                        continue;
                    }
                    if width == W::Bits32 {
                        // A complement reads a word; a conversion reads its
                        // operand at the source's width.
                        let unary = if let unary_term!(Bits32, BitwiseNot, value) = term {
                            Some((Int32Unary::Not, value.as_ref(), false, W::Bits32))
                        } else {
                            constants::word_cast_operand(term).map(
                                |(value, source, destination)| {
                                    (
                                        Int32Unary::Cast(source, destination),
                                        value,
                                        constants::signed_byte_load_operand(term).is_some(),
                                        W::of_machine_type(source),
                                    )
                                },
                            )
                        };
                        if let Some((op, value, inverse, operand_width)) = unary {
                            pending.push(Work::Unary(op, inverse));
                            pending.push(Work::Machine(value, operand_width));
                            continue;
                        }
                    }
                    if let Some((op, a, b)) = binary {
                        if !wide {
                            crate::instrumentation::record_deterministic_work(1);
                        }
                        pending.push(Work::Binary(op));
                        pending.push(Work::Machine(b, width));
                        pending.push(Work::Machine(a, width));
                        continue;
                    }
                    if let Some((op, a, b)) = term.as_binary()
                        && !op.is_float()
                        && width
                            == match op {
                                // A native narrow operator is a head of its
                                // own width.
                                crate::kernel::BitvectorBinaryOp::Machine(format, _)
                                    if format.format().bits() < 32 =>
                                {
                                    W::native(format)
                                }
                                op if op.is_bitvector32() => W::Bits32,
                                _ => W::Bits64,
                            }
                    {
                        let head = self.intern_node(Node::MachineBinary(op, width));
                        pending.push(Work::Call(head, 2));
                        // Wide shifts admit independently promoted counts. Without
                        // a source width, retain the complete count identity rather
                        // than guessing its carrier from the shifted value.
                        if matches!(
                            op,
                            crate::kernel::BitvectorBinaryOp::Machine(
                                MachineIntegerType::Int64
                                    | MachineIntegerType::UInt64
                                    | MachineIntegerType::Int8
                                    | MachineIntegerType::UInt8
                                    | MachineIntegerType::Int16
                                    | MachineIntegerType::UInt16,
                                MachineBinaryOp::ShiftRight
                            ) | crate::kernel::BitvectorBinaryOp::Machine(
                                MachineIntegerType::Int64 | MachineIntegerType::UInt64,
                                MachineBinaryOp::ShiftLeft
                            )
                        ) {
                            pending.push(Work::OpaqueCount(b));
                        } else if matches!(
                            op,
                            crate::kernel::BitvectorBinaryOp::Machine(
                                MachineIntegerType::Int8
                                    | MachineIntegerType::UInt8
                                    | MachineIntegerType::Int16
                                    | MachineIntegerType::UInt16,
                                MachineBinaryOp::ShiftLeft
                            )
                        ) {
                            // A native narrow shift's count is a 32-bit word,
                            // as a 32-bit shift's is (rule N).
                            pending.push(Work::Machine(b, W::Bits32));
                        } else {
                            pending.push(Work::Machine(b, width));
                        }
                        pending.push(Work::Machine(a, width));
                        continue;
                    }
                    if let Some((op, value)) = term.as_unary()
                        && !matches!(op, U::Float32Negate | U::Float64Negate)
                        && width
                            == match op {
                                U::Machine(
                                    crate::kernel::MachineIntegerType::Int32,
                                    crate::kernel::MachineUnaryOp::BitwiseNot,
                                )
                                | cast_op!(UInt32From64) => W::Bits32,
                                U::Cast {
                                    spelling: MachineCastSpelling::Generic,
                                    to: destination,
                                    ..
                                } => W::of_machine_type(destination),
                                U::Machine(format, _) if format.format().bits() < 32 => {
                                    W::native(format)
                                }
                                _ => W::Bits64,
                            }
                    {
                        let source = match op {
                            cast_op!(Int64From32)
                            | cast_op!(UInt64From32)
                            | cast_op!(Int64FromUInt32)
                            | cast_op!(UInt64FromInt32)
                            | U::Machine(
                                crate::kernel::MachineIntegerType::Int32,
                                crate::kernel::MachineUnaryOp::BitwiseNot,
                            ) => W::Bits32,
                            cast_op!(UInt32From64) | cast_op!(UInt64FromInt64) => W::Bits64,
                            U::Machine(format, _) => W::native(format),
                            U::Cast {
                                spelling: MachineCastSpelling::Generic,
                                from: source,
                                ..
                            } => W::of_machine_type(source),
                            U::Float32Negate | U::Float64Negate => unreachable!(),
                        };
                        let head = self.intern_node(Node::MachineUnary(op, width));
                        pending.push(Work::Call(head, 1));
                        pending.push(Work::Machine(value, source));
                        continue;
                    }
                    if let T::IntegerToMachine { value, destination } = term
                        && width == W::of_machine_type(*destination)
                    {
                        if let crate::kernel::IntegerTerm::Machine(source) = value.as_ref()
                            && source.ty() == *destination
                        {
                            // The observation is in this exact type's range by
                            // construction. Other widths or signednesses need
                            // their ordinary range evidence; do not erase them.
                            pending.push(Work::ObservationRoundTrip(*destination));
                            if let Some(root) = source.shared_operand() {
                                values.push(self.intern_shared_machine(root, width));
                            } else {
                                pending.push(Work::Machine(source.value(), width));
                            }
                            continue;
                        }
                        let head = self.intern_node(Node::IntegerToMachine(*destination));
                        pending.push(Work::Call(head, 1));
                        pending.push(Work::Integer(value));
                        continue;
                    }
                    // Rule C1: the cast `b as F`, a head applied to `b`'s
                    // class, linked with it and with the constants 0 and 1.
                    if let T::BoolCast { to, value } = term
                        && width == W::of_machine_type(*to)
                        && let Some(condition) = self.bool_node(value)
                    {
                        let head = self.intern_node(Node::BoolCast(*to));
                        let cast = self.intern_node(Node::Apply(head, condition));
                        let constant = |value: u32| match width {
                            W::Bits64 if to.format().is_signed() => {
                                T::int64_constant(i64::from(value))
                            }
                            W::Bits64 => T::uint64_constant(u64::from(value)),
                            W::Bits8 | W::Bits16 => T::narrow_constant(*to, u128::from(value)),
                            _ => T::constant(value),
                        };
                        if width != W::Bits128 {
                            let zero = self.intern_typed_machine(&constant(0), width);
                            let one = self.intern_typed_machine(&constant(1), width);
                            self.link_bool_cast(cast, condition, zero, one);
                        }
                        values.push(cast);
                        continue;
                    }
                    if let T::ClickFunctionApplication { name, arguments } = term {
                        let symbol = SharedPureApplication::intern(format!("click:{name}"), vec![]);
                        let head = self.intern_node(Node::Function(symbol, width, arguments.len()));
                        pending.push(Work::Call(head, arguments.len()));
                        pending.extend(arguments.iter().rev().map(Work::Argument));
                        continue;
                    }
                    // Legacy applications carry no argument sorts. Keep
                    // them opaque instead of guessing a machine width.
                    if width == W::Bits128 {
                        Node::Machine128(MachineAtom::new(
                            crate::kernel::MachineIntegerType::UInt128,
                            term.clone(),
                        ))
                    } else if matches!(width, W::Bits8 | W::Bits16) {
                        // A native narrow value, by its bits: both
                        // signednesses of one width share its classes, as
                        // the 32-bit words do, and a constant is keyed by
                        // its bits at the unsigned format.
                        let canonical = if width == W::Bits8 {
                            crate::kernel::MachineIntegerType::UInt8
                        } else {
                            crate::kernel::MachineIntegerType::UInt16
                        };
                        let atom = match term {
                            crate::kernel::native_constant!(_, bits) => {
                                T::narrow_constant(canonical, *bits)
                            }
                            _ => term.clone(),
                        };
                        Node::MachineNarrow(MachineAtom::new(canonical, atom))
                    } else if wide {
                        if let Some((memory, pointer)) = uint64_read(term) {
                            let address = self
                                .address(pointer.block.clone(), pointer.offset.clone())
                                .0;
                            let numeric = self.read_address(address);
                            let read =
                                self.intern_node(Node::UInt64Read(memory.read_identity(), numeric));
                            let retained_state = memory.read_identity();
                            let origin = super::load_origin(term, &memory);
                            let source = WideReadSource {
                                read,
                                retained_state: memory.arena_id(),
                                origin: origin.as_ref().map(|origin| origin.arena_id()),
                                address,
                            };
                            crate::instrumentation::record_deterministic_work(1);
                            if !self.registered_uint64_cell_reads.contains(&source) {
                                self.registered_uint64_cell_reads =
                                    self.registered_uint64_cell_reads.with_value(source);
                                self.pending_cell_reads.push(super::PendingCellRead {
                                    read,
                                    memory,
                                    origin,
                                    pointer,
                                    kind: super::CellRead::UInt64,
                                    only: None,
                                });
                            }
                            Node::UInt64Read(retained_state, numeric)
                        } else if let Some(pointer) = term.address_pointer() {
                            values.push(self.numeric_address(pointer));
                            continue;
                        } else {
                            Node::UInt64(MachineAtom::uint64(term.clone()))
                        }
                    } else {
                        let value = term.clone();
                        Node::Int32(MachineAtom::int32(value))
                    }
                }
                Work::Argument(argument) => {
                    match argument {
                        A::Value(value) => pending.push(Work::Value(value)),
                        A::SharedMachine(value) => {
                            let width = match value.ty().format().bits() {
                                8 => W::Bits8,
                                16 => W::Bits16,
                                32 => W::Bits32,
                                64 => W::Bits64,
                                128 => W::Bits128,
                                _ => unreachable!("machine argument width"),
                            };
                            pending.push(Work::Wrap(ArgumentTag::Value(value.ty().program_type())));
                            pending.push(Work::RetainedMachine(value, width));
                        }
                        A::Algebraic(term) => {
                            pending.push(Work::Wrap(ArgumentTag::Algebraic));
                            pending.push(Work::Algebraic(term));
                        }
                        A::Integer(term) => {
                            pending.push(Work::Wrap(ArgumentTag::Integer));
                            pending.push(Work::Integer(term));
                        }
                        A::ArrayRef {
                            memory,
                            pointer,
                            element_type,
                        } => {
                            pending.push(Work::Wrap(ArgumentTag::Array(
                                crate::kernel::intern_memory(memory.clone()).read_identity(),
                                *element_type,
                            )));
                            pending.push(Work::Value(pointer));
                        }
                    }
                    continue;
                }
                Work::Value(value) => {
                    let value = value.numeric_value();
                    let scalar = match value {
                        // A `Bool` travels as its 8-bit carrier (rule C1),
                        // and an 8- or 16-bit value is a value of its width.
                        ProgramValue::Bool(t) => Some((ProgramType::Bool, t, W::Bits8)),
                        ProgramValue::Int8(t) => Some((ProgramType::Int8, t, W::Bits8)),
                        ProgramValue::UInt8(t) => Some((ProgramType::UInt8, t, W::Bits8)),
                        ProgramValue::Int16(t) => Some((ProgramType::Int16, t, W::Bits16)),
                        ProgramValue::UInt16(t) => Some((ProgramType::UInt16, t, W::Bits16)),
                        ProgramValue::Int32(t) => Some((ProgramType::Int32, t, W::Bits32)),
                        ProgramValue::UInt32(t) => Some((ProgramType::UInt32, t, W::Bits32)),
                        ProgramValue::Int64(t) => Some((ProgramType::Int64, t, W::Bits64)),
                        ProgramValue::UInt64(t) => Some((ProgramType::UInt64, t, W::Bits64)),
                        ProgramValue::Int128(t) => Some((ProgramType::Int128, t, W::Bits128)),
                        ProgramValue::UInt128(t) => Some((ProgramType::UInt128, t, W::Bits128)),
                        _ => None,
                    };
                    if let Some((ty, term, width)) = scalar {
                        pending.push(Work::Wrap(ArgumentTag::Value(ty)));
                        pending.push(Work::Machine(term, width));
                        continue;
                    }
                    if let ProgramValue::Pointer(pointer) = value {
                        let address = self.numeric_address(pointer.pointer());
                        // Address, allocation origin and selected extent are
                        // distinct congruence operands. Only a complete value
                        // equality merges the latter two domains.
                        let root = self.designation_node(pointer.designation());
                        let extent = self.extent_node(pointer);
                        let metadata = pointer
                            .clone()
                            .with_address(crate::kernel::Pointer::null())
                            .with_designation(std::sync::Arc::new(crate::kernel::Pointer::null()))
                            .with_root_extent();
                        let head = self.opaque_argument(&A::Value(ProgramValue::Pointer(metadata)));
                        let node = self.intern_node(Node::Apply(head, root));
                        let node = self.intern_node(Node::Apply(node, extent));
                        let node = self.intern_node(Node::Apply(node, address));
                        self.retain_pointer_value(node, pointer.clone());
                        values.push(node);
                        continue;
                    } else {
                        values.push(self.opaque_argument(&A::Value(value.clone())));
                        continue;
                    }
                }
                Work::Wrap(tag) => {
                    let value = values.pop().expect("argument value");
                    let tag = self.intern_node(Node::ArgumentTag(tag));
                    Node::Apply(tag, value)
                }
                Work::ObservationRoundTrip(format) => {
                    let operand = values.pop().expect("observed machine operand");
                    let observe =
                        self.intern_node(Node::IntegerOperation(IntegerOperation::Observe(format)));
                    let observed = self.intern_node(Node::Apply(observe, operand));
                    let convert = self.intern_node(Node::IntegerToMachine(format));
                    let converted = self.intern_node(Node::Apply(convert, observed));
                    self.close(vec![(converted, operand)]);
                    values.push(converted);
                    continue;
                }
                Work::Call(mut head, count) => {
                    let constructor = self.constructor_heads.contains_key(&head);
                    for argument in values.split_off(values.len() - count) {
                        head = self.intern_node(Node::Apply(head, argument));
                    }
                    if constructor {
                        self.retain_constructor_application(head);
                    }
                    values.push(head);
                    continue;
                }
                Work::Unary(op, inverse) => {
                    let value = values.pop().expect("unary operand");
                    let node = self.intern_node(Node::Int32Unary(op, value));
                    if inverse {
                        self.register_byte_inverse(node, value);
                    }
                    values.push(node);
                    continue;
                }
                Work::NarrowCast {
                    source,
                    destination,
                    inverse,
                } => {
                    let value = values.pop().expect("cast operand");
                    let node = self.narrow_cast_node(source, destination, value, inverse);
                    values.push(node);
                    continue;
                }
                Work::Binary(op) => {
                    let b = values.pop().expect("right operand");
                    let a = values.pop().expect("left operand");
                    match op {
                        Binary::Int32Add => Node::Int32Add(a, b),
                        Binary::Int32(op) => Node::Int32Binary(op, a, b),
                        Binary::UInt64(op) => Node::UInt64Binary(op, a, b),
                    }
                }
            };
            let id = self.intern_node(node);
            if let Some(term) = scalar_source {
                self.register_scalar_witness(term, id);
            }
            values.push(id);
        }
        values.pop().expect("machine term")
    }

    /// The class of `Cast(source -> destination, v)` into an 8- or 16-bit
    /// format, given the class `value` of its operand `v`: the cast node,
    /// as every other conversion is interned (`Int32Unary::Cast` over a
    /// source of at most 32 bits, the applied `MachineUnary` over a 64-bit
    /// one), joined with the class of its word under rule K7
    /// (`representation::narrow_cast_word`): `w & m`, or `((w & m) ^ s) - s`
    /// for a signed destination, with `w` the operand's word or low word.
    ///
    /// The word is built from the operand's class, not from its term, so
    /// this adds at most five nodes and one merge whatever the operand's
    /// size, and a nested narrow cast is interned once. Its nodes are the
    /// ones the constructors' spelling of the word interns
    /// (`MachineTerm::bitwise_and`, `bitwise_xor`, `subtract`), so the
    /// written `x & 255u32` meets the cast's class.
    pub(super) fn narrow_cast_node(
        &mut self,
        source: MachineIntegerType,
        destination: MachineIntegerType,
        value: u64,
        inverse: bool,
    ) -> u64 {
        let (node, unions) = self.narrow_cast_with_word(source, destination, value, inverse);
        self.close(unions.to_vec());
        node
    }

    /// [`Self::narrow_cast_node`] with its rule-K7 union queued on `pending`
    /// instead of closed, for a caller that is closing already.
    pub(super) fn narrow_cast_parts(
        &mut self,
        source: MachineIntegerType,
        destination: MachineIntegerType,
        value: u64,
        pending: &mut PendingUnions,
    ) -> u64 {
        let (node, unions) = self.narrow_cast_with_word(source, destination, value, false);
        for union in unions {
            pending.push(union);
        }
        node
    }

    /// The narrow cast node, and the union of its 32-bit widening at its
    /// word's format with its rule-K7' word, not yet joined. The cast is a
    /// value of its own width, so the word joins its widening, never the
    /// node itself.
    fn narrow_cast_with_word(
        &mut self,
        source: MachineIntegerType,
        destination: MachineIntegerType,
        value: u64,
        inverse: bool,
    ) -> (u64, [(u64, u64); 1]) {
        use crate::kernel::BitvectorBinaryOp as B;
        crate::instrumentation::record_deterministic_work(1);
        let (mask, sign) = representation::narrow_carrier_mask(destination)
            .expect("a narrow destination has a carrier mask");
        let (node, word, word_format) = if source.format().bits() <= 32 {
            let node = self.intern_node(Node::Int32Unary(
                Int32Unary::Cast(source, destination),
                value,
            ));
            if inverse {
                self.register_byte_inverse(node, value);
            }
            // A narrow operand's word is its 32-bit widening: its `uint32`
            // widening where the graph has that one and not the `int32`
            // one, so a chain of `uint32` widenings adds no second widening
            // for the sibling relation to join through σ; its `int32`
            // widening otherwise.
            let (word, word_format) = if source.format().bits() < 32 {
                let widening = |to| Node::Int32Unary(Int32Unary::Cast(source, to), value);
                match (
                    self.nodes.get(&widening(MachineIntegerType::Int32)),
                    self.nodes
                        .get(&widening(MachineIntegerType::UInt32))
                        .copied(),
                ) {
                    (None, Some(unsigned)) => (unsigned, MachineIntegerType::UInt32),
                    _ => (
                        self.intern_node(widening(MachineIntegerType::Int32)),
                        MachineIntegerType::Int32,
                    ),
                }
            } else {
                (value, source)
            };
            (node, word, word_format)
        } else {
            let head = self.intern_node(Node::MachineUnary(
                U::Cast {
                    spelling: MachineCastSpelling::Generic,
                    from: source,
                    to: destination,
                },
                W::Bits32,
            ));
            let node = self.intern_node(Node::Apply(head, value));
            let low = self.intern_node(Node::MachineUnary(
                U::legacy_cast(MachineCastSpelling::UInt32From64),
                W::Bits32,
            ));
            (
                node,
                self.intern_node(Node::Apply(low, value)),
                MachineIntegerType::UInt32,
            )
        };
        let mask = self.intern_typed_machine(&T::constant(mask), W::Bits32);
        let mut carrier = self.intern_node(Node::Int32Binary(
            Int32Binary::Other(B::Machine(
                crate::kernel::MachineIntegerType::Int32,
                crate::kernel::MachineBinaryOp::BitwiseAnd,
            )),
            word,
            mask,
        ));
        if let Some(sign) = sign {
            // `bitwise_xor` orders a constant before the masked word.
            let sign = self.intern_typed_machine(&T::constant(sign), W::Bits32);
            let flipped =
                self.intern_node(Node::Int32Binary(Int32Binary::BitwiseXor, sign, carrier));
            carrier = self.intern_node(Node::Int32Binary(
                Int32Binary::Other(B::Machine(
                    crate::kernel::MachineIntegerType::Int32,
                    crate::kernel::MachineBinaryOp::Subtract,
                )),
                flipped,
                sign,
            ));
        }
        // The word is a value of `word_format`: the operand's own 32-bit
        // format, a narrow operand's widening's, or `uint32` for a 64-bit
        // operand's low word. The cast's widening at that format is the
        // masked word. The other widening is interned only where a term
        // names it; it is then σ of this one (the sibling relation,
        // `machine_relations`), so its word is σ of the masked word.
        let widening = self.intern_node(Node::Int32Unary(
            Int32Unary::Cast(destination, word_format),
            node,
        ));
        (node, [(widening, carrier)])
    }

    fn algebraic_type_token(&mut self, ty: &crate::kernel::AlgebraicType) -> SharedPureApplication {
        use crate::kernel::AlgebraicValueType as V;
        enum Work<'a> {
            Type(&'a V),
            Call(u64, usize),
        }
        let head = self.intern_node(Node::TypeName(
            ty.rigid,
            ty.name.clone(),
            ty.arguments.len(),
        ));
        let mut pending = vec![Work::Call(head, ty.arguments.len())];
        pending.extend(ty.arguments.iter().rev().map(Work::Type));
        let mut values = Vec::new();
        while let Some(work) = pending.pop() {
            crate::instrumentation::record_deterministic_work(1);
            let node = match work {
                Work::Type(V::Program(ty)) => Node::TypeC(*ty),
                Work::Type(V::ObjectPointer(ty, class)) => {
                    Node::TypeObjectPointer(*ty, class.clone())
                }
                Work::Type(V::Integer) => Node::TypeInteger,
                Work::Type(V::Parameter(name)) => Node::TypeName(true, name.clone(), 0),
                Work::Type(V::Algebraic { name, arguments }) => {
                    let head =
                        self.intern_node(Node::TypeName(false, name.clone(), arguments.len()));
                    pending.push(Work::Call(head, arguments.len()));
                    pending.extend(arguments.iter().rev().map(Work::Type));
                    continue;
                }
                Work::Call(mut head, count) => {
                    for argument in values.split_off(values.len() - count) {
                        head = self.intern_node(Node::Apply(head, argument));
                    }
                    values.push(head);
                    continue;
                }
            };
            values.push(self.intern_node(node));
        }
        let nominal = values.pop().expect("nominal type");
        let key = (ty.variants.as_ptr() as usize, nominal);
        if let Some((_, token)) = self.algebraic_types.get(&key) {
            return token.clone();
        }
        // Intern the full resolved root schema once per schema allocation and
        // nominal instantiation. Independently resolved equal types share a
        // token; identically named but different schemas do not.
        let token = SharedPureApplication::intern(
            "equality:algebraic-type".into(),
            vec![A::Algebraic(crate::kernel::AlgebraicTerm {
                algebraic_type: ty.clone(),
                node: crate::kernel::AlgebraicTermNode::Variable(Variable(0)),
            })],
        );
        self.algebraic_types
            .insert(key, (ty.variants.clone(), token.clone()));
        token
    }

    pub(super) fn algebraic_nodes(
        &mut self,
        a: &crate::kernel::AlgebraicTerm,
        b: &crate::kernel::AlgebraicTerm,
    ) -> Option<(u64, u64)> {
        if self.algebraic_type_token(&a.algebraic_type)
            != self.algebraic_type_token(&b.algebraic_type)
        {
            return None;
        }
        let a = self.intern_algebraic(a);
        let b = self.intern_algebraic(b);
        self.register_pending_loads();
        Some((a, b))
    }

    pub(in crate::kernel::equality_graph) fn are_algebraic_equal(
        &mut self,
        a: &crate::kernel::AlgebraicTerm,
        b: &crate::kernel::AlgebraicTerm,
    ) -> bool {
        self.algebraic_nodes(a, b)
            .is_some_and(|(a, b)| self.root(a) == self.root(b))
    }

    pub(in crate::kernel::equality_graph) fn add_algebraic_equality(
        &mut self,
        a: &crate::kernel::AlgebraicTerm,
        b: &crate::kernel::AlgebraicTerm,
    ) -> bool {
        let Some((left, right)) = self.algebraic_nodes(a, b) else {
            return false;
        };
        let changed = self.close(vec![(left, right)]);
        for (node, term) in [(left, a), (right, b)] {
            if matches!(
                term.node,
                crate::kernel::AlgebraicTermNode::Constructor { .. }
            ) {
                let root = self.root(node);
                if !self.algebraic_constructors.contains_key(&root) {
                    self.algebraic_constructors
                        .insert(root, Arc::new(term.clone()));
                }
            }
        }
        changed
    }

    pub(in crate::kernel::equality_graph) fn known_algebraic_constructor(
        &mut self,
        model: &crate::kernel::AlgebraicTerm,
    ) -> Option<crate::kernel::AlgebraicTerm> {
        let node = self.intern_algebraic(model);
        self.register_pending_loads();
        self.algebraic_constructors
            .get(&self.root(node))
            .map(|constructor| constructor.as_ref().clone())
    }

    pub(in crate::kernel::equality_graph) fn add_pointer_value_equality(
        &mut self,
        a: &crate::kernel::PointerValue,
        b: &crate::kernel::PointerValue,
    ) -> bool {
        let roots = (
            self.designation_node(a.designation()),
            self.designation_node(b.designation()),
        );
        let extents = (self.extent_node(a), self.extent_node(b));
        let a = self.intern_expression(
            None,
            None,
            None,
            Some(&ProgramValue::Pointer(a.clone())),
            None,
        );
        let b = self.intern_expression(
            None,
            None,
            None,
            Some(&ProgramValue::Pointer(b.clone())),
            None,
        );
        self.register_pending_loads();
        self.close(vec![roots, extents, (a, b)])
    }

    pub(in crate::kernel::equality_graph) fn merge_pointer_read_domains(
        &mut self,
        a: &crate::kernel::Pointer,
        b: &crate::kernel::Pointer,
    ) -> bool {
        if self.read_domains.equal(a, b) {
            return false;
        }
        let left = self.read_domains.representative(a);
        let right = self.read_domains.representative(b);
        self.read_domains.insert(a, b, |a, _| a.clone());
        let joined = self.read_domains.representative(a);
        // A source registration need not manufacture congruence applications.
        // Merge just the domain nodes that selected consumers already named;
        // later consumers select the retained domain representative directly.
        let mut pending = Vec::new();
        for nodes in [
            &mut self.read_designation_nodes,
            &mut self.read_extent_nodes,
        ] {
            let a = nodes.get(&left).copied();
            let b = nodes.get(&right).copied();
            nodes.remove(&left);
            nodes.remove(&right);
            if let Some(node) = a.or(b) {
                nodes.insert(joined.clone(), node);
            }
            if let (Some(a), Some(b)) = (a, b) {
                pending.push((a, b));
            }
        }
        self.close(pending);
        true
    }

    pub(in crate::kernel::equality_graph) fn merge_designations(
        &mut self,
        a: &crate::kernel::Pointer,
        b: &crate::kernel::Pointer,
    ) -> bool {
        let a = self.designation_node(a);
        let b = self.designation_node(b);
        self.close(vec![(a, b)])
    }

    pub(in crate::kernel::equality_graph) fn designations_equal(
        &mut self,
        a: &crate::kernel::Pointer,
        b: &crate::kernel::Pointer,
    ) -> bool {
        let a = self.designation_node(a);
        let b = self.designation_node(b);
        self.register_pending_loads();
        self.root(a) == self.root(b)
    }

    pub(in crate::kernel::equality_graph) fn pointer_values_equal(
        &mut self,
        a: &crate::kernel::PointerValue,
        b: &crate::kernel::PointerValue,
    ) -> bool {
        let a = self.intern_expression(
            None,
            None,
            None,
            Some(&ProgramValue::Pointer(a.clone())),
            None,
        );
        let b = self.intern_expression(
            None,
            None,
            None,
            Some(&ProgramValue::Pointer(b.clone())),
            None,
        );
        self.register_pending_loads();
        self.root(a) == self.root(b)
    }

    pub(super) fn retain_pointer_value(&mut self, node: u64, value: crate::kernel::PointerValue) {
        let root = self.root(node);
        let value = self
            .pointer_values
            .get(&root)
            .map_or(value.clone(), |previous| {
                crate::kernel::pointer_designations::prefer_pointer(previous, &value)
            });
        self.pointer_values.insert(root, value);
    }

    pub(in crate::kernel::equality_graph) fn pointer_value_representative(
        &mut self,
        value: &crate::kernel::PointerValue,
    ) -> crate::kernel::PointerValue {
        let node = self.intern_expression(
            None,
            None,
            None,
            Some(&ProgramValue::Pointer(value.clone())),
            None,
        );
        self.register_pending_loads();
        let representative = self
            .pointer_values
            .get(&self.root(node))
            .unwrap_or(value)
            .clone();
        if representative.extent_is_known() {
            return representative;
        }
        let extent = self.extent_node(value);
        let Some(witness) = self.extent_values.get(&self.root(extent)) else {
            return representative;
        };
        if !witness.extent_is_known() {
            return representative;
        }
        let adopted = representative
            .with_extent(witness.extent().cloned())
            .with_opaque_extent(witness.opaque_extent().cloned().map(std::sync::Arc::new));
        if witness.extent().is_none() {
            adopted.with_root_extent()
        } else {
            adopted
        }
    }

    fn extent_node(&mut self, value: &crate::kernel::PointerValue) -> u64 {
        let node = if let Some(extent) = value.extent() {
            let head = self.intern_node(Node::ArgumentTag(ArgumentTag::PointerSubobjectExtent));
            let width = self.intern_int32(&extent.width);
            let head = self.intern_node(Node::Apply(head, width));
            let start = self
                .address(extent.start.block.clone(), extent.start.offset.clone())
                .0;
            self.intern_node(Node::Apply(head, start))
        } else if value.extent_is_known() {
            self.intern_node(Node::ArgumentTag(ArgumentTag::PointerRootExtent))
        } else {
            self.opaque_extent_node(value.opaque_extent().unwrap_or(value.designation()))
        };
        let root = self.root(node);
        let witness = self
            .extent_values
            .get(&root)
            .map_or(value.clone(), |previous| {
                crate::kernel::pointer_designations::prefer_pointer(previous, value)
            });
        self.extent_values.insert(root, witness);
        node
    }

    fn opaque_extent_node(&mut self, origin: &crate::kernel::Pointer) -> u64 {
        let node = self.opaque_extent_node_without_calls(origin);
        self.retain_pointer_call_component(origin, node, ArgumentTag::PointerCallExtent);
        node
    }

    fn opaque_extent_node_without_calls(&mut self, origin: &crate::kernel::Pointer) -> u64 {
        let origin = self.read_domains.representative(origin);
        if let Some(node) = self.read_extent_nodes.get(&origin) {
            return *node;
        }
        if let Some(read) = origin.as_loaded_value() {
            let source = crate::kernel::prelude::canonical_load_projection_source(
                &read.defining_memory,
                &read.defining_address,
            )
            .unwrap_or(read.defining_memory);
            let cell = self
                .address(read.defining_address.block, read.defining_address.offset)
                .0;
            let head = self.intern_node(Node::ArgumentTag(ArgumentTag::PointerExtentRead(
                source.read_identity(),
            )));
            let node = self.intern_node(Node::Apply(head, cell));
            self.read_extent_nodes.insert(origin, node);
            return node;
        }
        self.intern_node(Node::OpaqueArgument(SharedPureApplication::intern(
            "<pointer-extent-origin>".into(),
            vec![A::Value(ProgramValue::Pointer(
                crate::kernel::PointerValue::new(origin.clone(), ProgramType::VoidPointer),
            ))],
        )))
    }

    /// Only a complete pointer-value equality can connect an opaque extent
    /// to the root-extent tag. Numeric address equality cannot do so.
    pub(in crate::kernel::equality_graph) fn opaque_extent_is_root(
        &mut self,
        origin: &crate::kernel::Pointer,
    ) -> bool {
        let extent = self.opaque_extent_node(origin);
        let root = self.intern_node(Node::ArgumentTag(ArgumentTag::PointerRootExtent));
        self.register_pending_loads();
        self.root(extent) == self.root(root)
    }

    pub(in crate::kernel::equality_graph) fn opaque_extents_equal(
        &mut self,
        a: &crate::kernel::Pointer,
        b: &crate::kernel::Pointer,
    ) -> bool {
        let a = self.opaque_extent_node(a);
        let b = self.opaque_extent_node(b);
        self.register_pending_loads();
        self.root(a) == self.root(b)
    }

    fn designation_node(&mut self, origin: &crate::kernel::Pointer) -> u64 {
        let node = self.designation_node_without_calls(origin);
        self.retain_pointer_call_component(origin, node, ArgumentTag::PointerCallDesignation);
        node
    }

    /// Complete result domains depend on complete arguments. Their parallel
    /// function head never joins raw output-address equations. Queue the one
    /// selected identity definition so nested calls stay iterative.
    fn retain_pointer_call_component(
        &mut self,
        origin: &crate::kernel::Pointer,
        component: u64,
        tag: ArgumentTag,
    ) {
        let PointerBlock::PureFunctionApplication(application) = &origin.block else {
            return;
        };
        // This internal constructor names numeric coordinates only. Equal
        // words cannot identify the designation or bounds of their casts.
        if application.integer_address_bits().is_some() {
            return;
        }
        if origin.offset != PointerOffsetTerm::Constant(0) {
            return;
        }
        let key = Node::PointerFunctionIdentity(application.clone());
        let new = !self.nodes.contains_key(&key);
        let identity = self.intern_node(key);
        if new {
            self.pending_pointer_identities
                .push((identity, application.clone()));
        }
        let head = self.intern_node(Node::ArgumentTag(tag));
        let projected = self.intern_node(Node::Apply(head, identity));
        self.close_with_affine_definition(vec![(component, projected)], true);
    }

    fn designation_node_without_calls(&mut self, origin: &crate::kernel::Pointer) -> u64 {
        // Congruence here uses the cell a complete pointer was read from.
        // Equality of the loaded pointer's numeric address never merges this
        // node with a different value origin.
        let origin = self.read_domains.representative(origin);
        if let Some(node) = self.read_designation_nodes.get(&origin) {
            return *node;
        }
        if let crate::kernel::PointerBlock::LoadedPointer(identity) = &origin.block
            && let Some((memory, cell)) = crate::kernel::eval::registered_pointer_load(*identity)
        {
            let source = crate::kernel::prelude::canonical_load_projection_source(&memory, &cell)
                .unwrap_or(memory);
            let cell = self.address(cell.block, cell.offset).0;
            let head = self.intern_node(Node::ArgumentTag(ArgumentTag::DesignationRead(
                source.read_identity(),
            )));
            let node = self.intern_node(Node::Apply(head, cell));
            self.read_designation_nodes.insert(origin, node);
            return node;
        }
        self.opaque_argument(&A::Value(ProgramValue::Pointer(
            crate::kernel::PointerValue::new(origin.clone(), ProgramType::VoidPointer),
        )))
    }

    fn opaque_argument(&mut self, argument: &A) -> u64 {
        if let A::Value(ProgramValue::UInt64(term)) = argument {
            return self.intern_node(Node::OpaqueMachineCount(MachineAtom::uint64(term.clone())));
        }
        // Map comparisons use stable IDs, not full algebraic values/states.
        self.intern_node(Node::OpaqueArgument(SharedPureApplication::intern(
            String::new(),
            vec![argument.clone()],
        )))
    }

    fn machine_comparison_kind(
        format: MachineIntegerType,
        relation: CompareRelation,
    ) -> Option<ConditionKind> {
        use CompareRelation::*;
        use ConditionKind::*;
        use MachineIntegerType::*;
        Some(match (format, relation) {
            (Int8 | UInt8 | Int16 | UInt16 | Int32 | UInt32, Equal) => Int32Eq,
            (Int32, LessThan) => Int32Lt,
            (Int32, LessEqual) => Int32Le,
            (Int32, GreaterThan) => Int32Gt,
            (Int32, GreaterEqual) => Int32Ge,
            (UInt32, LessThan) => UInt32Lt,
            (UInt32, LessEqual) => UInt32Le,
            (UInt32, GreaterThan) => UInt32Gt,
            (UInt32, GreaterEqual) => UInt32Ge,
            (Int64, Equal) => UInt64Eq,
            (Int64, LessThan) => Int64Lt,
            (Int64, LessEqual) => Int64Le,
            (Int64, GreaterThan) => Int64Gt,
            (Int64, GreaterEqual) => Int64Ge,
            (UInt64, LessThan) => UInt64Lt,
            (UInt64, LessEqual) => UInt64Le,
            (UInt64, GreaterThan) => UInt64Gt,
            (UInt64, GreaterEqual) => UInt64Ge,
            _ => return None,
        })
    }

    fn machine_comparison_width(
        format: MachineIntegerType,
        relation: CompareRelation,
        [left, right]: [crate::kernel::MachineOperandView<'_>; 2],
    ) -> W {
        if relation == CompareRelation::Equal && format.format().bits() == 32 {
            match left.root_width().or_else(|| right.root_width()) {
                Some(width @ (W::Bits8 | W::Bits16)) => width,
                _ => W::Bits32,
            }
        } else {
            W::of_machine_type(format)
        }
    }

    pub(in crate::kernel::equality_graph) fn machine_comparison_node(
        &mut self,
        format: MachineIntegerType,
        relation: CompareRelation,
        [left, right]: [crate::kernel::MachineOperandView<'_>; 2],
    ) -> Option<u64> {
        let kind = Self::machine_comparison_kind(format, relation)?;
        // Equality of a native narrow value uses its own carrier even when
        // written with the 32-bit equality constructor.
        let width = Self::machine_comparison_width(format, relation, [left, right]);
        let mut operand = |view| match view {
            crate::kernel::MachineOperandView::Shared(term) => {
                self.intern_shared_machine(term, width)
            }
            crate::kernel::MachineOperandView::Legacy(term) => {
                self.intern_typed_machine(term, width)
            }
        };
        let (left, right) = (operand(left), operand(right));
        Some(self.intern_node(Node::Condition(kind, left, right)))
    }

    pub(in crate::kernel::equality_graph) fn condition_node(
        &mut self,
        condition: &C,
    ) -> Option<u64> {
        use ConditionKind::*;
        if let C::Compare {
            format,
            relation,
            left,
            right,
        } = condition
        {
            return self.machine_comparison_node(
                *format,
                *relation,
                [
                    crate::kernel::MachineOperandView::Legacy(left),
                    crate::kernel::MachineOperandView::Legacy(right),
                ],
            );
        }
        let (kind, left, right) = match condition {
            C::IntegerEqual(a, b) => (IntegerEq, self.intern_integer(a), self.intern_integer(b)),
            C::IntegerNotEqual(a, b) => (IntegerNe, self.intern_integer(a), self.intern_integer(b)),
            C::IntegerLessThan(a, b) => (IntegerLt, self.intern_integer(a), self.intern_integer(b)),
            C::IntegerLessEqual(a, b) => {
                (IntegerLe, self.intern_integer(a), self.intern_integer(b))
            }
            C::IntegerGreaterThan(a, b) => {
                (IntegerGt, self.intern_integer(a), self.intern_integer(b))
            }
            C::IntegerGreaterEqual(a, b) => {
                (IntegerGe, self.intern_integer(a), self.intern_integer(b))
            }
            C::AlgebraicEqual(a, b) => {
                let (a, b) = self.algebraic_nodes(a, b)?;
                (AlgebraicEq, a, b)
            }
            C::Overflows {
                format: MachineIntegerType::Int32,
                op: OverflowOperation::Add,
                left: a,
                right: b,
            } => (Int32AddOverflow, self.intern_int32(a), self.intern_int32(b)),
            C::PointerValueEqual(a, b) => (
                PointerValueEq,
                self.intern_expression(
                    None,
                    None,
                    None,
                    Some(&ProgramValue::Pointer((**a).clone())),
                    None,
                ),
                self.intern_expression(
                    None,
                    None,
                    None,
                    Some(&ProgramValue::Pointer((**b).clone())),
                    None,
                ),
            ),
            C::PointerEqual(a, b) => (
                PointerEq,
                self.address(a.block.clone(), a.offset.clone()).0,
                self.address(b.block.clone(), b.offset.clone()).0,
            ),
            C::PointerOffsetEqual(a, b) => (OffsetEq, self.intern(a), self.intern(b)),
            C::BoolApplication(_) | C::BoolIf { .. } | C::BoolEqual(..) | C::BoolLoad(..) => {
                return self.bool_node(condition);
            }
            _ => return None,
        };
        let node = self.intern_node(Node::Condition(kind, left, right));
        if let C::PointerEqual(a, b) = condition
            && a.block == b.block
        {
            // These are two views of the same predicate, not a new premise.
            // Retaining both avoids reconstructing a cancelled base from an
            // arbitrary representative after later pointer aliases merge.
            let a = self.intern(&a.offset);
            let b = self.intern(&b.offset);
            let offsets = self.intern_node(Node::Condition(OffsetEq, a, b));
            self.close(vec![(node, offsets)]);
        }
        Some(node)
    }

    fn condition_kind(condition: &C) -> Option<ConditionKind> {
        if let C::Compare {
            format, relation, ..
        } = condition
        {
            return Self::machine_comparison_kind(*format, *relation);
        }
        Some(match condition {
            C::IntegerEqual(..) => ConditionKind::IntegerEq,
            C::IntegerNotEqual(..) => ConditionKind::IntegerNe,
            C::IntegerLessThan(..) => ConditionKind::IntegerLt,
            C::IntegerLessEqual(..) => ConditionKind::IntegerLe,
            C::IntegerGreaterThan(..) => ConditionKind::IntegerGt,
            C::IntegerGreaterEqual(..) => ConditionKind::IntegerGe,
            C::AlgebraicEqual(..) => ConditionKind::AlgebraicEq,
            C::Overflows {
                format: MachineIntegerType::Int32,
                op: OverflowOperation::Add,
                ..
            } => ConditionKind::Int32AddOverflow,
            C::PointerEqual(..) => ConditionKind::PointerEq,
            C::PointerValueEqual(..) => ConditionKind::PointerValueEq,
            C::PointerOffsetEqual(..) => ConditionKind::OffsetEq,
            C::BoolEqual(..) => ConditionKind::BoolEq,
            C::BoolApplication(_) | C::BoolIf { .. } | C::BoolLoad(..) => ConditionKind::BoolValue,
            _ => return None,
        })
    }

    /// The class of a `Bool` value (`design/machine-integers.md`, Stage 5).
    ///
    /// A literal is one class per value, annotated with its truth; a binder
    /// is its variable's class; an application is a call of its function's
    /// head on its argument classes, so applications to equal arguments are
    /// congruent; a conditional is a call of one head on its three classes;
    /// an equality is the condition node `BoolEq` on its operands' classes,
    /// true when they meet (rule L-Eq); a read is its state's read head
    /// applied to its address class. A comparison is its own condition node.
    /// Each node is interned once, so the work is the value's size. `None`
    /// for a condition the graph does not intern.
    pub(in crate::kernel::equality_graph) fn bool_node(&mut self, condition: &C) -> Option<u64> {
        let node = match condition {
            C::Constant(value) => {
                let node = self.intern_node(Node::BoolConstant(*value));
                self.retain_condition_truth(node, if *value { 1 } else { 2 });
                node
            }
            C::Variable(variable) => {
                let fresh = !self.nodes.contains_key(&Node::BoolVariable(*variable));
                let node = self.intern_node(Node::BoolVariable(*variable));
                if fresh && let Some(truth) = self.bool_binder_truth.get(variable).copied() {
                    self.retain_condition_truth(node, truth);
                }
                node
            }
            C::BoolApplication(application) => self.intern_bool_call(application),
            C::BoolIf {
                condition,
                then_condition,
                else_condition,
            } => {
                let mut node = self.intern_node(Node::BoolIf);
                for operand in [condition, then_condition, else_condition] {
                    let operand = self.bool_node(operand)?;
                    node = self.intern_node(Node::Apply(node, operand));
                }
                node
            }
            C::BoolEqual(left, right) => {
                let left = self.bool_node(left)?;
                let right = self.bool_node(right)?;
                self.intern_node(Node::Condition(ConditionKind::BoolEq, left, right))
            }
            C::BoolLoad(memory, pointer) => {
                let head = self.intern_node(Node::BoolRead(memory.read_identity()));
                let address = self
                    .address(pointer.block.clone(), pointer.offset.clone())
                    .0;
                self.intern_node(Node::Apply(head, address))
            }
            condition => self.condition_node(condition)?,
        };
        Some(node)
    }

    /// Admit a fact about a `Bool` value: its class's truth, and for a true
    /// equality the merge of its operands' classes (rule L-Eq). A binder's
    /// fact is admitted only once some `Bool` value has interned the binder,
    /// so a fact no `Bool` value names adds nothing. One node per subterm,
    /// one merge.
    pub(in crate::kernel::equality_graph) fn admit_bool_condition(
        &mut self,
        condition: &C,
        value: bool,
    ) -> bool {
        let truth = if value { 1 } else { 2 };
        let node = match condition {
            C::Variable(variable) => {
                let known = self.bool_binder_truth.get(variable).copied().unwrap_or(0);
                if known | truth != known {
                    self.bool_binder_truth.insert(*variable, known | truth);
                }
                match self.nodes.get(&Node::BoolVariable(*variable)) {
                    Some(node) => *node,
                    None => return false,
                }
            }
            C::BoolApplication(_) | C::BoolIf { .. } | C::BoolEqual(..) | C::BoolLoad(..) => {
                let Some(node) = self.bool_node(condition) else {
                    return false;
                };
                self.condition_kinds = self.condition_kinds.with_value((
                    Self::condition_kind(condition).expect("a `Bool` value has a kind"),
                    value,
                ));
                node
            }
            _ => return false,
        };
        self.register_pending_loads();
        if let (C::BoolEqual(..), true) = (condition, value)
            && let Some(Application::Condition(_, left, right)) =
                self.applications.get(&node).copied()
        {
            self.close(vec![(left, right)]);
        }
        self.retain_condition_truth(node, truth);
        true
    }

    /// Whether a `Bool` binder's class has the truth `value`, which an L-Eq
    /// merge can give it. A binder no `Bool` value has interned is not
    /// looked at further: its own facts are the fact context's.
    pub(in crate::kernel::equality_graph) fn knows_bool_binder(
        &self,
        variable: crate::kernel::Variable,
        value: bool,
    ) -> bool {
        let Some(node) = self.nodes.get(&Node::BoolVariable(variable)).copied() else {
            return false;
        };
        let truth = if value { 1 } else { 2 };
        self.condition_truth
            .get(&self.root(node))
            .is_some_and(|known| known & truth != 0)
    }

    /// Whether the graph holds `ConditionIs(condition, value)` for a `Bool`
    /// value: its class's truth, or for a true equality its operands' meeting.
    pub(in crate::kernel::equality_graph) fn knows_bool_condition(
        &mut self,
        condition: &C,
        value: bool,
    ) -> bool {
        let Some(node) = self.bool_node(condition) else {
            return false;
        };
        self.register_pending_loads();
        let truth = if value { 1 } else { 2 };
        if self
            .condition_truth
            .get(&self.root(node))
            .is_some_and(|known| known & truth != 0)
        {
            return true;
        }
        if let (C::BoolEqual(..), true) = (condition, value)
            && let Some(Application::Condition(_, left, right)) =
                self.applications.get(&node).copied()
        {
            return self.root(left) == self.root(right);
        }
        false
    }

    pub(in crate::kernel::equality_graph) fn may_know_condition(
        &self,
        condition: &C,
        value: bool,
    ) -> bool {
        Self::condition_kind(condition).is_some_and(|kind| {
            self.condition_kinds.contains(&(kind, value))
                // A narrow equation is false when its sides' classes hold
                // two constants (`knows_condition`).
                || (!value
                    && kind == ConditionKind::Int32Eq
                    && !self.narrow_constants.is_empty()
                    && self.narrow_equation(condition))
                || (kind == ConditionKind::OffsetEq
                    && self
                        .condition_kinds
                        .contains(&(ConditionKind::PointerEq, value)))
                || (kind == ConditionKind::PointerEq
                    && self
                        .condition_kinds
                        .contains(&(ConditionKind::OffsetEq, value)))
        })
    }

    pub(in crate::kernel::equality_graph) fn admit_machine_comparison(
        &mut self,
        format: MachineIntegerType,
        relation: CompareRelation,
        operands: [crate::kernel::MachineOperandView<'_>; 2],
        value: bool,
    ) -> bool {
        let Some(node) = self.machine_comparison_node(format, relation, operands) else {
            return false;
        };
        self.condition_kinds = self.condition_kinds.with_value((
            Self::machine_comparison_kind(format, relation).expect("supported comparison"),
            value,
        ));
        self.register_pending_loads();
        if format == MachineIntegerType::Int32 {
            use CompareRelation::*;
            let [a, b] = operands;
            let order = match (relation, value) {
                (LessThan, true) | (GreaterEqual, false) => Some((a, b, true)),
                (LessEqual, true) | (GreaterThan, false) => Some((a, b, false)),
                (GreaterThan, true) | (LessEqual, false) => Some((b, a, true)),
                (GreaterEqual, true) | (LessThan, false) => Some((b, a, false)),
                (Equal, _) => None,
            };
            if let Some((a, b, strict)) = order {
                if let Some(bound) = b.word32_constant() {
                    self.retain_signed_int32_interval(
                        a,
                        i64::from(i32::MIN),
                        i64::from(bound as i32) - i64::from(strict),
                    );
                }
                if let Some(bound) = a.word32_constant() {
                    self.retain_signed_int32_interval(
                        b,
                        i64::from(bound as i32) + i64::from(strict),
                        i64::from(i32::MAX),
                    );
                }
            }
        }
        self.retain_condition_truth(node, if value { 1 } else { 2 });
        if value
            && relation == CompareRelation::Equal
            && matches!(
                Self::machine_comparison_width(format, relation, operands),
                W::Bits8 | W::Bits16
            )
            && let Some(Application::Condition(ConditionKind::Int32Eq, left, right)) =
                self.applications.get(&node).copied()
        {
            self.close(vec![(left, right)]);
        }
        true
    }

    pub(in crate::kernel::equality_graph) fn admit_condition(
        &mut self,
        condition: &C,
        value: bool,
    ) -> bool {
        if let C::Compare {
            format,
            relation,
            left,
            right,
        } = condition
        {
            use crate::kernel::MachineOperandView as V;
            return self.admit_machine_comparison(
                *format,
                *relation,
                [V::Legacy(left), V::Legacy(right)],
                value,
            );
        }
        let Some(node) = self.condition_node(condition) else {
            return false;
        };
        self.condition_kinds = self.condition_kinds.with_value((
            Self::condition_kind(condition).expect("supported condition"),
            value,
        ));
        self.register_pending_loads();
        self.retain_condition_truth(node, if value { 1 } else { 2 });
        true
    }

    fn narrow_equation(&self, condition: &C) -> bool {
        let C::Compare {
            format,
            relation: CompareRelation::Equal,
            left,
            right,
        } = condition
        else {
            return false;
        };
        use crate::kernel::MachineOperandView as V;
        matches!(
            Self::machine_comparison_width(
                *format,
                CompareRelation::Equal,
                [V::Legacy(left), V::Legacy(right)]
            ),
            W::Bits8 | W::Bits16
        )
    }

    pub(in crate::kernel::equality_graph) fn may_know_observation_comparison(
        &self,
        view: &crate::kernel::machine_integer::comparison::NativeComparisonView<'_>,
        value: bool,
    ) -> bool {
        use crate::kernel::machine_integer::Relation;
        let format = if view.format == MachineIntegerType::UInt64
            && matches!(view.relation, Relation::Equal | Relation::NotEqual)
        {
            MachineIntegerType::Int64
        } else {
            view.format
        };
        if matches!(
            (view.relation, value),
            (Relation::Equal, true) | (Relation::NotEqual, false)
        ) {
            return true;
        }
        let relations: &[CompareRelation] =
            if matches!(view.relation, Relation::Equal | Relation::NotEqual) {
                &[CompareRelation::Equal]
            } else {
                &[
                    CompareRelation::LessThan,
                    CompareRelation::LessEqual,
                    CompareRelation::GreaterThan,
                    CompareRelation::GreaterEqual,
                ]
            };
        relations.iter().any(|relation| {
            Self::machine_comparison_kind(format, *relation).is_some_and(|kind| {
                self.condition_kinds.contains(&(kind, true))
                    || self.condition_kinds.contains(&(kind, false))
            })
        })
    }

    pub(in crate::kernel::equality_graph) fn knows_observation_comparison(
        &mut self,
        view: &crate::kernel::machine_integer::comparison::NativeComparisonView<'_>,
        value: bool,
    ) -> bool {
        use crate::kernel::machine_integer::Relation;
        let (relation, truth) = match view.relation {
            Relation::Equal => (CompareRelation::Equal, value),
            Relation::NotEqual => (CompareRelation::Equal, !value),
            Relation::Less => (CompareRelation::LessThan, value),
            Relation::LessEqual => (CompareRelation::LessEqual, value),
        };
        let format =
            if relation == CompareRelation::Equal && view.format == MachineIntegerType::UInt64 {
                MachineIntegerType::Int64
            } else {
                view.format
            };
        let operands = view
            .operands
            .each_ref()
            .map(|operand| operand.operand_view());
        if relation == CompareRelation::Equal && truth {
            let width = Self::machine_comparison_width(format, relation, operands);
            let [left, right] = operands.map(|operand| match operand {
                crate::kernel::MachineOperandView::Shared(term) => {
                    self.intern_shared_machine(term, width)
                }
                crate::kernel::MachineOperandView::Legacy(term) => {
                    self.intern_typed_machine(term, width)
                }
            });
            self.register_pending_loads();
            return self.root(left) == self.root(right);
        }
        use CompareRelation::*;
        let alternatives: &[(CompareRelation, bool, bool)] = match relation {
            LessThan => &[
                (LessThan, false, truth),
                (GreaterThan, true, truth),
                (GreaterEqual, false, !truth),
                (LessEqual, true, !truth),
            ],
            LessEqual => &[
                (LessEqual, false, truth),
                (GreaterEqual, true, truth),
                (GreaterThan, false, !truth),
                (LessThan, true, !truth),
            ],
            Equal => &[(Equal, false, truth)],
            _ => unreachable!("normalized comparison view"),
        };
        alternatives
            .iter()
            .copied()
            .any(|(relation, reverse, truth)| {
                let Some(kind) = Self::machine_comparison_kind(format, relation) else {
                    return false;
                };
                if !self.condition_kinds.contains(&(kind, truth)) {
                    return false;
                }
                let operands = if reverse {
                    [operands[1], operands[0]]
                } else {
                    operands
                };
                self.knows_machine_comparison(format, relation, operands, truth)
            })
    }

    pub(in crate::kernel::equality_graph) fn knows_machine_comparison(
        &mut self,
        format: MachineIntegerType,
        relation: CompareRelation,
        operands: [crate::kernel::MachineOperandView<'_>; 2],
        value: bool,
    ) -> bool {
        let Some(node) = self.machine_comparison_node(format, relation, operands) else {
            return false;
        };
        self.register_pending_loads();
        let truth = if value { 1 } else { 2 };
        if self
            .condition_truth
            .get(&self.root(node))
            .is_some_and(|known| known & truth != 0)
        {
            return true;
        }
        if relation == CompareRelation::Equal
            && matches!(
                Self::machine_comparison_width(format, relation, operands),
                W::Bits8 | W::Bits16
            )
            && let Some(Application::Condition(ConditionKind::Int32Eq, left, right)) =
                self.applications.get(&node).copied()
        {
            let (left, right) = (self.root(left), self.root(right));
            return if value {
                left == right
            } else {
                matches!((self.narrow_constants.get(&left), self.narrow_constants.get(&right)), (Some(a), Some(b)) if a != b)
            };
        }
        false
    }

    pub(in crate::kernel::equality_graph) fn may_know_int32_add_overflow(
        &self,
        value: bool,
    ) -> bool {
        self.condition_kinds
            .contains(&(ConditionKind::Int32AddOverflow, value))
    }

    pub(in crate::kernel::equality_graph) fn knows_int32_add_overflow_views(
        &mut self,
        operands: [crate::kernel::MachineOperandView<'_>; 2],
        value: bool,
    ) -> bool {
        let [left, right] = operands.map(|operand| match operand {
            crate::kernel::MachineOperandView::Shared(term) => {
                self.intern_shared_machine(term, W::Bits32)
            }
            crate::kernel::MachineOperandView::Legacy(term) => self.intern_int32(term),
        });
        let node = self.intern_node(Node::Condition(
            ConditionKind::Int32AddOverflow,
            left,
            right,
        ));
        self.register_pending_loads();
        let truth = if value { 1 } else { 2 };
        self.condition_truth
            .get(&self.root(node))
            .is_some_and(|known| known & truth != 0)
    }

    pub(in crate::kernel::equality_graph) fn knows_condition(
        &mut self,
        condition: &C,
        value: bool,
    ) -> bool {
        if let C::Compare {
            format,
            relation,
            left,
            right,
        } = condition
        {
            use crate::kernel::MachineOperandView as V;
            return self.knows_machine_comparison(
                *format,
                *relation,
                [V::Legacy(left), V::Legacy(right)],
                value,
            );
        }
        let Some(node) = self.condition_node(condition) else {
            return false;
        };
        self.register_pending_loads();
        let truth = if value { 1 } else { 2 };
        if self
            .condition_truth
            .get(&self.root(node))
            .is_some_and(|known| known & truth != 0)
        {
            return true;
        }
        let C::PointerOffsetEqual(a, b) = condition else {
            return false;
        };
        let left = self.intern(a);
        let right = self.intern(b);
        let (Some(left), Some(right)) = (
            self.addresses_by_offset.get(&self.root(left)).cloned(),
            self.addresses_by_offset.get(&self.root(right)).cloned(),
        ) else {
            return false;
        };
        // A common block makes this the same address predicate. Nominate only
        // addresses registered at these offsets, never scan ambient pointer facts
        // or infer offset disequality merely from distinct allocation identities.
        let (small, large) = if left.len() <= right.len() {
            (left, right)
        } else {
            (right, left)
        };
        for (block, a) in small.iter() {
            crate::instrumentation::record_deterministic_work(1);
            if let Some(b) = large.get(block) {
                for (a, b) in [(*a, *b), (*b, *a)] {
                    let address_condition =
                        self.intern_node(Node::Condition(ConditionKind::PointerEq, a, b));
                    if self
                        .condition_truth
                        .get(&self.root(address_condition))
                        .is_some_and(|known| known & truth != 0)
                    {
                        return true;
                    }
                }
            }
        }
        false
    }
}

impl C {
    pub(in crate::kernel::equality_graph) fn bitvector_sides_for_congruence(
        &self,
    ) -> Option<(&T, &T)> {
        match self {
            Self::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::Equal,
                left: a,
                right: b,
            }
            | Self::Overflows {
                format: MachineIntegerType::Int32,
                op: OverflowOperation::Add,
                left: a,
                right: b,
            }
            | Self::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::LessThan,
                left: a,
                right: b,
            }
            | Self::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::LessEqual,
                left: a,
                right: b,
            }
            | Self::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::GreaterThan,
                left: a,
                right: b,
            }
            | Self::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::GreaterEqual,
                left: a,
                right: b,
            }
            | Self::Compare {
                format: MachineIntegerType::Int64,
                relation: CompareRelation::Equal,
                left: a,
                right: b,
            }
            | Self::Compare {
                format: MachineIntegerType::Int64,
                relation: CompareRelation::LessThan,
                left: a,
                right: b,
            }
            | Self::Compare {
                format: MachineIntegerType::Int64,
                relation: CompareRelation::LessEqual,
                left: a,
                right: b,
            }
            | Self::Compare {
                format: MachineIntegerType::Int64,
                relation: CompareRelation::GreaterThan,
                left: a,
                right: b,
            }
            | Self::Compare {
                format: MachineIntegerType::Int64,
                relation: CompareRelation::GreaterEqual,
                left: a,
                right: b,
            }
            | Self::Compare {
                format: MachineIntegerType::UInt64,
                relation: CompareRelation::LessThan,
                left: a,
                right: b,
            }
            | Self::Compare {
                format: MachineIntegerType::UInt64,
                relation: CompareRelation::LessEqual,
                left: a,
                right: b,
            }
            | Self::Compare {
                format: MachineIntegerType::UInt64,
                relation: CompareRelation::GreaterThan,
                left: a,
                right: b,
            }
            | Self::Compare {
                format: MachineIntegerType::UInt64,
                relation: CompareRelation::GreaterEqual,
                left: a,
                right: b,
            } => Some((a, b)),
            _ => None,
        }
    }
}
