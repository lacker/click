//! Congruence signatures, not function evaluation or predicate search.
//! Curried application nodes have shallow keys and indexed parent uses. A late
//! operand merge therefore updates precisely the applications depending on it.
use super::*;
use crate::kernel::{
    Bitvector32Term as T, CType, CValue, ConditionTerm as C, PureFunctionArgument as A,
    SharedPureApplication,
};

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(super) enum ArgumentTag {
    Value(CType),
    Array((u32, u32), CType),
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
    OffsetEq,
}

impl TermClasses {
    /// Walk mixed-width machine applications once. In particular, a nested
    /// pure call does not recursively canonicalize every enclosing subtree.
    pub(super) fn intern_machine(&mut self, term: &T, wide: bool) -> u64 {
        enum Binary {
            Int32Add,
            Int32(Int32Binary),
            UInt64(UInt64Binary),
        }
        enum Work<'a> {
            Machine(&'a T, bool),
            Argument(&'a A),
            Value(&'a CValue),
            Wrap(ArgumentTag),
            Call(u64, usize),
            Binary(Binary),
        }
        let mut pending = vec![Work::Machine(term, wide)];
        let mut values = Vec::new();
        while let Some(work) = pending.pop() {
            // Preserve existing scalar work accounting; new argument/call
            // nodes are charged once each, like the old wide traversal.
            if !matches!(
                &work,
                Work::Machine(_, false) | Work::Binary(Binary::Int32Add | Binary::Int32(_))
            ) {
                crate::instrumentation::record_deterministic_work(1);
            }
            let node = match work {
                Work::Machine(term, wide) => {
                    let binary = if wide {
                        uint64_binary(term).map(|(op, a, b)| (Binary::UInt64(op), a, b))
                    } else {
                        match term {
                            T::Add(a, b) => Some((Binary::Int32Add, a.as_ref(), b.as_ref())),
                            T::UnsignedDivide(a, b) => Some((
                                Binary::Int32(Int32Binary::UnsignedDivide),
                                a.as_ref(),
                                b.as_ref(),
                            )),
                            T::UnsignedRemainder(a, b) => Some((
                                Binary::Int32(Int32Binary::UnsignedRemainder),
                                a.as_ref(),
                                b.as_ref(),
                            )),
                            T::BitwiseXor(a, b) => Some((
                                Binary::Int32(Int32Binary::BitwiseXor),
                                a.as_ref(),
                                b.as_ref(),
                            )),
                            _ => None,
                        }
                    };
                    if let Some((op, a, b)) = binary {
                        if !wide {
                            crate::instrumentation::record_deterministic_work(1);
                        }
                        pending.push(Work::Binary(op));
                        pending.push(Work::Machine(b, wide));
                        pending.push(Work::Machine(a, wide));
                        continue;
                    }
                    if let T::ClickFunctionApplication { name, arguments } = term {
                        let symbol = SharedPureApplication::intern(format!("click:{name}"), vec![]);
                        let head = self.intern_node(Node::Function(symbol, wide, arguments.len()));
                        pending.push(Work::Call(head, arguments.len()));
                        pending.extend(arguments.iter().rev().map(Work::Argument));
                        continue;
                    }
                    // Legacy applications carry no argument sorts. Keep
                    // them opaque instead of guessing a machine width.
                    if wide {
                        if let Some((memory, pointer)) = uint64_read(term) {
                            Node::UInt64Read(
                                memory.read_identity(),
                                self.address(pointer.block, pointer.offset).0,
                            )
                        } else if let T::PointerAddress(pointer) = term {
                            Node::UInt64Address(
                                self.address(pointer.block.clone(), pointer.offset.clone())
                                    .0,
                            )
                        } else {
                            Node::UInt64(MachineAtom::uint64(term.clone()))
                        }
                    } else {
                        Node::Int32(MachineAtom::int32(term.clone()))
                    }
                }
                Work::Argument(argument) => {
                    match argument {
                        A::Value(value) => pending.push(Work::Value(value)),
                        A::ArrayRef {
                            memory,
                            pointer,
                            element_type,
                        } => {
                            pending.push(Work::Wrap(ArgumentTag::Array(
                                crate::kernel::intern_c_memory(memory.clone()).read_identity(),
                                *element_type,
                            )));
                            pending.push(Work::Value(pointer));
                        }
                        // Binder-bearing terms stay opaque; graph registration
                        // never substitutes into a match or fold.
                        _ => {
                            values.push(self.opaque_argument(argument));
                            continue;
                        }
                    }
                    continue;
                }
                Work::Value(value) => {
                    let scalar = match value {
                        CValue::Int32(t) => Some((CType::Int32, t, false)),
                        CValue::UInt32(t) => Some((CType::UInt32, t, false)),
                        CValue::UInt64(t) => Some((CType::UInt64, t, true)),
                        _ => None,
                    };
                    if let Some((ty, term, wide)) = scalar {
                        pending.push(Work::Wrap(ArgumentTag::Value(ty)));
                        pending.push(Work::Machine(term, wide));
                        continue;
                    }
                    if let CValue::Pointer(pointer) = value {
                        // Native address equality does not equate semantic
                        // pointer values. Retain designated arguments whole
                        // until the graph supports their complete value sort.
                        if pointer.designation().is_some() {
                            values.push(self.opaque_argument(&A::Value(value.clone())));
                            continue;
                        }
                        let address = self
                            .address(
                                pointer.pointer().block.clone(),
                                pointer.pointer().offset.clone(),
                            )
                            .0;
                        let tag = self
                            .intern_node(Node::ArgumentTag(ArgumentTag::Value(pointer.c_type())));
                        Node::Apply(tag, address)
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
                Work::Call(mut head, count) => {
                    for argument in values.split_off(values.len() - count) {
                        head = self.intern_node(Node::Apply(head, argument));
                    }
                    values.push(head);
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
            values.push(self.intern_node(node));
        }
        values.pop().expect("machine term")
    }

    fn opaque_argument(&mut self, argument: &A) -> u64 {
        // Map comparisons use stable IDs, not full algebraic values/snapshots.
        self.intern_node(Node::OpaqueArgument(SharedPureApplication::intern(
            String::new(),
            vec![argument.clone()],
        )))
    }

    pub(in crate::kernel::equality_graph) fn condition_node(
        &mut self,
        condition: &C,
    ) -> Option<u64> {
        use ConditionKind::*;
        let (kind, left, right) = match condition {
            C::Bitvector32Equal(a, b) => (Int32Eq, self.intern_int32(a), self.intern_int32(b)),
            C::Bitvector32SignedAddOverflows(a, b) => {
                (Int32AddOverflow, self.intern_int32(a), self.intern_int32(b))
            }
            C::Bitvector32SignedLessThan(a, b) => {
                (Int32Lt, self.intern_int32(a), self.intern_int32(b))
            }
            C::Bitvector32SignedLessEqual(a, b) => {
                (Int32Le, self.intern_int32(a), self.intern_int32(b))
            }
            C::Bitvector32SignedGreaterThan(a, b) => {
                (Int32Gt, self.intern_int32(a), self.intern_int32(b))
            }
            C::Bitvector32SignedGreaterEqual(a, b) => {
                (Int32Ge, self.intern_int32(a), self.intern_int32(b))
            }
            C::Bitvector64Equal(a, b) => (UInt64Eq, self.intern_uint64(a), self.intern_uint64(b)),
            C::Bitvector64SignedLessThan(a, b) => {
                (Int64Lt, self.intern_uint64(a), self.intern_uint64(b))
            }
            C::Bitvector64SignedLessEqual(a, b) => {
                (Int64Le, self.intern_uint64(a), self.intern_uint64(b))
            }
            C::Bitvector64SignedGreaterThan(a, b) => {
                (Int64Gt, self.intern_uint64(a), self.intern_uint64(b))
            }
            C::Bitvector64SignedGreaterEqual(a, b) => {
                (Int64Ge, self.intern_uint64(a), self.intern_uint64(b))
            }
            C::Bitvector64UnsignedLessThan(a, b) => {
                (UInt64Lt, self.intern_uint64(a), self.intern_uint64(b))
            }
            C::Bitvector64UnsignedLessEqual(a, b) => {
                (UInt64Le, self.intern_uint64(a), self.intern_uint64(b))
            }
            C::Bitvector64UnsignedGreaterThan(a, b) => {
                (UInt64Gt, self.intern_uint64(a), self.intern_uint64(b))
            }
            C::Bitvector64UnsignedGreaterEqual(a, b) => {
                (UInt64Ge, self.intern_uint64(a), self.intern_uint64(b))
            }
            C::PointerEqual(a, b) => (
                PointerEq,
                self.address(a.block.clone(), a.offset.clone()).0,
                self.address(b.block.clone(), b.offset.clone()).0,
            ),
            C::PointerOffsetEqual(a, b) => (OffsetEq, self.intern(a), self.intern(b)),
            _ => return None,
        };
        Some(self.intern_node(Node::Condition(kind, left, right)))
    }

    fn condition_kind(condition: &C) -> Option<ConditionKind> {
        Some(match condition {
            C::Bitvector32Equal(..) => ConditionKind::Int32Eq,
            C::Bitvector32SignedAddOverflows(..) => ConditionKind::Int32AddOverflow,
            C::Bitvector64Equal(..) => ConditionKind::UInt64Eq,
            C::PointerEqual(..) => ConditionKind::PointerEq,
            C::PointerOffsetEqual(..) => ConditionKind::OffsetEq,
            C::Bitvector32SignedLessThan(..) => ConditionKind::Int32Lt,
            C::Bitvector32SignedLessEqual(..) => ConditionKind::Int32Le,
            C::Bitvector32SignedGreaterThan(..) => ConditionKind::Int32Gt,
            C::Bitvector32SignedGreaterEqual(..) => ConditionKind::Int32Ge,
            C::Bitvector64SignedLessThan(..) => ConditionKind::Int64Lt,
            C::Bitvector64SignedLessEqual(..) => ConditionKind::Int64Le,
            C::Bitvector64SignedGreaterThan(..) => ConditionKind::Int64Gt,
            C::Bitvector64SignedGreaterEqual(..) => ConditionKind::Int64Ge,
            C::Bitvector64UnsignedLessThan(..) => ConditionKind::UInt64Lt,
            C::Bitvector64UnsignedLessEqual(..) => ConditionKind::UInt64Le,
            C::Bitvector64UnsignedGreaterThan(..) => ConditionKind::UInt64Gt,
            C::Bitvector64UnsignedGreaterEqual(..) => ConditionKind::UInt64Ge,
            _ => return None,
        })
    }

    pub(in crate::kernel::equality_graph) fn may_know_condition(
        &self,
        condition: &C,
        value: bool,
    ) -> bool {
        Self::condition_kind(condition)
            .is_some_and(|kind| self.condition_kinds.contains(&(kind, value)))
    }

    pub(in crate::kernel::equality_graph) fn admit_condition(
        &mut self,
        condition: &C,
        value: bool,
    ) -> bool {
        let Some(node) = self.condition_node(condition) else {
            return false;
        };
        self.condition_kinds = self.condition_kinds.with_value((
            Self::condition_kind(condition).expect("supported condition"),
            value,
        ));
        self.register_pending_loads();
        // Only signed 32-bit order facts contribute to this interval. Wide
        // and unsigned comparisons retain their separate semantic orders.
        let order = match (condition, value) {
            (C::Bitvector32SignedLessThan(a, b), true)
            | (C::Bitvector32SignedLessEqual(a, b), false) => Some((a, b, true, value)),
            (C::Bitvector32SignedLessEqual(a, b), true)
            | (C::Bitvector32SignedLessThan(a, b), false) => Some((a, b, false, value)),
            (C::Bitvector32SignedGreaterThan(a, b), true)
            | (C::Bitvector32SignedGreaterEqual(a, b), false) => Some((b, a, true, value)),
            (C::Bitvector32SignedGreaterEqual(a, b), true)
            | (C::Bitvector32SignedGreaterThan(a, b), false) => Some((b, a, false, value)),
            _ => None,
        };
        if let Some((a, b, strict, forward)) = order {
            let (a, b) = if forward { (a, b) } else { (b, a) };
            if let Some(bound) = crate::kernel::canonical_term(b).as_const() {
                self.retain_signed_int32_interval(
                    a,
                    i64::from(i32::MIN),
                    i64::from(bound as i32) - i64::from(strict),
                );
            }
            if let Some(bound) = crate::kernel::canonical_term(a).as_const() {
                self.retain_signed_int32_interval(
                    b,
                    i64::from(bound as i32) + i64::from(strict),
                    i64::from(i32::MAX),
                );
            }
        }
        let root = self.root(node);
        let truth = self.condition_truth.get(&root).copied().unwrap_or(0);
        self.condition_truth
            .insert(root, truth | if value { 1 } else { 2 });
        true
    }

    pub(in crate::kernel::equality_graph) fn knows_condition(
        &mut self,
        condition: &C,
        value: bool,
    ) -> bool {
        let Some(node) = self.condition_node(condition) else {
            return false;
        };
        self.register_pending_loads();
        self.condition_truth
            .get(&self.root(node))
            .is_some_and(|truth| truth & if value { 1 } else { 2 } != 0)
    }
}

impl C {
    pub(in crate::kernel::equality_graph) fn bitvector_sides_for_congruence(
        &self,
    ) -> Option<(&T, &T)> {
        match self {
            Self::Bitvector32Equal(a, b)
            | Self::Bitvector32SignedAddOverflows(a, b)
            | Self::Bitvector32SignedLessThan(a, b)
            | Self::Bitvector32SignedLessEqual(a, b)
            | Self::Bitvector32SignedGreaterThan(a, b)
            | Self::Bitvector32SignedGreaterEqual(a, b)
            | Self::Bitvector64Equal(a, b)
            | Self::Bitvector64SignedLessThan(a, b)
            | Self::Bitvector64SignedLessEqual(a, b)
            | Self::Bitvector64SignedGreaterThan(a, b)
            | Self::Bitvector64SignedGreaterEqual(a, b)
            | Self::Bitvector64UnsignedLessThan(a, b)
            | Self::Bitvector64UnsignedLessEqual(a, b)
            | Self::Bitvector64UnsignedGreaterThan(a, b)
            | Self::Bitvector64UnsignedGreaterEqual(a, b) => Some((a, b)),
            _ => None,
        }
    }
}
