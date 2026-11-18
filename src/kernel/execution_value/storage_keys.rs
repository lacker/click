//! Keys project shared syntax without caching an enclosing native value tree.
//! Selected opaque leaves retain the existing native descriptor contract.
use super::*;
use std::{
    cmp::Ordering,
    hash::{Hash, Hasher},
    sync::Arc,
};

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub(in crate::kernel) struct BooleanStorageKey(BooleanKeyKind);

// Keep the word/cast split private: all BoolCast inputs are projected by the
// constructor, so a raw Word can never alias a projected Cast.
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
enum BooleanKeyKind {
    Word(MachineTerm),
    Cast(MachineIntegerType, ConditionStorageKey),
}
impl BooleanStorageKey {
    pub(super) fn native(word: &MachineTerm) -> Self {
        Self(match word {
            MachineTerm::BoolCast { to, value } => {
                BooleanKeyKind::Cast(*to, ConditionStorageKey::native(value))
            }
            _ => BooleanKeyKind::Word(word.clone()),
        })
    }
    pub(super) fn shared(root: &KernelTerm) -> Self {
        if root.ty() == &KernelType::Program(ProgramType::Bool) {
            return match root.node() {
                KernelTermNode::Variable(v) => {
                    Self(BooleanKeyKind::Word(MachineTerm::Variable(*v)))
                }
                KernelTermNode::Legacy(value) => {
                    let PureFunctionArgument::Value(ProgramValue::Bool(word)) = value.value()
                    else {
                        unreachable!()
                    };
                    Self::native(word)
                }
                _ => unreachable!("raw Boolean carrier"),
            };
        }
        Self(
            if let Some(value) = BooleanOperandView::Shared(root).constant() {
                BooleanKeyKind::Word(MachineTerm::bool_cast(
                    MachineIntegerType::UInt8,
                    ConditionTerm::Constant(value),
                ))
            } else {
                BooleanKeyKind::Cast(MachineIntegerType::UInt8, root.condition_storage_key())
            },
        )
    }
}
impl PartialOrd for BooleanStorageKey {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for BooleanStorageKey {
    fn cmp(&self, other: &Self) -> Ordering {
        match (&self.0, &other.0) {
            (BooleanKeyKind::Word(a), BooleanKeyKind::Word(b)) => a.cmp(b),
            (BooleanKeyKind::Cast(at, a), BooleanKeyKind::Cast(bt, b)) => {
                at.cmp(bt).then_with(|| a.cmp(b))
            }
            (BooleanKeyKind::Word(a), BooleanKeyKind::Cast(..)) => {
                native_machine_rank(a).cmp(&BOOL_CAST_RANK)
            }
            (BooleanKeyKind::Cast(..), BooleanKeyKind::Word(b)) => {
                BOOL_CAST_RANK.cmp(&native_machine_rank(b))
            }
        }
    }
}

// Native MachineTerm variant order, shared by both family projections. The
// exhaustive match forces a review when a new opaque word variant is added.
const PURE_APPLICATION_RANK: u8 = 6;
const CLICK_APPLICATION_RANK: u8 = 7;
const FLOAT32_NEGATE_RANK: u8 = 13;
const FLOAT32_BINARY_RANK: u8 = 14;
const FLOAT64_NEGATE_RANK: u8 = 15;
const FLOAT64_BINARY_RANK: u8 = 16;
const BOOL_CAST_RANK: u8 = 17;
fn native_machine_rank(value: &MachineTerm) -> u8 {
    match value {
        MachineTerm::Constant { .. } => 0,
        MachineTerm::Variable(_) => 1,
        MachineTerm::Binary { .. } => 2,
        MachineTerm::Unary { .. } => 3,
        MachineTerm::If { .. } => 4,
        MachineTerm::RangeFold { .. } => 5,
        MachineTerm::PureFunctionApplication { .. } => PURE_APPLICATION_RANK,
        MachineTerm::ClickFunctionApplication { .. } => CLICK_APPLICATION_RANK,
        MachineTerm::AlgebraicMatch { .. } => 8,
        MachineTerm::MemoryLoad(..) => 9,
        MachineTerm::IntegerAddress(..) => 10,
        MachineTerm::IntegerToMachine { .. } => 11,
        MachineTerm::Cast { .. } => 12,
        MachineTerm::Float32Negate(_) => FLOAT32_NEGATE_RANK,
        MachineTerm::Float32Binary { .. } => FLOAT32_BINARY_RANK,
        MachineTerm::Float64Negate(_) => FLOAT64_NEGATE_RANK,
        MachineTerm::Float64Binary { .. } => FLOAT64_BINARY_RANK,
        MachineTerm::BoolCast { .. } => BOOL_CAST_RANK,
        MachineTerm::ThreadHandle(_) => 18,
    }
}

#[derive(Clone, Debug)]
pub(in crate::kernel) struct ConditionStorageKey(Arc<ConditionKeyData>);
#[derive(Debug, Hash)]
struct ConditionKeyData {
    shape: ConditionShape,
    fingerprint: u64,
}
#[derive(Debug, Hash)]
enum ConditionShape {
    Atom(ConditionTerm),
    If([ConditionStorageKey; 3]),
    Equal([ConditionStorageKey; 2]),
}
impl ConditionStorageKey {
    fn new(shape: ConditionShape) -> Self {
        crate::instrumentation::record_deterministic_work(1);
        let mut hash = std::collections::hash_map::DefaultHasher::new();
        shape.hash(&mut hash);
        Self(Arc::new(ConditionKeyData {
            shape,
            fingerprint: hash.finish(),
        }))
    }
    pub(in crate::kernel) fn shared(root: &KernelTerm) -> Self {
        match root.node() {
            KernelTermNode::BoolIf { arguments } => Self::new(ConditionShape::If(
                arguments.each_ref().map(KernelTerm::condition_storage_key),
            )),
            KernelTermNode::BoolEqual { arguments } => Self::new(ConditionShape::Equal(
                arguments.each_ref().map(KernelTerm::condition_storage_key),
            )),
            _ => Self::native(&BooleanOperandView::Shared(root).identity_leaf()),
        }
    }
    fn native(term: &ConditionTerm) -> Self {
        enum Task<'a> {
            Enter(&'a ConditionTerm),
            If,
            Equal,
        }
        let mut pending = vec![Task::Enter(term)];
        let mut values = Vec::new();
        while let Some(task) = pending.pop() {
            match task {
                Task::Enter(ConditionTerm::BoolIf {
                    condition,
                    then_condition,
                    else_condition,
                }) => {
                    pending.push(Task::If);
                    pending.extend(
                        [else_condition, then_condition, condition].map(|v| Task::Enter(v)),
                    );
                }
                Task::Enter(ConditionTerm::BoolEqual(a, b)) => {
                    pending.push(Task::Equal);
                    pending.push(Task::Enter(b));
                    pending.push(Task::Enter(a));
                }
                Task::Enter(term) => values.push(Self::new(ConditionShape::Atom(term.clone()))),
                Task::If => {
                    let no = values.pop().unwrap();
                    let yes = values.pop().unwrap();
                    let guard = values.pop().unwrap();
                    values.push(Self::new(ConditionShape::If([guard, yes, no])));
                }
                Task::Equal => {
                    let b = values.pop().unwrap();
                    let a = values.pop().unwrap();
                    values.push(Self::new(ConditionShape::Equal([a, b])));
                }
            }
        }
        values.pop().expect("condition key")
    }
}
impl ConditionShape {
    fn rank(&self) -> u8 {
        match self {
            Self::If(_) => 17,
            Self::Equal(_) => 18,
            Self::Atom(value) => match value {
                ConditionTerm::Constant(_) => 0,
                ConditionTerm::Variable(_) => 1,
                ConditionTerm::AlgebraicEqual(..) => 2,
                ConditionTerm::Compare { .. } => 3,
                ConditionTerm::Overflows { .. } => 4,
                ConditionTerm::Float32(_) => 5,
                ConditionTerm::Float64(_) => 6,
                ConditionTerm::AddressOffsetEqual(..) => 7,
                ConditionTerm::AddressEqual(..) => 8,
                ConditionTerm::PointerEqual(..) => 9,
                ConditionTerm::IntegerLessThan(..) => 10,
                ConditionTerm::IntegerLessEqual(..) => 11,
                ConditionTerm::IntegerGreaterThan(..) => 12,
                ConditionTerm::IntegerGreaterEqual(..) => 13,
                ConditionTerm::IntegerEqual(..) => 14,
                ConditionTerm::IntegerNotEqual(..) => 15,
                ConditionTerm::BoolApplication(_) => 16,
                ConditionTerm::BoolIf { .. } | ConditionTerm::BoolEqual(..) => {
                    unreachable!("projected connective")
                }
                ConditionTerm::BoolLoad(..) => 19,
            },
        }
    }
}
impl Hash for ConditionStorageKey {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.0.fingerprint.hash(state);
    }
}
impl PartialEq for ConditionStorageKey {
    fn eq(&self, other: &Self) -> bool {
        self.cmp(other).is_eq()
    }
}
impl Eq for ConditionStorageKey {}
impl PartialOrd for ConditionStorageKey {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for ConditionStorageKey {
    fn cmp(&self, other: &Self) -> Ordering {
        let mut pending = vec![(self, other)];
        let mut seen = std::collections::HashSet::new();
        while let Some((a, b)) = pending.pop() {
            if Arc::ptr_eq(&a.0, &b.0) || !seen.insert((Arc::as_ptr(&a.0), Arc::as_ptr(&b.0))) {
                continue;
            }
            crate::instrumentation::record_deterministic_work(1);
            let order = a.0.shape.rank().cmp(&b.0.shape.rank());
            if !order.is_eq() {
                return order;
            }
            match (&a.0.shape, &b.0.shape) {
                (ConditionShape::Atom(a), ConditionShape::Atom(b)) => {
                    let order = a.cmp(b);
                    if !order.is_eq() {
                        return order;
                    }
                }
                (ConditionShape::If(a), ConditionShape::If(b)) => {
                    pending.extend(a.iter().zip(b).rev())
                }
                (ConditionShape::Equal(a), ConditionShape::Equal(b)) => {
                    pending.extend(a.iter().zip(b).rev())
                }
                _ => unreachable!("same condition key rank"),
            }
        }
        Ordering::Equal
    }
}

/// Native ProgramValue variant order. Numeric local keys live in the separate
/// machine-observation family; numeric memory cells keep native structural keys.
fn native_rank(value: &ProgramValue) -> u8 {
    match value {
        ProgramValue::PointerInteger(_) => 0,
        ProgramValue::Void => 1,
        ProgramValue::Bool(_) => 2,
        ProgramValue::Int8(_) => 3,
        ProgramValue::Int16(_) => 4,
        ProgramValue::Int32(_) => 5,
        ProgramValue::UInt8(_) => 6,
        ProgramValue::UInt16(_) => 7,
        ProgramValue::UInt32(_) => 8,
        ProgramValue::Int64(_) => 9,
        ProgramValue::UInt64(_) => 10,
        ProgramValue::Int128(_) => 11,
        ProgramValue::UInt128(_) => 12,
        ProgramValue::Float32(_) => 13,
        ProgramValue::Float64(_) => 14,
        ProgramValue::Pointer(_) => 15,
        ProgramValue::Parameter(_) => 16,
    }
}
#[derive(Eq, PartialEq)]
pub(super) enum NativeStorageIdentity<'a> {
    Boolean(&'a BooleanStorageKey),
    Float32(&'a FloatStorageKey),
    Float64(&'a FloatStorageKey),
    Algebraic(&'a AlgebraicStorageKey),
    Pointer(&'a PointerStorageKey),
    Word(&'a WordKey),
    Value(&'a ProgramValue),
}
impl NativeStorageIdentity<'_> {
    fn rank(&self) -> u8 {
        match self {
            Self::Boolean(_) => 2,
            Self::Float32(_) => 13,
            Self::Float64(_) => 14,
            Self::Algebraic(_) => 16,
            Self::Word(_) => 8,
            Self::Pointer(_) => 15,
            Self::Value(v) => native_rank(v),
        }
    }
}
impl Hash for NativeStorageIdentity<'_> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.rank().hash(state);
        match self {
            Self::Boolean(v) => v.hash(state),
            Self::Float32(v) | Self::Float64(v) => v.hash(state),
            Self::Algebraic(v) => v.hash(state),
            Self::Word(v) => v.hash(state),
            Self::Pointer(v) => v.hash(state),
            Self::Value(v) => v.hash(state),
        }
    }
}
impl PartialOrd for NativeStorageIdentity<'_> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for NativeStorageIdentity<'_> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.rank()
            .cmp(&other.rank())
            .then_with(|| match (self, other) {
                (Self::Boolean(a), Self::Boolean(b)) => a.cmp(b),
                (Self::Float32(a), Self::Float32(b)) | (Self::Float64(a), Self::Float64(b)) => {
                    a.cmp(b)
                }
                (Self::Algebraic(a), Self::Algebraic(b)) => a.cmp(b),
                (Self::Pointer(a), Self::Pointer(b)) => a.cmp(b),
                (Self::Word(a), Self::Word(b)) => a.cmp(b),
                (Self::Word(a), Self::Value(ProgramValue::UInt32(b))) => a.cmp_native(b),
                (Self::Value(ProgramValue::UInt32(a)), Self::Word(b)) => b.cmp_native(a).reverse(),
                (Self::Value(a), Self::Value(b)) => a.cmp(b),
                _ => unreachable!("each migrated family uses its projection"),
            })
    }
}

impl Drop for ConditionStorageKey {
    fn drop(&mut self) {
        fn take(key: &mut ConditionStorageKey, pending: &mut Vec<ConditionStorageKey>) {
            if let Some(data) = Arc::get_mut(&mut key.0) {
                match std::mem::replace(
                    &mut data.shape,
                    ConditionShape::Atom(ConditionTerm::Constant(false)),
                ) {
                    ConditionShape::If(children) => pending.extend(children),
                    ConditionShape::Equal(children) => pending.extend(children),
                    ConditionShape::Atom(_) => {}
                }
            }
        }
        let mut pending = Vec::new();
        take(self, &mut pending);
        while let Some(mut child) = pending.pop() {
            take(&mut child, &mut pending);
        }
    }
}

mod word;
pub(in crate::kernel) use word::WordKey;

mod pointer;
pub(in crate::kernel) use pointer::PointerStorageKey;
pub(in crate::kernel) use pointer::for_root as pointer_for_root;

mod algebraic;
pub(in crate::kernel) use algebraic::AlgebraicStorageKey;
pub(in crate::kernel) use algebraic::for_root as algebraic_for_root;

mod float;
pub(in crate::kernel) use float::FloatStorageKey;

thread_local! {
    // Syntax is immutable across state restores, but a fresh verification must
    // pay for its own selected key construction regardless of earlier runs.
    static CONDITION_KEYS: std::cell::RefCell<crate::id_hash::U64Map<ConditionStorageKey>> = Default::default();
}
pub(in crate::kernel) fn clear_session_key_memos() {
    CONDITION_KEYS.with(|keys| keys.borrow_mut().clear());
    float::clear_session_key_memos();
    algebraic::clear_session_key_memos();
    pointer::clear_session_key_memos();
}
pub(in crate::kernel) fn condition_for_root(source: &KernelTerm) -> ConditionStorageKey {
    CONDITION_KEYS.with(|keys| {
        let mut pending = vec![(source, false)];
        while let Some((root, finish)) = pending.pop() {
            if keys.borrow().contains_key(&root.id()) {
                continue;
            }
            if !finish {
                match root.node() {
                    KernelTermNode::BoolIf { arguments } => {
                        pending.push((root, true));
                        pending.extend(arguments.iter().rev().map(|child| (child, false)));
                        continue;
                    }
                    KernelTermNode::BoolEqual { arguments } => {
                        pending.push((root, true));
                        pending.extend(arguments.iter().rev().map(|child| (child, false)));
                        continue;
                    }
                    _ => {}
                }
            }
            let key = ConditionStorageKey::shared(root);
            keys.borrow_mut().insert(root.id(), key);
        }
        keys.borrow()
            .get(&source.id())
            .expect("condition storage key")
            .clone()
    })
}

pub(in crate::kernel) fn float_for_root(root: &KernelTerm) -> FloatStorageKey {
    float::for_root(root)
}
