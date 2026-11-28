//! Evaluated machine operands in immutable resource descriptors.
//! Native input and selected native output retain their exact syntax; shared
//! producers own their common root and reuse its existing compatibility reader.
use super::*;
use crate::kernel::execution_value::storage_keys::ConditionStorageKey;
use crate::kernel::{ExecutionValue, RetainedProgramValue};

#[derive(Clone)]
pub struct StoredMachineTerm(RetainedProgramValue);
impl From<OldMachineTerm> for StoredMachineTerm {
    fn from(value: OldMachineTerm) -> Self {
        Self::new(MachineIntegerType::Int32, value)
    }
}
impl From<u32> for StoredMachineTerm {
    fn from(value: u32) -> Self {
        OldMachineTerm::constant(value).into()
    }
}
impl StoredMachineTerm {
    pub(crate) fn new(ty: MachineIntegerType, value: OldMachineTerm) -> Self {
        let value = match ty {
            MachineIntegerType::Int8 => ProgramValue::Int8(value),
            MachineIntegerType::UInt8 => ProgramValue::UInt8(value),
            MachineIntegerType::Int16 => ProgramValue::Int16(value),
            MachineIntegerType::UInt16 => ProgramValue::UInt16(value),
            MachineIntegerType::Int32 => ProgramValue::Int32(value),
            MachineIntegerType::UInt32 => ProgramValue::UInt32(value),
            MachineIntegerType::Int64 => ProgramValue::Int64(value),
            MachineIntegerType::UInt64 => ProgramValue::UInt64(value),
            MachineIntegerType::Int128 => ProgramValue::Int128(value),
            MachineIntegerType::UInt128 => ProgramValue::UInt128(value),
        };
        Self(value.into())
    }
    pub(crate) fn from_value(value: ExecutionValue) -> Option<Self> {
        MachineIntegerType::from_program_type(value.program_type())?;
        if let ExecutionValue::Native(value) = &value
            && !matches!(
                value,
                ProgramValue::Int8(_)
                    | ProgramValue::UInt8(_)
                    | ProgramValue::Int16(_)
                    | ProgramValue::UInt16(_)
                    | ProgramValue::Int32(_)
                    | ProgramValue::UInt32(_)
                    | ProgramValue::Int64(_)
                    | ProgramValue::UInt64(_)
                    | ProgramValue::Int128(_)
                    | ProgramValue::UInt128(_)
            )
        {
            return None;
        }
        Some(Self(value.into()))
    }
    pub(crate) fn as_const(&self) -> Option<u32> {
        self.operand_view().word32_constant()
    }
    pub(crate) fn map_native(
        &self,
        rewrite: impl FnOnce(&OldMachineTerm) -> OldMachineTerm,
    ) -> Self {
        Self::new(
            MachineIntegerType::from_program_type(self.0.program_type())
                .expect("machine descriptor"),
            rewrite(self.old_form()),
        )
    }
    pub(crate) fn operand_view(&self) -> MachineOperandView<'_> {
        match self.root() {
            Some(root) => MachineOperandView::Shared(root),
            None => MachineOperandView::Old(self.old_form()),
        }
    }
    pub(crate) fn value(&self) -> &ExecutionValue {
        self.0.value()
    }
    pub(crate) fn root(&self) -> Option<&KernelTerm> {
        self.0.root()
    }
    fn storage_key(&self) -> &crate::kernel::execution_value::storage_keys::ScalarStorageKey {
        use crate::kernel::execution_value::storage_keys::ProgramStorageKey;
        let ProgramStorageKey::Scalar(_, key) = self.0.storage_key() else {
            unreachable!("machine descriptor");
        };
        key
    }

    pub(crate) fn old_form(&self) -> &OldMachineTerm {
        match self.0.old_form() {
            ProgramValue::Bool(v)
            | ProgramValue::Int8(v)
            | ProgramValue::UInt8(v)
            | ProgramValue::Int16(v)
            | ProgramValue::UInt16(v)
            | ProgramValue::Int32(v)
            | ProgramValue::UInt32(v)
            | ProgramValue::Int64(v)
            | ProgramValue::UInt64(v)
            | ProgramValue::Int128(v)
            | ProgramValue::UInt128(v) => v,
            _ => unreachable!("machine descriptor operand"),
        }
    }
}
impl std::fmt::Debug for StoredMachineTerm {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.old_form().fmt(f)
    }
}
impl PartialEq for StoredMachineTerm {
    fn eq(&self, other: &Self) -> bool {
        self.cmp(other).is_eq()
    }
}
impl Eq for StoredMachineTerm {}
impl PartialOrd for StoredMachineTerm {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for StoredMachineTerm {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        match (self.root(), other.root()) {
            (None, None) => self.old_form().cmp(other.old_form()),
            (Some(a), Some(b)) if a == b => std::cmp::Ordering::Equal,
            _ => self.storage_key().cmp(other.storage_key()),
        }
    }
}
impl std::hash::Hash for StoredMachineTerm {
    fn hash<H: std::hash::Hasher>(&self, h: &mut H) {
        self.old_form().hash(h);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::hash::{Hash, Hasher};
    #[test]
    fn native_descriptor_machine_inputs_keep_exact_syntax_and_hash() {
        let _session = crate::kernel::VerificationSession::enter();
        fn hash(v: &impl Hash) -> u64 {
            let mut h = std::collections::hash_map::DefaultHasher::new();
            v.hash(&mut h);
            h.finish()
        }
        let values = [
            OldMachineTerm::constant(7),
            OldMachineTerm::uint32_constant(7),
            OldMachineTerm::uint64_constant(7),
            OldMachineTerm::Variable(Variable(10993613)),
        ];
        for ty in [MachineIntegerType::Int32, MachineIntegerType::UInt64] {
            for value in &values {
                let stored = StoredMachineTerm::new(ty, value.clone());
                assert_eq!(stored.old_form(), value);
                assert_eq!(hash(&stored), hash(value));
                assert_eq!(format!("{stored:?}"), format!("{value:?}"));
                for other in &values {
                    let other_stored = StoredMachineTerm::new(ty, other.clone());
                    assert_eq!(stored == other_stored, value == other);
                    assert_eq!(stored.cmp(&other_stored), value.cmp(other));
                }
            }
        }
    }
}

/// Exact program payload storage for protocol values and native output DTOs.
#[derive(Clone)]
pub struct StoredProgramValue(RetainedProgramValue);
impl From<ProgramValue> for StoredProgramValue {
    fn from(value: ProgramValue) -> Self {
        Self(value.into())
    }
}
impl From<ExecutionValue> for StoredProgramValue {
    fn from(value: ExecutionValue) -> Self {
        Self(
            crate::kernel::StoredExecutionValue::from(value)
                .into_value()
                .into(),
        )
    }
}
impl From<StoredProgramValue> for ProgramValue {
    fn from(value: StoredProgramValue) -> Self {
        value.0.into_native_compat()
    }
}
impl StoredProgramValue {
    pub(crate) fn value(&self) -> &ExecutionValue {
        self.0.value()
    }
    pub(crate) fn root(&self) -> Option<&KernelTerm> {
        self.0.root()
    }
    pub(crate) fn old_form(&self) -> &ProgramValue {
        self.0.old_form()
    }
}

/// An exact native Integer field, or an already-produced common Integer.
#[derive(Clone)]
pub struct StoredIntegerTerm(StoredInteger);
#[derive(Clone)]
enum StoredInteger {
    Input(Arc<IntegerTerm>),
    Shared(KernelTerm),
}
impl From<IntegerTerm> for StoredIntegerTerm {
    fn from(value: IntegerTerm) -> Self {
        if let Some(root) = value.mathematical_root() {
            Self(StoredInteger::Shared(root))
        } else {
            Self(StoredInteger::Input(Arc::new(value)))
        }
    }
}
impl StoredIntegerTerm {
    pub(crate) fn from_root(root: KernelTerm) -> Option<Self> {
        (root.ty() == &KernelType::Integer).then(|| Self(StoredInteger::Shared(root)))
    }
    pub(crate) fn root(&self) -> Option<&KernelTerm> {
        match &self.0 {
            StoredInteger::Input(_) => None,
            StoredInteger::Shared(root) => Some(root),
        }
    }
    pub(crate) fn into_shared(self) -> SharedIntegerTerm {
        match self.0 {
            StoredInteger::Shared(root) => SharedIntegerTerm::from_root(root),
            StoredInteger::Input(value) => Arc::unwrap_or_clone(value).into(),
        }
    }

    fn exact_key(&self) -> super::integer::IntegerShallowKey {
        self.root()
            .and_then(KernelTerm::integer_exact_key)
            .unwrap_or_else(|| self.old_form().shallow_key())
    }

    pub(crate) fn old_form(&self) -> &IntegerTerm {
        match &self.0 {
            StoredInteger::Input(value) => value,
            StoredInteger::Shared(root) => {
                root.integer_native_compat().expect("Integer field output")
            }
        }
    }
    pub(crate) fn into_native_compat(self) -> IntegerTerm {
        match self.0 {
            StoredInteger::Input(value) => {
                Arc::try_unwrap(value).unwrap_or_else(|value| (*value).clone())
            }
            StoredInteger::Shared(root) => root
                .integer_native_compat()
                .expect("Integer field output")
                .clone(),
        }
    }
}

/// Exact algebraic field input and retained algebraic expression output.
#[derive(Clone)]
pub struct StoredAlgebraicTerm(StoredAlgebraic);
#[derive(Clone)]
enum StoredAlgebraic {
    Input(Arc<AlgebraicTerm>),
    Shared(KernelTerm),
}
impl From<AlgebraicTerm> for StoredAlgebraicTerm {
    fn from(value: AlgebraicTerm) -> Self {
        Self(StoredAlgebraic::Input(Arc::new(value)))
    }
}
impl StoredAlgebraicTerm {
    pub(crate) fn from_root(root: KernelTerm) -> Option<Self> {
        matches!(root.ty(), KernelType::Algebraic(_)).then(|| Self(StoredAlgebraic::Shared(root)))
    }
    pub(crate) fn root(&self) -> Option<&KernelTerm> {
        match &self.0 {
            StoredAlgebraic::Input(_) => None,
            StoredAlgebraic::Shared(root) => Some(root),
        }
    }
    pub(crate) fn into_native_compat(self) -> AlgebraicTerm {
        match self.0 {
            StoredAlgebraic::Input(value) => Arc::unwrap_or_clone(value),
            StoredAlgebraic::Shared(root) => KernelTermExport::default()
                .algebraic(&root)
                .expect("algebraic field output"),
        }
    }
    pub(crate) fn old_form(&self) -> &AlgebraicTerm {
        match &self.0 {
            StoredAlgebraic::Input(value) => value,
            StoredAlgebraic::Shared(root) => root
                .algebraic_native_term()
                .expect("algebraic field output"),
        }
    }
}

/// A native condition input or one retained logical Bool root. Native output
/// reuses the root's existing Boolean argument slot rather than another cache.
#[derive(Clone)]
pub struct StoredConditionTerm(StoredCondition);
#[derive(Clone)]
enum StoredCondition {
    Input(Arc<NativeConditionInput>),
    Shared(KernelTerm),
}
struct NativeConditionInput {
    value: OldConditionTerm,
    connective_key: std::sync::OnceLock<ConditionStorageKey>,
}
impl From<OldConditionTerm> for StoredConditionTerm {
    fn from(value: OldConditionTerm) -> Self {
        let root = match &value {
            OldConditionTerm::Constant(value) => {
                return Self::constant(*value);
            }
            OldConditionTerm::Variable(variable) => {
                return Self(StoredCondition::Shared(KernelTerm::variable(
                    KernelType::Bool,
                    *variable,
                )));
            }
            OldConditionTerm::Overflows {
                format,
                op,
                left,
                right,
            } => Self::written_overflow_root(
                *format,
                *op,
                [left.as_ref(), right.as_ref()].map(MachineOperandView::Old),
            ),
            crate::kernel::integer_comparison_condition!(_, _) => {
                KernelTermImport::default().condition(&value)
            }
            OldConditionTerm::PointerEqual(left, right) => {
                KernelTerm::pointer_equal_raw([left.shared().clone(), right.shared().clone()])
            }
            OldConditionTerm::AddressEqual(left, right) => {
                KernelTerm::address_equal_raw([left.shared().clone(), right.shared().clone()])
            }
            OldConditionTerm::AddressOffsetEqual(left, right) => {
                KernelTerm::address_offset_equal_raw([
                    left.shared().clone(),
                    right.shared().clone(),
                ])
            }
            _ => {
                return Self(StoredCondition::Input(Arc::new(NativeConditionInput {
                    value,
                    connective_key: std::sync::OnceLock::new(),
                })));
            }
        };
        // Old readers can borrow the already-produced condition regardless
        // of whether another verification has requested it before.
        root.retain_old_condition_output(value);
        Self(StoredCondition::Shared(root))
    }
}
/// Exact operands of a stored pointer-domain equality, in written order.
pub(crate) enum PointerEquality<'a> {
    Address(&'a [SharedAddress; 2]),
    Offset(&'a [SharedAddressOffset; 2]),
    Pointer(&'a [SharedPointer; 2]),
}

// A borrowed lookup in the existing native fact map. Both the stored key
// and the query hash and compare through OldConditionTerm's written identity.
trait BorrowedConditionKey {
    fn written_identity(&self) -> ConditionIdentity<'_>;
}
impl BorrowedConditionKey for OldConditionTerm {
    fn written_identity(&self) -> ConditionIdentity<'_> {
        self.identity()
    }
}
impl BorrowedConditionKey for ConditionIdentity<'_> {
    fn written_identity(&self) -> ConditionIdentity<'_> {
        *self
    }
}
impl PartialEq for dyn BorrowedConditionKey + '_ {
    fn eq(&self, other: &Self) -> bool {
        self.written_identity() == other.written_identity()
    }
}
impl Eq for dyn BorrowedConditionKey + '_ {}
impl PartialOrd for dyn BorrowedConditionKey + '_ {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for dyn BorrowedConditionKey + '_ {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.written_identity().cmp(&other.written_identity())
    }
}
impl std::hash::Hash for dyn BorrowedConditionKey + '_ {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.written_identity().hash(state);
    }
}
impl<'a> std::borrow::Borrow<dyn BorrowedConditionKey + 'a> for OldConditionTerm {
    fn borrow(&self) -> &(dyn BorrowedConditionKey + 'a) {
        self
    }
}

impl crate::kernel::fact_collections::FactMap<OldConditionTerm, bool> {
    pub(in crate::kernel) fn literal_value(&self, literal: bool) -> Option<bool> {
        self.get(&ConditionIdentity::Constant(literal) as &dyn BorrowedConditionKey)
            .copied()
    }

    pub(in crate::kernel) fn written_overflow_value(
        &self,
        format: MachineIntegerType,
        op: OverflowOperation,
        left: &OldMachineTerm,
        right: &OldMachineTerm,
    ) -> Option<bool> {
        self.get(&ConditionIdentity::Overflows {
            format,
            op,
            left,
            right,
        } as &dyn BorrowedConditionKey)
            .copied()
    }
}

/// Borrowed operands at interfaces shared with written condition producers.
#[derive(Clone, Copy)]
pub(crate) enum WrittenPointerEquality<'a> {
    Address([&'a Address; 2]),
    Offset([&'a AddressOffset; 2]),
    Pointer([&'a Pointer; 2]),
}

impl<'a> WrittenPointerEquality<'a> {
    pub(crate) fn from_condition(value: &'a OldConditionTerm) -> Option<Self> {
        match value {
            OldConditionTerm::AddressEqual(a, b) => Some(Self::Address([a, b])),
            OldConditionTerm::AddressOffsetEqual(a, b) => Some(Self::Offset([a, b])),
            OldConditionTerm::PointerEqual(a, b) => Some(Self::Pointer([a, b])),
            _ => None,
        }
    }
    fn identity(self) -> ConditionIdentity<'a> {
        match self {
            Self::Address([a, b]) => ConditionIdentity::AddressEqual(a, b),
            Self::Offset([a, b]) => ConditionIdentity::AddressOffsetEqual(a, b),
            Self::Pointer([a, b]) => ConditionIdentity::PointerEqual(a, b),
        }
    }
    fn reversed(self) -> Self {
        match self {
            Self::Address([a, b]) => Self::Address([b, a]),
            Self::Offset([a, b]) => Self::Offset([b, a]),
            Self::Pointer([a, b]) => Self::Pointer([b, a]),
        }
    }

    /// Exact fact lookup uses the same constant folding as the reversed
    /// address and offset constructors. Full pointer equality stays as written.
    pub(crate) fn reversed_exact_value(
        self,
        facts: &crate::kernel::fact_collections::FactMap<OldConditionTerm, bool>,
    ) -> Option<bool> {
        let reversed = self.reversed();
        let constant = match reversed {
            Self::Address([a, b]) => a
                .shared()
                .equality_value(b.shared(), SharedAddressOffset::written_constant),
            Self::Offset([a, b]) => a
                .shared()
                .equality_value(b.shared(), SharedAddressOffset::written_constant),
            Self::Pointer(_) => None,
        };
        let key = constant.map_or_else(|| reversed.identity(), ConditionIdentity::Constant);
        facts.get(&key as &dyn BorrowedConditionKey).copied()
    }

    pub(crate) fn cited_value(
        self,
        facts: &std::collections::HashMap<OldConditionTerm, bool>,
    ) -> Option<bool> {
        let lookup = |pair: Self| {
            facts
                .get(&pair.identity() as &dyn BorrowedConditionKey)
                .copied()
        };
        lookup(self).or_else(|| lookup(self.reversed()))
    }
}

impl PointerEquality<'_> {
    pub(crate) fn with_written<R>(&self, read: impl FnOnce(WrittenPointerEquality<'_>) -> R) -> R {
        match self {
            Self::Address(pair) => read(WrittenPointerEquality::Address(
                pair.each_ref()
                    .map(|a| a.written().expect("written address")),
            )),
            Self::Offset(pair) => {
                read(WrittenPointerEquality::Offset(pair.each_ref().map(|a| {
                    AddressOffset::try_from_ref(a).expect("written offset")
                })))
            }
            Self::Pointer(pair) => {
                let written = pair
                    .each_ref()
                    .map(|p| p.export().expect("written pointer"));
                read(WrittenPointerEquality::Pointer(written.each_ref()))
            }
        }
    }
    pub(crate) fn matches_condition(&self, from: &OldConditionTerm) -> bool {
        WrittenPointerEquality::from_condition(from)
            .is_some_and(|from| self.with_written(|pair| pair.identity() == from.identity()))
    }
    pub(crate) fn is_reflexive(&self) -> bool {
        match self {
            Self::Address([a, b]) => a.syntax_equal(b),
            Self::Offset([a, b]) => a.syntax_equal(b),
            Self::Pointer([a, b]) => a.condition_syntax_equal(b),
        }
    }

    pub(crate) fn mirrored(&self) -> StoredConditionTerm {
        let root = match self {
            Self::Address([a, b]) => KernelTerm::address_equal_raw([b.clone(), a.clone()]),
            Self::Offset([a, b]) => KernelTerm::address_offset_equal_raw([b.clone(), a.clone()]),
            Self::Pointer([a, b]) => KernelTerm::pointer_equal_raw([b.clone(), a.clone()]),
        };
        StoredConditionTerm(StoredCondition::Shared(root))
    }
}
impl StoredConditionTerm {
    pub(crate) fn pointer_equality(&self) -> Option<PointerEquality<'_>> {
        match self.root()?.node() {
            KernelTermNode::AddressEqual { arguments, .. } => {
                Some(PointerEquality::Address(arguments))
            }
            KernelTermNode::AddressOffsetEqual { arguments } => {
                Some(PointerEquality::Offset(arguments))
            }
            KernelTermNode::PointerEqual(pair) => Some(PointerEquality::Pointer(pair.arguments())),
            _ => None,
        }
    }

    /// Logical lowering keeps a reflexive thin, non-null pointer comparison
    /// as written evidence. Both address operands carry the left declaration.
    pub(crate) fn logical_pointer_equal(left: &Pointer, right: &Pointer) -> Self {
        if left == right && !left.is_null() && !left.is_wide() {
            let address = left.address().shared();
            return Self(StoredCondition::Shared(KernelTerm::address_equal_raw([
                address.clone(),
                address.clone(),
            ])));
        }
        Self::pointer_equal(left, right)
    }

    pub(crate) fn algebraic_equal(left: &AlgebraicTerm, right: &AlgebraicTerm) -> Self {
        let mut import = KernelTermImport::for_exact_field_inputs();
        Self(StoredCondition::Shared(KernelTerm::algebraic_equal_raw([
            import.algebraic(left),
            import.algebraic(right),
        ])))
    }

    pub(crate) fn pointer_equal(left: &Pointer, right: &Pointer) -> Self {
        let root = match left.equality_kind(right) {
            PointerEqualityKind::Complete => {
                KernelTerm::pointer_equal_raw([left.shared().clone(), right.shared().clone()])
            }
            PointerEqualityKind::Address => {
                return Self::address_equal(left.address(), right.address());
            }
            PointerEqualityKind::IntegerAddress => KernelTermImport::for_exact_field_inputs()
                .integer_address_equality(
                    MachineIntegerType::Int64,
                    [left.address().shared(), right.address().shared()],
                ),
        };
        Self(StoredCondition::Shared(root))
    }

    /// Construct an address comparison from written operands, preserving the
    /// producer's block payloads when the comparison stays symbolic.
    pub(crate) fn address_equal(left: &Address, right: &Address) -> Self {
        Self(StoredCondition::Shared(KernelTerm::address_equal_with(
            [left.shared().clone(), right.shared().clone()],
            SharedAddressOffset::written_constant,
        )))
    }

    /// Preserve operand order and spelling for exact overflow premises.
    pub(crate) fn written_overflow(
        format: MachineIntegerType,
        op: OverflowOperation,
        operands: [MachineOperandView<'_>; 2],
    ) -> Self {
        Self(StoredCondition::Shared(Self::written_overflow_root(
            format, op, operands,
        )))
    }

    fn written_overflow_root(
        format: MachineIntegerType,
        op: OverflowOperation,
        operands: [MachineOperandView<'_>; 2],
    ) -> KernelTerm {
        let roots = operands.map(|operand| match operand {
            MachineOperandView::Shared(root) => root.clone(),
            MachineOperandView::Old(
                written @ (OldMachineTerm::Constant { .. } | OldMachineTerm::Variable(_)),
            ) => KernelTermImport::for_exact_field_inputs().machine(format, written),
            MachineOperandView::Old(written) => {
                KernelTerm::written_machine_operand(format, written)
            }
        });
        KernelTerm::boolean_overflow_raw(format, op, roots)
    }

    /// A signed count bound folds two literal words and keeps the written
    /// direction for exact fact lookup otherwise.
    pub(in crate::kernel) fn signed_int32_at_least(
        left: &OldMachineTerm,
        right: &OldMachineTerm,
    ) -> Self {
        let format = MachineIntegerType::Int32;
        let mut import = KernelTermImport::for_exact_field_inputs();
        let operands = [left, right].map(|operand| import.machine(format, operand));
        Self::from_root(KernelTerm::boolean_comparison(
            format,
            CompareRelation::GreaterEqual,
            operands,
        ))
        .expect("signed int32 comparison")
    }

    pub(crate) fn constant(value: bool) -> Self {
        Self(StoredCondition::Shared(KernelTerm::boolean_literal(value)))
    }

    pub(crate) fn kernel_operand(&self) -> KernelTerm {
        self.root()
            .cloned()
            .unwrap_or_else(|| KernelTermImport::default().condition(self.old_form()))
    }

    pub(crate) fn operand_view(&self) -> BooleanOperandView<'_> {
        match self.root() {
            Some(root) => BooleanOperandView::Shared(root),
            None => BooleanOperandView::Native(self.old_form()),
        }
    }
    pub(crate) fn from_root(root: KernelTerm) -> Option<Self> {
        (root.ty() == &KernelType::Bool).then(|| Self(StoredCondition::Shared(root)))
    }
    /// Already-evaluated scalar conditions produced by the loop guard checker.
    pub(crate) fn from_minted(value: OldConditionTerm) -> Self {
        let root = KernelTermImport::for_exact_field_inputs().condition(&value);
        root.retain_old_condition_output(value);
        Self::from_root(root).expect("logical condition")
    }
    pub(crate) fn root(&self) -> Option<&KernelTerm> {
        match &self.0 {
            StoredCondition::Input(_) => None,
            StoredCondition::Shared(root) => Some(root),
        }
    }
    pub(crate) fn old_form(&self) -> &OldConditionTerm {
        match &self.0 {
            StoredCondition::Input(input) => &input.value,
            StoredCondition::Shared(root) => {
                if let KernelTermNode::BoolLiteral(value) = root.node() {
                    return if *value {
                        &OldConditionTerm::Constant(true)
                    } else {
                        &OldConditionTerm::Constant(false)
                    };
                }
                let ProgramValue::Bool(OldMachineTerm::BoolCast { value, .. }) =
                    root.old_boolean_value().expect("logical Bool output")
                else {
                    unreachable!("condition output");
                };
                value
            }
        }
    }
}

/// Retained contract displacement. Opaque indices retain their exact
/// carrier in the corresponding typed machine input.
#[derive(Clone)]
pub struct StoredPointerOffset(Arc<PointerOffsetStorage>);

struct PointerOffsetStorage {
    key: crate::kernel::execution_value::storage_keys::OffsetKey,
    value: PointerOffsetValue,
}

struct PointerOffsetValue {
    root: SharedAddressOffset,
    native: OnceLock<AddressOffset>,
}

impl From<AddressOffset> for StoredPointerOffset {
    fn from(written: AddressOffset) -> Self {
        Self::from_rewritten_root(written.into_shared())
    }
}

impl StoredPointerOffset {
    pub(in crate::kernel) fn from_rewritten_root(root: SharedAddressOffset) -> Self {
        let key = crate::kernel::execution_value::storage_keys::offset_for_root(&root);
        Self(Arc::new(PointerOffsetStorage {
            key,
            value: PointerOffsetValue {
                root,
                native: OnceLock::new(),
            },
        }))
    }

    #[cfg(test)]
    pub(crate) fn has_cached_native_offset(&self) -> bool {
        self.0.value.native.get().is_some()
    }

    pub(in crate::kernel) fn from_written(written: &AddressOffset) -> Self {
        Self::from_rewritten_root(written.shared().clone())
    }

    pub(crate) fn old_form(&self) -> &AddressOffset {
        let PointerOffsetValue { root, native } = &self.0.value;
        native.get_or_init(|| AddressOffset::try_from_shared(root.clone()).expect("stored offset"))
    }

    pub(crate) fn root(&self) -> &SharedAddressOffset {
        &self.0.value.root
    }
}

impl std::fmt::Debug for StoredProgramValue {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.old_form().fmt(f)
    }
}
impl PartialEq for StoredProgramValue {
    fn eq(&self, other: &Self) -> bool {
        self.cmp(other).is_eq()
    }
}
impl Eq for StoredProgramValue {}
impl PartialOrd for StoredProgramValue {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for StoredProgramValue {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.0.cmp(&other.0)
    }
}
impl std::hash::Hash for StoredProgramValue {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.old_form().hash(state);
    }
}
impl std::fmt::Debug for StoredIntegerTerm {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.old_form().fmt(f)
    }
}
impl PartialEq for StoredIntegerTerm {
    fn eq(&self, other: &Self) -> bool {
        if let (Some(left), Some(right)) = (self.root(), other.root()) {
            if left == right {
                return true;
            }
            if let (Some(left), Some(right)) = (
                left.retained_integer_exact_id(),
                right.retained_integer_exact_id(),
            ) {
                return left == right;
            }
        }
        self.exact_key() == other.exact_key()
    }
}
impl Eq for StoredIntegerTerm {}
impl PartialOrd for StoredIntegerTerm {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for StoredIntegerTerm {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        if matches!((self.root(), other.root()), (Some(left), Some(right)) if left == right) {
            std::cmp::Ordering::Equal
        } else {
            self.exact_key().cmp(&other.exact_key())
        }
    }
}
impl std::hash::Hash for StoredIntegerTerm {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.exact_key().hash(state);
    }
}
impl std::fmt::Debug for StoredAlgebraicTerm {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.old_form().fmt(f)
    }
}
impl PartialEq for StoredAlgebraicTerm {
    fn eq(&self, other: &Self) -> bool {
        self.cmp(other).is_eq()
    }
}
impl Eq for StoredAlgebraicTerm {}
impl PartialOrd for StoredAlgebraicTerm {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for StoredAlgebraicTerm {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        if let (Some(left), Some(right)) = (self.root(), other.root()) {
            if left == right {
                return std::cmp::Ordering::Equal;
            }
            if matches!(left.node(), KernelTermNode::Constructor(_))
                && matches!(right.node(), KernelTermNode::Constructor(_))
            {
                use crate::kernel::execution_value::storage_keys::algebraic_for_root;
                return algebraic_for_root(left).cmp(&algebraic_for_root(right));
            }
        }
        self.old_form().cmp(other.old_form())
    }
}
impl std::hash::Hash for StoredAlgebraicTerm {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.old_form().hash(state);
    }
}
impl std::fmt::Debug for StoredConditionTerm {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.old_form().fmt(f)
    }
}
impl StoredConditionTerm {
    /// The same ordering and hash as the written condition. Address comparisons
    /// already hold the operands that the identity borrows.
    fn with_atomic_identity<R>(&self, read: impl FnOnce(ConditionIdentity<'_>) -> R) -> R {
        let operand = self.operand_view();
        if let Some(value) = operand.constant() {
            return read(ConditionIdentity::Constant(value));
        }
        if let Some(variable) = operand.variable() {
            return read(ConditionIdentity::Variable(variable));
        }
        if let Some([left, right]) = operand.written_algebraic_equality() {
            return read(ConditionIdentity::AlgebraicEqual(left, right));
        }
        match self.pointer_equality() {
            Some(pair) => pair.with_written(|written| read(written.identity())),
            None => read(self.old_form().identity()),
        }
    }

    fn connective_key(&self) -> Option<ConditionStorageKey> {
        match &self.0 {
            StoredCondition::Shared(root)
                if matches!(
                    root.node(),
                    KernelTermNode::BoolIf { .. } | KernelTermNode::BoolEqual { .. }
                ) =>
            {
                Some(root.condition_storage_key())
            }
            StoredCondition::Input(input)
                if matches!(
                    input.value,
                    OldConditionTerm::BoolIf { .. } | OldConditionTerm::BoolEqual(..)
                ) =>
            {
                Some(
                    input
                        .connective_key
                        .get_or_init(|| ConditionStorageKey::native(&input.value))
                        .clone(),
                )
            }
            _ => None,
        }
    }
}
impl PartialEq for StoredConditionTerm {
    fn eq(&self, other: &Self) -> bool {
        self.cmp(other).is_eq()
    }
}
impl Eq for StoredConditionTerm {}
impl PartialOrd for StoredConditionTerm {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for StoredConditionTerm {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        use std::cmp::Ordering;
        if matches!((self.root(), other.root()), (Some(left), Some(right)) if left == right) {
            return Ordering::Equal;
        }
        match (self.connective_key(), other.connective_key()) {
            (Some(left), Some(right)) => left.cmp(&right),
            // BoolIf and BoolEqual follow all atomic conditions in OldConditionTerm.
            (Some(_), None) => Ordering::Greater,
            (None, Some(_)) => Ordering::Less,
            (None, None) => self
                .with_atomic_identity(|left| other.with_atomic_identity(|right| left.cmp(&right))),
        }
    }
}
impl std::hash::Hash for StoredConditionTerm {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        if let Some(key) = self.connective_key() {
            key.hash(state);
        } else {
            self.with_atomic_identity(|value| value.hash(state));
        }
    }
}
impl std::fmt::Debug for StoredPointerOffset {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.old_form().fmt(f)
    }
}
impl PartialEq for StoredPointerOffset {
    fn eq(&self, other: &Self) -> bool {
        self.0.key == other.0.key
    }
}
impl Eq for StoredPointerOffset {}
impl PartialOrd for StoredPointerOffset {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for StoredPointerOffset {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.0.key.cmp(&other.0.key)
    }
}
impl std::hash::Hash for StoredPointerOffset {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.0.key.hash(state);
    }
}

#[cfg(test)]
mod protocol_value_tests {
    use super::*;
    use std::hash::{Hash, Hasher};
    fn hash(value: &impl Hash) -> u64 {
        let mut h = std::collections::hash_map::DefaultHasher::new();
        value.hash(&mut h);
        h.finish()
    }
    #[test]
    fn mathematical_integer_descriptor_identity_uses_retained_children() {
        let _session = crate::kernel::VerificationSession::enter();
        let variable = Variable(87654011);
        let native = IntegerTerm::Add(
            IntegerTerm::Variable(variable).into(),
            IntegerTerm::constant_i64(87654012).into(),
        );
        let root = KernelTerm::integer_operation(
            KernelIntegerOperator::Add,
            vec![
                KernelTerm::variable(KernelType::Integer, variable),
                KernelTerm::integer_literal(87654012.into()),
            ],
        )
        .unwrap();
        let input = StoredIntegerTerm::from(native.clone());
        let retained = StoredIntegerTerm::from_root(root.clone()).unwrap();
        assert_eq!(input, retained);
        assert_eq!(input.cmp(&retained), std::cmp::Ordering::Equal);
        assert_eq!(hash(&input), hash(&native));
        assert_eq!(hash(&retained), hash(&native));
        assert!(!root.has_cached_native_argument());
    }

    #[test]
    fn retained_contract_offset_preserves_written_identity_after_input_drops() {
        let _session = crate::kernel::VerificationSession::enter();
        let first = AddressOffset::scaled_int32_node(OldMachineTerm::Variable(Variable(998981)), 4);
        let second =
            AddressOffset::scaled_int64_node(OldMachineTerm::Variable(Variable(998982)), 8, true);
        let input = AddressOffset::raw_add(first, second);
        let expected_debug = format!("{input:?}");
        let stored = StoredPointerOffset::from(input);
        let _ = hash(&stored);
        assert!(!stored.has_cached_native_offset());
        assert_eq!(format!("{stored:?}"), expected_debug);

        let same = StoredPointerOffset::from(stored.old_form().clone());
        let distinct = StoredPointerOffset::from(AddressOffset::raw_add(
            AddressOffset::constant(0),
            stored.old_form().clone(),
        ));
        assert_eq!(stored, same);
        assert_ne!(stored, distinct);
        assert_eq!(
            stored.cmp(&distinct),
            stored.old_form().cmp(distinct.old_form()),
        );
        assert_eq!(hash(&stored), hash(&same));
    }

    #[test]
    fn retained_contract_offset_keeps_opaque_index_carrier() {
        let _session = crate::kernel::VerificationSession::enter();
        let index = SharedMachineIntegerTerm::index(
            MachineIntegerType::Int32,
            OldMachineTerm::PureFunctionApplication {
                name: "opaque_displacement".into(),
                arguments: vec![OldMachineTerm::Variable(Variable(998985))],
            },
        );
        let source = AddressOffset::int32_scaled(index.clone(), 4);
        let stored = StoredPointerOffset::from_written(&source.clone());
        let root = stored.root();
        let first = KernelAddressOffset::index_key(root.node().index().unwrap()).unwrap();
        assert!(std::ptr::eq(
            first.structural_value(),
            index.structural_value()
        ));
        assert_eq!(first, index);
        let equal = StoredPointerOffset::from(AddressOffset::int32_scaled(
            SharedMachineIntegerTerm::index(index.ty(), index.structural_value().clone()),
            4,
        ));
        assert_ne!(stored.root(), equal.root());
        assert_eq!(stored, equal);
        assert_eq!(stored.cmp(&equal), std::cmp::Ordering::Equal);
        // A leaf key hashes as the written offset it stores.
        let written = source.clone();
        assert_eq!(hash(&stored), hash(&written));
        assert_eq!(hash(&equal), hash(&written));
        assert!(!stored.has_cached_native_offset());
        assert!(!equal.has_cached_native_offset());
        assert_eq!(stored.old_form(), &source);
    }

    #[test]
    fn protocol_native_values_keep_exact_identity_and_scalar_conditions_round_trip() {
        let _session = crate::kernel::VerificationSession::enter();
        let values = [
            ProgramValue::Int32(OldMachineTerm::constant(7)),
            ProgramValue::UInt32(OldMachineTerm::uint32_constant(7)),
            ProgramValue::Bool(OldMachineTerm::constant(2)),
            ProgramValue::Float32(OldMachineTerm::uint32_constant(0x7fc00123)),
            ProgramValue::Float64(OldMachineTerm::uint64_constant(0x8000000000000000)),
        ];
        for value in &values {
            let stored = StoredProgramValue::from(value.clone());
            assert_eq!(hash(&stored), hash(value));
            assert_eq!(format!("{stored:?}"), format!("{value:?}"));
            for other in &values {
                let other_stored = StoredProgramValue::from(other.clone());
                assert_eq!(stored == other_stored, value == other);
                assert_eq!(stored.cmp(&other_stored), value.cmp(other));
            }
        }
        let conditions = [
            OldConditionTerm::Constant(false),
            OldConditionTerm::Constant(true),
            OldConditionTerm::Variable(Variable(10993642)),
            OldConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::Equal,
                left: Box::new(OldMachineTerm::Variable(Variable(10993643))),
                right: Box::new(OldMachineTerm::constant(1)),
            },
            OldConditionTerm::BoolEqual(
                Box::new(OldConditionTerm::Compare {
                    format: MachineIntegerType::UInt32,
                    relation: CompareRelation::LessThan,
                    left: Box::new(OldMachineTerm::Variable(Variable(10993644))),
                    right: Box::new(OldMachineTerm::uint32_constant(1)),
                }),
                Box::new(OldConditionTerm::Constant(false)),
            ),
        ];
        for value in &conditions {
            for stored in [
                StoredConditionTerm::from(value.clone()),
                StoredConditionTerm::from_minted(value.clone()),
            ] {
                if matches!(
                    value,
                    OldConditionTerm::Constant(_) | OldConditionTerm::Variable(_)
                ) {
                    let root = KernelTermImport::default().condition(value);
                    assert_eq!(stored.root(), Some(&root));
                    assert_eq!(hash(&stored), hash(value));
                }
                assert_eq!(stored.old_form(), value);
                assert_eq!(
                    hash(&stored),
                    hash(&StoredConditionTerm::from(value.clone()))
                );
                assert_eq!(format!("{stored:?}"), format!("{value:?}"));
                for other in &conditions {
                    let other_stored = StoredConditionTerm::from(other.clone());
                    assert_eq!(stored == other_stored, value == other);
                    assert_eq!(stored.cmp(&other_stored), value.cmp(other));
                }
            }
        }
    }
    #[test]
    fn retained_program_values_compare_pointers_and_float_trees_without_export() {
        use crate::kernel::effective_type::{CAccessClass, CScalarClass};

        let _session = crate::kernel::VerificationSession::enter();
        let pointer = Pointer::new(
            Address::symbolic(Variable(998991)),
            ProgramType::Int32Pointer,
        );
        let pointers = [CScalarClass::Int, CScalarClass::Char].map(|class| {
            pointer
                .clone()
                .with_declared_object_class(Some(CAccessClass::Scalar(class)))
        });
        let [left, right] = pointers.each_ref().map(|pointer| {
            let root = KernelTerm::shared_pointer_value(pointer.shared().clone());
            StoredProgramValue::from(ExecutionValue::Shared(root))
        });
        assert_ne!(left.root(), right.root());
        assert_eq!(left == right, pointers[0] == pointers[1]);
        assert_eq!(left.cmp(&right), pointers[0].cmp(&pointers[1]));
        assert!(!left.root().unwrap().has_cached_native_argument());
        assert!(!right.root().unwrap().has_cached_native_argument());

        let floats = [0x3f800000, 0x40000000].map(|bits| {
            OldMachineTerm::Float32Negate(Box::new(OldMachineTerm::uint32_constant(bits)))
        });
        let [left, right] = floats.each_ref().map(|term| {
            let root = KernelTermImport::default().float(KernelFloatType::Float32, term);
            StoredProgramValue::from(ExecutionValue::Shared(root))
        });
        assert!(left != right);
        assert_eq!(left.cmp(&right), floats[0].cmp(&floats[1]));
        assert!(!left.root().unwrap().has_cached_native_argument());
        assert!(!right.root().unwrap().has_cached_native_argument());
    }

    #[test]
    fn retained_algebraic_ordering_keeps_constructor_fields_unboxed() {
        let _session = crate::kernel::VerificationSession::enter();
        let constructors = [1, 2].map(|value| {
            let mut constructor =
                crate::kernel::KernelMatch::test_scrutinee(vec![AlgebraicValueType::Integer]);
            constructor.node = AlgebraicTermNode::Constructor {
                variant: "Arm".into(),
                fields: vec![AlgebraicValue::Integer(IntegerTerm::constant_i64(value))],
            };
            constructor
        });
        let [left, right] = constructors.each_ref().map(|value| {
            StoredAlgebraicTerm::from_root(KernelTermImport::default().algebraic(value)).unwrap()
        });
        assert!(left != right);
        assert_eq!(left.cmp(&right), constructors[0].cmp(&constructors[1]));
        assert!(!left.root().unwrap().has_cached_native_argument());
        assert!(!right.root().unwrap().has_cached_native_argument());
    }

    #[test]
    fn reversed_pointer_fact_lookup_preserves_folded_and_written_keys() {
        let a = Address::symbolic(Variable(982861));
        let b = Address::symbolic(Variable(982862));
        let p = Pointer::new(a.clone(), ProgramType::Int32Pointer);
        let q = Pointer::new(b.clone(), ProgramType::Int32Pointer);
        let x = AddressOffset::variable(Variable(982863));
        let y = AddressOffset::constant(3);
        let z = AddressOffset::constant(4);
        for (pair, expected) in [
            (
                WrittenPointerEquality::Address([&a, &b]),
                OldConditionTerm::address_equal(b.clone(), a.clone()),
            ),
            (
                WrittenPointerEquality::Address([&a, &a]),
                OldConditionTerm::Constant(true),
            ),
            (
                WrittenPointerEquality::Offset([&x, &y]),
                OldConditionTerm::address_offset_equal(y.clone(), x.clone()),
            ),
            (
                WrittenPointerEquality::Offset([&y, &z]),
                OldConditionTerm::Constant(false),
            ),
            (
                WrittenPointerEquality::Pointer([&p, &q]),
                OldConditionTerm::PointerEqual(Box::new(q.clone()), Box::new(p.clone())),
            ),
            (
                WrittenPointerEquality::Pointer([&p, &p]),
                OldConditionTerm::PointerEqual(Box::new(p.clone()), Box::new(p.clone())),
            ),
        ] {
            assert_eq!(pair.reversed_exact_value(&Default::default()), None);
            for truth in [false, true] {
                let facts = [(expected.clone(), truth)].into_iter().collect();
                assert_eq!(pair.reversed_exact_value(&facts), Some(truth));
            }
        }
    }

    #[test]
    fn shared_address_comparisons_keep_written_order_and_hash() {
        let _session = crate::kernel::VerificationSession::enter();
        let a = Address::symbolic(Variable(982866));
        let b = Address::symbolic(Variable(982867));
        let x = AddressOffset::variable(Variable(982868));
        let y = AddressOffset::constant(7);
        let written = [
            OldConditionTerm::Constant(false),
            OldConditionTerm::AddressEqual(Box::new(a.clone()), Box::new(b.clone())),
            OldConditionTerm::AddressEqual(Box::new(b), Box::new(a)),
            OldConditionTerm::AddressOffsetEqual(Box::new(x.clone()), Box::new(y.clone())),
            OldConditionTerm::AddressOffsetEqual(Box::new(y), Box::new(x)),
        ];
        let stored = written.each_ref().map(|value| {
            StoredConditionTerm::from_root(KernelTermImport::default().condition(value)).unwrap()
        });
        for (i, left) in stored.iter().enumerate() {
            assert_eq!(hash(left), hash(&written[i]));
            for (j, right) in stored.iter().enumerate() {
                assert_eq!(left.cmp(right), written[i].cmp(&written[j]));
            }
        }
        assert!(
            stored
                .iter()
                .all(|condition| !condition.root().unwrap().has_cached_native_argument())
        );
    }

    #[test]
    fn retained_condition_ordering_keeps_connectives_unboxed() {
        let _session = crate::kernel::VerificationSession::enter();
        let input = |variable| OldConditionTerm::BoolIf {
            condition: Box::new(OldConditionTerm::Variable(variable)),
            then_condition: Box::new(OldConditionTerm::Constant(true)),
            else_condition: Box::new(OldConditionTerm::Constant(false)),
        };
        let values = [input(Variable(10993742)), input(Variable(10993743))];
        let roots = values
            .each_ref()
            .map(|condition| KernelTermImport::default().condition(condition));
        let [left, right] = roots
            .each_ref()
            .map(|root| StoredConditionTerm::from_root(root.clone()).unwrap());
        assert_ne!(left, right);
        assert_eq!(left.cmp(&right), values[0].cmp(&values[1]));
        let native = StoredConditionTerm::from(values[0].clone());
        assert_eq!(left, native);
        assert_eq!(hash(&left), hash(&native));
        assert!(roots.iter().all(|root| !root.has_cached_native_argument()));
    }

    #[test]
    fn minted_condition_native_views_reuse_the_produced_output_without_exports() {
        let _session = crate::kernel::VerificationSession::enter();
        let value = OldMachineTerm::if_then_else(
            OldConditionTerm::Variable(Variable(10993740)),
            OldMachineTerm::Variable(Variable(10993741)),
            OldMachineTerm::constant(3),
        );
        let native = OldConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::LessEqual,
            left: Box::new(value),
            right: Box::new(OldMachineTerm::constant(9)),
        };
        let exports = KernelTermExport::machine_export_count();
        let stored = StoredConditionTerm::from_minted(native.clone());
        assert!(stored.root().is_some());
        assert_eq!(stored.old_form(), &native);
        assert_eq!(format!("{stored:?}"), format!("{native:?}"));
        let view = BooleanOperandView::Shared(stored.root().unwrap()).native();
        assert!(matches!(&view, std::borrow::Cow::Borrowed(_)));
        assert_eq!(view.as_ref(), &native);
        assert_eq!(KernelTermExport::machine_export_count(), exports);
    }

    #[test]
    fn condition_proposition_storage_keeps_roots_and_native_fact_identity() {
        let _session = crate::kernel::VerificationSession::enter();
        for condition in [
            OldConditionTerm::Constant(false),
            OldConditionTerm::Constant(true),
            OldConditionTerm::Variable(Variable(10993711)),
            OldConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::LessThan,
                left: Box::new(OldMachineTerm::Variable(Variable(10993712))),
                right: Box::new(OldMachineTerm::constant(9)),
            },
        ] {
            let root = KernelTermImport::for_exact_field_inputs().condition(&condition);
            for truth in [false, true] {
                let native = Proposition::condition_is(condition.clone(), truth);
                let shared = Proposition::condition_is(
                    StoredConditionTerm::from_root(root.clone()).unwrap(),
                    truth,
                );
                let Proposition::ConditionIs(stored, actual_truth) = shared.clone() else {
                    unreachable!();
                };
                assert_eq!(stored.root(), Some(&root));
                assert_eq!(actual_truth, truth);
                assert_eq!(shared, native);
                assert_eq!(shared.cmp(&native), std::cmp::Ordering::Equal);
                assert_eq!(hash(&shared), hash(&native));
                assert_eq!(format!("{shared:?}"), format!("{native:?}"));
                assert_eq!(shared.old_condition(), native.old_condition());
            }
        }
    }

    #[test]
    fn condition_proposition_visitors_keep_shared_substitution_and_native_scope() {
        let _session = crate::kernel::VerificationSession::enter();
        let variable = Variable(10993713);
        let condition = OldConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::Equal,
            left: Box::new(OldMachineTerm::Variable(variable)),
            right: Box::new(OldMachineTerm::constant(3)),
        };
        let root = KernelTermImport::for_exact_field_inputs().condition(&condition);
        let native = Proposition::condition_is(condition, false);
        let shared =
            Proposition::condition_is(StoredConditionTerm::from_root(root).unwrap(), false);
        for capture in [false, true] {
            let mut expected = Default::default();
            let mut actual = Default::default();
            if capture {
                crate::kernel::reasoning::collect_proposition_capture_variables(
                    &native,
                    &mut expected,
                );
                crate::kernel::reasoning::collect_proposition_capture_variables(
                    &shared,
                    &mut actual,
                );
            } else {
                crate::kernel::reasoning::collect_proposition_bitvector_variables(
                    &native,
                    &mut expected,
                );
                crate::kernel::reasoning::collect_proposition_bitvector_variables(
                    &shared,
                    &mut actual,
                );
            }
            assert_eq!(actual, expected);
            assert!(actual.contains(&variable));
        }
        let replacement = OldMachineTerm::Variable(Variable(10993714));
        let expected = crate::kernel::reasoning::substitute_bitvector_variable_in_proposition(
            &native,
            variable,
            &replacement,
        );
        let actual = crate::kernel::reasoning::substitute_bitvector_variable_in_proposition(
            &shared,
            variable,
            &replacement,
        );
        let Proposition::ConditionIs(stored, _) = &actual else {
            unreachable!();
        };
        assert!(stored.root().is_some());
        assert_eq!(actual, expected);
    }

    mod scaling_tests {
        use super::*;
        include!("../../scaling_tests/kernel/primitives/descriptor_values.rs");
    }
}

// Selected native DTO view for existing output assertions. Production stores
// and value visitors retain their common operands.
#[cfg(test)]
impl ExpressionOutcome<StoredProgramValue> {
    pub(crate) fn old_form(&self) -> ExpressionOutcome {
        self.clone().map_value(Into::into)
    }
}

#[cfg(test)]
mod proposition_outcome_tests {
    use super::*;
    #[test]
    fn expression_theorem_output_keeps_the_evaluators_common_root() {
        let _session = crate::kernel::VerificationSession::enter();
        let root =
            KernelTerm::variable(KernelType::Program(ProgramType::Int32), Variable(10993661));
        let state = ExecutionState::new().with_retained_local("result", root.clone().into());
        let exports = KernelTermExport::machine_export_count();
        let theorem = crate::kernel::prove_program_expression_evaluation(
            state,
            ProgramExpression::Variable("result".into()),
        )
        .unwrap();
        let Proposition::ProgramExpressionEvaluates {
            outcome: ExpressionOutcome::Value(value),
            ..
        } = theorem.proposition()
        else {
            panic!("value");
        };
        assert_eq!(value.root(), Some(&root));
        assert_eq!(KernelTermExport::machine_export_count(), exports);
    }
}

#[cfg(test)]
mod loadable_count_tests {
    use super::*;
    use std::hash::{Hash, Hasher};
    #[test]
    fn loadable_count_inputs_keep_exact_native_format_and_hash() {
        let _session = crate::kernel::VerificationSession::enter();
        let debug = |value: &dyn std::fmt::Debug| format!("{value:?}");
        for wide in [false, true] {
            for bytes in [
                OldMachineTerm::constant(7),
                OldMachineTerm::uint32_constant(7),
                OldMachineTerm::uint64_constant(7),
                OldMachineTerm::Variable(Variable(10993681)),
            ] {
                let stored = StoredMachineTerm::new(
                    if wide {
                        MachineIntegerType::UInt64
                    } else {
                        MachineIntegerType::Int32
                    },
                    bytes.clone(),
                );
                let fact = Proposition::MemoryLoadable {
                    point: Default::default(),
                    memory: SymbolicMemory::new(),
                    base: Address::symbolic(Variable(10993682)),
                    bytes: stored,
                    wide,
                };
                let Proposition::MemoryLoadable {
                    bytes: stored,
                    wide: actual,
                    ..
                } = &fact
                else {
                    unreachable!()
                };
                assert_eq!(*actual, wide);
                assert_eq!(stored.old_form(), &bytes);
                assert_eq!(debug(stored), debug(&bytes));
                let mut a = std::collections::hash_map::DefaultHasher::new();
                let mut b = std::collections::hash_map::DefaultHasher::new();
                stored.hash(&mut a);
                bytes.hash(&mut b);
                assert_eq!(a.finish(), b.finish());
            }
        }
    }
}

#[cfg(test)]
mod term_payload_contract_tests {
    use super::*;
    use crate::kernel::VerificationSession;
    use std::hash::{Hash, Hasher};

    fn hash(value: &impl Hash) -> u64 {
        let mut state = std::collections::hash_map::DefaultHasher::new();
        value.hash(&mut state);
        state.finish()
    }

    fn algebraic(pointer: Pointer) -> AlgebraicTerm {
        let mut value = KernelMatch::test_scrutinee(vec![AlgebraicValueType::Program(
            ProgramType::Int32Pointer,
        )]);
        value.node = AlgebraicTermNode::Constructor {
            variant: "Arm".into(),
            fields: vec![AlgebraicValue::Program(ProgramValue::Pointer(pointer))],
        };
        value
    }

    #[test]
    fn integer_and_algebraic_carriers_preserve_exact_native_identity() {
        let _session = VerificationSession::enter();
        let integers = [
            IntegerTerm::constant_i64(7),
            IntegerTerm::Variable(Variable(991700)),
            IntegerTerm::Add(
                IntegerTerm::Variable(Variable(991700)).into(),
                IntegerTerm::constant_i64(0).into(),
            ),
        ];
        for value in &integers {
            let stored = StoredIntegerTerm::from(value.clone());
            assert!(
                stored
                    .root()
                    .is_some_and(KernelTerm::is_mathematical_integer)
            );
            assert_eq!(stored.old_form(), value);
            assert_eq!(hash(&stored), hash(value));
            assert_eq!(format!("{stored:?}"), format!("{value:?}"));
            for other in &integers {
                let other_stored = StoredIntegerTerm::from(other.clone());
                assert_eq!(stored == other_stored, value == other);
                assert_eq!(stored.cmp(&other_stored), value.cmp(other));
            }
            let retained = StoredIntegerTerm::from_root(
                KernelTermImport::for_exact_field_inputs().integer(&value.clone().into()),
            )
            .unwrap();
            assert_eq!(retained.old_form(), value);
            assert_eq!(retained, stored);
            assert_eq!(hash(&retained), hash(value));
            assert_eq!(stored.into_native_compat(), *value);
        }
        let pointer = Pointer::new(
            Address::symbolic(Variable(991701)),
            ProgramType::Int32Pointer,
        );
        let values = [
            algebraic(pointer.clone()),
            algebraic(pointer.with_declared_object_class(Some(
                crate::kernel::effective_type::CAccessClass::Scalar(
                    crate::kernel::effective_type::CScalarClass::Int,
                ),
            ))),
        ];
        for value in &values {
            let input = StoredAlgebraicTerm::from(value.clone());
            let root = KernelTermImport::for_exact_field_inputs().algebraic(value);
            let retained = StoredAlgebraicTerm::from_root(root).unwrap();
            assert!(input.root().is_none());
            for stored in [&input, &retained] {
                assert_eq!(stored.old_form(), value);
                assert_eq!(format!("{stored:?}"), format!("{value:?}"));
                assert_eq!(hash(stored), hash(value));
                for other in &values {
                    let other = StoredAlgebraicTerm::from(other.clone());
                    assert_eq!(stored == &other, value == other.old_form());
                    assert_eq!(stored.cmp(&other), value.cmp(other.old_form()));
                }
            }
            let pointer = |value: &AlgebraicTerm| {
                let AlgebraicTermNode::Constructor { fields, .. } = &value.node else {
                    unreachable!()
                };
                let AlgebraicValue::Program(ProgramValue::Pointer(pointer)) = &fields[0] else {
                    unreachable!()
                };
                pointer.object_class()
            };
            assert_eq!(pointer(retained.old_form()), pointer(value));
        }
    }

    #[test]
    fn machine_descriptor_admission_preserves_word32_format_and_rejects_nonmachine_sorts() {
        let _session = VerificationSession::enter();
        for format in [MachineIntegerType::Int32, MachineIntegerType::UInt32] {
            let variables = [Variable(991710), Variable(991711)];
            let root = KernelTerm::arithmetic_binary(
                format,
                MachineBinaryOp::Add,
                variables.map(|variable| {
                    KernelTerm::variable(KernelType::Program(format.program_type()), variable)
                }),
            )
            .unwrap();
            let stored =
                StoredMachineTerm::from_value(ExecutionValue::Shared(root.clone())).unwrap();
            let exports = KernelTermExport::machine_export_count();
            assert_eq!(stored.clone().root().map(KernelTerm::id), Some(root.id()));
            assert!(!root.has_cached_native_argument());
            assert_eq!(KernelTermExport::machine_export_count(), exports);
            let native = OldMachineTerm::Binary {
                format,
                op: MachineBinaryOp::Add,
                left: Box::new(OldMachineTerm::Variable(variables[0])),
                right: Box::new(OldMachineTerm::Variable(variables[1])),
            };
            let input = StoredMachineTerm::from(native.clone());
            assert_eq!(stored.old_form(), &native);
            assert_eq!(stored, input);
            assert_eq!(hash(&stored), hash(&native));
        }
        for ty in [KernelType::Bool, KernelType::Program(ProgramType::Float32)] {
            let root = KernelTerm::variable(ty, Variable(991712));
            assert!(StoredMachineTerm::from_value(ExecutionValue::Shared(root.clone())).is_none());
            assert!(!root.has_cached_native_argument());
        }
    }

    #[test]
    fn retained_and_native_payload_clones_keep_growing_prefixes_unmaterialized() {
        let _session = VerificationSession::enter();
        let ty = KernelMatch::test_scrutinee(Vec::new()).algebraic_type;
        for size in [16, 64, 256] {
            let mut integer = KernelTerm::variable(KernelType::Integer, Variable(991720));
            let mut algebraic =
                KernelTerm::variable(KernelType::Algebraic(ty.clone()), Variable(991721));
            for _ in 0..size {
                integer = KernelTerm::integer_operation(
                    KernelIntegerOperator::Add,
                    vec![integer.clone(), integer],
                )
                .unwrap();
                algebraic = KernelTerm::algebraic_call(
                    ty.clone(),
                    "stored_shared_dag".into(),
                    vec![(algebraic.clone(), None), (algebraic, None)],
                );
            }
            let exports = (
                KernelTermExport::machine_export_count(),
                KernelTermExport::algebraic_export_count(),
            );
            let integers = StoredIntegerTerm::from_root(integer.clone()).unwrap();
            let algebraics = StoredAlgebraicTerm::from_root(algebraic.clone()).unwrap();
            for _ in 0..32 {
                assert_eq!(
                    integers.clone().root().map(KernelTerm::id),
                    Some(integer.id())
                );
                assert_eq!(
                    algebraics.clone().root().map(KernelTerm::id),
                    Some(algebraic.id())
                );
                assert!(!integer.has_cached_native_argument());
                assert!(!algebraic.has_cached_native_argument());
            }
            assert_eq!(
                (
                    KernelTermExport::machine_export_count(),
                    KernelTermExport::algebraic_export_count()
                ),
                exports
            );
            let native = StoredIntegerTerm::from(IntegerTerm::Variable(Variable(991722)));
            assert!(std::ptr::eq(native.old_form(), native.clone().old_form()));
        }
    }

    #[test]
    fn consuming_program_storage_moves_an_owned_native_address_prefix() {
        for size in [16, 64, 256] {
            let mut offset = AddressOffset::constant(0);
            for index in 0..size {
                offset = AddressOffset::raw_add(
                    offset,
                    AddressOffset::variable(Variable(991730 + index)),
                );
            }
            let value = ProgramValue::pointer(Address::new(
                AddressBase::Symbolic(Variable(991729)),
                offset,
            ));
            let ProgramValue::Pointer(pointer) = &value else {
                unreachable!()
            };
            let OffsetView::Add(left, right) = pointer.address().offset.view() else {
                unreachable!()
            };
            let allocations = [std::ptr::from_ref(left), std::ptr::from_ref(right)];
            let value = ProgramValue::from(StoredProgramValue::from(value));
            let ProgramValue::Pointer(pointer) = value else {
                unreachable!()
            };
            let address = pointer.into_pointer();
            let OffsetView::Add(left, right) = address.offset.view() else {
                unreachable!()
            };
            assert_eq!(
                [std::ptr::from_ref(left), std::ptr::from_ref(right)],
                allocations
            );
        }
    }
}
