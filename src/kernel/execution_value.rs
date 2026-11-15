//! Values retained between evaluation and execution boundaries.
//! Compatibility reads are explicit; a shared value owns only its common root.
use super::prelude::*;

#[derive(Clone, Debug, Eq)]
pub enum ExecutionValue {
    Native(ProgramValue),
    Shared(KernelTerm),
}

impl PartialEq for ExecutionValue {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Native(a), Self::Native(b)) => a == b,
            (Self::Shared(a), Self::Shared(b)) => {
                a == b
                    || (matches!(a.ty(), KernelType::Algebraic(_))
                        && a.ty() == b.ty()
                        && a.algebraic_syntax_equal(b))
                    || (a.ty() == &KernelType::Bool
                        && b.ty() == &KernelType::Bool
                        && BooleanOperandView::Shared(a)
                            .syntax_equal(BooleanOperandView::Shared(b)))
                    || matches!((a.pointer_payload(), b.pointer_payload()),
                        (Some(a), Some(b)) if a.same_source_payload(b))
                    || match (a.pointer_native(), b.pointer_native()) {
                        (Some(a), Some(b)) => a == b,
                        _ => false,
                    }
                    || (a.ty() == b.ty()
                        && (a.has_machine_matches() || b.has_machine_matches())
                        && crate::kernel::shared_machine_syntax_equal(a, b))
            }
            _ => false,
        }
    }
}

impl From<ProgramValue> for ExecutionValue {
    fn from(value: ProgramValue) -> Self {
        Self::Native(value)
    }
}
impl From<KernelTerm> for ExecutionValue {
    fn from(value: KernelTerm) -> Self {
        Self::Shared(value)
    }
}
impl ExecutionValue {
    pub fn shared(&self) -> Option<&KernelTerm> {
        match self {
            Self::Shared(root) => Some(root),
            Self::Native(_) => None,
        }
    }
    pub fn native_payload(&self) -> Option<&ProgramValue> {
        match self {
            Self::Native(value) => Some(value),
            Self::Shared(root) => root
                .pointer_native()
                .or_else(|| root.boolean_native())
                .or_else(|| {
                    matches!(root.node(), KernelTermNode::Variable(_))
                        .then(|| root.algebraic_native_value())
                        .flatten()
                }),
        }
    }
    pub fn pointer(&self) -> Option<&PointerValue> {
        let value = match self {
            Self::Native(value) => value,
            Self::Shared(root) => root.pointer_native()?,
        };
        match value {
            ProgramValue::Pointer(pointer) => Some(pointer),
            _ => None,
        }
    }
    pub fn byte_width(&self) -> u32 {
        self.program_type().byte_width()
    }
    /// Retain machine expressions and producer-defined pointer reads at their
    /// execution boundary. Other result families keep their exact native payloads.
    pub(in crate::kernel) fn retain_native(value: ProgramValue) -> Self {
        if let ProgramValue::Parameter(term) = &value {
            return KernelTermImport::default().algebraic(term).into();
        }
        if let ProgramValue::Pointer(pointer) = &value
            && let Some(root) = KernelTerm::retained_pointer_read(pointer)
        {
            return Self::Shared(root);
        }
        if let crate::kernel::integer_c_value!(term) = &value {
            // Scalar leaves have no expression prefix to retain. Keep their
            // existing cheap reading, including condition truth values.
            if matches!(
                term,
                MachineTerm::Constant { .. } | MachineTerm::Variable(_)
            ) {
                return Self::Native(value);
            }
            let format = MachineIntegerType::from_program_type(value.program_type()).unwrap();
            if let Some(root) = KernelTermImport::default().machine_arithmetic(format, term) {
                return Self::Shared(root);
            }
        }
        Self::Native(value)
    }

    /// Admit a completed address formation or cast. Load roots keep their
    /// definitions; other pointer producers are activated by their own slices.
    pub(in crate::kernel) fn retain_formed_pointer(value: ProgramValue) -> Self {
        let value = Self::retain_native(value);
        match value {
            Self::Native(ProgramValue::Pointer(pointer)) => {
                KernelTerm::shared_pointer_value(SharedPointerValue::import_produced(&pointer))
                    .into()
            }
            value => value,
        }
    }

    /// A branch handoff retains an existing producer root or admits its
    /// selected complete pointer value without changing any other carrier.
    pub(in crate::kernel) fn retain_pointer_result(self) -> Self {
        match self {
            Self::Native(value @ ProgramValue::Pointer(_)) => Self::retain_formed_pointer(value),
            value => value,
        }
    }

    pub(in crate::kernel) fn with_pointer_binding(
        self,
        program_type: ProgramType,
        volatile: bool,
        constant: bool,
    ) -> Self {
        if let Self::Shared(root) = &self
            && let Some(pointer) = root.pointer_payload()
        {
            return root
                .with_pointer_payload(pointer.with_binding_type_and_qualifiers(
                    program_type,
                    volatile,
                    constant,
                ))
                .into();
        }
        Self::retain_formed_pointer(
            self.into_native()
                .retag_pointer(program_type)
                .with_pointer_pointee_volatile(volatile)
                .with_pointer_pointee_constant(constant),
        )
    }

    /// Preserve the selected producer after an existing native conversion or
    /// entry-metadata operation. A changed address/type forms a new value.
    pub(in crate::kernel) fn retain_checked_pointer(&self, value: ProgramValue) -> Self {
        if let (Some(root), ProgramValue::Pointer(pointer)) = (self.shared(), &value) {
            return root.refined_pointer_argument(pointer).into();
        }
        if value.program_type().is_pointer() {
            Self::retain_formed_pointer(value)
        } else {
            value.into()
        }
    }

    /// Argument coercion leaves a logical Bool unchanged when the destination
    /// is also Bool. Other conversions keep the established pointer policy.
    pub(in crate::kernel) fn retain_coerced_argument(&self, value: ProgramValue) -> Self {
        if self.shared().is_some_and(|root| {
            root.ty() == &KernelType::Bool || matches!(root.ty(), KernelType::Algebraic(_))
        }) && self.program_type() == value.program_type()
        {
            self.clone()
        } else {
            self.retain_checked_pointer(value)
        }
    }

    /// Retain one selected operand before crossing a native checking boundary.
    pub(in crate::kernel) fn common_operand(&self) -> KernelTerm {
        match self {
            Self::Shared(root) => root.clone(),
            Self::Native(ProgramValue::Pointer(pointer)) => {
                KernelTerm::retained_pointer_read(pointer).unwrap_or_else(|| {
                    KernelTerm::shared_pointer_value(SharedPointerValue::import_produced(pointer))
                })
            }
            Self::Native(value) => {
                KernelTermImport::default().argument(&PureFunctionArgument::Value(value.clone()))
            }
        }
    }

    /// Read the logical truth carried by a Bool value. Raw C words keep the
    /// existing nonzero test; already logical roots remain shared.
    pub(in crate::kernel) fn boolean(&self) -> Option<KernelTerm> {
        match self {
            Self::Shared(root) if root.ty() == &KernelType::Bool => Some(root.clone()),
            Self::Native(ProgramValue::Bool(word)) => Some(
                KernelTermImport::default().condition(&ConditionTerm::truth_of_bool_word(word)),
            ),
            _ => None,
        }
    }

    pub(in crate::kernel) fn algebraic(&self) -> Option<KernelTerm> {
        match self {
            Self::Shared(root) if matches!(root.ty(), KernelType::Algebraic(_)) => {
                Some(root.clone())
            }
            Self::Native(ProgramValue::Parameter(value)) => {
                Some(KernelTermImport::default().algebraic(value))
            }
            _ => None,
        }
    }

    pub(in crate::kernel) fn retain_algebraic_result(self) -> Self {
        match self {
            Self::Native(ProgramValue::Parameter(value)) => {
                KernelTermImport::default().algebraic(&value).into()
            }
            value => value,
        }
    }

    pub fn into_native(self) -> ProgramValue {
        match self {
            Self::Native(value) => value,
            Self::Shared(term) => {
                if let Some(value) = term.algebraic_native_value() {
                    return value.clone();
                }
                if let Some(value) = term.boolean_native() {
                    return value.clone();
                }
                if let Some(value) = term.pointer_native() {
                    return value.clone();
                }
                if matches!(term.node(), KernelTermNode::Call { .. }) {
                    let KernelType::Program(ty) = term.ty() else {
                        unreachable!()
                    };
                    let format = MachineIntegerType::from_program_type(*ty)
                        .expect("machine call result type");
                    // The native result carrier needs only this call root.
                    // Keep numeric argument DAGs shared across the handoff;
                    // explicit KernelTermExport remains the structural export.
                    return format.value_from_term(
                        term.machine_conversion_leaf()
                            .expect("machine call root")
                            .clone(),
                    );
                }
                let PureFunctionArgument::Value(value) = KernelTermExport::default()
                    .argument(&term)
                    .expect("machine expression result")
                else {
                    unreachable!()
                };
                value
            }
        }
    }
    pub fn native(&self) -> std::borrow::Cow<'_, ProgramValue> {
        match self {
            Self::Native(value) => std::borrow::Cow::Borrowed(value),
            Self::Shared(_) => std::borrow::Cow::Owned(self.clone().into_native()),
        }
    }
    pub fn program_type(&self) -> ProgramType {
        match self {
            Self::Native(value) => value.program_type(),
            Self::Shared(term) => match term.ty() {
                KernelType::Program(ty) => *ty,
                KernelType::Bool => ProgramType::Bool,
                KernelType::Algebraic(ty) => ProgramType::Parameter(TypeParameterName::of(ty)),
                _ => unreachable!(),
            },
        }
    }
    pub(in crate::kernel) fn machine(
        &self,
    ) -> Option<(MachineIntegerType, MachineOperandView<'_>)> {
        let format = MachineIntegerType::from_program_type(self.program_type())?;
        match self {
            Self::Native(value) => {
                let (crate::kernel::integer_c_value!(term)) = value else {
                    return None;
                };
                Some((format, MachineOperandView::Legacy(term)))
            }
            Self::Shared(term) => Some((format, MachineOperandView::Shared(term))),
        }
    }
}

impl<V> ExpressionPath<V> {
    pub(in crate::kernel) fn map_value<W>(self, map: impl FnOnce(V) -> W) -> ExpressionPath<W> {
        ExpressionPath {
            outcome: self.outcome.map_value(map),
            facts: self.facts,
            obligations: self.obligations,
        }
    }
}

impl ExpressionPath<ExecutionValue> {
    pub(in crate::kernel) fn into_native(self) -> ExpressionPath {
        self.map_value(ExecutionValue::into_native)
    }
}

impl From<ExpressionPath> for ExpressionPath<ExecutionValue> {
    fn from(path: ExpressionPath) -> Self {
        path.map_value(ExecutionValue::retain_native)
    }
}

/// A memory cell's common pointer or Boolean carrier. Its key is exactly the previous
/// ProgramValue key, including for native numeric cells. Native observations
/// are explicit and borrow the selected value's cached compatibility view.
#[derive(Clone)]
pub struct StoredMemoryValue(ExecutionValue);
impl std::fmt::Debug for StoredMemoryValue {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Debug::fmt(self.native(), f)
    }
}
impl StoredMemoryValue {
    pub fn native(&self) -> &ProgramValue {
        self.0
            .native_payload()
            .or_else(|| self.0.shared()?.algebraic_native_value())
            .expect("native cell or retained value")
    }
    pub(crate) fn value(&self) -> &ExecutionValue {
        &self.0
    }
    pub(crate) fn with_native_value(&self, value: ProgramValue) -> Self {
        if self.value().shared().is_some() {
            self.value().retain_checked_pointer(value).into()
        } else {
            value.into()
        }
    }
    pub(crate) fn into_value(self) -> ExecutionValue {
        self.0
    }
    pub(crate) fn into_native(self) -> ProgramValue {
        self.0.into_native()
    }
    pub(crate) fn program_type(&self) -> ProgramType {
        self.0.program_type()
    }
    pub(crate) fn byte_width(&self) -> u32 {
        self.0.byte_width()
    }
}
impl From<ProgramValue> for StoredMemoryValue {
    fn from(value: ProgramValue) -> Self {
        Self(value.into())
    }
}
impl From<ExecutionValue> for StoredMemoryValue {
    fn from(value: ExecutionValue) -> Self {
        if value.shared().is_some_and(|root| {
            root.pointer_payload().is_none()
                && root.ty() != &KernelType::Bool
                && !matches!(root.ty(), KernelType::Algebraic(_))
        }) {
            Self(value.into_native().into())
        } else {
            Self(value)
        }
    }
}
impl PartialEq for StoredMemoryValue {
    fn eq(&self, other: &Self) -> bool {
        self.native() == other.native()
    }
}
impl Eq for StoredMemoryValue {}
impl std::hash::Hash for StoredMemoryValue {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        std::hash::Hash::hash(self.native(), state)
    }
}
impl PartialOrd for StoredMemoryValue {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for StoredMemoryValue {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.native().cmp(other.native())
    }
}
impl PartialEq<ProgramValue> for StoredMemoryValue {
    fn eq(&self, other: &ProgramValue) -> bool {
        self.native() == other
    }
}
impl PartialEq<StoredMemoryValue> for ProgramValue {
    fn eq(&self, other: &StoredMemoryValue) -> bool {
        self == other.native()
    }
}

/// A local or outcome value keeps its exact producer payload. Stored identity observes the
/// same native machine key across native and retained storage representations;
/// specification producer equality remains exact on ExecutionValue itself.
#[derive(Clone, Debug)]
pub struct StoredExecutionValue(std::sync::Arc<StoredValueData>);
#[derive(Debug)]
struct StoredValueData {
    value: ExecutionValue,
    identity: std::sync::OnceLock<Option<SharedMachineIntegerTerm>>,
}
#[derive(Eq, PartialEq, Hash, Ord, PartialOrd)]
enum StoredIdentity<'a> {
    Machine(&'a SharedMachineIntegerTerm),
    Native(&'a ProgramValue),
}
impl StoredExecutionValue {
    fn identity(&self) -> StoredIdentity<'_> {
        match self.0.identity.get_or_init(|| match &self.0.value {
            ExecutionValue::Shared(root)
                if root.pointer_payload().is_some()
                    || root.ty() == &KernelType::Bool
                    || matches!(root.ty(), KernelType::Algebraic(_)) =>
            {
                None
            }
            ExecutionValue::Shared(root) => Some(
                SharedMachineIntegerTerm::observe_shared(
                    MachineIntegerType::from_program_type(self.program_type())
                        .expect("machine storage"),
                    root.clone(),
                )
                .expect("retained machine storage"),
            ),
            ExecutionValue::Native(value) => {
                let (crate::kernel::integer_c_value!(term)) = value else {
                    return None;
                };
                Some(SharedMachineIntegerTerm::intern(
                    MachineIntegerType::from_program_type(value.program_type()).unwrap(),
                    term.clone(),
                ))
            }
        }) {
            Some(identity) => StoredIdentity::Machine(identity),
            None => StoredIdentity::Native(
                self.native_payload()
                    .or_else(|| self.shared()?.algebraic_native_value())
                    .expect("native storage"),
            ),
        }
    }
    pub fn matches_native(&self, value: &ProgramValue) -> bool {
        self == &Self::from(value.clone())
    }
    pub fn into_value(self) -> ExecutionValue {
        match std::sync::Arc::try_unwrap(self.0) {
            Ok(data) => data.value,
            Err(data) => data.value.clone(),
        }
    }
    pub fn into_native(self) -> ProgramValue {
        self.into_value().into_native()
    }
}
impl std::ops::Deref for StoredExecutionValue {
    type Target = ExecutionValue;
    fn deref(&self) -> &Self::Target {
        &self.0.value
    }
}
impl From<ExecutionValue> for StoredExecutionValue {
    fn from(value: ExecutionValue) -> Self {
        let value = if value.shared().is_some_and(|root| {
            !root.is_shared_machine_operand()
                && root.pointer_payload().is_none()
                && root.ty() != &KernelType::Bool
                && !matches!(root.ty(), KernelType::Algebraic(_))
        }) {
            ExecutionValue::Native(value.into_native())
        } else {
            value
        };
        Self(std::sync::Arc::new(StoredValueData {
            value,
            identity: Default::default(),
        }))
    }
}
impl From<ProgramValue> for StoredExecutionValue {
    fn from(value: ProgramValue) -> Self {
        ExecutionValue::from(value).into()
    }
}
impl From<StoredExecutionValue> for ExecutionValue {
    fn from(value: StoredExecutionValue) -> Self {
        value.into_value()
    }
}
impl PartialEq for StoredExecutionValue {
    fn eq(&self, other: &Self) -> bool {
        self.identity() == other.identity()
    }
}
impl Eq for StoredExecutionValue {}
impl std::hash::Hash for StoredExecutionValue {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        std::hash::Hash::hash(&self.identity(), state);
    }
}
impl PartialOrd for StoredExecutionValue {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for StoredExecutionValue {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.identity().cmp(&other.identity())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn algebraic_storage_preserves_roots_and_native_key_contracts() {
        let _session = crate::kernel::VerificationSession::enter();
        let ty = TypeParameterName::intern("StoredAlgebraicT").algebraic_type();
        let roots = [
            KernelTerm::variable(KernelType::Algebraic(ty.clone()), Variable(999764)),
            KernelTerm::algebraic_read(
                ty.clone(),
                intern_memory(Memory::new()),
                SharedPointerAddress::import(&Pointer::symbolic(Variable(999765))),
            ),
        ];
        fn hash(value: &impl std::hash::Hash) -> u64 {
            use std::hash::Hasher;
            let mut hasher = std::collections::hash_map::DefaultHasher::new();
            std::hash::Hash::hash(value, &mut hasher);
            hasher.finish()
        }
        for root in roots {
            let value = ExecutionValue::Shared(root.clone());
            let native = value.clone().into_native();
            let stored = StoredExecutionValue::from(value.clone());
            let expected = StoredExecutionValue::from(native.clone());
            assert_eq!(stored, expected);
            assert_eq!(stored.cmp(&expected), std::cmp::Ordering::Equal);
            assert_eq!(hash(&stored), hash(&expected));
            assert_eq!(stored.clone().into_value().shared(), Some(&root));
            assert_eq!(
                value.retain_coerced_argument(native.clone()).shared(),
                Some(&root)
            );
            let cell = StoredMemoryValue::from(value);
            assert_eq!(cell.native(), &native);
            assert_eq!(hash(&cell), hash(&native));
            assert_eq!(cell.into_value().shared(), Some(&root));
        }
    }
    #[test]
    fn boolean_storage_preserves_roots_and_native_keys() {
        let _session = crate::kernel::VerificationSession::enter();
        let variable = KernelTerm::variable(KernelType::Bool, Variable(999500));
        let roots = [
            KernelTermImport::default().condition(&ConditionTerm::Constant(false)),
            variable.clone(),
            KernelTerm::boolean_if([
                variable.clone(),
                KernelTerm::variable(KernelType::Bool, Variable(999501)),
                KernelTermImport::default().condition(&ConditionTerm::Constant(true)),
            ]),
            KernelTermImport::default()
                .boolean_call(&SharedPureApplication::intern("stored_bool".into(), vec![])),
        ];
        fn hash(value: &impl std::hash::Hash) -> u64 {
            use std::hash::Hasher;
            let mut h = std::collections::hash_map::DefaultHasher::new();
            std::hash::Hash::hash(value, &mut h);
            h.finish()
        }
        for root in roots {
            let native = ExecutionValue::Shared(root.clone()).into_native();
            let stored = StoredExecutionValue::from(ExecutionValue::Shared(root.clone()));
            let native_stored = StoredExecutionValue::from(native.clone());
            assert_eq!(stored, native_stored);
            assert_eq!(hash(&stored), hash(&native_stored));
            assert_eq!(stored.clone().into_value().shared(), Some(&root));
            assert_eq!(stored.into_value().shared(), Some(&root));
            let cell = StoredMemoryValue::from(ExecutionValue::Shared(root.clone()));
            assert_eq!(cell.native(), &native);
            assert_eq!(hash(&cell), hash(&native));
            for other in [
                ProgramValue::Void,
                ProgramValue::Bool(MachineTerm::Constant {
                    format: MachineIntegerType::UInt8,
                    bits: 2,
                }),
                native.clone(),
            ] {
                assert_eq!(
                    cell.cmp(&StoredMemoryValue::from(other.clone())),
                    native.cmp(&other)
                );
                assert_eq!(
                    StoredExecutionValue::from(ExecutionValue::Shared(root.clone()))
                        .cmp(&StoredExecutionValue::from(other.clone())),
                    native_stored.cmp(&StoredExecutionValue::from(other))
                );
            }
            let address = Memory::local_pointer("stored_bool");
            let memory = Memory::new()
                .with_block(address.block.clone(), 1)
                .store_retained(address.clone(), cell.into_value());
            assert_eq!(
                memory.known_retained_value(&address).unwrap().shared(),
                Some(&root)
            );
            assert_eq!(memory.known_value(&address), Some(native));
            assert!(std::ptr::eq(
                root.boolean_native().unwrap(),
                root.boolean_native().unwrap()
            ));
        }
        let raw = ProgramValue::Bool(MachineTerm::Constant {
            format: MachineIntegerType::UInt8,
            bits: 2,
        });
        let cell = StoredMemoryValue::from(raw.clone());
        assert_eq!(cell.native(), &raw);
        assert!(cell.value().shared().is_none());
    }

    #[test]
    fn local_storage_identity_matches_native_without_changing_producer_equality() {
        let _session = crate::kernel::VerificationSession::enter();
        let term = MachineTerm::machine_binary(
            MachineIntegerType::UInt32,
            MachineBinaryOp::Multiply,
            MachineTerm::Variable(Variable(998320)),
            MachineTerm::uint32_constant(3),
        );
        let native = ExecutionValue::from(ProgramValue::UInt32(term.clone()));
        let root = KernelTermImport::default().machine(MachineIntegerType::UInt32, &term);
        let shared = ExecutionValue::from(root.clone());
        assert_ne!(native, shared, "producer equality stays exact");
        let exports = KernelTermExport::machine_export_count();
        let native = StoredExecutionValue::from(native);
        let shared = StoredExecutionValue::from(shared);
        assert_eq!(native, shared);
        assert_eq!(native.cmp(&shared), std::cmp::Ordering::Equal);
        let hash = |value: &StoredExecutionValue| {
            use std::hash::{Hash, Hasher};
            let mut hash = std::collections::hash_map::DefaultHasher::new();
            value.hash(&mut hash);
            hash.finish()
        };
        assert_eq!(hash(&native), hash(&shared));
        assert_eq!(shared.shared(), Some(&root));
        assert_eq!(KernelTermExport::machine_export_count(), exports);
    }

    #[test]
    fn pointer_local_storage_retains_root_and_native_identity() {
        let _session = crate::kernel::VerificationSession::enter();
        let pointer = PointerValue::new(
            Pointer::symbolic(Variable(1027000)),
            ProgramType::Int32Pointer,
        );
        let root = KernelTerm::shared_pointer_call(
            KernelTerm::checked_call(
                KernelType::Program(ProgramType::Int32Pointer),
                "local_source".into(),
                vec![],
            ),
            SharedPointerValue::import(&pointer),
        );
        let stored = StoredExecutionValue::from(ExecutionValue::Shared(root.clone()));
        let native = StoredExecutionValue::from(ProgramValue::Pointer(pointer.clone()));
        assert_eq!(stored, native);
        assert_eq!(stored.cmp(&native), std::cmp::Ordering::Equal);
        let hash = |value: &StoredExecutionValue| {
            use std::hash::{Hash, Hasher};
            let mut h = std::collections::hash_map::DefaultHasher::new();
            value.hash(&mut h);
            h.finish()
        };
        assert_eq!(hash(&stored), hash(&native));
        assert_eq!(stored.shared(), Some(&root));
        let mut state = ExecutionState::new();
        state.locals.set_retained_typed_with_all_qualifiers(
            "p",
            stored,
            ProgramType::Int32Pointer,
            false,
            false,
            false,
            false,
        );
        assert_eq!(state.locals.get("p").unwrap().shared(), Some(&root));
        for (volatile, constant) in [(false, true), (true, true), (true, false), (false, false)] {
            let value = ExecutionValue::Shared(root.clone()).with_pointer_binding(
                ProgramType::Int32Pointer,
                volatile,
                constant,
            );
            assert!(matches!(
                value.shared().unwrap().node(),
                KernelTermNode::PointerCall { .. }
            ));
            let expected = pointer
                .clone()
                .with_pointee_volatile(volatile)
                .with_pointee_constant(constant);
            assert!(
                value
                    .shared()
                    .unwrap()
                    .pointer_payload()
                    .unwrap()
                    .same_source_payload(&SharedPointerValue::import(&expected))
            );
            assert_eq!(value.pointer().unwrap().pointee_constant(), constant);
            assert_eq!(value.pointer().unwrap().pointee_volatile(), volatile);
        }
        let retagged = ExecutionValue::Shared(root).with_pointer_binding(
            ProgramType::VoidPointer,
            false,
            false,
        );
        assert_eq!(retagged.program_type(), ProgramType::VoidPointer);
        assert!(matches!(
            retagged.shared().unwrap().node(),
            KernelTermNode::PointerValue { .. }
        ));
    }

    #[test]
    fn pointer_memory_cells_keep_roots_and_the_previous_native_key() {
        let _session = crate::kernel::VerificationSession::enter();
        let pointer = PointerValue::new(
            Pointer::symbolic(Variable(1027500)),
            ProgramType::Int32Pointer,
        )
        .with_pointee_constant(true);
        let native = ProgramValue::Pointer(pointer.clone());
        let root = KernelTerm::shared_pointer_value(SharedPointerValue::import(&pointer));
        let retained = StoredMemoryValue::from(ExecutionValue::Shared(root.clone()));
        let native_cell = StoredMemoryValue::from(native.clone());
        assert_eq!(retained, native_cell);
        assert_eq!(retained.cmp(&native_cell), std::cmp::Ordering::Equal);
        fn hash(value: &impl std::hash::Hash) -> u64 {
            use std::hash::Hasher;
            let mut hash = std::collections::hash_map::DefaultHasher::new();
            std::hash::Hash::hash(value, &mut hash);
            hash.finish()
        }
        assert_eq!(hash(&retained), hash(&native));
        assert_eq!(hash(&native_cell), hash(&native));
        assert_eq!(format!("{retained:?}"), format!("{native:?}"));
        let address = Pointer::symbolic(Variable(1027501));
        let mut cells = CellStore::new();
        cells.insert_retained(address.clone(), retained);
        assert_eq!(cells.get_retained(&address).unwrap().shared(), Some(&root));
        assert_eq!(cells.get(&address), Some(native.clone()));
        assert_eq!(cells.iter().next().unwrap().1, &native);
        assert!(
            cells
                .get_retained(&address)
                .unwrap()
                .pointer()
                .unwrap()
                .pointee_constant()
        );
    }

    #[test]
    fn pointer_store_history_keeps_the_root_after_cache_forgetting() {
        let _session = crate::kernel::VerificationSession::enter();
        let address = Memory::local_pointer("retained_pointer_cell");
        let pointer = PointerValue::new(
            Pointer::symbolic(Variable(1027600)),
            ProgramType::Int32Pointer,
        )
        .with_pointee_constant(true);
        let root = KernelTerm::shared_pointer_call(
            KernelTerm::checked_call(
                KernelType::Program(ProgramType::Int32Pointer),
                "stored_source".into(),
                vec![],
            ),
            SharedPointerValue::import(&pointer),
        );
        let memory = Memory::new()
            .with_block(address.block.clone(), C_POINTER_BYTE_WIDTH)
            .store_retained(address.clone(), ExecutionValue::Shared(root.clone()));
        assert_eq!(
            memory.known_retained_value(&address).unwrap().shared(),
            Some(&root)
        );
        let forgotten = memory.without_possible_aliasing_cells(
            &address.offset_by_bytes(1),
            1,
            &PureFactContext::new(),
        );
        assert!(forgotten.known_value(&address).is_none());
        for retained_state in [&memory, &forgotten] {
            let origin =
                Pointer::loaded_value(&crate::kernel::intern_memory_ref(retained_state), &address);
            let recovered =
                crate::kernel::memory_provenance::complete_pointer_carrier_read_retained_value(
                    &origin,
                    &PureFactContext::new(),
                )
                .unwrap();
            assert_eq!(recovered.shared(), Some(&root));
            assert!(recovered.pointer().unwrap().pointee_constant());
            let paths = crate::kernel::eval::evaluate_retained_memory_load_paths(
                retained_state,
                address.clone(),
                ProgramType::Int32Pointer,
                ExecutionFacts::new(),
                vec![],
                &PureFactContext::new(),
                false,
                false,
                None,
                None,
            );
            assert_eq!(paths.len(), 1);
            let ExpressionOutcome::Value(loaded) = &paths[0].outcome else {
                panic!("retained pointer load: {:?}", paths[0].outcome);
            };
            assert_eq!(loaded.shared(), Some(&root));
            assert!(loaded.pointer().unwrap().pointee_constant());
        }
    }

    #[test]
    fn execution_outcomes_preserve_native_values_and_refusals() {
        let value = ProgramValue::Int32(MachineTerm::constant(7));
        let outcome = ExpressionOutcome::Value(value.clone()).map_value(ExecutionValue::from);
        assert_eq!(
            outcome.map_value(ExecutionValue::into_native),
            ExpressionOutcome::Value(value)
        );
        let undefined =
            ExpressionOutcome::<ProgramValue>::UndefinedBehavior(UndefinedBehavior::SignedOverflow);
        assert_eq!(
            undefined
                .clone()
                .map_value(ExecutionValue::from)
                .map_value(ExecutionValue::into_native),
            undefined
        );
    }
}

#[cfg(test)]
mod scaling_tests {
    include!("../scaling_tests/kernel/execution_value.rs");
}
