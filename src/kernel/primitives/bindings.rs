use super::*;

/// Prepared source ownership shared by every declaration of a function.
#[derive(Clone, Debug)]
pub struct LocalFunctionId(Arc<LocalFunctionIdentity>);
#[derive(Debug)]
struct LocalFunctionIdentity {
    source: Option<String>,
    function: String,
    fingerprint: u64,
    /// Each source spelling the function's declarations use, and whether it
    /// names one declaration that shadows nothing. Presentation metadata
    /// only: it is never part of identity.
    spellings: std::sync::Mutex<BTreeMap<String, bool>>,
}
impl LocalFunctionId {
    pub fn new(source: Option<String>, function: String) -> Self {
        let mut hasher = std::collections::hash_map::DefaultHasher::new();
        (&source, &function).hash(&mut hasher);
        Self(Arc::new(LocalFunctionIdentity {
            source,
            function,
            fingerprint: hasher.finish(),
            spellings: std::sync::Mutex::new(BTreeMap::new()),
        }))
    }
    pub(crate) fn source_and_name(&self) -> (Option<&str>, &str) {
        (self.0.source.as_deref(), &self.0.function)
    }

    /// Records a declaration's source spelling as the C parser declares it.
    /// A spelling is unique when one declaration of the function uses it and
    /// that declaration shadows no visible name, local or file-scope.
    pub fn record_declaration_spelling(&self, spelling: &str, shadows: bool) {
        let mut spellings = self.0.spellings.lock().expect("spelling table lock");
        spellings
            .entry(spelling.to_owned())
            .and_modify(|unique| *unique = false)
            .or_insert(!shadows);
    }
    fn spelling_is_unique(&self, spelling: &str) -> bool {
        self.0
            .spellings
            .lock()
            .expect("spelling table lock")
            .get(spelling)
            .copied()
            .unwrap_or(false)
    }
    fn identity(&self) -> (&Option<String>, &str) {
        (&self.0.source, &self.0.function)
    }
}
impl PartialEq for LocalFunctionId {
    fn eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.0, &other.0) || self.identity() == other.identity()
    }
}
impl Eq for LocalFunctionId {}
impl PartialOrd for LocalFunctionId {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for LocalFunctionId {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        if Arc::ptr_eq(&self.0, &other.0) {
            std::cmp::Ordering::Equal
        } else {
            self.identity().cmp(&other.identity())
        }
    }
}
impl Hash for LocalFunctionId {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.0.fingerprint.hash(state);
    }
}

/// A declaration's identity within a prepared C function. Its source spelling
/// is metadata, never part of the identity used for storage or execution.
#[derive(Clone, Debug)]
pub struct LocalBindingId(Arc<LocalDeclaration>);
#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd)]
enum LocalBindingKind {
    Source,
    Temporary,
    PreparedArgument,
    LoopEscape,
    EnumerateCount,
    SliceIteratorSlice,
    ChunkIterator(ChunkIteratorField),
    IteratorOption(IteratorOptionField),
    RangeStart,
    RangeEnd,
    CompoundLiteral,
    SliceComponent,
    ReturnPlace,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
enum ChunkIteratorField {
    Remaining,
    RemainingLength,
    Remainder,
    RemainderLength,
    Size,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
enum IteratorOptionField {
    Tag,
    Pointer,
    Length,
    Index,
}

#[derive(Debug)]
struct LocalDeclaration {
    owner: LocalFunctionId,
    parameter: bool,
    kind: LocalBindingKind,
    ordinal: u32,
    scope_depth: u32,
    spelling: Option<String>,
    program_type: OnceLock<ProgramType>,
    array_shape: OnceLock<Arc<[u32]>>,
    struct_name: OnceLock<Arc<str>>,
    /// For a prepared argument, the callee parameter it is passed as: the
    /// object is spelled `R.parameter(name)` at its call's region `R`.
    call_parameter: Option<Arc<str>>,
}
impl LocalBindingId {
    pub fn new(
        owner: LocalFunctionId,
        parameter: bool,
        ordinal: u32,
        spelling: Option<String>,
    ) -> Self {
        Self(Arc::new(LocalDeclaration {
            owner,
            parameter,
            kind: LocalBindingKind::Source,
            ordinal,
            scope_depth: 0,
            spelling,
            program_type: OnceLock::new(),
            array_shape: OnceLock::new(),
            struct_name: OnceLock::new(),
            call_parameter: None,
        }))
    }
    /// A frontend temporary is distinct from all source declaration ordinals.
    pub(crate) fn temporary(owner: LocalFunctionId, ordinal: u32) -> Self {
        Self::new_unnamed(owner, ordinal, LocalBindingKind::Temporary)
    }

    pub(crate) fn prepared_argument(owner: LocalFunctionId, ordinal: u32) -> Self {
        Self::new_unnamed(owner, ordinal, LocalBindingKind::PreparedArgument)
    }

    /// The object a call receives as its by-value parameter `parameter`,
    /// initialized by the caller before the call.
    pub(crate) fn prepared_argument_for(
        owner: LocalFunctionId,
        ordinal: u32,
        parameter: &str,
    ) -> Self {
        let mut declaration = Self::prepared_argument(owner, ordinal);
        Arc::get_mut(&mut declaration.0)
            .expect("a new declaration is unshared")
            .call_parameter = Some(Arc::from(parameter));
        declaration
    }

    /// The callee parameter this prepared argument is passed as.
    pub(crate) fn call_parameter(&self) -> Option<&str> {
        self.0.call_parameter.as_deref()
    }

    /// An unnamed object identified by its written compound literal occurrence.
    pub(crate) fn compound_literal(owner: LocalFunctionId, ordinal: u32) -> Self {
        Self::new_unnamed(owner, ordinal, LocalBindingKind::CompoundLiteral)
    }

    /// Runtime storage for one slice of a Rust pair of slices, as
    /// `split_at` returns: one wide value (`design/rust-slice-values.md`).
    pub(crate) fn slice_component(owner: LocalFunctionId, ordinal: u32) -> Self {
        Self::new_unnamed(owner, ordinal, LocalBindingKind::SliceComponent)
    }

    pub(crate) fn return_place(owner: LocalFunctionId) -> Self {
        Self::new_unnamed(owner, 0, LocalBindingKind::ReturnPlace)
    }

    pub(crate) fn is_return_place(&self) -> bool {
        self.0.kind == LocalBindingKind::ReturnPlace
    }

    fn new_unnamed(owner: LocalFunctionId, ordinal: u32, kind: LocalBindingKind) -> Self {
        Self(Arc::new(LocalDeclaration {
            owner,
            parameter: false,
            kind,
            ordinal,
            scope_depth: 0,
            spelling: None,
            program_type: OnceLock::new(),
            array_shape: OnceLock::new(),
            struct_name: OnceLock::new(),
            call_parameter: None,
        }))
    }
    pub(crate) fn loop_escape(owner: LocalFunctionId, ordinal: u32) -> Self {
        Self(Arc::new(LocalDeclaration {
            owner,
            parameter: false,
            kind: LocalBindingKind::LoopEscape,
            ordinal,
            scope_depth: 0,
            spelling: None,
            program_type: OnceLock::from(ProgramType::Int32),
            array_shape: OnceLock::new(),
            struct_name: OnceLock::new(),
            call_parameter: None,
        }))
    }

    pub(crate) fn enumerate_count(owner: LocalFunctionId, ordinal: u32) -> Self {
        Self(Arc::new(LocalDeclaration {
            owner,
            parameter: false,
            kind: LocalBindingKind::EnumerateCount,
            ordinal,
            scope_depth: 0,
            spelling: None,
            program_type: OnceLock::from(ProgramType::UInt64),
            array_shape: OnceLock::new(),
            struct_name: OnceLock::new(),
            call_parameter: None,
        }))
    }

    pub(crate) fn chunk_iterator_fields(owner: LocalFunctionId, ordinal: u32) -> [Self; 5] {
        use ChunkIteratorField::*;
        [
            (Remaining, ProgramType::UInt8Pointer),
            (RemainingLength, ProgramType::UInt64),
            (Remainder, ProgramType::UInt8Pointer),
            (RemainderLength, ProgramType::UInt64),
            (Size, ProgramType::UInt64),
        ]
        .map(|(field, ty)| {
            Self::iterator_field(&owner, ordinal, LocalBindingKind::ChunkIterator(field), ty)
        })
    }

    pub(crate) fn iterator_option_fields(
        owner: &LocalFunctionId,
        ordinal: u32,
        pointer_type: ProgramType,
    ) -> [Self; 2] {
        [
            (IteratorOptionField::Tag, ProgramType::Int32),
            (IteratorOptionField::Pointer, pointer_type),
        ]
        .map(|(field, ty)| {
            Self::iterator_field(owner, ordinal, LocalBindingKind::IteratorOption(field), ty)
        })
    }

    pub(crate) fn iterator_option_length(owner: &LocalFunctionId, ordinal: u32) -> Self {
        Self::iterator_field(
            owner,
            ordinal,
            LocalBindingKind::IteratorOption(IteratorOptionField::Length),
            ProgramType::UInt64,
        )
    }

    pub(crate) fn iterator_option_index(owner: &LocalFunctionId, ordinal: u32) -> Self {
        Self::iterator_field(
            owner,
            ordinal,
            LocalBindingKind::IteratorOption(IteratorOptionField::Index),
            ProgramType::UInt64,
        )
    }

    fn iterator_field(
        owner: &LocalFunctionId,
        ordinal: u32,
        kind: LocalBindingKind,
        ty: ProgramType,
    ) -> Self {
        Self(Arc::new(LocalDeclaration {
            owner: owner.clone(),
            parameter: false,
            kind,
            ordinal,
            scope_depth: 0,
            spelling: None,
            program_type: OnceLock::from(ty),
            array_shape: OnceLock::new(),
            struct_name: OnceLock::new(),
            call_parameter: None,
        }))
    }

    /// The slice a slice iterator still covers, one wide value of
    /// `slice_type` (`design/rust-slice-values.md`, step 4b).
    pub(crate) fn slice_iterator_slice(
        owner: LocalFunctionId,
        ordinal: u32,
        slice_type: ProgramType,
    ) -> Self {
        Self::iterator_field(
            &owner,
            ordinal,
            LocalBindingKind::SliceIteratorSlice,
            slice_type,
        )
    }

    pub(crate) fn range_bounds(owner: LocalFunctionId, ordinal: u32, ty: ProgramType) -> [Self; 2] {
        [LocalBindingKind::RangeStart, LocalBindingKind::RangeEnd]
            .map(|kind| Self::iterator_field(&owner, ordinal, kind, ty))
    }

    pub(crate) fn is_iterator_field(&self) -> bool {
        matches!(
            self.0.kind,
            LocalBindingKind::EnumerateCount
                | LocalBindingKind::SliceIteratorSlice
                | LocalBindingKind::ChunkIterator(_)
                | LocalBindingKind::RangeStart
                | LocalBindingKind::RangeEnd
        )
    }

    pub(crate) fn is_iterator_option_field(&self) -> bool {
        matches!(self.0.kind, LocalBindingKind::IteratorOption(_))
    }

    pub fn is_temporary(&self) -> bool {
        matches!(
            self.0.kind,
            LocalBindingKind::Temporary
                | LocalBindingKind::PreparedArgument
                | LocalBindingKind::SliceComponent
        )
    }

    pub(crate) fn is_prepared_argument(&self) -> bool {
        self.0.kind == LocalBindingKind::PreparedArgument
    }
    pub(crate) fn with_scope_depth(self, scope_depth: u32) -> Self {
        Self(Arc::new(LocalDeclaration {
            owner: self.0.owner.clone(),
            parameter: self.0.parameter,
            kind: self.0.kind,
            ordinal: self.0.ordinal,
            scope_depth,
            spelling: self.0.spelling.clone(),
            program_type: OnceLock::new(),
            array_shape: OnceLock::new(),
            struct_name: OnceLock::new(),
            call_parameter: self.0.call_parameter.clone(),
        }))
    }
    pub fn owner(&self) -> &LocalFunctionId {
        &self.0.owner
    }
    pub fn scope_depth(&self) -> u32 {
        self.0.scope_depth
    }
    pub fn source(&self) -> Option<&str> {
        self.0.owner.0.source.as_deref()
    }
    pub fn function(&self) -> &str {
        &self.0.owner.0.function
    }
    pub fn ordinal(&self) -> u32 {
        self.0.ordinal
    }
    pub fn is_parameter(&self) -> bool {
        self.0.parameter
    }
    pub(crate) fn is_compound_literal(&self) -> bool {
        self.0.kind == LocalBindingKind::CompoundLiteral
    }
    pub fn spelling(&self) -> Option<&str> {
        self.0.spelling.as_deref()
    }
    /// The C spelling a proof writes for this declaration, when that spelling
    /// names no other declaration of its function and no file-scope object,
    /// and is not a Click word. Wherever the declaration is in scope, the
    /// spelling resolves back to it; the typed identity spells it otherwise.
    pub fn source_spelling(&self) -> Option<&str> {
        let spelling = self.spelling()?;
        (self.0.owner.spelling_is_unique(spelling) && !is_click_expression_word(spelling))
            .then_some(spelling)
    }
    /// Source type metadata is filled by the C declaration builder before lowering.
    pub(crate) fn initialize_program_type(&self, ty: ProgramType) {
        let _ = self.0.program_type.set(ty);
    }
    pub(crate) fn initialize_array_shape(&self, shape: &[u32]) {
        let _ = self.0.array_shape.set(Arc::from(shape));
    }
    pub(crate) fn initialize_struct_name(&self, name: &str) {
        let _ = self.0.struct_name.set(Arc::from(name));
    }
    pub fn array_shape(&self) -> Option<&[u32]> {
        self.0.array_shape.get().map(|shape| shape.as_ref())
    }
    pub fn struct_name(&self) -> Option<&str> {
        self.0.struct_name.get().map(|name| name.as_ref())
    }
    pub fn program_type(&self) -> Option<ProgramType> {
        self.0.program_type.get().copied()
    }
    fn identity(&self) -> (&LocalFunctionId, LocalBindingKind, bool, u32) {
        (&self.0.owner, self.0.kind, self.0.parameter, self.0.ordinal)
    }
}

impl PartialEq for LocalBindingId {
    fn eq(&self, other: &Self) -> bool {
        self.identity() == other.identity()
    }
}
impl Eq for LocalBindingId {}
impl PartialOrd for LocalBindingId {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for LocalBindingId {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.identity().cmp(&other.identity())
    }
}
impl Hash for LocalBindingId {
    fn hash<H: Hasher>(&self, state: &mut H) {
        match self.0.kind {
            // Preserve the hash domain of existing declaration identities.
            LocalBindingKind::Source => {
                (&self.0.owner, self.0.parameter, self.0.ordinal).hash(state)
            }
            LocalBindingKind::Temporary => (&self.0.owner, 2u8, self.0.ordinal).hash(state),
            LocalBindingKind::LoopEscape => (&self.0.owner, 3u8, self.0.ordinal).hash(state),
            LocalBindingKind::EnumerateCount => (&self.0.owner, 4u8, self.0.ordinal).hash(state),
            LocalBindingKind::PreparedArgument => (&self.0.owner, 5u8, self.0.ordinal).hash(state),
            LocalBindingKind::SliceIteratorSlice => {
                (&self.0.owner, 7u8, self.0.ordinal).hash(state)
            }
            LocalBindingKind::ChunkIterator(field) => {
                (&self.0.owner, 9u8, self.0.ordinal, field).hash(state)
            }
            LocalBindingKind::IteratorOption(field) => {
                (&self.0.owner, 10u8, self.0.ordinal, field).hash(state)
            }
            LocalBindingKind::RangeStart => (&self.0.owner, 11u8, self.0.ordinal).hash(state),
            LocalBindingKind::RangeEnd => (&self.0.owner, 12u8, self.0.ordinal).hash(state),
            LocalBindingKind::CompoundLiteral => (&self.0.owner, 13u8, self.0.ordinal).hash(state),
            // Hashed as the slice half of the retired pointer and length
            // pair was, so every other hash stays as it was.
            LocalBindingKind::SliceComponent => {
                (&self.0.owner, 14u8, self.0.ordinal, false).hash(state)
            }
            LocalBindingKind::ReturnPlace => (&self.0.owner, 15u8).hash(state),
        }
    }
}
/// A declaration is written by its C spelling where that names it
/// ([`LocalBindingId::source_spelling`]), and by its typed identity,
/// `"file.c"::function.local(N)`, otherwise.
impl std::fmt::Display for LocalBindingId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.source_spelling() {
            Some(spelling) => f.write_str(spelling),
            None => self.canonical().fmt(f),
        }
    }
}

/// The typed declaration selector, `"file.c"::f.local(i)`, which names the
/// declaration everywhere and is the only head a `.storage(...)` suffix takes.
pub struct CanonicalLocalBinding<'a>(&'a LocalBindingId);

impl LocalBindingId {
    pub fn canonical(&self) -> CanonicalLocalBinding<'_> {
        CanonicalLocalBinding(self)
    }
}

impl std::fmt::Display for CanonicalLocalBinding<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let id = self.0;
        if id.is_return_place() {
            return f.write_str("<return storage>");
        }
        if id.is_temporary() {
            return f.write_str("<temporary storage>");
        }
        if id.0.kind == LocalBindingKind::LoopEscape {
            return f.write_str("<loop escape>");
        }
        let range_bound = match id.0.kind {
            LocalBindingKind::RangeStart => Some("start"),
            LocalBindingKind::RangeEnd => Some("end"),
            _ => None,
        };
        if let Some(bound) = range_bound {
            return write!(
                f,
                "<range {bound} of {:?}::{}.local({})>",
                id.source(),
                id.function(),
                id.ordinal()
            );
        }
        let slice_field = match id.0.kind {
            LocalBindingKind::EnumerateCount => return f.write_str("<enumeration count>"),
            LocalBindingKind::SliceIteratorSlice => Some("slice"),
            _ => None,
        };
        if let Some(field) = slice_field {
            // Include the declaration identity in symbolic storage diagnostics.
            return write!(
                f,
                "<slice iterator {field} of {:?}::{}.local({})>",
                id.source(),
                id.function(),
                id.ordinal()
            );
        }
        if let LocalBindingKind::ChunkIterator(field) = id.0.kind {
            let field = match field {
                ChunkIteratorField::Remaining => "remaining pointer",
                ChunkIteratorField::RemainingLength => "remaining length",
                ChunkIteratorField::Remainder => "remainder pointer",
                ChunkIteratorField::RemainderLength => "remainder length",
                ChunkIteratorField::Size => "chunk size",
            };
            return write!(
                f,
                "<chunk iterator {field} of {:?}::{}.local({})>",
                id.source(),
                id.function(),
                id.ordinal()
            );
        }
        if let LocalBindingKind::IteratorOption(field) = id.0.kind {
            let field = match field {
                IteratorOptionField::Tag => "tag",
                IteratorOptionField::Pointer => "pointer",
                IteratorOptionField::Length => "length",
                IteratorOptionField::Index => "index",
            };
            return write!(
                f,
                "<iterator option {field} of {:?}::{}.local({})>",
                id.source(),
                id.function(),
                id.ordinal()
            );
        }
        if let Some(source) = id.source() {
            write!(f, "{source:?}::")?;
        }
        write!(
            f,
            "{}.{}({})",
            id.function(),
            if id.is_compound_literal() {
                "compound_literal"
            } else if id.is_parameter() {
                "parameter"
            } else {
                "local"
            },
            id.ordinal()
        )
    }
}

/// A specification binder identity occupies a separate namespace from source
/// names and C declarations. Cloning a term retains its lexical identity.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct GeneratedBinderId(u64);
// Explicit numeric spellings and internally allocated names share a typed namespace.
// Reserve intervals so sparse user spellings do not exhaust or linearly probe it.
#[derive(Default)]
struct BinderIds {
    next: u64,
    reserved: std::collections::BTreeMap<u64, u64>,
}
impl BinderIds {
    fn reserve(&mut self, number: u64) {
        let mut start = number;
        let mut end = number;
        if let Some((&left, &right)) = self.reserved.range(..=number).next_back() {
            if right >= number {
                return;
            }
            if right.checked_add(1) == Some(number) {
                start = left;
                self.reserved.remove(&left);
            }
        }
        if let Some((&left, &right)) = self.reserved.range(number..).next()
            && number.checked_add(1) == Some(left)
        {
            end = right;
            self.reserved.remove(&left);
        }
        self.reserved.insert(start, end);
    }
    fn fresh(&mut self) -> u64 {
        if let Some((_, &end)) = self.reserved.range(..=self.next).next_back()
            && end >= self.next
        {
            self.next = end
                .checked_add(1)
                .expect("specification binder identity space exhausted");
        }
        let number = self.next;
        self.reserve(number);
        self.next = number
            .checked_add(1)
            .expect("specification binder identity space exhausted");
        number
    }
}
fn binder_ids() -> &'static std::sync::Mutex<BinderIds> {
    static IDS: std::sync::OnceLock<std::sync::Mutex<BinderIds>> = std::sync::OnceLock::new();
    IDS.get_or_init(|| {
        std::sync::Mutex::new(BinderIds {
            next: 1,
            ..Default::default()
        })
    })
}
impl GeneratedBinderId {
    pub(crate) fn fresh() -> Self {
        crate::instrumentation::record_deterministic_work(1);
        Self(binder_ids().lock().unwrap().fresh())
    }
    pub(crate) fn from_spelling(number: u64) -> Self {
        binder_ids().lock().unwrap().reserve(number);
        Self(number)
    }
    pub fn number(self) -> u64 {
        self.0
    }
    pub fn binding_name(self) -> BindingName {
        BindingName::Generated(self)
    }
}
type BinderSpelling = std::rc::Rc<dyn Fn(GeneratedBinderId) -> Option<std::rc::Rc<str>>>;

thread_local! {
    static GENERATED_BINDER_SPELLING: std::cell::RefCell<Option<BinderSpelling>> =
        const { std::cell::RefCell::new(None) };
}

/// Gives a generated binder a lexical spelling while emitting a certificate.
pub(crate) struct GeneratedBinderSpellingScope(Option<BinderSpelling>);

impl GeneratedBinderSpellingScope {
    pub(crate) fn is_active() -> bool {
        GENERATED_BINDER_SPELLING.with(|slot| slot.borrow().is_some())
    }

    pub(crate) fn enter(
        spelling: impl Fn(GeneratedBinderId) -> Option<std::rc::Rc<str>> + 'static,
    ) -> Self {
        Self(GENERATED_BINDER_SPELLING.with(|slot| slot.replace(Some(std::rc::Rc::new(spelling)))))
    }
}

impl Drop for GeneratedBinderSpellingScope {
    fn drop(&mut self) {
        GENERATED_BINDER_SPELLING.with(|slot| slot.replace(self.0.take()));
    }
}

impl std::fmt::Display for GeneratedBinderId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let spelling = GENERATED_BINDER_SPELLING
            .with(|slot| slot.borrow().as_ref().and_then(|spell| spell(*self)));
        if let Some(spelling) = spelling {
            f.write_str(&spelling)
        } else {
            write!(f, "binder({})", self.0)
        }
    }
}

/// The C declaration owning static storage. File ownership uses the root
/// translation unit, including for declarations brought in through a header.
#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum StaticBindingOwner {
    File(Option<String>),
    Function(LocalFunctionId),
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct StaticBindingMetadata {
    pub program_type: ProgramType,
    pub array_shape: Option<Arc<[u32]>>,
    pub struct_name: Option<Arc<str>>,
    pub aggregate: bool,
    pub volatile: bool,
    pub pointee_volatile: bool,
    pub constant: bool,
    pub pointee_constant: bool,
}

/// Stable identity of one static object; metadata is prepared from the final
/// compatible declaration and is excluded from storage identity.
#[derive(Clone, Debug)]
pub struct StaticBindingId(Arc<StaticDeclaration>);
#[derive(Debug)]
struct StaticDeclaration {
    owner: StaticBindingOwner,
    ordinal: u32,
    spelling: String,
    fingerprint: u64,
    metadata: OnceLock<StaticBindingMetadata>,
    struct_name: OnceLock<Arc<str>>,
}
impl StaticBindingId {
    pub fn new(owner: StaticBindingOwner, ordinal: u32, spelling: String) -> Self {
        let mut hasher = std::collections::hash_map::DefaultHasher::new();
        (&owner, ordinal).hash(&mut hasher);
        Self(Arc::new(StaticDeclaration {
            owner,
            ordinal,
            spelling,
            fingerprint: hasher.finish(),
            metadata: OnceLock::new(),
            struct_name: OnceLock::new(),
        }))
    }
    pub fn owner(&self) -> &StaticBindingOwner {
        &self.0.owner
    }
    pub fn ordinal(&self) -> u32 {
        self.0.ordinal
    }
    pub fn spelling(&self) -> &str {
        &self.0.spelling
    }
    pub fn source(&self) -> Option<&str> {
        match &self.0.owner {
            StaticBindingOwner::File(source) => source.as_deref(),
            StaticBindingOwner::Function(owner) => owner.0.source.as_deref(),
        }
    }
    pub fn function(&self) -> Option<&str> {
        match &self.0.owner {
            StaticBindingOwner::File(_) => None,
            StaticBindingOwner::Function(owner) => Some(&owner.0.function),
        }
    }
    pub(crate) fn initialize_metadata(&self, metadata: StaticBindingMetadata) {
        let _ = self.0.metadata.set(metadata);
    }
    pub fn metadata(&self) -> Option<&StaticBindingMetadata> {
        self.0.metadata.get()
    }
    pub fn program_type(&self) -> Option<ProgramType> {
        self.metadata().map(|m| m.program_type)
    }
    pub fn array_shape(&self) -> Option<&[u32]> {
        self.metadata()?.array_shape.as_deref()
    }
    pub(crate) fn initialize_struct_name(&self, name: &str) {
        let _ = self.0.struct_name.set(Arc::from(name));
    }
    pub fn struct_name(&self) -> Option<&str> {
        self.0
            .struct_name
            .get()
            .map(AsRef::as_ref)
            .or_else(|| self.metadata()?.struct_name.as_deref())
    }
    fn identity(&self) -> (&StaticBindingOwner, u32) {
        (&self.0.owner, self.0.ordinal)
    }
}
impl PartialEq for StaticBindingId {
    fn eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.0, &other.0) || self.identity() == other.identity()
    }
}
impl Eq for StaticBindingId {}
impl PartialOrd for StaticBindingId {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for StaticBindingId {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.identity().cmp(&other.identity())
    }
}
impl Hash for StaticBindingId {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.0.fingerprint.hash(state);
    }
}
impl std::fmt::Display for StaticBindingId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if let Some(source) = self.source() {
            write!(f, "{source:?}::")?;
        }
        if let Some(function) = self.function() {
            write!(f, "{function}.")?;
        }
        write!(f, "static({})", self.ordinal())
    }
}

/// Named bindings remain available to the other frontends and proof/model
/// binders. C automatic objects always use the declaration alternative.
#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum BindingName {
    Named(String),
    Local(LocalBindingId),
    Static(StaticBindingId),
    /// The current contract's return value; never a source declaration.
    ContractResult,
    /// The current exceptional postcondition's payload; never a declaration.
    ContractException,
    /// A lexical proof binder, never a program object.
    Generated(GeneratedBinderId),
    /// The address carrying a reference binding. The referent's binding is
    /// structural identity; an address-looking source string is never a carrier.
    ReferenceCarrier(Arc<BindingName>),
}

impl AddressBase {
    /// Allocation carrying a declaration's metadata or a load's point and
    /// cell. The process-wide term store can outlive either producer.
    pub(super) fn block_payload(&self) -> Option<std::num::NonZeroUsize> {
        let pointer = match self {
            Self::Load(load) | Self::SliceData(load) => return Some(load.payload_id()),
            Self::AutomaticLocal { binding, .. } => Arc::as_ptr(&binding.0).cast::<()>(),
            Self::StaticObject { binding } => Arc::as_ptr(&binding.0).cast(),
            Self::ReferenceCarrier { referent, .. } => Arc::as_ptr(referent).cast(),
            _ => return None,
        };
        std::num::NonZeroUsize::new(pointer.addr())
    }
}

impl BindingName {
    pub fn reference_carrier(referent: impl Into<BindingName>) -> Self {
        Self::ReferenceCarrier(Arc::new(referent.into()))
    }
    /// A source type-table lookup, separate from lexical value/storage lookup.
    pub(crate) fn metadata_in<'a, T>(&self, map: &'a impl NamedBindingMap<T>) -> Option<&'a T> {
        self.metadata_name().and_then(|name| map.get_named(name))
    }
    /// Key for Surface tables that carry parameter metadata by proof spelling.
    pub(crate) fn metadata_name(&self) -> Option<&str> {
        match self {
            _ => self.unresolved_name(),
        }
    }
    pub fn reference_referent(&self) -> Option<&BindingName> {
        match self {
            Self::ReferenceCarrier(referent) => Some(referent),
            _ => None,
        }
    }
    /// Unresolved source spelling for a metadata lookup. This never identifies
    /// execution storage: the carrier and its referent remain different keys.
    pub(crate) fn unresolved_name(&self) -> Option<&str> {
        match self {
            Self::Named(name) => Some(name),
            Self::ReferenceCarrier(referent) => referent.unresolved_name(),
            _ => None,
        }
    }
    /// A lexical source spelling, absent for frontend temporaries and outcomes.
    pub fn source_spelling(&self) -> Option<&str> {
        match self {
            Self::Named(name) => Some(name),
            Self::Local(id) => id.spelling(),
            Self::Static(id) => Some(id.spelling()),
            Self::ReferenceCarrier(_)
            | Self::ContractResult
            | Self::ContractException
            | Self::Generated(_) => None,
        }
    }
    pub fn source_name(&self) -> &str {
        match self {
            Self::Named(name) => name,
            Self::ReferenceCarrier(referent) => referent.source_name(),
            Self::Local(id) => id.spelling().unwrap_or(""),
            Self::Static(id) => id.spelling(),
            Self::ContractResult => "result",
            Self::ContractException => "exception",
            Self::Generated(_) => "",
        }
    }
    pub fn static_id(&self) -> Option<&StaticBindingId> {
        match self {
            Self::Static(id) => Some(id),
            _ => None,
        }
    }
    pub fn program_type(&self) -> Option<ProgramType> {
        match self {
            Self::Local(id) => id.program_type(),
            Self::Static(id) => id.program_type(),
            _ => None,
        }
    }
    pub fn array_shape(&self) -> Option<&[u32]> {
        match self {
            Self::Local(id) => id.array_shape(),
            Self::Static(id) => id.array_shape(),
            _ => None,
        }
    }
    pub fn struct_name(&self) -> Option<&str> {
        match self {
            Self::Local(id) => id.struct_name(),
            Self::Static(id) => id.struct_name(),
            _ => None,
        }
    }
    pub fn local_id(&self) -> Option<&LocalBindingId> {
        match self {
            Self::Local(id) => Some(id),
            _ => None,
        }
    }
    pub fn named(&self) -> Option<&str> {
        match self {
            Self::Named(name) => Some(name),
            _ => None,
        }
    }
}

/// Declaration metadata participates in program identity (including source
/// spelling changes), while storage and references use only `reference`.
#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct BindingDeclaration {
    reference: BindingName,
    spelling: Option<Arc<str>>,
    array_shape: Option<Arc<[u32]>>,
    struct_name: Option<Arc<str>>,
    scope_depth: u32,
    static_metadata: Option<Arc<StaticBindingMetadata>>,
}
impl BindingDeclaration {
    pub fn binding(&self) -> &BindingName {
        &self.reference
    }
    pub fn spelling(&self) -> Option<&str> {
        self.spelling.as_deref()
    }
    pub fn source_name(&self) -> &str {
        self.spelling().unwrap_or("")
    }
}
impl From<BindingName> for BindingDeclaration {
    fn from(reference: BindingName) -> Self {
        let spelling = match &reference {
            BindingName::Named(name) => Some(Arc::from(name.as_str())),
            BindingName::Local(id) => id.spelling().map(Arc::from),
            BindingName::Static(id) => Some(Arc::from(id.spelling())),
            BindingName::ContractResult => Some(Arc::from("result")),
            BindingName::ContractException => Some(Arc::from("exception")),
            BindingName::Generated(_) => None,
            BindingName::ReferenceCarrier(referent) => Some(Arc::from(referent.source_name())),
        };
        let scope_depth = reference.local_id().map_or(0, LocalBindingId::scope_depth);
        let array_shape = reference.array_shape().map(Arc::from);
        let struct_name = reference.struct_name().map(Arc::from);
        let static_metadata = reference
            .static_id()
            .and_then(StaticBindingId::metadata)
            .map(|metadata| Arc::new(metadata.clone()));
        Self {
            static_metadata,
            reference,
            spelling,
            array_shape,
            struct_name,
            scope_depth,
        }
    }
}
impl From<&BindingDeclaration> for BindingName {
    fn from(declaration: &BindingDeclaration) -> Self {
        declaration.reference.clone()
    }
}
impl From<BindingDeclaration> for BindingName {
    fn from(declaration: BindingDeclaration) -> Self {
        declaration.reference
    }
}
impl std::ops::Deref for BindingDeclaration {
    type Target = BindingName;
    fn deref(&self) -> &BindingName {
        &self.reference
    }
}
impl std::fmt::Display for BindingDeclaration {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.reference.fmt(f)
    }
}
impl From<String> for BindingName {
    fn from(name: String) -> Self {
        Self::Named(name)
    }
}
impl From<&str> for BindingName {
    fn from(name: &str) -> Self {
        Self::Named(name.to_owned())
    }
}
impl From<&String> for BindingName {
    fn from(name: &String) -> Self {
        Self::Named(name.clone())
    }
}
impl From<&BindingName> for BindingName {
    fn from(name: &BindingName) -> Self {
        name.clone()
    }
}
impl From<LocalBindingId> for BindingName {
    fn from(id: LocalBindingId) -> Self {
        Self::Local(id)
    }
}
/// Words a Surface expression reads as something other than a program
/// variable, so a C declaration with one of these spellings is written by its
/// typed identity.
fn is_click_expression_word(spelling: &str) -> bool {
    matches!(
        spelling,
        "result"
            | "exception"
            | "true"
            | "false"
            | "and"
            | "or"
            | "not"
            | "implies"
            | "iff"
            | "forall"
            | "exists"
            | "old"
            | "at"
            | "function"
            | "loop"
            | "region"
            | "statement"
            | "iteration"
            | "null"
            | "nullptr"
            | "sizeof"
            | "in"
            | "if"
            | "else"
            | "let"
            | "by"
    )
}

impl std::fmt::Display for BindingName {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Named(name) => f.write_str(name),
            Self::ReferenceCarrier(referent) => write!(f, "&{referent}"),
            Self::Local(id) => id.fmt(f),
            Self::Static(id) => id.fmt(f),
            Self::ContractResult => f.write_str("result"),
            Self::ContractException => f.write_str("exception"),
            Self::Generated(id) => id.fmt(f),
        }
    }
}

/// Per-execution storage identity, independent of the declaration and spelling.
#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum LocalStorageInstance {
    Implicit,
    ValueParameter,
    Lifetime(u64),
    Frame(u64),
}

impl From<std::sync::Arc<str>> for BindingName {
    fn from(name: std::sync::Arc<str>) -> Self {
        Self::Named(name.to_string())
    }
}
impl From<&std::sync::Arc<str>> for BindingName {
    fn from(name: &std::sync::Arc<str>) -> Self {
        Self::Named(name.to_string())
    }
}
impl BindingName {
    pub fn is_named(&self, name: &str) -> bool {
        self.named() == Some(name)
    }
    pub(crate) fn named_in<'a, T>(&self, map: &'a impl NamedBindingMap<T>) -> Option<&'a T> {
        map.get_binding(self)
    }
}

pub(crate) trait NamedBindingMap<T> {
    fn get_named(&self, name: &str) -> Option<&T>;
    fn get_binding(&self, name: &BindingName) -> Option<&T> {
        name.named().and_then(|name| self.get_named(name))
    }
}
impl<T> NamedBindingMap<T> for BTreeMap<String, T> {
    fn get_named(&self, name: &str) -> Option<&T> {
        self.get(name)
    }
}
impl<T> NamedBindingMap<T> for crate::persistent::PersistentMap<String, T> {
    fn get_named(&self, name: &str) -> Option<&T> {
        self.get(name)
    }
}

impl From<&&BindingName> for BindingName {
    fn from(name: &&BindingName) -> Self {
        (*name).clone()
    }
}

impl std::fmt::Display for LocalStorageInstance {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Implicit => f.write_str("implicit"),
            Self::ValueParameter => f.write_str("parameter"),
            Self::Lifetime(id) => write!(f, "lifetime, {id}"),
            Self::Frame(id) => write!(f, "frame, {id}"),
        }
    }
}

impl From<String> for BindingDeclaration {
    fn from(name: String) -> Self {
        BindingName::from(name).into()
    }
}
impl From<&str> for BindingDeclaration {
    fn from(name: &str) -> Self {
        BindingName::from(name).into()
    }
}

impl From<StaticBindingId> for BindingName {
    fn from(id: StaticBindingId) -> Self {
        Self::Static(id)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn reference_carriers_have_structural_identity_and_separate_storage() {
        let owner = LocalFunctionId::new(Some("references.cpp".into()), "f".into());
        let referent: BindingName = local(&owner, 0, "x", 0);
        let shadow: BindingName = local(&owner, 1, "x", 1);
        let carrier = BindingName::reference_carrier(referent.clone());
        assert_eq!(carrier.reference_referent(), Some(&referent));
        assert_ne!(carrier, referent);
        assert_ne!(carrier, BindingName::from("&x"));
        assert_ne!(carrier, BindingName::reference_carrier(shadow));
        assert!(carrier.source_spelling().is_none());
        let first = SymbolicMemory::frame_local_pointer(1, carrier.clone());
        assert_ne!(first, SymbolicMemory::frame_local_pointer(1, referent));
        assert_ne!(first, SymbolicMemory::frame_local_pointer(1, "&x"));
        assert_ne!(
            first,
            SymbolicMemory::frame_local_pointer(2, carrier.clone())
        );
        assert!(first.base.is_local_block());
        assert!(first.blocks_proven_distinct(&SymbolicMemory::frame_local_pointer(2, carrier)));
    }

    #[test]
    fn carrier_metadata_does_not_resolve_an_ordinary_value_name() {
        let carrier = BindingName::reference_carrier("x");
        let names = BTreeMap::from([("x".to_owned(), 7)]);
        assert_eq!(carrier.metadata_in(&names), Some(&7));
        assert!(carrier.named_in(&names).is_none());
        let mut locals = LocalEnvironment::default();
        locals.set("x", int32(1));
        locals.set("&x", int32(2));
        locals.set(carrier.clone(), int32(3));
        assert_eq!(locals.get("x").unwrap().native().as_ref(), &int32(1));
        assert_eq!(locals.get("&x").unwrap().native().as_ref(), &int32(2));
        assert_eq!(locals.get(&carrier).unwrap().native().as_ref(), &int32(3));
    }

    #[test]
    fn entry_resource_arguments_capture_the_reference_pointer_by_source_metadata() {
        let carrier = BindingName::reference_carrier("x");
        let variable = ProgramExpression::Variable(carrier);
        let fake = ProgramExpression::Variable("&x".into());
        let pointer = ProgramValue::pointer(Address::symbolic(Variable(71)));
        let other = ProgramValue::pointer(Address::symbolic(Variable(72)));
        let spec = ResourceSpec::declared_with_argument_states(
            ResourceFamily::Composite,
            ResourceAccessMode::Own,
            "references".into(),
            vec![variable.clone(), fake, variable.clone()],
            vec![
                ResourceStateSource::Entry,
                ResourceStateSource::Entry,
                ResourceStateSource::Current,
            ],
            vec![ProgramType::Int32Pointer; 3],
            ResourceTransferRole::Consume,
            ResourceStateSource::Current,
        )
        .unwrap()
        .with_captured_entry_parameters(&BTreeMap::from([
            ("x".into(), pointer.clone()),
            ("&x".into(), other.clone()),
        ]));
        assert_eq!(
            spec.declared_arguments().unwrap(),
            &[
                ProgramExpression::Value(pointer),
                ProgramExpression::Value(other),
                variable,
            ]
        );
    }

    fn local(owner: &LocalFunctionId, ordinal: u32, name: &str, depth: u32) -> BindingName {
        LocalBindingId::new(owner.clone(), false, ordinal, Some(name.into()))
            .with_scope_depth(depth)
            .into()
    }

    #[test]
    fn temporary_ids_are_distinct_from_declarations_and_legacy_spellings() {
        let owner = LocalFunctionId::new(Some("unit.cpp".into()), "f".into());
        let temporary: BindingName = LocalBindingId::temporary(owner.clone(), 0).into();
        let source = local(&owner, 0, "__click_cpp_return_value", 0);
        let parameter: BindingName =
            LocalBindingId::new(owner.clone(), true, 0, Some("p".into())).into();
        let mut locals = LocalEnvironment::new();
        locals.set(&temporary, int32(7));
        for (index, binding) in [
            source.clone(),
            parameter,
            "__click_cpp_return_value".into(),
            "__click_cpp_unwind_exception".into(),
            "__click_cpp_nested_value_0".into(),
        ]
        .into_iter()
        .enumerate()
        {
            assert_ne!(temporary, binding);
            locals.set(&binding, int32(index as u32));
            assert_eq!(locals.get(&temporary).unwrap().native().as_ref(), &int32(7));
            assert!(
                SymbolicMemory::local_pointer(&temporary)
                    .base
                    .proven_distinct(&SymbolicMemory::local_pointer(binding).base)
            );
        }
        assert_eq!(temporary.source_spelling(), None);
        assert_eq!(locals.active_source_name(&temporary), None);
        assert_eq!(locals.resolve_binding(&temporary), temporary);
        assert_ne!(temporary, BindingName::from(temporary.to_string()));
        assert_ne!(temporary, LocalBindingId::temporary(owner, 1).into());
        assert_ne!(
            temporary,
            LocalBindingId::temporary(
                LocalFunctionId::new(Some("other.cpp".into()), "f".into()),
                0
            )
            .into()
        );
    }

    #[test]
    fn contract_result_is_neither_a_source_name_nor_a_string_alias() {
        let owner = LocalFunctionId::new(None, "f".into());
        let source = local(&owner, 0, "result", 1);
        let mut locals = LocalEnvironment::new();
        locals.set(&source, int32(3));
        locals.bind_logical_typed("result", int32(7), ProgramType::Int32);
        locals.set(CONTRACT_RESULT, int32(11));
        locals.set("@click:result", int32(13));
        for (name, expected) in [
            (source.clone(), 3),
            (BindingName::from("result"), 7),
            (CONTRACT_RESULT, 11),
            (BindingName::from("@click:result"), 13),
        ] {
            assert_eq!(
                locals.get(&name).unwrap().native().as_ref(),
                &int32(expected)
            );
            assert_eq!(locals.resolve_binding(&name), name);
        }
        assert_eq!(locals.active_source_name(&CONTRACT_RESULT), None);
        assert_eq!(CONTRACT_RESULT.named(), None);
        assert_eq!(CONTRACT_RESULT.to_string(), "result");
        let result_slot = SymbolicMemory::local_pointer(CONTRACT_RESULT);
        assert_eq!(result_slot.base, AddressBase::ContractResult);
        for binding in [
            source,
            BindingName::from("result"),
            BindingName::from("@click:result"),
        ] {
            assert!(
                result_slot
                    .base
                    .proven_distinct(&SymbolicMemory::local_pointer(binding).base)
            );
        }
    }

    #[test]
    fn contract_exception_is_neither_a_source_name_nor_a_string_alias() {
        let owner = LocalFunctionId::new(None, "f".into());
        let source = local(&owner, 0, "exception", 1);
        let mut locals = LocalEnvironment::new();
        locals.set(&source, int32(3));
        locals.bind_logical_typed("exception", int32(7), ProgramType::Int32);
        locals.set(CONTRACT_EXCEPTION, int32(11));
        locals.set("__click_exception", int32(13));
        for (name, expected) in [
            (source.clone(), 3),
            (BindingName::from("exception"), 7),
            (CONTRACT_EXCEPTION, 11),
            (BindingName::from("__click_exception"), 13),
        ] {
            assert_eq!(
                locals.get(&name).unwrap().native().as_ref(),
                &int32(expected)
            );
            assert_eq!(locals.resolve_binding(&name), name);
        }
        assert_eq!(locals.active_source_name(&CONTRACT_EXCEPTION), None);
        assert_eq!(CONTRACT_EXCEPTION.named(), None);
        assert_eq!(CONTRACT_EXCEPTION.to_string(), "exception");
        let result_slot = SymbolicMemory::local_pointer(CONTRACT_EXCEPTION);
        assert_eq!(result_slot.base, AddressBase::ContractException);
        assert!(
            result_slot
                .base
                .proven_distinct(&AddressBase::ContractResult)
        );
        for binding in [
            source,
            BindingName::from("exception"),
            BindingName::from("__click_exception"),
        ] {
            assert!(
                result_slot
                    .base
                    .proven_distinct(&SymbolicMemory::local_pointer(binding).base)
            );
        }
    }

    #[test]
    fn declaration_identity_is_separate_from_spelling_and_program_metadata() {
        let owner = LocalFunctionId::new(Some("unit.c".into()), "f".into());
        let first = local(&owner, 0, "x", 1);
        let renamed = local(&owner, 0, "y", 2);
        assert_eq!(first, renamed);
        assert_ne!(
            BindingDeclaration::from(first.clone()),
            BindingDeclaration::from(renamed)
        );
        assert_ne!(first, local(&owner, 1, "x", 1));
        assert_ne!(
            first,
            LocalBindingId::new(owner, true, 0, Some("x".into())).into()
        );
    }

    #[test]
    fn lexical_lookup_and_logical_binders_keep_exact_declarations() {
        let owner = LocalFunctionId::new(None, "f".into());
        let outer = local(&owner, 1, "x", 1);
        // Declaration introduction order need not be lexical nesting order,
        // for example when a GNU initializer declares another object.
        let inner = local(&owner, 0, "x", 2);
        let mut locals = LocalEnvironment::new();
        locals.set(&outer, int32(3));
        locals.set(&inner, int32(7));
        assert_eq!(locals.get("x").unwrap().native().as_ref(), &int32(7));
        assert_eq!(locals.get(&outer).unwrap().native().as_ref(), &int32(3));
        locals.bind_logical_typed("x", int32(11), ProgramType::Int32);
        assert_eq!(locals.get("x").unwrap().native().as_ref(), &int32(11));
        assert_eq!(locals.get(&inner).unwrap().native().as_ref(), &int32(7));
        locals.remove("x");
        assert_eq!(locals.get("x").unwrap().native().as_ref(), &int32(7));
        locals.remove(&inner);
        assert_eq!(locals.get("x").unwrap().native().as_ref(), &int32(3));
    }

    #[test]
    fn source_declarations_and_execution_storage_instances_are_distinct() {
        let owner = LocalFunctionId::new(None, "f".into());
        let binding = local(&owner, 0, "x", 1);
        let same_name_elsewhere = local(&LocalFunctionId::new(None, "g".into()), 0, "x", 1);
        let addresses = [
            SymbolicMemory::local_pointer(&binding),
            SymbolicMemory::value_parameter_pointer(&binding),
            SymbolicMemory::local_lifetime_pointer(1, &binding),
            SymbolicMemory::local_lifetime_pointer(2, &binding),
            SymbolicMemory::frame_local_pointer(1, &binding),
            SymbolicMemory::frame_local_pointer(2, &binding),
            SymbolicMemory::local_pointer(same_name_elsewhere),
        ];
        for (index, address) in addresses.iter().enumerate() {
            for other in &addresses[index + 1..] {
                assert!(address.base.proven_distinct(&other.base));
            }
        }
    }

    #[test]
    fn a_declaration_is_written_by_its_spelling_only_when_unambiguous() {
        let owner = LocalFunctionId::new(Some("unit.c".into()), "f".into());
        let declare = |ordinal, name: &str, shadows| {
            owner.record_declaration_spelling(name, shadows);
            LocalBindingId::new(owner.clone(), false, ordinal, Some(name.into()))
        };
        let unique = declare(0, "count", false);
        let first = declare(1, "i", false);
        let reused = declare(2, "i", false);
        let shadowing = declare(3, "total", true);
        let reserved = declare(4, "result", false);
        assert_eq!(unique.to_string(), "count");
        assert_eq!(first.to_string(), "\"unit.c\"::f.local(1)");
        assert_eq!(reused.to_string(), "\"unit.c\"::f.local(2)");
        assert_eq!(shadowing.to_string(), "\"unit.c\"::f.local(3)");
        assert_eq!(reserved.to_string(), "\"unit.c\"::f.local(4)");
        // A declaration the parser never recorded keeps its typed identity.
        let unrecorded = LocalBindingId::new(owner.clone(), true, 0, Some("n".into()));
        assert_eq!(unrecorded.to_string(), "\"unit.c\"::f.parameter(0)");
        // Spellings are per function: another function's `count` is its own.
        let other = LocalFunctionId::new(Some("unit.c".into()), "g".into());
        other.record_declaration_spelling("count", false);
        assert_eq!(unique.to_string(), "count");
    }
}

#[cfg(test)]
mod scaling_tests {
    use super::*;
    include!("../../scaling_tests/kernel/primitives/bindings.rs");
}
