//! Addresses: one shared handle per address, holding the producer's block
//! atom, its interned block identity and its shared displacement.
//!
//! [`SharedAddress`] is the kernel's view: its equality and hash are exact
//! producer identity, which kernel-term identity derives from. A block of a
//! kind with a scalar identity is compared by its atom; every other block by
//! its interned identity, where a pure call's identity is its payload, not
//! the logical call. [`Address`] is the written view of the same handle, the
//! production address type: its equality, order and hash are logical, by the
//! block atom and the offset's written syntax, as ordered maps, cell-store
//! range scans and fact sets require.
//!
//! The interner assigns block identities only. Each handle keeps the atom its
//! producer built, so the metadata a binding carries beside its identity (a
//! source spelling, a program type, a struct name) is always its producer's,
//! never that of another declaration, in this or another verification, that
//! happens to share the identity and interned it first.
use super::offsets::SharedAddressOffset;
use super::*;
use std::cmp::Ordering;

/// The block identity a handle carries beside its atom.
#[derive(Clone)]
enum BlockIdentity {
    // These atoms already have scalar identities. They need neither an arena
    // allocation nor weak-entry cleanup.
    Inline,
    Interned(Arc<BlockData>),
}

struct BlockData {
    id: u64,
    /// The atom the identity was first interned from: only the interner's
    /// key. Handles read their own atom.
    key: AddressBase,
}

/// Whether two atoms are one exact block: pure calls by payload, every
/// other block by its atom.
fn exact_block_equal(left: &AddressBase, right: &AddressBase) -> bool {
    match (left, right) {
        (AddressBase::PureFunctionApplication(a), AddressBase::PureFunctionApplication(b)) => {
            a.payload_id() == b.payload_id()
        }
        (a, b) => a == b,
    }
}

fn exact_block_fingerprint(block: &AddressBase) -> u64 {
    let mut hash = crate::id_hash::FingerprintHasher::default();
    match block {
        AddressBase::PureFunctionApplication(call) => {
            10u64.hash(&mut hash);
            call.payload_id().hash(&mut hash);
        }
        block => block.hash(&mut hash),
    }
    hash.finish()
}

fn is_inline_block(block: &AddressBase) -> bool {
    matches!(
        block,
        AddressBase::Symbolic(_)
            | AddressBase::FunctionSymbolic(_)
            | AddressBase::ExternalArgument
            | AddressBase::ExternalObject(_)
            | AddressBase::Load(_)
            | AddressBase::SliceData(_)
            | AddressBase::Heap(_)
            | AddressBase::Temporary(_)
    )
}

const INTERNER_SHARDS: usize = 16;

#[derive(Default)]
struct InternerShard {
    nodes: HashMap<u64, Vec<Weak<BlockData>>>,
    cleanup: VecDeque<u64>,
}

static NEXT_BLOCK_ID: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);

fn interner_shard(fingerprint: u64) -> &'static Mutex<InternerShard> {
    static SHARDS: std::sync::OnceLock<[Mutex<InternerShard>; INTERNER_SHARDS]> =
        std::sync::OnceLock::new();
    let shards = SHARDS.get_or_init(Default::default);
    &shards[(fingerprint % INTERNER_SHARDS as u64) as usize]
}

impl BlockIdentity {
    /// The identity of `block`: interned for every kind without a scalar
    /// identity.
    ///
    /// This is where an address's block is admitted. Interning reads the
    /// selected atom once, so it charges one unit plus the atom's variable
    /// bytes (a name, or a string literal's identity and bytes), whether or
    /// not the block was live already: the charge depends only on the atom,
    /// never on what this or another verification interned before. Removing
    /// dead entries is bounded arena upkeep run when an entry is inserted;
    /// whether that happens depends on process-wide liveness, so it is not
    /// charged.
    fn intern(block: &AddressBase) -> Self {
        if is_inline_block(block) {
            return Self::Inline;
        }
        let bytes = match block {
            AddressBase::Concrete(name) | AddressBase::Function(name) => name.len(),
            AddressBase::StringLiteral { identity, bytes } => {
                identity.payload_bytes().saturating_add(bytes.len())
            }
            _ => 0,
        };
        crate::instrumentation::record_deterministic_work(1 + bytes);
        let fingerprint = exact_block_fingerprint(block);
        let mut shard = interner_shard(fingerprint).lock().expect("block arena");
        let bucket = shard.nodes.entry(fingerprint).or_default();
        if let Some(node) = bucket
            .iter()
            .filter_map(Weak::upgrade)
            .find(|node| exact_block_equal(&node.key, block))
        {
            return Self::Interned(node);
        }
        let node = Arc::new(BlockData {
            id: NEXT_BLOCK_ID.fetch_add(1, std::sync::atomic::Ordering::Relaxed),
            key: block.clone(),
        });
        bucket.retain(|node| node.strong_count() > 0);
        bucket.push(Arc::downgrade(&node));
        let shard = &mut *shard;
        for _ in 0..shard.cleanup.len().min(8) {
            let key = shard.cleanup.pop_front().unwrap();
            let Some(bucket) = shard.nodes.get_mut(&key) else {
                continue;
            };
            bucket.retain(|node| node.strong_count() > 0);
            if bucket.is_empty() {
                shard.nodes.remove(&key);
            } else {
                shard.cleanup.push_back(key);
            }
        }
        shard.cleanup.push_back(fingerprint);
        Self::Interned(node)
    }

    /// The identity a new written address at this block takes. An
    /// observation key's inline call block (`SharedAddressBase::observation`)
    /// is interned again, as every written address's block is.
    fn written(&self, atom: &AddressBase) -> Self {
        match self {
            Self::Inline if !is_inline_block(atom) => Self::intern(atom),
            identity => identity.clone(),
        }
    }

    fn exact_equal(&self, other: &Self, left: &AddressBase, right: &AddressBase) -> bool {
        match (self, other) {
            (Self::Inline, Self::Inline) => left == right,
            (Self::Interned(a), Self::Interned(b)) => a.id == b.id,
            _ => false,
        }
    }

    fn exact_hash<H: Hasher>(&self, atom: &AddressBase, state: &mut H) {
        match self {
            Self::Inline => {
                0u8.hash(state);
                atom.hash(state);
            }
            Self::Interned(node) => {
                1u8.hash(state);
                node.id.hash(state);
            }
        }
    }

    /// Whether two blocks, each with its atom, are logically one block:
    /// one interned identity is one atom; distinct interned identities of
    /// kinds other than pure calls are distinct atoms.
    fn logical_equal(&self, other: &Self, left: &AddressBase, right: &AddressBase) -> bool {
        match (self, other) {
            (Self::Interned(a), Self::Interned(b)) if a.id == b.id => true,
            (Self::Interned(_), Self::Interned(_))
                if !matches!(left, AddressBase::PureFunctionApplication(_)) =>
            {
                false
            }
            _ => left == right,
        }
    }

    fn same_interned(&self, other: &Self) -> bool {
        matches!((self, other), (Self::Interned(a), Self::Interned(b)) if a.id == b.id)
    }
}

/// A block handle for kernel rewrites: the producer's atom and its identity.
#[derive(Clone)]
pub(crate) struct SharedAddressBase {
    atom: AddressBase,
    identity: BlockIdentity,
}

impl std::fmt::Debug for SharedAddressBase {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self.identity {
            BlockIdentity::Inline => f
                .debug_tuple("SharedAddressBase")
                .field(&self.atom)
                .finish(),
            BlockIdentity::Interned(node) => {
                f.debug_tuple("SharedAddressBase").field(&node.id).finish()
            }
        }
    }
}

impl PartialEq for SharedAddressBase {
    fn eq(&self, other: &Self) -> bool {
        self.identity
            .exact_equal(&other.identity, &self.atom, &other.atom)
    }
}
impl Eq for SharedAddressBase {}
impl Hash for SharedAddressBase {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.identity.exact_hash(&self.atom, state);
    }
}

impl SharedAddressBase {
    /// Admits `block` ([`BlockIdentity::intern`] states the charge).
    #[cfg(test)]
    pub(crate) fn new(block: AddressBase) -> Self {
        Self {
            identity: BlockIdentity::intern(&block),
            atom: block,
        }
    }

    /// Observation keys use the application's semantic scalar identity.
    /// Producer handles continue to retain its exact payload identity.
    pub(crate) fn observation(&self) -> Self {
        match &self.atom {
            AddressBase::PureFunctionApplication(_) => Self {
                atom: self.atom.clone(),
                identity: BlockIdentity::Inline,
            },
            _ => self.clone(),
        }
    }

    #[cfg(test)]
    pub(crate) fn native_atom(&self) -> &AddressBase {
        &self.atom
    }

    /// The written address `offset` bytes into this block. The block
    /// identity is reused, not interned again.
    pub(crate) fn address(&self, offset: AddressOffset) -> Address {
        Address(SharedAddress::from_parts(
            self.identity.written(&self.atom),
            self.atom.clone(),
            offset,
        ))
    }
}

/// A block as a key: compared, ordered and hashed as its atom, as an
/// `AddressBase` key is, and building addresses in the block from its
/// retained identity instead of admitting the block again.
#[derive(Clone)]
pub(crate) struct AddressBlock(SharedAddressBase);

impl AddressBlock {
    /// The block `address` is in.
    pub(crate) fn of(address: &Address) -> Self {
        Self(address.block())
    }

    /// A key for `block` that is only compared, as a range bound or a
    /// lookup: it admits nothing. An address built from it admits the block.
    pub(crate) fn key(block: &AddressBase) -> Self {
        Self(SharedAddressBase {
            atom: block.clone(),
            identity: BlockIdentity::Inline,
        })
    }

    /// The address `offset` bytes into this block.
    pub(crate) fn at(&self, offset: AddressOffset) -> Address {
        self.0.address(offset)
    }
}

impl std::ops::Deref for AddressBlock {
    type Target = AddressBase;
    fn deref(&self) -> &AddressBase {
        &self.0.atom
    }
}

impl std::fmt::Debug for AddressBlock {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.atom.fmt(f)
    }
}

impl PartialEq for AddressBlock {
    fn eq(&self, other: &Self) -> bool {
        self.0
            .identity
            .logical_equal(&other.0.identity, &self.0.atom, &other.0.atom)
    }
}
impl Eq for AddressBlock {}
impl PartialOrd for AddressBlock {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for AddressBlock {
    fn cmp(&self, other: &Self) -> Ordering {
        if self.0.identity.same_interned(&other.0.identity) {
            Ordering::Equal
        } else {
            self.0.atom.cmp(&other.0.atom)
        }
    }
}
impl Hash for AddressBlock {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.0.atom.hash(state);
    }
}

/// An address's block and displacement, read through [`Address`] (and
/// [`SharedAddress`]); never a value of its own.
#[expect(
    clippy::manual_non_exhaustive,
    reason = "only the defining module may construct the address handle parts"
)]
pub struct AddressParts {
    pub base: AddressBase,
    pub offset: AddressOffset,
    _handle_only: (),
}

struct SharedAddressData {
    parts: AddressParts,
    identity: BlockIdentity,
}

/// The kernel's address handle. Cloning inspects only the handle; equality
/// and hash are exact producer identity (module documentation).
#[derive(Clone)]
pub struct SharedAddress(Arc<SharedAddressData>);

impl std::fmt::Debug for SharedAddress {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("SharedAddress")
            .field("base", &self.block())
            .field("offset", self.offset())
            .finish()
    }
}

impl PartialEq for SharedAddress {
    fn eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.0, &other.0)
            || (self
                .0
                .identity
                .exact_equal(&other.0.identity, self.atom(), other.atom())
                && self.offset() == other.offset())
    }
}

impl Eq for SharedAddress {}

impl Hash for SharedAddress {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.0.identity.exact_hash(self.atom(), state);
        self.offset().hash(state);
    }
}

impl SharedAddress {
    pub(in crate::kernel) fn is_null(&self) -> bool {
        matches!(self.atom(), AddressBase::Concrete(name) if name == "null")
            && matches!(self.offset().node(), KernelAddressOffset::Constant(0))
    }

    pub(in crate::kernel) fn integer_address_bits(&self) -> Option<&OldMachineTerm> {
        if matches!(self.offset().node(), KernelAddressOffset::Constant(0))
            && let AddressBase::PureFunctionApplication(application) = self.atom()
        {
            application.integer_address_bits()
        } else {
            None
        }
    }

    fn from_parts(identity: BlockIdentity, base: AddressBase, offset: AddressOffset) -> Self {
        Self(Arc::new(SharedAddressData {
            parts: AddressParts {
                base,
                offset,
                _handle_only: (),
            },
            identity,
        }))
    }

    /// A kernel-built address. It charges its one allocation.
    pub(crate) fn new(base: SharedAddressBase, offset: SharedAddressOffset) -> Self {
        crate::instrumentation::record_deterministic_work(1);
        Self::from_parts(
            base.identity,
            base.atom,
            AddressOffset::from_shared_unchecked(offset),
        )
    }

    /// The producer's block atom.
    pub(crate) fn atom(&self) -> &AddressBase {
        &self.0.parts.base
    }

    /// The exact displacement handle.
    pub(crate) fn offset(&self) -> &SharedAddressOffset {
        self.0.parts.offset.shared()
    }

    /// The block handle, for rebuilding this block at another displacement.
    pub(crate) fn block(&self) -> SharedAddressBase {
        SharedAddressBase {
            atom: self.0.parts.base.clone(),
            identity: self.0.identity.clone(),
        }
    }

    /// Whether this handle's block is exactly `block`.
    pub(crate) fn has_block(&self, block: &SharedAddressBase) -> bool {
        self.0
            .identity
            .exact_equal(&block.identity, self.atom(), &block.atom)
    }

    /// Whether both handles have one exact block (`SharedAddressBase` equality).
    pub(crate) fn same_exact_block(&self, other: &Self) -> bool {
        self.0
            .identity
            .exact_equal(&other.0.identity, self.atom(), other.atom())
    }

    pub(crate) fn syntax_equal(&self, other: &Self) -> bool {
        self.0
            .identity
            .logical_equal(&other.0.identity, self.atom(), other.atom())
            && self.offset().syntax_equal(other.offset())
    }

    /// The written view of this handle, or why one of its offset's indices
    /// has no explicit output.
    pub(crate) fn written(&self) -> Result<&Address, &'static str> {
        AddressOffset::check_written(self.offset())?;
        // SAFETY: `Address` is a `repr(transparent)` wrapper of
        // `SharedAddress`, and its offset was just checked to be written.
        Ok(unsafe { &*(self as *const SharedAddress as *const Address) })
    }

    /// The written view of a handle known to be written: a part of a
    /// written pointer ([`crate::kernel::Pointer`]), whose addresses were
    /// written when it was built.
    pub(crate) fn written_view(&self) -> &Address {
        // SAFETY: `Address` is a `repr(transparent)` wrapper of
        // `SharedAddress`; the caller holds a written handle.
        unsafe { &*(self as *const SharedAddress as *const Address) }
    }

    /// Whether both are one handle.
    pub(crate) fn same_handle(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.0, &other.0)
    }

    /// The written view as an owned handle ([`Self::written`]), whose block
    /// has a written address's identity: an observation key's inline call
    /// block is interned again.
    pub(crate) fn export(&self) -> Result<Address, &'static str> {
        let written = self.written()?;
        Ok(match &self.0.identity {
            BlockIdentity::Inline if !is_inline_block(self.atom()) => {
                written.with_offset(written.offset.clone())
            }
            _ => written.clone(),
        })
    }
}

/// The production address: a shared handle compared by its written syntax
/// (module documentation). Its equality, order and hash are those of the
/// native address struct it replaced: block atom, then written offset.
/// Reading `address.base` and `address.offset` goes through [`AddressParts`];
/// an address is changed by building a new handle.
#[repr(transparent)]
#[derive(Clone)]
pub struct Address(SharedAddress);

impl Address {
    /// The address `offset` bytes into `base`. A block without a scalar
    /// identity is interned here ([`BlockIdentity::intern`] states the
    /// charge); constructing any other address charges nothing.
    pub fn new(base: AddressBase, offset: AddressOffset) -> Self {
        Self(SharedAddress::from_parts(
            BlockIdentity::intern(&base),
            base,
            offset,
        ))
    }

    /// A range bound or lookup key in `block`: it admits nothing, so it is
    /// only compared, never stored or handed to a kernel term. An address
    /// derived from it admits the block.
    pub(crate) fn range_bound(block: &AddressBase, offset: AddressOffset) -> Self {
        Self(SharedAddress::from_parts(
            BlockIdentity::Inline,
            block.clone(),
            offset,
        ))
    }

    /// The same block at `offset`. The block identity is reused.
    pub fn with_offset(&self, offset: AddressOffset) -> Self {
        Self(SharedAddress::from_parts(
            self.0.0.identity.written(&self.base),
            self.base.clone(),
            offset,
        ))
    }

    /// `base` at this address's offset.
    pub fn with_base(&self, base: AddressBase) -> Self {
        Self::new(base, self.offset.clone())
    }

    pub fn set_offset(&mut self, offset: AddressOffset) {
        *self = self.with_offset(offset);
    }

    pub fn set_base(&mut self, base: AddressBase) {
        *self = self.with_base(base);
    }

    /// The block and offset, taken without cloning when this is the only
    /// handle.
    pub fn into_parts(self) -> (AddressBase, AddressOffset) {
        match Arc::try_unwrap(self.0.0) {
            Ok(data) => (data.parts.base, data.parts.offset),
            Err(shared) => (shared.parts.base.clone(), shared.parts.offset.clone()),
        }
    }

    /// The kernel handle: the same allocation, compared exactly.
    pub(crate) fn shared(&self) -> &SharedAddress {
        &self.0
    }

    pub(crate) fn into_shared(self) -> SharedAddress {
        self.0
    }

    pub(crate) fn block(&self) -> SharedAddressBase {
        self.0.block()
    }
}

impl std::ops::Deref for Address {
    type Target = AddressParts;
    fn deref(&self) -> &AddressParts {
        &self.0.0.parts
    }
}

impl std::fmt::Debug for Address {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Address")
            .field("base", &self.base)
            .field("offset", &self.offset)
            .finish()
    }
}

impl PartialEq for Address {
    fn eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.0.0, &other.0.0)
            || (self
                .0
                .0
                .identity
                .logical_equal(&other.0.0.identity, &self.base, &other.base)
                && self.offset == other.offset)
    }
}

impl Eq for Address {}

impl PartialOrd for Address {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Address {
    /// The native struct's derived order: block atom, then written offset.
    fn cmp(&self, other: &Self) -> Ordering {
        if Arc::ptr_eq(&self.0.0, &other.0.0) {
            return Ordering::Equal;
        }
        let base = if self.0.0.identity.same_interned(&other.0.0.identity) {
            Ordering::Equal
        } else {
            self.base.cmp(&other.base)
        };
        base.then_with(|| self.offset.cmp(&other.offset))
    }
}

impl Hash for Address {
    /// The native struct's derived hash stream: block atom, then the
    /// written offset's stream. Fact-set treap priorities hash addresses,
    /// so the values are kept.
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.base.hash(state);
        self.offset.hash(state);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn address_atoms_round_trip_without_changing_identity_or_offset_shape() {
        let blocks = vec![
            AddressBase::Concrete("object".into()),
            AddressBase::StringLiteral {
                identity: StringLiteralId::new("literal", 0),
                bytes: vec![0, 255],
            },
            AddressBase::Function("function".into()),
            AddressBase::FunctionSymbolic(Variable(998001)),
            AddressBase::ExternalArgument,
            AddressBase::ExternalObject(Variable(998002)),
            AddressBase::Symbolic(Variable(998003)),
            Address::loaded_value(
                &crate::kernel::intern_memory(SymbolicMemory::new()),
                &Address::symbolic(Variable(998004)),
            )
            .base
            .clone(),
            AddressBase::PureFunctionApplication(SharedPureApplication::intern(
                "call".into(),
                vec![],
            )),
            AddressBase::Heap(998005),
            AddressBase::Temporary(998006),
        ];
        for block in blocks {
            let offset = AddressOffset::raw_add(
                AddressOffset::constant(0),
                AddressOffset::variable(Variable(998007)),
            );
            let source = Address::new(block.clone(), offset.clone());
            let shared = source.shared().clone();
            assert_eq!(shared.export().unwrap(), source);
            let again = Address::new(block, offset);
            assert_eq!(again, source);
            assert_eq!(again.shared(), &shared);
            assert!(matches!(
                shared.offset().node(),
                KernelAddressOffset::Add(_)
            ));
        }
    }

    /// Two declarations with one identity (here, from two programs that
    /// both name `"drift.c"::drift.local(0)`) can carry different metadata.
    /// The block identity is shared, but each address reads its own
    /// producer's spelling and type, whichever declaration interned first.
    #[test]
    fn interned_blocks_keep_each_producers_binding_metadata() {
        let declaration = |spelling: &str, ty: ProgramType| {
            let owner = LocalFunctionId::new(Some("drift.c".into()), "drift".into());
            owner.record_declaration_spelling(spelling, false);
            let binding = LocalBindingId::new(owner, false, 0, Some(spelling.into()));
            binding.initialize_program_type(ty);
            binding
        };
        let first = declaration("x", ProgramType::Int32);
        let second = declaration("y", ProgramType::Int64);
        assert_eq!(first, second);
        let address = |binding: LocalBindingId| {
            Address::new(
                AddressBase::AutomaticLocal {
                    binding,
                    instance: LocalStorageInstance::Implicit,
                },
                AddressOffset::constant(0),
            )
        };
        let retained = address(first);
        let produced = address(second);
        assert!(retained.shared().same_exact_block(produced.shared()));
        assert_eq!(retained, produced);
        let kernel = produced.shared().clone();
        for view in [&produced, kernel.written().unwrap()] {
            let AddressBase::AutomaticLocal { binding, .. } = &view.base else {
                panic!("local block")
            };
            assert_eq!(binding.spelling(), Some("y"));
            assert_eq!(binding.program_type(), Some(ProgramType::Int64));
            assert_eq!(binding.to_string(), "y");
        }
        let first = crate::kernel::Pointer::new(retained, ProgramType::UInt8Pointer);
        let second = crate::kernel::Pointer::new(produced, ProgramType::UInt8Pointer);
        let forward = StoredConditionTerm::logical_pointer_equal(&first, &second);
        let reverse = StoredConditionTerm::logical_pointer_equal(&second, &first);
        for (comparison, name, ty) in [
            (forward, "x", ProgramType::Int32),
            (reverse, "y", ProgramType::Int64),
        ] {
            assert!(!comparison.root().unwrap().has_cached_native_argument());
            for address in comparison.operand_view().pointer_addresses().unwrap() {
                let AddressBase::AutomaticLocal { binding, .. } = address.atom() else {
                    panic!("expected local block")
                };
                assert_eq!(binding.spelling(), Some(name));
                assert_eq!(binding.program_type(), Some(ty));
            }
        }
    }

    #[test]
    fn address_equality_keeps_each_producers_binding_metadata() {
        let _session = crate::kernel::VerificationSession::enter();
        for (order, declarations) in [
            [("x", ProgramType::Int32), ("y", ProgramType::Int64)],
            [("y", ProgramType::Int64), ("x", ProgramType::Int32)],
        ]
        .into_iter()
        .enumerate()
        {
            let other = Address::symbolic(Variable(999040));
            let mut numeric_roots = Vec::new();
            let stored = declarations.map(|(name, ty)| {
                let owner = LocalFunctionId::new(None, format!("address_equal_{order}"));
                owner.record_declaration_spelling(name, false);
                let binding = LocalBindingId::new(owner, false, 0, Some(name.into()));
                binding.initialize_program_type(ty);
                let local = Address::new(
                    AddressBase::AutomaticLocal {
                        binding,
                        instance: LocalStorageInstance::Implicit,
                    },
                    AddressOffset::constant(0),
                );
                // Converting to a numeric address is another interning boundary.
                let numeric = KernelTerm::shared_pointer_address_observation(
                    MachineIntegerType::UInt64,
                    local.shared().clone(),
                    AddressObjectClass::NONE,
                );
                let OldMachineTerm::IntegerAddress(exported, _) =
                    KernelTermExport::machine(&numeric).unwrap()
                else {
                    panic!("expected numeric address")
                };
                let AddressBase::AutomaticLocal { binding, .. } = &exported.base else {
                    panic!("expected local block")
                };
                assert_eq!(binding.spelling(), Some(name));
                assert_eq!(binding.program_type(), Some(ty));
                numeric_roots.push(numeric);
                let stored = StoredConditionTerm::address_equal(&local, &other);
                let root = stored.root().unwrap();
                assert!(!root.has_cached_native_argument());
                let displaced = local.with_offset(AddressOffset::raw_add(
                    AddressOffset::constant(1),
                    AddressOffset::constant(-1),
                ));
                let raw = KernelTerm::address_equal_raw([
                    displaced.into_shared(),
                    other.shared().clone(),
                ]);
                let source = crate::kernel::Proposition::condition_is(
                    StoredConditionTerm::from_root(raw.clone()).unwrap(),
                    false,
                );
                let crate::kernel::Proposition::ConditionIs(canonical, false) =
                    crate::kernel::canonical_condition_fact(&source)
                else {
                    panic!("expected negative address fact")
                };
                assert_eq!(canonical.root(), Some(root));
                assert!(!raw.has_cached_native_argument());
                assert!(!root.has_cached_native_argument());
                let native = StoredConditionTerm::from(OldConditionTerm::AddressEqual(
                    Box::new(local),
                    Box::new(other.clone()),
                ));
                assert_eq!(native.root(), Some(root));
                stored
            });
            assert_ne!(numeric_roots[0], numeric_roots[1]);
            let roots = stored.each_ref().map(|term| term.root().unwrap());
            assert_ne!(roots[0], roots[1]);
            assert_eq!(stored[0], stored[1]);
            let locals = stored.each_ref().map(|term| {
                let [local, _] = term.operand_view().pointer_addresses().unwrap();
                local
            });
            let reflexive = crate::kernel::Proposition::condition_is(
                StoredConditionTerm::from_root(KernelTerm::address_equal_raw(locals)).unwrap(),
                true,
            );
            let goal =
                crate::kernel::Proposition::condition_is(StoredConditionTerm::constant(true), true);
            assert_eq!(
                crate::kernel::proof::equality_rewrite::rewrite_proposition_by_exact_equality(
                    &goal,
                    &reflexive,
                    &[],
                )
                .unwrap(),
                goal
            );
            let facts = std::collections::HashSet::from([stored[0].clone()]);
            assert!(facts.contains(&stored[1]));
            let observations =
                roots.map(crate::kernel::primitives::integer::observation_identity::normalize);
            assert_eq!(observations[0], observations[1]);
            for (term, (name, ty)) in stored.iter().zip(declarations) {
                let fact = crate::kernel::Proposition::condition_is(term.clone(), true);
                let Some(crate::kernel::Proposition::ConditionIs(reversed, true)) =
                    crate::kernel::proof::equality_rewrite::reverse_equality(&fact)
                else {
                    panic!("expected reversed address equality");
                };
                let [left, right] = term.operand_view().pointer_addresses().unwrap();
                // Both possible result roots are already interned. Rebuilding
                // local == other must select this declaration's exact root.
                let third = Address::symbolic(Variable(999048)).into_shared();
                let equality = |arguments| {
                    crate::kernel::Proposition::condition_is(
                        StoredConditionTerm::from_root(KernelTerm::address_equal_raw(arguments))
                            .unwrap(),
                        true,
                    )
                };
                let goal = equality([left.clone(), third.clone()]);
                let cited = equality([third, right.clone()]);
                let crate::kernel::Proposition::ConditionIs(result, true) =
                    crate::kernel::proof::equality_rewrite::rewrite_proposition_by_exact_equality(
                        &goal,
                        &cited,
                        std::slice::from_ref(&cited),
                    )
                    .unwrap()
                else {
                    panic!("expected rewritten address equality");
                };
                assert_eq!(result.root(), term.root());
                assert_eq!(
                    reversed.operand_view().pointer_addresses().unwrap(),
                    [right, left]
                );
                let premise = crate::kernel::Proposition::condition_is(reversed, true);
                let loadable = crate::kernel::Proposition::MemoryLoadable {
                    point: Default::default(),
                    memory: crate::kernel::SymbolicMemory::new(),
                    base: other.clone(),
                    bytes: OldMachineTerm::constant(1).into(),
                    wide: false,
                };
                let crate::kernel::Proposition::MemoryLoadable { base, .. } =
                    crate::kernel::proof::equality_rewrite::rewrite_proposition_by_exact_equality(
                        &loadable,
                        &premise,
                        std::slice::from_ref(&premise),
                    )
                    .unwrap()
                else {
                    panic!("expected rewritten loadability claim");
                };
                let AddressBase::AutomaticLocal { binding, .. } = &base.base else {
                    panic!("expected rewritten local block");
                };
                assert_eq!(binding.spelling(), Some(name));
                assert_eq!(binding.program_type(), Some(ty));
                let pointers = crate::kernel::proof::term_rewrite::proposition_pointer_terms(&fact);
                let [local, right] = pointers.as_slice() else {
                    panic!("expected both address equality operands");
                };
                assert_eq!(right, &other);
                let AddressBase::AutomaticLocal { binding, .. } = &local.base else {
                    panic!("expected local block");
                };
                assert_eq!(binding.spelling(), Some(name));
                assert_eq!(binding.program_type(), Some(ty));
                let exported = KernelTermExport::condition(term.root().unwrap()).unwrap();
                for written in [term.old_form(), &exported] {
                    let OldConditionTerm::AddressEqual(local, _) = written else {
                        panic!("expected address equality")
                    };
                    let AddressBase::AutomaticLocal { binding, .. } = &local.base else {
                        panic!("expected local block")
                    };
                    assert_eq!(binding.spelling(), Some(name));
                    assert_eq!(binding.program_type(), Some(ty));
                }
            }
        }
    }

    #[test]
    fn address_equality_keeps_the_load_from_its_own_session() {
        let produce = || {
            let _session = crate::kernel::VerificationSession::enter();
            let memory = crate::kernel::intern_memory(crate::kernel::SymbolicMemory::new());
            let cell = Address::symbolic(Variable(999043));
            let address = Address::loaded_value(&memory, &cell);
            let format = MachineIntegerType::UInt64;
            let numeric = KernelTerm::shared_pointer_address_observation(
                format,
                address.shared().clone(),
                AddressObjectClass::NONE,
            );
            let zero =
                KernelTermImport::default().machine(format, &OldMachineTerm::uint64_constant(0));
            let comparison =
                KernelTerm::boolean_comparison(format, CompareRelation::Equal, [numeric, zero]);
            assert_eq!(
                comparison,
                KernelTerm::address_equal_raw([
                    address.shared().clone(),
                    Address::null().into_shared()
                ])
            );
            let root = KernelTerm::address_equal_raw([address.into_shared(), cell.into_shared()]);
            (root, memory.arena_id())
        };
        let first = produce();
        let second = produce();
        assert_ne!(first.1, second.1);
        assert_ne!(first.0, second.0);
        let load_ids = [first, second].map(|(root, arena)| {
            let KernelTermNode::AddressEqual { arguments, .. } = root.node() else {
                panic!("expected address equality")
            };
            let AddressBase::Load(load) = arguments[0].atom() else {
                panic!("expected load")
            };
            assert_eq!(load.point().shared_memory().arena_id(), arena);
            load.id()
        });
        assert_eq!(load_ids[0], load_ids[1]);
    }

    #[test]
    fn exact_call_payloads_remain_separate_from_logical_call_identity() {
        let a = SharedPureApplication::intern("call".into(), vec![]);
        let b = SharedPureApplication::intern("call".into(), vec![]);
        assert_eq!(a, b);
        assert_ne!(a.payload_id(), b.payload_id());
        let address = |call| {
            Address::new(
                AddressBase::PureFunctionApplication(call),
                AddressOffset::constant(0),
            )
        };
        let left = address(a.clone());
        let right = address(b);
        assert_ne!(left.shared(), right.shared());
        assert_eq!(left, right);
        let mut hashes = [&left, &right]
            .map(|address| {
                let mut hash = std::collections::hash_map::DefaultHasher::new();
                address.hash(&mut hash);
                hash.finish()
            })
            .to_vec();
        hashes.dedup();
        assert_eq!(hashes.len(), 1);
        let AddressBase::PureFunctionApplication(output) = &left.base else {
            panic!("call")
        };
        assert_eq!(output.payload_id(), a.payload_id());
    }

    /// The written view keeps the deleted native struct's derived traits:
    /// order by block atom then offset, and its hash stream.
    #[test]
    fn written_addresses_keep_native_order_and_hash() {
        let blocks = [
            AddressBase::Concrete("b".into()),
            AddressBase::Concrete("a".into()),
            AddressBase::Symbolic(Variable(998101)),
            AddressBase::Heap(3),
        ];
        let offsets = [AddressOffset::constant(8), AddressOffset::constant(0)];
        for left_block in &blocks {
            for right_block in &blocks {
                for left_offset in &offsets {
                    for right_offset in &offsets {
                        let left = Address::new(left_block.clone(), left_offset.clone());
                        let right = Address::new(right_block.clone(), right_offset.clone());
                        assert_eq!(
                            left.cmp(&right),
                            (left_block, left_offset).cmp(&(right_block, right_offset))
                        );
                        assert_eq!(
                            left == right,
                            (left_block, left_offset) == (right_block, right_offset)
                        );
                    }
                }
            }
            let mut native = std::collections::hash_map::DefaultHasher::new();
            left_block.hash(&mut native);
            offsets[0].hash(&mut native);
            let mut written = std::collections::hash_map::DefaultHasher::new();
            Address::new(left_block.clone(), offsets[0].clone()).hash(&mut written);
            assert_eq!(native.finish(), written.finish());
        }
    }
}
#[cfg(test)]
mod scaling_tests {
    include!("../../../scaling_tests/kernel/primitives/kernel_term/addresses.rs");
}
