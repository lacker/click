//! Exact read descriptions and the version identities used to compare them.
//!
//! `MachineTerm::memory_read` constructs the exact descriptor. Selecting a
//! comparison identity is a separate legacy operation: it may choose another
//! memory state, but never mutates the descriptor it receives. Observation
//! publication is separate from both. The parent module retains the existing
//! cache and compatibility policy until logical reads migrate to exact states.

use super::*;

/// A borrowed view of the exact memory, address, and kind written in a read.
/// Constructing this view performs no version selection or registry lookup.
#[derive(Clone, Copy)]
pub(super) struct ScalarReadDescriptor<'a> {
    term: &'a MachineTerm,
    memory: &'a SharedMemory,
    pointer: &'a Pointer,
    kind: LoadKind,
}

impl<'a> ScalarReadDescriptor<'a> {
    pub(super) fn memory(&self) -> &'a SharedMemory {
        self.memory
    }

    pub(super) fn pointer(&self) -> &'a Pointer {
        self.pointer
    }

    pub(super) fn from_term(term: &'a MachineTerm) -> Option<Self> {
        let MachineTerm::MemoryLoad(memory, pointer, kind) = term else {
            return None;
        };
        Some(Self {
            term,
            memory,
            pointer,
            kind: *kind,
        })
    }
}

/// A selected read's comparison identity, distinct from the exact descriptor.
///
/// This transparent wrapper preserves the existing cache representation. Its
/// term conversion is deliberately named as legacy policy: current callers
/// still retain selected version reads, rather than their original descriptors.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct ScalarReadComparisonIdentity(MachineTerm);

impl ScalarReadComparisonIdentity {
    pub(super) fn as_legacy_read(&self) -> &MachineTerm {
        &self.0
    }

    pub(super) fn into_legacy_read(self) -> MachineTerm {
        self.0
    }
}

/// The existing cold version-selection route, with no new callers or walks.
/// This does not publish the selected read's observation; the compatibility
/// adapter does so once, after selection and before filling its cache.
/// `observed_bytes` distinguishes a known access width from the conservative
/// untyped default, preserving the adapter's cache invalidation rules.
pub(super) fn select_comparison_identity(
    read: ScalarReadDescriptor<'_>,
) -> (ScalarReadComparisonIdentity, Option<u32>) {
    let ScalarReadDescriptor {
        term: bits,
        memory: origin,
        pointer: original_pointer,
        kind: original_kind,
    } = read;
    let canonical = crate::kernel::memory_provenance::canonicalize_atomic_loads(bits);
    let candidate = match &canonical {
        MachineTerm::Variable(variable) => registered_load_term_for_variable(variable)
            .filter(
                |read| matches!(read, MachineTerm::MemoryLoad(_, address, kind) if address.as_ref() == original_pointer && *kind == original_kind),
            )
            .unwrap_or_else(|| bits.clone()),
        MachineTerm::MemoryLoad(memory, pointer, kind) if pointer.as_ref() == original_pointer && *kind == original_kind => {
            let held = memory
                .memory()
                .known_value(pointer)
                .and_then(|value| crate::kernel::spec::program_value_bitvector_term(&value))
                .and_then(|held| match held {
                    MachineTerm::Variable(variable) => registered_load_term_for_variable(&variable),
                    read @ MachineTerm::MemoryLoad(..) => Some(read),
                    _ => None,
                })
                .filter(|held| {
                    matches!(held, MachineTerm::MemoryLoad(_, at, held_kind)
                    if at == pointer && held_kind == kind)
                });
            held.unwrap_or(canonical)
        }
        _ => bits.clone(),
    };
    let MachineTerm::MemoryLoad(memory, pointer, kind) = candidate else {
        unreachable!("selected scalar read")
    };
    let recorded_bytes = recorded_load_access_width(origin, original_pointer)
        .or_else(|| recorded_load_access_width(&memory, &pointer))
        .or_else(|| {
            existing_read_access_width(origin, original_pointer, original_kind)
                .max(existing_read_access_width(&memory, &pointer, kind))
        });
    let bytes = recorded_bytes.unwrap_or_else(|| kind.unrecorded_access_byte_width());
    let version = crate::kernel::resource_tracker::last_same_version_point(
        crate::kernel::resource_tracker::TrackedResource::Cell {
            pointer: &pointer,
            bytes,
        },
        &crate::kernel::resource_tracker::VersionPoint::at(&memory),
    )
    .map(|point| point.shared_memory().clone())
    .unwrap_or(memory);
    (
        ScalarReadComparisonIdentity(MachineTerm::MemoryLoad(version, pointer, kind)),
        recorded_bytes,
    )
}

/// Publish width, defining state, and live origin for a selected identity.
/// This is bookkeeping, not the construction or selection of the read term.
pub(super) fn record_comparison_observation(
    identity: &ScalarReadComparisonIdentity,
    origin: &SharedMemory,
    observed_bytes: Option<u32>,
) {
    let MachineTerm::MemoryLoad(memory, pointer, kind) = identity.as_legacy_read() else {
        unreachable!("selected scalar read identity");
    };
    let id = match observed_bytes {
        Some(bytes) => read_observations::record(memory, pointer, *kind, origin, bytes),
        None => read_observations::record_untyped(memory, pointer, *kind, origin),
    };
    read_observations::select(id);
}
