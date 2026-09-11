//! Opaque atoms used by the checked mathematical-Integer affine fragment.
//!
//! Range folds are not expanded by affine normalization.  They are leaves
//! whose identity is recomputed from the checked, snapshot-aware alpha key
//! for the complete fold term.  The interner below only uses the key's
//! fingerprint to select a bucket; equality within a bucket always compares
//! the retained exact key.  This keeps a hash collision from merging two
//! proof atoms while keeping the hot affine map keyed by a compact id.

use super::fact_keys::{IntegerFoldAlphaKey, integer_fold_alpha_key};
use crate::kernel::SharedIntegerTerm;
use std::collections::{HashMap, VecDeque};
use std::fmt;
use std::hash::{Hash, Hasher};
use std::sync::{Arc, Mutex, OnceLock, Weak};

/// The exact canonical identity for one live fold atom.
///
/// The key remains behind the `Arc` so that compact affine ordering never
/// compares a deep fold tree.  It also prevents a compact-id collision from
/// becoming a proof collision: two records with the same fingerprint receive
/// different ids unless their exact keys compare equal.
pub(crate) struct IntegerFoldAtomRecord {
    id: u64,
    key: IntegerFoldAlphaKey,
}

impl IntegerFoldAtomRecord {
    fn new(id: u64, key: IntegerFoldAlphaKey) -> Self {
        Self { id, key }
    }

    pub(crate) fn id(&self) -> u64 {
        self.id
    }

    pub(crate) fn fingerprint(&self) -> u64 {
        self.key.fingerprint()
    }
}

impl fmt::Debug for IntegerFoldAtomRecord {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("IntegerFoldAtomRecord")
            .field("id", &self.id)
            .field("fingerprint", &self.fingerprint())
            .finish()
    }
}

/// A compact atom identity.  The fold variant retains its exact canonical
/// key in an `Arc` while all map ordering and equality use the unique id.
#[derive(Clone)]
pub(crate) enum IntegerAffineAtom {
    Variable(crate::kernel::Variable),
    Machine(u64),
    Application(u64),
    Fold(Arc<IntegerFoldAtomRecord>),
}

impl fmt::Debug for IntegerAffineAtom {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Variable(variable) => formatter.debug_tuple("Variable").field(variable).finish(),
            Self::Machine(id) => formatter.debug_tuple("Machine").field(id).finish(),
            Self::Application(id) => formatter.debug_tuple("Application").field(id).finish(),
            Self::Fold(record) => formatter.debug_tuple("Fold").field(&record.id()).finish(),
        }
    }
}

impl PartialEq for IntegerAffineAtom {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Variable(left), Self::Variable(right)) => left == right,
            (Self::Machine(left), Self::Machine(right)) => left == right,
            (Self::Application(left), Self::Application(right)) => left == right,
            (Self::Fold(left), Self::Fold(right)) => left.id() == right.id(),
            _ => false,
        }
    }
}

impl Eq for IntegerAffineAtom {}

impl Ord for IntegerAffineAtom {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        use std::cmp::Ordering;
        let tag = |atom: &Self| match atom {
            Self::Variable(_) => 0u8,
            Self::Machine(_) => 1,
            Self::Application(_) => 2,
            Self::Fold(_) => 3,
        };
        match tag(self).cmp(&tag(other)) {
            Ordering::Equal => match (self, other) {
                (Self::Variable(left), Self::Variable(right)) => left.cmp(right),
                (Self::Machine(left), Self::Machine(right)) => left.cmp(right),
                (Self::Application(left), Self::Application(right)) => left.cmp(right),
                (Self::Fold(left), Self::Fold(right)) => left.id().cmp(&right.id()),
                _ => unreachable!("atom tags already match"),
            },
            ordering => ordering,
        }
    }
}

impl PartialOrd for IntegerAffineAtom {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Hash for IntegerAffineAtom {
    fn hash<H: Hasher>(&self, state: &mut H) {
        match self {
            Self::Variable(variable) => {
                0u8.hash(state);
                variable.hash(state);
            }
            Self::Machine(id) => {
                1u8.hash(state);
                id.hash(state);
            }
            Self::Application(id) => {
                2u8.hash(state);
                id.hash(state);
            }
            Self::Fold(record) => {
                3u8.hash(state);
                record.id().hash(state);
            }
        }
    }
}

struct IntegerFoldAtomInterner {
    buckets: HashMap<u64, Vec<Weak<IntegerFoldAtomRecord>>>,
    cleanup: VecDeque<(u64, usize)>,
    next_id: u64,
}

static INTEGER_FOLD_ATOM_INTERNER: OnceLock<Mutex<IntegerFoldAtomInterner>> = OnceLock::new();

fn interner() -> &'static Mutex<IntegerFoldAtomInterner> {
    INTEGER_FOLD_ATOM_INTERNER.get_or_init(|| {
        Mutex::new(IntegerFoldAtomInterner {
            buckets: HashMap::new(),
            cleanup: VecDeque::new(),
            next_id: 0,
        })
    })
}

impl IntegerFoldAtomInterner {
    fn clean_some(&mut self) -> bool {
        let limit = self.cleanup.len().min(8);
        for _ in 0..limit {
            let Some((fingerprint, pointer)) = self.cleanup.pop_front() else {
                break;
            };
            let mut requeue = false;
            if let Some(bucket) = self.buckets.get_mut(&fingerprint) {
                let mut exhausted = false;
                bucket.retain(|candidate| {
                    if crate::instrumentation::deadline_exceeded_with_work(1) {
                        exhausted = true;
                        return true;
                    }
                    let live_target =
                        candidate.as_ptr() as usize == pointer && candidate.strong_count() != 0;
                    if live_target {
                        requeue = true;
                    }
                    candidate.as_ptr() as usize != pointer || candidate.strong_count() != 0
                });
                if exhausted {
                    self.cleanup.push_front((fingerprint, pointer));
                    return false;
                }
                if bucket.is_empty() {
                    self.buckets.remove(&fingerprint);
                }
            }
            if requeue {
                self.cleanup.push_back((fingerprint, pointer));
            }
        }
        true
    }

    fn intern(&mut self, key: IntegerFoldAlphaKey) -> Option<Arc<IntegerFoldAtomRecord>> {
        if !self.clean_some() {
            return None;
        }
        // The snapshot-aware key accounts for its complete canonical graph
        // before hashing. This includes nested machine payloads and pointer
        // snapshots, so a deep key cannot hide behind a unit charge here.
        let fingerprint = key.checked_fingerprint()?;
        if let Some(bucket) = self.buckets.get(&fingerprint) {
            for candidate in bucket {
                let Some(record) = candidate.upgrade() else {
                    continue;
                };
                // Fingerprints only select this bucket. Exact equality is
                // separately checked and charged by the retained key API.
                if record.key.checked_eq(&key)? {
                    return Some(record);
                }
            }
        }
        let id = self.next_id;
        self.next_id = self
            .next_id
            .checked_add(1)
            .expect("Integer affine fold atom identity exhausted");
        let record = Arc::new(IntegerFoldAtomRecord::new(id, key));
        self.buckets
            .entry(fingerprint)
            .or_default()
            .push(Arc::downgrade(&record));
        self.cleanup
            .push_back((fingerprint, Arc::as_ptr(&record) as usize));
        Some(record)
    }
}

/// Recompute and intern the exact checked identity of one RangeFold term.
///
/// The caller must supply the complete shared term captured from the checked
/// proof state.  In particular, a caller-provided node id or fingerprint is
/// never accepted as a substitute for this kernel recomputation.
pub(crate) fn intern_integer_fold_atom(
    term: &SharedIntegerTerm,
) -> Option<Arc<IntegerFoldAtomRecord>> {
    let key = integer_fold_alpha_key(term)?;
    interner()
        .lock()
        .expect("Integer affine fold atom interner lock poisoned")
        .intern(key)
}
