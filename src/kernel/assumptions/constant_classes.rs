//! Equality classes of the true `Bitvector32Equal` condition facts, each
//! carrying the constant its members are proved to denote.
//!
//! A term's constant after equality normalization is the merge, over every
//! term the equality facts connect it to, of the constant that term folds to
//! from its own operands. Walking those facts per query re-derives a counter's
//! whole history at every use: after `N` calls that each ensure
//! `x_k == x_{k-1} + 1`, one query walks `N` facts and scans every fact at each
//! of them. This index keeps the answer instead. Each fact joins the classes
//! of its two sides, and each class keeps the merge of its members' folded
//! constants as `Known(c) | Ambiguous | Unknown`, updated on every insertion:
//!
//! - a union merges the two classes' constants, so two different constants
//!   anywhere in one class make it `Ambiguous`, exactly as the walk found them
//!   when it reached both;
//! - a class whose constant changes re-folds the compound terms that use one
//!   of its members as an operand (`users`), and so on outward. A constant only
//!   ever rises from `Unknown` to `Known(c)` to `Ambiguous`, so each registered
//!   term is re-folded at most twice per operand along one path.
//!
//! A signed byte read `int8(u)` (`Bitvector32Term::signed_byte`) is both
//! folded and inverted. It folds from `u` like an arithmetic term, and when
//! `u` is a byte load (`signed_byte_load_operand`) its class's constant also
//! settles `u`: the conversion is a bijection from `0..=255` onto
//! `-128..=127`, so `int8(u) == k` with `k` in that range means
//! `u == k mod 256`. Both directions are the same index the checker and the
//! search read, so neither tool decides a byte the other cannot.
//!
//! A query is then one lookup. Two things the index does not state are asked
//! at query time, of the queried term's class only: a conditional member is
//! decided under the whole context, and a load member of a class that is still
//! `Unknown` is compared with the loads of settled classes at the same address
//! (`settled_loads`), because two loads of one cell at different snapshots can
//! be proved equal by memory reasoning no fact states. A settled class is not
//! bridged: a second constant reached through a proved load equality would
//! make the context inconsistent, which the constant it already has cannot
//! make unsound.

use super::*;

/// One class of terms the recorded equality facts prove equal.
#[derive(Clone, Debug)]
struct ConstantClass {
    members: crate::persistent::PersistentSet<Bitvector32Term>,
    constant: SignedConstantResolution,
    /// Registered compound terms with a member of this class as a direct
    /// operand: the terms whose fold changes when this constant does.
    users: crate::persistent::PersistentSet<Bitvector32Term>,
    /// Load members, by the memory-blind fingerprint of the loaded pointer.
    loads: crate::persistent::PersistentMap<u64, crate::persistent::PersistentSet<Bitvector32Term>>,
    /// Members headed by a conditional, which only the whole context decides.
    conditionals: crate::persistent::PersistentSet<Bitvector32Term>,
    /// Members that are signed reads of a byte load, whose constant also
    /// settles the byte (`signed_byte_load_operand`).
    signed_bytes: crate::persistent::PersistentSet<Bitvector32Term>,
}

#[derive(Clone, Debug, Default)]
pub(in crate::kernel) struct ConstantClasses {
    class_of: crate::persistent::PersistentMap<Bitvector32Term, u64>,
    classes: crate::persistent::PersistentMap<u64, ConstantClass>,
    /// Load members of classes whose constant is not `Unknown`, by the
    /// memory-blind fingerprint of the loaded pointer, with their class.
    settled_loads: crate::persistent::PersistentMap<
        u64,
        crate::persistent::PersistentMap<Bitvector32Term, u64>,
    >,
    next_id: u64,
}

/// The direct operands of a term whose constant is a function of its
/// operands' constants, in the order the fold reads them.
fn arithmetic_operands(term: &Bitvector32Term) -> Option<Vec<&Bitvector32Term>> {
    match term {
        crate::kernel::binary_bitvector32_term!(left, right) => Some(vec![left, right]),
        Bitvector32Term::BitwiseNot(value) => Some(vec![value]),
        term => term.signed_byte_operand().map(|value| vec![value]),
    }
}

/// The byte load a signed byte read converts, when its operand is one.
///
/// Inverting `int8(u) == k` needs `u` in `0..=255`, the domain on which the
/// conversion is injective. A `UInt8` memory load (or the registered
/// variable naming one) holds exactly one byte, zero-extended, whatever
/// produced the term, so its range is structural rather than a fact. Other
/// operands are folded forward but never inverted.
fn signed_byte_load_operand(term: &Bitvector32Term) -> Option<&Bitvector32Term> {
    let operand = term.signed_byte_operand()?;
    matches!(
        crate::kernel::eval::viewed_as_memory_load(operand),
        Some(Bitvector32Term::MemoryLoad(
            _,
            _,
            crate::kernel::LoadKind::UInt8
        ))
    )
    .then_some(operand)
}

/// The constant of the byte `u` given the constant of `int8(u)`. A known
/// signed value `k` in `-128..=127` is the conversion of exactly one byte,
/// `k mod 256`. A value outside that range is the conversion of no byte: the
/// context is contradictory, and the byte is left as it was rather than given
/// a value it cannot have. `Unknown` and `Ambiguous` add nothing.
fn signed_byte_inverse(signed: SignedConstantResolution) -> SignedConstantResolution {
    match signed {
        SignedConstantResolution::Known(value @ -128..=127) => {
            SignedConstantResolution::Known(i64::from(value as i8 as u8))
        }
        _ => SignedConstantResolution::Unknown,
    }
}

/// Folds an arithmetic term from its operands' resolutions: `Ambiguous` if
/// any operand is, the evaluated constant if every operand is known, and
/// `Unknown` otherwise (including a term that is not arithmetic).
pub(super) fn fold_arithmetic(
    term: &Bitvector32Term,
    mut operand: impl FnMut(&Bitvector32Term) -> SignedConstantResolution,
) -> SignedConstantResolution {
    if let Some((operator, left, right)) = term.as_binary()
        && operator.is_bitvector32()
    {
        return match (operand(left), operand(right)) {
            (SignedConstantResolution::Ambiguous, _) | (_, SignedConstantResolution::Ambiguous) => {
                SignedConstantResolution::Ambiguous
            }
            (SignedConstantResolution::Known(left), SignedConstantResolution::Known(right)) => {
                SignedConstantResolution::from_term(operator.build(
                    Bitvector32Term::Constant(left as i32 as u32),
                    Bitvector32Term::Constant(right as i32 as u32),
                ))
            }
            _ => SignedConstantResolution::Unknown,
        };
    }
    match term {
        Bitvector32Term::BitwiseNot(value) => operand(value).map(|value| {
            Bitvector32Term::bitwise_not(Bitvector32Term::Constant(value as i32 as u32))
        }),
        // The conversion's own constant fold: a byte constant `c` in
        // `0..=255` converts to its two's-complement value, and a constant
        // outside the byte range stays unfolded (`Unknown`).
        term => match term.signed_byte_operand() {
            Some(value) => operand(value).map(|value| {
                Bitvector32Term::signed_byte(Bitvector32Term::Constant(value as i32 as u32))
            }),
            None => SignedConstantResolution::Unknown,
        },
    }
}

/// The memory-blind fingerprint of the pointer a load term reads, if the
/// term is a load or a registered load variable.
pub(super) fn load_key(term: &Bitvector32Term) -> Option<(u64, Bitvector32Term)> {
    let viewed = crate::kernel::eval::viewed_as_memory_load(term)?;
    let Bitvector32Term::MemoryLoad(_, pointer, _) = &viewed else {
        return None;
    };
    Some((memory_blind_pointer_fingerprint(pointer), viewed))
}

impl ConstantClasses {
    /// The class of a registered term and its constant.
    pub(super) fn class_constant(
        &self,
        term: &Bitvector32Term,
    ) -> Option<SignedConstantResolution> {
        let id = self.class_of.get(term)?;
        Some(self.classes.get(id)?.constant)
    }

    /// Files one true equality fact.
    pub(super) fn assume_equal(&mut self, left: &Bitvector32Term, right: &Bitvector32Term) {
        let left_constant = signed_bitvector_constant(left);
        let right_constant = signed_bitvector_constant(right);
        match (left_constant, right_constant) {
            (Some(_), Some(_)) => {}
            (Some(constant), None) | (None, Some(constant)) => {
                let term = if left_constant.is_some() { right } else { left };
                let id = self.register(term);
                self.raise_constant(id, SignedConstantResolution::Known(constant));
            }
            (None, None) => {
                let left = self.register(left);
                let right = self.register(right);
                self.union(left, right);
            }
        }
    }

    /// The operand resolutions available from the index alone: a constant,
    /// or a registered term's class constant.
    fn indexed_resolution(&self, term: &Bitvector32Term) -> SignedConstantResolution {
        if let Some(value) = signed_bitvector_constant(term) {
            return SignedConstantResolution::Known(value);
        }
        self.class_constant(term)
            .unwrap_or(SignedConstantResolution::Unknown)
    }

    /// Registers a term (and its arithmetic operands) as a singleton class
    /// unless it already has one, returning its class.
    fn register(&mut self, term: &Bitvector32Term) -> u64 {
        if let Some(id) = self.class_of.get(term) {
            return *id;
        }
        crate::instrumentation::record_deterministic_work(1);
        let mut operand_classes = Vec::new();
        if let Some(operands) = arithmetic_operands(term) {
            for operand in operands {
                if signed_bitvector_constant(operand).is_none() {
                    operand_classes.push(self.register(operand));
                }
            }
        }
        let constant = fold_arithmetic(term, |operand| self.indexed_resolution(operand));
        let id = self.next_id;
        self.next_id += 1;
        let mut loads = crate::persistent::PersistentMap::default();
        if let Some((key, _)) = load_key(term) {
            loads = loads.with_inserted(
                key,
                crate::persistent::PersistentSet::default().with_value(term.clone()),
            );
        }
        let conditionals = if matches!(term, Bitvector32Term::If { .. }) {
            crate::persistent::PersistentSet::default().with_value(term.clone())
        } else {
            crate::persistent::PersistentSet::default()
        };
        let signed_bytes = if signed_byte_load_operand(term).is_some() {
            crate::persistent::PersistentSet::default().with_value(term.clone())
        } else {
            crate::persistent::PersistentSet::default()
        };
        self.classes = self.classes.with_inserted(
            id,
            ConstantClass {
                members: crate::persistent::PersistentSet::default().with_value(term.clone()),
                constant: SignedConstantResolution::Unknown,
                users: crate::persistent::PersistentSet::default(),
                loads,
                conditionals,
                signed_bytes,
            },
        );
        self.class_of = self.class_of.with_inserted(term.clone(), id);
        for operand in operand_classes {
            let mut class = self
                .classes
                .get(&operand)
                .expect("registered operand")
                .clone();
            class.users = class.users.with_value(term.clone());
            self.classes = self.classes.with_inserted(operand, class);
        }
        self.raise_constant(id, constant);
        id
    }

    /// Merges `constant` into one class's constant and, if that changed it,
    /// re-folds every term that depends on it.
    fn raise_constant(&mut self, id: u64, constant: SignedConstantResolution) {
        let mut pending = vec![(id, constant)];
        while let Some((id, constant)) = pending.pop() {
            crate::instrumentation::record_deterministic_work(1);
            let mut class = self.classes.get(&id).expect("class").clone();
            let merged = class.constant.merge(constant);
            if merged == class.constant {
                continue;
            }
            let was_unknown = class.constant == SignedConstantResolution::Unknown;
            class.constant = merged;
            let users = class.users.iter().cloned().collect::<Vec<_>>();
            let inverted = self.signed_byte_inversions(&class.signed_bytes, merged);
            let loads = if was_unknown {
                class
                    .loads
                    .iter()
                    .flat_map(|(key, terms)| terms.iter().map(|term| (*key, term.clone())))
                    .collect::<Vec<_>>()
            } else {
                Vec::new()
            };
            self.classes = self.classes.with_inserted(id, class);
            for (key, term) in loads {
                self.settle_load(key, term, id);
            }
            for user in users {
                crate::instrumentation::record_deterministic_work(1);
                let folded = fold_arithmetic(&user, |operand| self.indexed_resolution(operand));
                let user_class = *self.class_of.get(&user).expect("registered user");
                pending.push((user_class, folded));
            }
            pending.extend(inverted);
        }
    }

    /// The byte classes settled by a class's signed byte members taking the
    /// constant `signed`: one per member, each the class of the member's
    /// byte load (registered with the member), raised to the byte's value.
    fn signed_byte_inversions(
        &self,
        signed_bytes: &crate::persistent::PersistentSet<Bitvector32Term>,
        signed: SignedConstantResolution,
    ) -> Vec<(u64, SignedConstantResolution)> {
        let byte = signed_byte_inverse(signed);
        if byte == SignedConstantResolution::Unknown {
            return Vec::new();
        }
        signed_bytes
            .iter()
            .filter_map(|member| {
                crate::instrumentation::record_deterministic_work(1);
                let operand = signed_byte_load_operand(member)?;
                Some((*self.class_of.get(operand)?, byte))
            })
            .collect()
    }

    fn settle_load(&mut self, key: u64, term: Bitvector32Term, id: u64) {
        crate::instrumentation::record_deterministic_work(1);
        let settled = self.settled_loads.get(&key).cloned().unwrap_or_default();
        self.settled_loads = self
            .settled_loads
            .with_inserted(key, settled.with_inserted(term, id));
    }

    /// Joins two classes: the smaller one's members are relabelled into the
    /// larger, and whichever side's constant the merge raises re-folds its
    /// users.
    fn union(&mut self, left: u64, right: u64) {
        if left == right {
            return;
        }
        let left_class = self.classes.get(&left).expect("class").clone();
        let right_class = self.classes.get(&right).expect("class").clone();
        let (root, mut kept, absorbed_id, absorbed) =
            if (left_class.members.len(), right) >= (right_class.members.len(), left) {
                (left, left_class, right, right_class)
            } else {
                (right, right_class, left, left_class)
            };
        let kept_constant = kept.constant;
        let absorbed_constant = absorbed.constant;
        // The kept class's own loads are filed as settled when this union
        // is what settles it; they are already filed under `root` otherwise.
        let kept_loads = if kept_constant == SignedConstantResolution::Unknown
            && absorbed_constant != SignedConstantResolution::Unknown
        {
            kept.loads
                .iter()
                .flat_map(|(key, terms)| terms.iter().map(|term| (*key, term.clone())))
                .collect::<Vec<_>>()
        } else {
            Vec::new()
        };
        for member in absorbed.members.iter() {
            crate::instrumentation::record_deterministic_work(1);
            self.class_of = self.class_of.with_inserted(member.clone(), root);
            kept.members = kept.members.with_value(member.clone());
        }
        for user in absorbed.users.iter() {
            kept.users = kept.users.with_value(user.clone());
        }
        for conditional in absorbed.conditionals.iter() {
            kept.conditionals = kept.conditionals.with_value(conditional.clone());
        }
        // Signed byte members whose class constant this union raises settle
        // their bytes, as a raised constant does in `raise_constant`.
        let kept_signed_bytes = kept.signed_bytes.clone();
        let absorbed_signed_bytes = absorbed.signed_bytes.clone();
        for signed_byte in absorbed.signed_bytes.iter() {
            crate::instrumentation::record_deterministic_work(1);
            kept.signed_bytes = kept.signed_bytes.with_value(signed_byte.clone());
        }
        let mut relabelled_loads = Vec::new();
        for (key, terms) in absorbed.loads.iter() {
            let mut merged = kept.loads.get(key).cloned().unwrap_or_default();
            for term in terms.iter() {
                crate::instrumentation::record_deterministic_work(1);
                merged = merged.with_value(term.clone());
                relabelled_loads.push((*key, term.clone()));
            }
            kept.loads = kept.loads.with_inserted(*key, merged);
        }
        let kept_users = kept.users.clone();
        let absorbed_users = absorbed.users;

        kept.constant = kept_constant.merge(absorbed_constant);
        let merged = kept.constant;
        self.classes = self
            .classes
            .without_key(&absorbed_id)
            .with_inserted(root, kept);
        if merged != SignedConstantResolution::Unknown {
            // Every load of a settled class is filed under its current class.
            for (key, term) in kept_loads.into_iter().chain(relabelled_loads) {
                self.settle_load(key, term, root);
            }
        }
        // Re-fold the users whose operand constant the union raised.
        let mut refold = Vec::new();
        if merged != kept_constant {
            refold.extend(kept_users.iter().cloned());
        }
        if merged != absorbed_constant {
            refold.extend(absorbed_users.iter().cloned());
        }
        for user in refold {
            crate::instrumentation::record_deterministic_work(1);
            let folded = fold_arithmetic(&user, |operand| self.indexed_resolution(operand));
            let user_class = *self.class_of.get(&user).expect("registered user");
            self.raise_constant(user_class, folded);
        }
        let mut inverted = Vec::new();
        if merged != kept_constant {
            inverted.extend(self.signed_byte_inversions(&kept_signed_bytes, merged));
        }
        if merged != absorbed_constant {
            inverted.extend(self.signed_byte_inversions(&absorbed_signed_bytes, merged));
        }
        for (byte_class, byte) in inverted {
            self.raise_constant(byte_class, byte);
        }
    }

    /// Loads of settled classes at the address `key` names, with their class.
    pub(super) fn settled_loads_at(
        &self,
        key: u64,
    ) -> impl Iterator<Item = (&Bitvector32Term, u64)> + '_ {
        self.settled_loads
            .get(&key)
            .into_iter()
            .flat_map(|terms| terms.iter().map(|(term, id)| (term, *id)))
    }

    /// The conditional members of one class.
    pub(super) fn conditional_members(&self, id: u64) -> Vec<Bitvector32Term> {
        self.classes.get(&id).map_or_else(Vec::new, |class| {
            class.conditionals.iter().cloned().collect()
        })
    }

    /// Every pair of a load member of class `id` and a load of another,
    /// settled class at the same memory-blind address. Only addresses with a
    /// settled load are enumerated, so a class no settled class shares an
    /// address with costs one lookup per address it loads.
    pub(super) fn bridgeable_loads(&self, id: u64) -> Vec<(Bitvector32Term, Bitvector32Term, u64)> {
        let Some(class) = self.classes.get(&id) else {
            return Vec::new();
        };
        let mut pairs = Vec::new();
        for (key, members) in class.loads.iter() {
            crate::instrumentation::record_deterministic_work(1);
            let Some(candidates) = self.settled_loads.get(key) else {
                continue;
            };
            for (candidate, candidate_class) in candidates.iter() {
                if *candidate_class == id {
                    continue;
                }
                for member in members.iter() {
                    crate::instrumentation::record_deterministic_work(1);
                    pairs.push((member.clone(), candidate.clone(), *candidate_class));
                }
            }
        }
        pairs
    }

    pub(super) fn class_id(&self, term: &Bitvector32Term) -> Option<u64> {
        self.class_of.get(term).copied()
    }

    pub(super) fn constant_of_class(&self, id: u64) -> SignedConstantResolution {
        self.classes
            .get(&id)
            .map_or(SignedConstantResolution::Unknown, |class| class.constant)
    }
}
