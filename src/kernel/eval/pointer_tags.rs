//! Tag arithmetic on pointer addresses.
//!
//! A word of the form `address(p) + t` is a tagged address. Addition and
//! subtraction keep that form by exact modular integer identities, so no
//! obligation is needed to track it. A bit operation relies on the low
//! address bits being zero: clearing tag bits with `& ~m` keeps the address
//! with a masked tag, reading them with `& m` yields the masked tag alone,
//! and setting them with `| b` folds into the tag. Each such step is valid
//! only when the pointer is aligned to the alignment the mask presumes and
//! the tag stays below it, so a tag can never carry into or read an address
//! bit. Evaluation never rewrites a word; the decision layer applies these
//! rules when their conditions are decided, and the cast back to a pointer
//! records the undecided ones as obligations.
//!
//! Every decision here also reports the exact facts it used, so a smart
//! closure can retain them and a simple `arithmetic using` step can check
//! the same decision from those facts alone.

use super::operators::CBitwiseOperation;
use super::*;

pub(in crate::kernel) struct TaggedAddress {
    pub(in crate::kernel) pointer: Pointer,
    pub(in crate::kernel) tag: Bitvector32Term,
}

/// The exact facts a decision consulted, and whether every step could name
/// its fact. An incomplete record still decides; it just cannot certify.
pub(in crate::kernel) struct UsedFacts {
    pub(in crate::kernel) premises: Vec<Proposition>,
    pub(in crate::kernel) complete: bool,
}

impl Default for UsedFacts {
    fn default() -> Self {
        Self::new()
    }
}

impl UsedFacts {
    pub(in crate::kernel) fn new() -> Self {
        Self {
            premises: Vec::new(),
            complete: true,
        }
    }

    fn cite(&mut self, premise: Proposition) {
        if !self.premises.contains(&premise) {
            self.premises.push(premise);
        }
    }
}

/// How an undecided alignment or tag-bound condition is treated.
enum Undecided<'a> {
    /// Leave the word unrecognized.
    Reject,
    /// Record the condition as an obligation and continue.
    Oblige(&'a mut Vec<ProofObligation>),
}

/// A refuted condition names what the operation needed.
pub(in crate::kernel) struct Refuted(pub(in crate::kernel) String);

/// A tag sum with a zero side is the other side, so a tag read from a fact
/// such as `word == address(next) + color` is exactly `color`.
fn add_tag(left: Bitvector32Term, right: Bitvector32Term) -> Bitvector32Term {
    if left.uint64_as_const() == Some(0) {
        return right;
    }
    if right.uint64_as_const() == Some(0) {
        return left;
    }
    Bitvector32Term::uint64_add(left, right)
}

/// The alignment a tag-clearing mask presumes: `!mask + 1` when the mask
/// clears exactly the low bits.
fn clearing_mask_alignment(mask: u64) -> Option<u64> {
    let alignment = (!mask).checked_add(1)?;
    alignment.is_power_of_two().then_some(alignment)
}

/// The alignment a tag-reading mask presumes: `mask + 1` when the mask
/// selects exactly the low bits.
fn reading_mask_alignment(mask: u64) -> Option<u64> {
    let alignment = mask.checked_add(1)?;
    (alignment.is_power_of_two() && alignment > 1).then_some(alignment)
}

impl PureFactContext {
    /// Decides `condition` and cites the exact fact that settled it when one
    /// can be named: a stored fact in either orientation, an alignment base
    /// fact, or nothing for a constant or a structural pointer decision. Any
    /// other route leaves the record incomplete.
    pub(in crate::kernel) fn decide_citing(
        &self,
        condition: &ConditionTerm,
        used: &mut UsedFacts,
    ) -> Option<bool> {
        if let ConditionTerm::Constant(value) = condition {
            return Some(*value);
        }
        for stored in [condition.clone(), condition.flipped()] {
            if let Some(value) = self.condition_facts.get(&stored).copied() {
                used.cite(Proposition::ConditionIs(stored, value));
                return Some(value);
            }
        }
        if let Some((pointer, alignment)) = condition.as_pointer_alignment()
            && let Some((aligned, premise)) = self.pointer_alignment_decision(pointer, alignment)
        {
            if let Some(premise) = premise {
                used.cite(premise);
            }
            return Some(aligned);
        }
        if let ConditionTerm::PointerEqual(left, right) = condition {
            if left == right {
                return Some(true);
            }
            if left.blocks_proven_distinct(right) {
                return Some(false);
            }
        }
        let decided = self.decide(condition);
        if decided.is_some() {
            used.complete = false;
        }
        decided
    }
}

fn require(
    form: &TaggedAddress,
    alignment: u64,
    operation: &str,
    assumptions: &PureFactContext,
    undecided: &mut Undecided<'_>,
    used: &mut UsedFacts,
) -> Result<bool, Refuted> {
    let conditions = [
        (
            ConditionTerm::pointer_aligned(form.pointer.clone(), alignment),
            format!("the pointer aligned to {alignment} bytes"),
        ),
        (
            ConditionTerm::uint64_less_than(
                form.tag.clone(),
                Bitvector32Term::UInt64Constant(alignment),
            ),
            format!("the tag below {alignment}"),
        ),
    ];
    for (condition, what) in conditions {
        match assumptions.decide_citing(&condition, used) {
            Some(true) => {}
            Some(false) => {
                return Err(Refuted(format!(
                    "{operation} on a tagged pointer address needs {what}, which is refuted"
                )));
            }
            None => match undecided {
                Undecided::Reject => return Ok(false),
                Undecided::Oblige(obligations) => {
                    let context = format!("{operation} on a tagged pointer address needs {what}");
                    if add_proof_obligation_with_context(
                        obligations,
                        assumptions,
                        Proposition::ConditionIs(condition, true),
                        Some(&context),
                    )
                    .is_none()
                    {
                        return Err(Refuted(format!("{context}, which is refuted")));
                    }
                }
            },
        }
    }
    Ok(true)
}

fn form_of(
    term: &Bitvector32Term,
    assumptions: &PureFactContext,
    undecided: &mut Undecided<'_>,
    used: &mut UsedFacts,
    through_facts: bool,
) -> Result<Option<TaggedAddress>, Refuted> {
    let direct = match term {
        Bitvector32Term::PointerAddress(pointer) => Some(TaggedAddress {
            pointer: pointer.as_ref().clone(),
            tag: Bitvector32Term::UInt64Constant(0),
        }),
        Bitvector32Term::UInt64Add(left, right) => {
            if let Some(form) = form_of(left, assumptions, undecided, used, through_facts)? {
                Some(TaggedAddress {
                    pointer: form.pointer,
                    tag: add_tag(form.tag, right.as_ref().clone()),
                })
            } else {
                form_of(right, assumptions, undecided, used, through_facts)?.map(|form| {
                    TaggedAddress {
                        pointer: form.pointer,
                        tag: add_tag(left.as_ref().clone(), form.tag),
                    }
                })
            }
        }
        Bitvector32Term::UInt64Subtract(left, right) => {
            form_of(left, assumptions, undecided, used, through_facts)?.map(|form| TaggedAddress {
                pointer: form.pointer,
                tag: Bitvector32Term::uint64_subtract(form.tag, right.as_ref().clone()),
            })
        }
        Bitvector32Term::UInt64BitwiseAnd(left, right)
        | Bitvector32Term::UInt64BitwiseOr(left, right) => {
            let operation = if matches!(term, Bitvector32Term::UInt64BitwiseAnd(_, _)) {
                CBitwiseOperation::And
            } else {
                CBitwiseOperation::Or
            };
            let (inner, constant) = match (left.uint64_as_const(), right.uint64_as_const()) {
                (None, Some(constant)) => (left, constant),
                (Some(constant), None) => (right, constant),
                _ => return Ok(None),
            };
            let Some(form) = form_of(inner, assumptions, undecided, used, through_facts)? else {
                return Ok(None);
            };
            match operation {
                CBitwiseOperation::And => {
                    let Some(alignment) = clearing_mask_alignment(constant) else {
                        return Ok(None);
                    };
                    if !require(
                        &form,
                        alignment,
                        "clearing tag bits",
                        assumptions,
                        undecided,
                        used,
                    )? {
                        return Ok(None);
                    }
                    Some(TaggedAddress {
                        pointer: form.pointer,
                        tag: Bitvector32Term::uint64_bitwise_and(
                            form.tag,
                            Bitvector32Term::UInt64Constant(constant),
                        ),
                    })
                }
                CBitwiseOperation::Or => {
                    let Some(alignment) = constant
                        .checked_add(1)
                        .and_then(u64::checked_next_power_of_two)
                    else {
                        return Ok(None);
                    };
                    if constant != 0
                        && !require(
                            &form,
                            alignment,
                            "setting tag bits",
                            assumptions,
                            undecided,
                            used,
                        )?
                    {
                        return Ok(None);
                    }
                    Some(TaggedAddress {
                        pointer: form.pointer,
                        tag: Bitvector32Term::uint64_bitwise_or(
                            form.tag,
                            Bitvector32Term::UInt64Constant(constant),
                        ),
                    })
                }
                CBitwiseOperation::Xor => None,
            }
        }
        _ => None,
    };
    if direct.is_some() || !through_facts {
        return Ok(direct);
    }
    // One exact recorded 64-bit equality may name the word's address form,
    // as a resource fact `word == address(next) + tag` does.
    for (equal, fact) in assumptions.recorded_uint64_equals(term) {
        if let Some(form) = form_of(&equal, assumptions, undecided, used, false)? {
            used.cite(Proposition::ConditionIs(fact, true));
            return Ok(Some(form));
        }
    }
    Ok(None)
}

/// `term` as `address(pointer) + tag` using only decided conditions.
pub(in crate::kernel) fn tagged_address_form(
    term: &Bitvector32Term,
    assumptions: &PureFactContext,
    used: &mut UsedFacts,
) -> Option<TaggedAddress> {
    form_of(term, assumptions, &mut Undecided::Reject, used, true)
        .ok()
        .flatten()
}

/// `term & mask` with a tag-reading mask, as the masked tag alone, using
/// only decided conditions.
pub(in crate::kernel) fn masked_tag_value(
    term: &Bitvector32Term,
    assumptions: &PureFactContext,
    used: &mut UsedFacts,
) -> Option<Bitvector32Term> {
    let Bitvector32Term::UInt64BitwiseAnd(left, right) = term else {
        return None;
    };
    let (inner, mask) = match (left.uint64_as_const(), right.uint64_as_const()) {
        (None, Some(mask)) => (left, mask),
        (Some(mask), None) => (right, mask),
        _ => return None,
    };
    let alignment = reading_mask_alignment(mask)?;
    let form = tagged_address_form(inner, assumptions, used)?;
    require(
        &form,
        alignment,
        "reading tag bits",
        assumptions,
        &mut Undecided::Reject,
        used,
    )
    .ok()
    .filter(|decided| *decided)?;
    Some(Bitvector32Term::uint64_bitwise_and(
        form.tag,
        Bitvector32Term::UInt64Constant(mask),
    ))
}

/// The pointer a 64-bit word converts back to: its recorded address with the
/// tag proven zero. Undecided alignment, tag-bound, and zero-tag conditions
/// become obligations; a refuted one is an error. `Ok(None)` means the word
/// has no recorded pointer origin.
pub(in crate::kernel) fn cast_tagged_address_to_pointer(
    term: &Bitvector32Term,
    assumptions: &PureFactContext,
    obligations: &mut Vec<ProofObligation>,
) -> Result<Option<Pointer>, String> {
    let mut used = UsedFacts::new();
    let form = match form_of(
        term,
        assumptions,
        &mut Undecided::Oblige(obligations),
        &mut used,
        true,
    ) {
        Ok(Some(form)) => form,
        Ok(None) => return Ok(None),
        Err(Refuted(message)) => return Err(message),
    };
    let tag_is_zero =
        ConditionTerm::uint64_equal(form.tag.clone(), Bitvector32Term::UInt64Constant(0));
    match assumptions.decide(&tag_is_zero) {
        Some(true) => Ok(Some(form.pointer)),
        Some(false) => Err(
            "integer-to-pointer cast of a tagged address requires the tag bits proven zero; \
             they are refuted"
                .to_string(),
        ),
        None => {
            let context = "integer-to-pointer cast of a tagged address requires the tag bits \
                           proven zero";
            if add_proof_obligation_with_context(
                obligations,
                assumptions,
                Proposition::ConditionIs(tag_is_zero, true),
                Some(context),
            )
            .is_none()
            {
                return Err(format!("{context}; they are refuted"));
            }
            Ok(Some(form.pointer))
        }
    }
}
