//! The labels Click prints for proof obligations and accepts back from
//! `click expand --claim`, `click audit --claim`, and diagnostics.
//!
//! A claim is named by its owner (a function, theorem, or tactic) and either
//! the name the author wrote (`ensures sorted: P` is `f.sorted`) or the kind
//! of clause it was written as and its 0-based position among the owner's
//! clauses of that kind: the third written `ensures` is `f.ensures_2`
//! however many `owns` or `produces` clauses come before it. A grouped proof
//! is `f.contract`.
//!
//! The label is a display and lookup name only. The kernel identifies a
//! claim by its position among the owner's flattened claims
//! ([`crate::kernel::CFunctionContractClaimKey`]); a flattened aggregate
//! clause gives several kernel claims the one label of the clause the author
//! wrote.

/// The kind of written clause a claim comes from; its word names the claim.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub(crate) enum ClaimClauseKind {
    /// `ensures P`.
    Ensures,
    /// `exceptional ensures P`.
    ExceptionalEnsures,
    /// `owns R`: the function returns the resource it was lent.
    Owns,
    /// `produces R`, including one nested in a contract `if`.
    Produces,
}

impl ClaimClauseKind {
    const ALL: [Self; 4] = [
        Self::Ensures,
        Self::ExceptionalEnsures,
        Self::Owns,
        Self::Produces,
    ];

    /// The word a label spells the kind with.
    pub(crate) const fn word(self) -> &'static str {
        match self {
            Self::Ensures => "ensures",
            Self::ExceptionalEnsures => "exceptional_ensures",
            Self::Owns => "owns",
            Self::Produces => "produces",
        }
    }

    /// The kind of a postcondition clause, read from the clause itself. The
    /// parser records the kind as written; this serves blocks built without
    /// a source and agrees with the parser for every clause it builds.
    pub(crate) fn of_ensure(clause: &super::EnsureClause) -> Self {
        match clause.ensure() {
            super::Ensure::Resource(_) if clause.borrowed() => Self::Owns,
            super::Ensure::Resource(_) => Self::Produces,
            super::Ensure::Proposition(_) => Self::Ensures,
        }
    }
}

/// One written claim clause: its kind and its 0-based position among its
/// owner's clauses of that kind.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub(crate) struct ClaimClauseId {
    pub(crate) kind: ClaimClauseKind,
    pub(crate) index: usize,
}

/// Numbers written clauses per kind, in source order.
#[derive(Clone, Debug, Default)]
pub(crate) struct ClaimClauseCounter {
    counts: [usize; ClaimClauseKind::ALL.len()],
}

impl ClaimClauseCounter {
    /// The id of the next written clause of `kind`.
    pub(crate) fn next(&mut self, kind: ClaimClauseKind) -> ClaimClauseId {
        let count = &mut self.counts[kind as usize];
        let id = ClaimClauseId {
            kind,
            index: *count,
        };
        *count += 1;
        id
    }
}

/// The label of a claim of `owner`: its written name, or its clause kind
/// and per-kind index.
pub(crate) fn claim_label(owner: &str, name: Option<&str>, id: ClaimClauseId) -> String {
    match name {
        Some(name) => format!("{owner}.{name}"),
        None => format!("{owner}.{}_{}", id.kind.word(), id.index),
    }
}

/// The label of `owner`'s grouped proof, or of a tactic's whole contract.
pub(crate) fn contract_claim_label(owner: &str) -> String {
    format!("{owner}.contract")
}

/// The label of a function's body-safety obligation, proved when the
/// contract states no claim.
pub(crate) fn body_safety_label(owner: &str) -> String {
    format!("{owner}.body_safety")
}

/// The label of a loop phase proof: `f.loop(0).initialize` or
/// `f.loop(0).preserve`.
pub(crate) fn loop_phase_claim_label(owner: &str, loop_index: usize, phase: &str) -> String {
    format!("{owner}.loop({loop_index}).{phase}")
}

/// The loop index and phase a loop phase label of `owner` names, by
/// [`loop_phase_claim_label`].
pub(crate) fn parse_loop_phase_claim_label<'a>(
    owner: &str,
    label: &'a str,
) -> Option<(usize, &'a str)> {
    let rest = label.strip_prefix(owner)?.strip_prefix(".loop(")?;
    let (loop_index, phase) = rest.split_once(").")?;
    matches!(phase, "initialize" | "preserve")
        .then_some(())
        .and(loop_index.parse().ok())
        .map(|loop_index| (loop_index, phase))
}

/// The ids of written clauses flattened into claims: `source_clauses[i]` is
/// the written clause claim `i` came from and `kinds[c]` the kind of written
/// clause `c`. Members of one flattened clause share its id.
pub(crate) fn flattened_claim_ids(
    kinds: &[ClaimClauseKind],
    source_clauses: &[usize],
) -> Vec<ClaimClauseId> {
    let mut counter = ClaimClauseCounter::default();
    let written = kinds
        .iter()
        .map(|kind| counter.next(*kind))
        .collect::<Vec<_>>();
    source_clauses
        .iter()
        .map(|source| written[*source])
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn each_clause_kind_counts_separately() {
        use ClaimClauseKind::*;
        let ids = flattened_claim_ids(
            &[Owns, Ensures, Produces, Owns, Ensures],
            &[0, 1, 2, 2, 3, 4],
        );
        let labels = ids
            .iter()
            .map(|id| claim_label("f", None, *id))
            .collect::<Vec<_>>();
        assert_eq!(
            labels,
            [
                "f.owns_0",
                "f.ensures_0",
                "f.produces_0",
                "f.produces_0",
                "f.owns_1",
                "f.ensures_1"
            ]
        );
        assert_eq!(
            claim_label(
                "f",
                Some("sorted"),
                ClaimClauseId {
                    kind: Ensures,
                    index: 3
                }
            ),
            "f.sorted"
        );
        assert_eq!(
            claim_label(
                "f",
                None,
                ClaimClauseId {
                    kind: ExceptionalEnsures,
                    index: 1
                }
            ),
            "f.exceptional_ensures_1"
        );
        assert_eq!(contract_claim_label("f"), "f.contract");
        assert_eq!(
            loop_phase_claim_label("f", 2, "preserve"),
            "f.loop(2).preserve"
        );
        assert_eq!(
            parse_loop_phase_claim_label("f", "f.loop(2).preserve"),
            Some((2, "preserve"))
        );
        assert_eq!(parse_loop_phase_claim_label("f", "f.loop(2).other"), None);
        assert_eq!(
            parse_loop_phase_claim_label("g", "f.loop(2).preserve"),
            None
        );
    }
}
