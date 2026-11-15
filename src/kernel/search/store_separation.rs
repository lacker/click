//! Planning-only inspection of the cells one checked statement step forgot.
//!
//! A scalar store keeps a cached cell of the written array only on direct
//! evidence that the two element indices (`int32`, or 64-bit of one
//! signedness) differ
//! (`reasoning::pointers_directly_distinct_for_store`), and a miss forgets the
//! value. The implicit tail reads here which index disequalities would have
//! kept the forgotten cells, proves the ones it can before the statement, and
//! runs the statement again. A requested `--trace-proof` reads the same
//! inspection to show which cells a traced step dropped. Checking never calls
//! this.
use crate::kernel::primitives::HashedOrdMapChange;
use crate::kernel::{
    CompareRelation, MachineIntegerType, Memory, Pointer, Proposition, SharedMachineIntegerTerm,
};

/// One cached cell a statement forgot beside a store into the same array.
pub(crate) struct ForgottenStoreCell {
    /// The cached cell the statement no longer holds.
    pub(crate) cell: Pointer,
    /// The cell the statement wrote beside it.
    pub(crate) store: Pointer,
    /// The fact the store-time check reads: the two element indices differ.
    pub(crate) indices_differ: Proposition,
    /// The written cell's element index, the left operand of the
    /// comparison `indices_differ` denies.
    pub(crate) store_index: SharedMachineIntegerTerm,
    /// The forgotten cell's element index, its right operand.
    pub(crate) cell_index: SharedMachineIntegerTerm,
    /// The format the two indices are compared in: `int32`, or `int64` or
    /// `uint64` for 64-bit indices of that signedness.
    pub(crate) format: MachineIntegerType,
}

/// How many (forgotten cell, written cell) pairs one inspection compares.
const MAX_COMPARED_PAIRS: usize = 64;

/// The cells `before` caches that `after` no longer holds, paired with each
/// cell `after` gained or changed in the same block at another element index
/// of a common base. Only the cells on which the two memories differ are
/// visited (the persistent concrete maps' diff skips shared subtrees; run
/// slots are not inspected), at most
/// [`MAX_COMPARED_PAIRS`] pairs are compared, and at most `limit` returned.
pub(crate) fn cells_forgotten_beside_stores(
    before: &Memory,
    after: &Memory,
    limit: usize,
) -> Vec<ForgottenStoreCell> {
    let mut forgotten = Vec::new();
    let mut written = Vec::new();
    // Only concrete cells: a seeded run's slots are never laid out here, so
    // a store into a long run costs its concrete changes alone.
    for change in before.cells.concrete().diff(after.cells.concrete()) {
        crate::instrumentation::record_deterministic_work(1);
        match change {
            HashedOrdMapChange::Removed(pointer) => forgotten.push(pointer),
            HashedOrdMapChange::Added(pointer) | HashedOrdMapChange::Changed(pointer) => {
                written.push(pointer)
            }
        }
    }
    let mut pairs = Vec::new();
    let mut compared = 0usize;
    for cell in forgotten {
        for store in &written {
            if pairs.len() >= limit || compared >= MAX_COMPARED_PAIRS {
                return pairs;
            }
            compared += 1;
            crate::instrumentation::record_deterministic_work(1);
            // The same pair and format the store-time check compares.
            let Some(indices) = crate::kernel::reasoning::common_base_store_indices(cell, store)
            else {
                continue;
            };
            let equal = indices.comparison(CompareRelation::Equal, true);
            pairs.push(ForgottenStoreCell {
                cell: cell.clone(),
                store: (*store).clone(),
                indices_differ: Proposition::ConditionIs(equal, false),
                store_index: indices.right,
                cell_index: indices.left,
                format: indices.format,
            });
        }
    }
    pairs
}

/// The element indices of a goal that denies the equality of two element
/// addresses of one common base whose scaled indices share an element width
/// and an index format (`int32`, or `int64` or `uint64`), the conclusion
/// shape of `separation::distinct_elements`: the left address's index, the
/// right address's, and their format. It reads the two pointers' offsets
/// only; `solve` uses it to decline other pointer disequalities before
/// searching and to spell the law's two indices.
pub(crate) fn element_address_disequality_indices(
    goal: &Proposition,
) -> Option<(
    SharedMachineIntegerTerm,
    SharedMachineIntegerTerm,
    MachineIntegerType,
)> {
    let Proposition::ConditionIs(crate::kernel::ConditionTerm::PointerEqual(left, right), false) =
        goal
    else {
        return None;
    };
    crate::kernel::reasoning::common_base_store_indices(left, right)
        .map(|indices| (indices.left, indices.right, indices.format))
}
