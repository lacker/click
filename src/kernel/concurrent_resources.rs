//! Resource authority admitted at a suspended worker boundary.
//!
//! This is a conservative internal classification, not a declaration that a
//! resource type is universally thread-safe. A stable view still needs the
//! checked loan plan, and an exclusive transfer still needs the checked
//! partition and join recovery. Protocol and population resources have no
//! asynchronous transition yet.

use super::eval::is_external_memory_pointer;
use super::{Bitvector32Term, CResource, CResourceFact};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum WorkerResourceClass {
    ExclusiveExternalMemory,
    StableMemoryView,
    ImplicitOrNonexternalMemory,
    CompositeOrPopulation,
    Token,
    Instance,
}

impl WorkerResourceClass {
    pub(super) fn of(fact: &CResourceFact) -> Self {
        match fact {
            CResourceFact::Own(CResource::Memory(range), quantity)
                if quantity.as_ref() == &Bitvector32Term::Constant(1)
                    && is_external_memory_pointer(range.base()) =>
            {
                Self::ExclusiveExternalMemory
            }
            CResourceFact::View(CResource::Memory(_)) => Self::StableMemoryView,
            CResourceFact::Own(CResource::Memory(_), _) => Self::ImplicitOrNonexternalMemory,
            CResourceFact::Own(CResource::Composite { .. }, _)
            | CResourceFact::View(CResource::Composite { .. }) => Self::CompositeOrPopulation,
            CResourceFact::Own(CResource::Token { .. }, _)
            | CResourceFact::View(CResource::Token { .. }) => Self::Token,
            CResourceFact::Own(CResource::Instance(_), _)
            | CResourceFact::View(CResource::Instance(_)) => Self::Instance,
        }
    }

    pub(super) fn may_enter_worker(self) -> bool {
        matches!(self, Self::ExclusiveExternalMemory | Self::StableMemoryView)
    }

    pub(super) fn may_return_from_worker(self) -> bool {
        self == Self::ExclusiveExternalMemory
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::{CMemoryRange, Pointer, PointerOffsetTerm};

    fn cell(block: &str) -> CMemoryRange {
        CMemoryRange::new(
            Pointer {
                block: block.into(),
                offset: PointerOffsetTerm::Constant(0),
            },
            0.into(),
            1.into(),
        )
    }

    #[test]
    fn worker_boundary_transfers_only_exclusive_external_memory_and_stable_views() {
        let owned = WorkerResourceClass::of(&CResourceFact::own_memory(cell("heap:counter")));
        assert!(owned.may_enter_worker() && owned.may_return_from_worker());

        let viewed = WorkerResourceClass::of(&CResourceFact::view_memory(cell("local:job")));
        assert!(viewed.may_enter_worker());
        assert!(!viewed.may_return_from_worker());

        let local_owner = WorkerResourceClass::of(&CResourceFact::own_memory(cell("local:job")));
        assert!(!local_owner.may_enter_worker());
        assert!(!local_owner.may_return_from_worker());

        let duplicate_memory = WorkerResourceClass::of(&CResourceFact::own_quantity(
            CResource::Memory(cell("heap:counter")),
            2.into(),
        ));
        assert!(!duplicate_memory.may_enter_worker());
    }

    #[test]
    fn worker_boundary_refuses_population_and_protocol_resources() {
        let counted = WorkerResourceClass::of(&CResourceFact::own_quantity(
            CResource::Composite {
                name: "object_ref".into(),
                arguments: Vec::new().into(),
            },
            2.into(),
        ));
        assert_eq!(counted, WorkerResourceClass::CompositeOrPopulation);
        assert!(!counted.may_enter_worker());
        assert!(!counted.may_return_from_worker());

        let token =
            WorkerResourceClass::of(&CResourceFact::own_token("lock_handle".into(), vec![]));
        assert_eq!(token, WorkerResourceClass::Token);
        assert!(!token.may_enter_worker());

        let composite_view = WorkerResourceClass::of(&CResourceFact::view_composite(
            "protected_counter".into(),
            vec![],
        ));
        assert!(!composite_view.may_enter_worker());
    }
}
