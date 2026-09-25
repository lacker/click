//! Exclusive sequential population openings. Membership remains in the
//! resource context, but cannot independently reopen a suspended body.
use super::{CState, PureFactContext, ResourceArguments};
use crate::persistent::PersistentSet;
use std::sync::{
    Arc,
    atomic::{AtomicU64, Ordering},
};

type Key = (String, ResourceArguments);
#[derive(Clone, Default)]
pub(super) struct PopulationAccess(Option<Arc<Frame>>);
struct Frame {
    id: u64,
    key: Key,
    active: PersistentSet<Key>,
    parent: PopulationAccess,
}
impl PopulationAccess {
    fn id(&self) -> u64 {
        self.0.as_ref().map_or(0, |frame| frame.id)
    }
    fn contains(&self, key: &Key) -> bool {
        self.0
            .as_ref()
            .is_some_and(|frame| frame.active.contains(key))
    }
    fn open(&self, key: Key) -> Result<Self, &'static str> {
        if self.contains(&key) {
            return Err("population body is already open");
        }
        static NEXT: AtomicU64 = AtomicU64::new(1);
        let id = NEXT.fetch_add(1, Ordering::Relaxed);
        assert_ne!(id, 0, "population access identity exhausted");
        let active = self
            .0
            .as_ref()
            .map_or_else(PersistentSet::default, |frame| frame.active.clone())
            .with_value(key.clone());
        Ok(Self(Some(Arc::new(Frame {
            id,
            key,
            active,
            parent: self.clone(),
        }))))
    }
    fn close(&self, key: &Key) -> Result<Self, &'static str> {
        let frame = self
            .0
            .as_ref()
            .ok_or("population has no open restoration scope")?;
        if &frame.key != key {
            return Err("population restoration scopes must close in order");
        }
        Ok(frame.parent.clone())
    }
}
impl PartialEq for PopulationAccess {
    fn eq(&self, other: &Self) -> bool {
        self.id() == other.id()
    }
}
impl Eq for PopulationAccess {}
impl PartialOrd for PopulationAccess {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for PopulationAccess {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.id().cmp(&other.id())
    }
}
impl std::hash::Hash for PopulationAccess {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.id().hash(state);
    }
}
impl std::fmt::Debug for PopulationAccess {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_tuple("PopulationAccess").field(&self.id()).finish()
    }
}
impl PopulationAccess {
    pub(super) fn checks_rewrite(&self, after: &Self, key: &(String, ResourceArguments)) -> bool {
        self == after
            || after.0.as_ref().is_some_and(|frame| {
                frame.parent == *self && &frame.key == key && !self.contains(key)
            })
            || self
                .0
                .as_ref()
                .is_some_and(|frame| frame.parent == *after && &frame.key == key)
    }
}
impl CState {
    pub(crate) fn population_body_is_open(
        &self,
        name: &str,
        arguments: &ResourceArguments,
        assumptions: &PureFactContext,
    ) -> bool {
        if self.population_access.0.is_none() {
            return false;
        }
        let key = self
            .counted_population_proven_equal(name, arguments, assumptions)
            .map(|(name, arguments, _)| (name, arguments))
            .unwrap_or_else(|| (name.to_owned(), arguments.clone()));
        self.population_access.contains(&key)
    }
    pub(crate) fn open_population_body(
        mut self,
        name: String,
        arguments: ResourceArguments,
    ) -> Result<Self, &'static str> {
        self.population_access = self.population_access.open((name, arguments))?;
        Ok(self)
    }
    pub(crate) fn close_population_body(
        mut self,
        name: String,
        arguments: ResourceArguments,
    ) -> Result<Self, &'static str> {
        self.population_access = self.population_access.close(&(name, arguments))?;
        Ok(self)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    fn key(index: usize) -> Key {
        (format!("population-{index:08}"), Arc::from([]))
    }
    #[test]
    fn scopes_are_exclusive_ordered_and_cannot_reuse_an_old_epoch() {
        let closed = PopulationAccess::default();
        let outer = closed.open(key(1)).unwrap();
        assert!(outer.open(key(1)).is_err());
        let inner = outer.open(key(2)).unwrap();
        assert!(inner.close(&key(1)).is_err());
        assert_eq!(inner.close(&key(2)).unwrap(), outer);
        assert_eq!(outer.close(&key(1)).unwrap(), closed);
        let reopened = closed.open(key(1)).unwrap();
        assert_ne!(outer, reopened);
        assert!(!outer.checks_rewrite(&reopened, &key(1)));
        assert!(!closed.checks_rewrite(&inner, &key(2)));
        assert!(!outer.checks_rewrite(&closed, &key(2)));
        assert!(closed.checks_rewrite(&outer, &key(1)));
        assert!(outer.checks_rewrite(&closed, &key(1)));
    }
    #[test]
    fn selected_scope_work_is_logarithmic_and_close_restores_the_same_root() {
        for size in [8usize, 32, 128, 512] {
            let mut access = PopulationAccess::default();
            for index in 0..size {
                access = access.open(key(index)).unwrap();
            }
            let (next, work) =
                crate::persistent::measure_persistent_work(|| access.open(key(size)).unwrap());
            assert!(
                work > 0 && work < 20 * (size.ilog2() as usize + 1),
                "size {size}: {work}"
            );
            let (restored, work) =
                crate::persistent::measure_persistent_work(|| next.close(&key(size)).unwrap());
            assert_eq!(restored, access);
            assert_eq!(work, 0);
        }
    }
}
