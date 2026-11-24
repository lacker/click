use super::*;
use crate::kernel::GeneratedBinderId;

/// Source names and generated identities inhabit disjoint namespaces.
#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub enum SurfaceBinder {
    Written(String),
    Generated(GeneratedBinderId),
}
impl SurfaceBinder {
    pub(crate) fn fresh() -> Self {
        Self::Generated(GeneratedBinderId::fresh())
    }
    pub fn written(&self) -> Option<&str> {
        match self {
            Self::Written(name) => Some(name),
            Self::Generated(_) => None,
        }
    }
    pub(crate) fn kernel_name(&self) -> crate::kernel::BindingName {
        match self {
            Self::Written(name) => name.into(),
            Self::Generated(id) => id.binding_name(),
        }
    }
    pub(crate) fn reference(&self) -> SurfaceTerm {
        match self {
            Self::Written(name) => SurfaceTerm::Binding(name.clone()),
            Self::Generated(id) => {
                SurfaceTerm::ProgramExpression(ProgramExpression::Variable(id.binding_name()))
            }
        }
    }
}
impl From<String> for SurfaceBinder {
    fn from(name: String) -> Self {
        Self::Written(name)
    }
}
impl From<&str> for SurfaceBinder {
    fn from(name: &str) -> Self {
        Self::Written(name.into())
    }
}
impl From<&String> for SurfaceBinder {
    fn from(name: &String) -> Self {
        Self::Written(name.clone())
    }
}
impl From<&SurfaceBinder> for SurfaceBinder {
    fn from(name: &SurfaceBinder) -> Self {
        name.clone()
    }
}
impl fmt::Display for SurfaceBinder {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Written(name) => name.fmt(f),
            Self::Generated(id) => id.fmt(f),
        }
    }
}
impl PartialEq<str> for SurfaceBinder {
    fn eq(&self, name: &str) -> bool {
        self.written() == Some(name)
    }
}
impl PartialEq<&str> for SurfaceBinder {
    fn eq(&self, name: &&str) -> bool {
        self.written() == Some(*name)
    }
}
impl PartialEq<String> for SurfaceBinder {
    fn eq(&self, name: &String) -> bool {
        self.written() == Some(name.as_str())
    }
}
impl PartialEq<SurfaceBinder> for String {
    fn eq(&self, name: &SurfaceBinder) -> bool {
        name == self
    }
}

/// A borrowed key keeps source lookups allocation-free and generated lookups typed.
pub(super) enum BinderKeyRef<'a> {
    Written(&'a str),
    Generated(&'a GeneratedBinderId),
}
pub(super) trait BinderKey {
    fn binder_key(&self) -> Option<BinderKeyRef<'_>>;
}
impl BinderKey for str {
    fn binder_key(&self) -> Option<BinderKeyRef<'_>> {
        Some(BinderKeyRef::Written(self))
    }
}
impl BinderKey for String {
    fn binder_key(&self) -> Option<BinderKeyRef<'_>> {
        Some(BinderKeyRef::Written(self))
    }
}
impl BinderKey for SurfaceBinder {
    fn binder_key(&self) -> Option<BinderKeyRef<'_>> {
        Some(match self {
            Self::Written(name) => BinderKeyRef::Written(name),
            Self::Generated(id) => BinderKeyRef::Generated(id),
        })
    }
}
impl BinderKey for GeneratedBinderId {
    fn binder_key(&self) -> Option<BinderKeyRef<'_>> {
        Some(BinderKeyRef::Generated(self))
    }
}
impl<T: BinderKey + ?Sized> BinderKey for &T {
    fn binder_key(&self) -> Option<BinderKeyRef<'_>> {
        (*self).binder_key()
    }
}
impl From<GeneratedBinderId> for SurfaceBinder {
    fn from(id: GeneratedBinderId) -> Self {
        Self::Generated(id)
    }
}
impl From<&GeneratedBinderId> for SurfaceBinder {
    fn from(id: &GeneratedBinderId) -> Self {
        Self::Generated(*id)
    }
}

// Each entry retains its typed key so iteration can borrow it. The source
// index still admits allocation-free borrowed-str queries.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct BinderMap<V> {
    written: BTreeMap<String, (SurfaceBinder, V)>,
    generated: BTreeMap<GeneratedBinderId, (SurfaceBinder, V)>,
}
impl<V> Default for BinderMap<V> {
    fn default() -> Self {
        Self {
            written: BTreeMap::new(),
            generated: BTreeMap::new(),
        }
    }
}
impl<V> BinderMap<V> {
    pub fn new() -> Self {
        Self::default()
    }
    pub fn get<Q: BinderKey + ?Sized>(&self, key: &Q) -> Option<&V> {
        match key.binder_key()? {
            BinderKeyRef::Written(name) => self.written.get(name),
            BinderKeyRef::Generated(id) => self.generated.get(id),
        }
        .map(|(_, value)| value)
    }
    pub fn contains_key<Q: BinderKey + ?Sized>(&self, key: &Q) -> bool {
        self.get(key).is_some()
    }
    pub fn insert<N: Into<SurfaceBinder>>(&mut self, key: N, value: V) -> Option<V> {
        let key = key.into();
        match &key {
            SurfaceBinder::Written(name) => self.written.insert(name.clone(), (key, value)),
            SurfaceBinder::Generated(id) => self.generated.insert(*id, (key, value)),
        }
        .map(|(_, value)| value)
    }
    pub fn remove<Q: BinderKey + ?Sized>(&mut self, key: &Q) -> Option<V> {
        match key.binder_key()? {
            BinderKeyRef::Written(name) => self.written.remove(name),
            BinderKeyRef::Generated(id) => self.generated.remove(id),
        }
        .map(|(_, value)| value)
    }
    pub fn len(&self) -> usize {
        self.written.len() + self.generated.len()
    }
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
    pub fn iter(&self) -> impl Iterator<Item = (&SurfaceBinder, &V)> {
        self.written
            .values()
            .chain(self.generated.values())
            .map(|(key, value)| (key, value))
    }
}
type BinderMapIter<'a, V> = std::iter::Map<
    std::iter::Chain<
        std::collections::btree_map::Values<'a, String, (SurfaceBinder, V)>,
        std::collections::btree_map::Values<'a, GeneratedBinderId, (SurfaceBinder, V)>,
    >,
    fn(&'a (SurfaceBinder, V)) -> (&'a SurfaceBinder, &'a V),
>;
impl<'a, V> IntoIterator for &'a BinderMap<V> {
    type Item = (&'a SurfaceBinder, &'a V);
    type IntoIter = BinderMapIter<'a, V>;
    fn into_iter(self) -> Self::IntoIter {
        self.written
            .values()
            .chain(self.generated.values())
            .map(|(key, value)| (key, value))
    }
}
impl<V, N: Into<SurfaceBinder>> FromIterator<(N, V)> for BinderMap<V> {
    fn from_iter<T: IntoIterator<Item = (N, V)>>(items: T) -> Self {
        let mut result = Self::new();
        result.extend(items);
        result
    }
}
impl<V, N: Into<SurfaceBinder>> Extend<(N, V)> for BinderMap<V> {
    fn extend<T: IntoIterator<Item = (N, V)>>(&mut self, items: T) {
        for (key, value) in items {
            self.insert(key, value);
        }
    }
}
impl<V, N: Into<SurfaceBinder>> From<BTreeMap<N, V>> for BinderMap<V> {
    fn from(items: BTreeMap<N, V>) -> Self {
        items.into_iter().collect()
    }
}

#[derive(Debug, PartialEq, Eq)]
pub(super) struct PersistentBinderMap<V> {
    written: PersistentMap<String, (SurfaceBinder, V)>,
    generated: PersistentMap<GeneratedBinderId, (SurfaceBinder, V)>,
}
impl<V: Clone> Clone for PersistentBinderMap<V> {
    fn clone(&self) -> Self {
        Self {
            written: self.written.clone(),
            generated: self.generated.clone(),
        }
    }
}
impl<V> Default for PersistentBinderMap<V> {
    fn default() -> Self {
        Self {
            written: PersistentMap::default(),
            generated: PersistentMap::default(),
        }
    }
}
impl<V> PersistentBinderMap<V> {
    #[cfg(test)]
    pub fn shares_root_with(&self, other: &Self) -> bool {
        self.written.shares_root_with(&other.written)
            && self.generated.shares_root_with(&other.generated)
    }

    pub fn get<Q: BinderKey + ?Sized>(&self, key: &Q) -> Option<&V> {
        match key.binder_key()? {
            BinderKeyRef::Written(name) => self.written.get(name),
            BinderKeyRef::Generated(id) => self.generated.get(id),
        }
        .map(|(_, value)| value)
    }
    pub fn contains_key<Q: BinderKey + ?Sized>(&self, key: &Q) -> bool {
        self.get(key).is_some()
    }
    pub fn insert<N: Into<SurfaceBinder>>(&mut self, key: N, value: V) {
        let key = key.into();
        match &key {
            SurfaceBinder::Written(name) => self.written.insert(name.clone(), (key, value)),
            SurfaceBinder::Generated(id) => self.generated.insert(*id, (key, value)),
        }
    }
    pub fn remove<Q: BinderKey + ?Sized>(&mut self, key: &Q) {
        match key.binder_key() {
            Some(BinderKeyRef::Written(name)) => self.written.remove(&name.to_owned()),
            Some(BinderKeyRef::Generated(id)) => self.generated.remove(id),
            None => {}
        }
    }
    pub fn with_inserted<N: Into<SurfaceBinder>>(&self, key: N, value: V) -> Self
    where
        V: Clone,
    {
        let mut result = self.clone();
        result.insert(key, value);
        result
    }
    pub fn without_key<Q: BinderKey + ?Sized>(&self, key: &Q) -> Self
    where
        V: Clone,
    {
        let mut result = self.clone();
        result.remove(key);
        result
    }
    pub fn len(&self) -> usize {
        self.written.len() + self.generated.len()
    }
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
    pub fn iter(&self) -> impl Iterator<Item = (&SurfaceBinder, &V)> {
        self.written
            .values()
            .chain(self.generated.values())
            .map(|(key, value)| (key, value))
    }
    pub fn keys(&self) -> impl Iterator<Item = &SurfaceBinder> {
        self.iter().map(|(key, _)| key)
    }
    pub fn diff<'a>(
        &'a self,
        other: &'a Self,
    ) -> impl Iterator<Item = (&'a SurfaceBinder, Option<&'a V>, Option<&'a V>)>
    where
        V: PartialEq,
    {
        self.written
            .diff(&other.written)
            .map(|(_, before, after)| {
                (
                    &before.or(after).unwrap().0,
                    before.map(|(_, v)| v),
                    after.map(|(_, v)| v),
                )
            })
            .chain(
                self.generated
                    .diff(&other.generated)
                    .map(|(_, before, after)| {
                        (
                            &before.or(after).unwrap().0,
                            before.map(|(_, v)| v),
                            after.map(|(_, v)| v),
                        )
                    }),
            )
    }
}
// The persistent map's values iterator is opaque; use its concrete entry iterator.
pub(super) struct PersistentBinderMapEntries<'a, V> {
    written: crate::persistent::PersistentMapIter<'a, String, (SurfaceBinder, V)>,
    generated: crate::persistent::PersistentMapIter<'a, GeneratedBinderId, (SurfaceBinder, V)>,
}
impl<'a, V> Iterator for PersistentBinderMapEntries<'a, V> {
    type Item = (&'a SurfaceBinder, &'a V);
    fn next(&mut self) -> Option<Self::Item> {
        self.written
            .next()
            .map(|(_, (key, value))| (key, value))
            .or_else(|| self.generated.next().map(|(_, (key, value))| (key, value)))
    }
}
impl<'a, V> IntoIterator for &'a PersistentBinderMap<V> {
    type Item = (&'a SurfaceBinder, &'a V);
    type IntoIter = PersistentBinderMapEntries<'a, V>;
    fn into_iter(self) -> Self::IntoIter {
        PersistentBinderMapEntries {
            written: self.written.iter(),
            generated: self.generated.iter(),
        }
    }
}
impl<V, N: Into<SurfaceBinder>> FromIterator<(N, V)> for PersistentBinderMap<V> {
    fn from_iter<T: IntoIterator<Item = (N, V)>>(items: T) -> Self {
        let mut result = Self::default();
        result.extend(items);
        result
    }
}
impl<V, N: Into<SurfaceBinder>> Extend<(N, V)> for PersistentBinderMap<V> {
    fn extend<T: IntoIterator<Item = (N, V)>>(&mut self, items: T) {
        for (key, value) in items {
            self.insert(key, value);
        }
    }
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(super) struct BinderSet {
    written: BTreeSet<String>,
    generated: BTreeSet<GeneratedBinderId>,
}
impl BinderSet {
    pub fn new() -> Self {
        Self::default()
    }
    pub fn contains<Q: BinderKey + ?Sized>(&self, key: &Q) -> bool {
        match key.binder_key() {
            Some(BinderKeyRef::Written(name)) => self.written.contains(name),
            Some(BinderKeyRef::Generated(id)) => self.generated.contains(id),
            None => false,
        }
    }
    pub fn insert<N: Into<SurfaceBinder>>(&mut self, key: N) -> bool {
        match key.into() {
            SurfaceBinder::Written(name) => self.written.insert(name),
            SurfaceBinder::Generated(id) => self.generated.insert(id),
        }
    }
    pub fn remove<Q: BinderKey + ?Sized>(&mut self, key: &Q) -> bool {
        match key.binder_key() {
            Some(BinderKeyRef::Written(name)) => self.written.remove(name),
            Some(BinderKeyRef::Generated(id)) => self.generated.remove(id),
            None => false,
        }
    }
}
impl<N: Into<SurfaceBinder>> FromIterator<N> for BinderSet {
    fn from_iter<T: IntoIterator<Item = N>>(items: T) -> Self {
        let mut result = Self::new();
        for key in items {
            result.insert(key);
        }
        result
    }
}
impl<N: Into<SurfaceBinder>> Extend<N> for BinderSet {
    fn extend<T: IntoIterator<Item = N>>(&mut self, items: T) {
        for key in items {
            self.insert(key);
        }
    }
}

/// Undo-log scopes preserve only the changed bindings, in either namespace.
#[derive(Clone, Debug)]
pub(super) struct ScopedBinders<V> {
    names: BinderMap<V>,
    shadowed: Vec<(SurfaceBinder, Option<V>)>,
}
impl<V> Default for ScopedBinders<V> {
    fn default() -> Self {
        Self {
            names: BinderMap::new(),
            shadowed: Vec::new(),
        }
    }
}
impl<V> ScopedBinders<V> {
    pub fn new(names: BinderMap<V>) -> Self {
        Self {
            names,
            shadowed: Vec::new(),
        }
    }
    pub fn reset<N: Into<SurfaceBinder>>(&mut self, values: impl IntoIterator<Item = (N, V)>) {
        self.names = values.into_iter().collect();
        self.shadowed.clear();
    }
    pub fn scope(&self) -> crate::surface::scoped_names::Scope {
        crate::surface::scoped_names::Scope(self.shadowed.len())
    }
    pub fn bind<N: Into<SurfaceBinder>>(&mut self, name: N, value: V) {
        let name = name.into();
        let previous = self.names.insert(name.clone(), value);
        self.shadowed.push((name, previous));
    }
    pub fn hide<N: Into<SurfaceBinder>>(&mut self, name: N) {
        let name = name.into();
        let previous = self.names.remove(&name);
        self.shadowed.push((name, previous));
    }
    pub fn end_with(
        &mut self,
        scope: crate::surface::scoped_names::Scope,
        mut restored: impl FnMut(&SurfaceBinder, Option<&V>),
    ) {
        while self.shadowed.len() > scope.0 {
            let (name, previous) = self.shadowed.pop().expect("binding above scope");
            match previous {
                Some(value) => {
                    self.names.insert(name.clone(), value);
                }
                None => {
                    self.names.remove(&name);
                }
            }
            restored(&name, self.names.get(&name));
        }
    }
    pub fn end(&mut self, scope: crate::surface::scoped_names::Scope) {
        self.end_with(scope, |_, _| {});
    }
    pub fn names(&self) -> &BinderMap<V> {
        &self.names
    }
    pub fn get<Q: BinderKey + ?Sized>(&self, key: &Q) -> Option<&V> {
        self.names.get(key)
    }
}
impl From<SurfaceBinder> for crate::kernel::BindingName {
    fn from(name: SurfaceBinder) -> Self {
        name.kernel_name()
    }
}
impl From<&SurfaceBinder> for crate::kernel::BindingName {
    fn from(name: &SurfaceBinder) -> Self {
        name.kernel_name()
    }
}

impl BinderKey for crate::kernel::BindingName {
    fn binder_key(&self) -> Option<BinderKeyRef<'_>> {
        match self {
            Self::Named(name) => Some(BinderKeyRef::Written(name)),
            Self::Generated(id) => Some(BinderKeyRef::Generated(id)),
            _ => None,
        }
    }
}
impl<V> crate::kernel::NamedBindingMap<V> for BinderMap<V> {
    fn get_named(&self, name: &str) -> Option<&V> {
        self.get(name)
    }
    fn get_binding(&self, name: &crate::kernel::BindingName) -> Option<&V> {
        self.get(name)
    }
}
impl<V> crate::kernel::NamedBindingMap<V> for PersistentBinderMap<V> {
    fn get_named(&self, name: &str) -> Option<&V> {
        self.get(name)
    }
    fn get_binding(&self, name: &crate::kernel::BindingName) -> Option<&V> {
        self.get(name)
    }
}

impl PartialEq<SurfaceBinder> for str {
    fn eq(&self, other: &SurfaceBinder) -> bool {
        other == self
    }
}
impl PartialEq<&SurfaceBinder> for str {
    fn eq(&self, other: &&SurfaceBinder) -> bool {
        *other == self
    }
}
impl<V, N: Into<SurfaceBinder>, const L: usize> From<[(N, V); L]> for BinderMap<V> {
    fn from(items: [(N, V); L]) -> Self {
        items.into_iter().collect()
    }
}
impl<V, N: Into<SurfaceBinder>, const L: usize> From<[(N, V); L]> for PersistentBinderMap<V> {
    fn from(items: [(N, V); L]) -> Self {
        items.into_iter().collect()
    }
}

impl From<crate::kernel::BindingName> for SurfaceBinder {
    fn from(name: crate::kernel::BindingName) -> Self {
        match name {
            crate::kernel::BindingName::Named(name) => Self::Written(name),
            crate::kernel::BindingName::Generated(id) => Self::Generated(id),
            _ => unreachable!("a lexical binder is not a C object"),
        }
    }
}
impl From<&crate::kernel::BindingName> for SurfaceBinder {
    fn from(name: &crate::kernel::BindingName) -> Self {
        name.clone().into()
    }
}

impl IntoIterator for BinderSet {
    type Item = SurfaceBinder;
    type IntoIter = std::iter::Chain<
        std::iter::Map<std::collections::btree_set::IntoIter<String>, fn(String) -> SurfaceBinder>,
        std::iter::Map<
            std::collections::btree_set::IntoIter<GeneratedBinderId>,
            fn(GeneratedBinderId) -> SurfaceBinder,
        >,
    >;
    fn into_iter(self) -> Self::IntoIter {
        self.written
            .into_iter()
            .map(SurfaceBinder::Written as fn(String) -> SurfaceBinder)
            .chain(
                self.generated
                    .into_iter()
                    .map(SurfaceBinder::Generated as fn(GeneratedBinderId) -> SurfaceBinder),
            )
    }
}
impl PartialEq<SurfaceBinder> for &str {
    fn eq(&self, other: &SurfaceBinder) -> bool {
        other == *self
    }
}

impl SurfaceTerm {
    pub(super) fn generated_binder(&self) -> Option<GeneratedBinderId> {
        match self {
            Self::ProgramExpression(ProgramExpression::Variable(
                crate::kernel::BindingName::Generated(id),
            )) => Some(*id),
            Self::AlgebraicVariable {
                name: SurfaceBinder::Generated(id),
                ..
            } => Some(*id),
            _ => None,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn generated_binders_are_distinct_from_written_names_and_restore_scopes() {
        let first = SurfaceBinder::fresh();
        let second = SurfaceBinder::fresh();
        assert_ne!(first, second);
        assert_ne!(first, SurfaceBinder::Written(first.to_string()));
        let mut scope = ScopedBinders::default();
        scope.bind(&first, 1);
        scope.bind("__click_binder_0", 2);
        let mark = scope.scope();
        scope.bind(&first, 3);
        scope.hide("__click_binder_0");
        scope.bind(&second, 4);
        scope.end(mark);
        assert_eq!(scope.get(&first), Some(&1));
        assert_eq!(scope.get("__click_binder_0"), Some(&2));
        assert_eq!(scope.get(&second), None);
    }
    #[test]
    fn lexical_binders_and_beta_capture_roundtrip() {
        for source in [
            "theorem check() { ensures forall (value: Integer) { value == value } by { let other = intro(); close(); } }",
            "theorem check() { ensures (|i: Integer| -> Integer { i + 1 })(41) == 42 by close(); }",
            "theorem check() { ensures (|i: uint64| -> uint64 { i + 1u64 })(41u64) == 42u64 by close(); }",
            "spec enum Boxed { Value(Integer) } function unpack(b: Boxed) -> Integer { match b { Boxed::Value(value) => value } } theorem check() { ensures unpack(Boxed::Value(42)) == 42 by { unfold(unpack(Boxed::Value(42))); close(); } }",
            "theorem check() { ensures (let value: fn(Integer) -> Integer = |x: Integer| -> Integer { x + 1 }; value(41)) == 42 by close(); }",
            "theorem check(lo: int32, hi: int32) { requires lo < hi; ensures (lo..hi).all(|i| { i < hi }) by { intro(); intro(); close(); } }",
            "function apply(x: Integer, y: Integer) -> Integer { (|y: Integer| -> Integer { x + y })(0) } theorem check(y: Integer) { ensures apply(y, 99) == y by { unfold(apply(y, 99)); close(); } }",
            "theorem check(__click_binder_0: Integer, __lambda_0: Integer, __click_lambda_0: Integer) { ensures (|x: Integer| -> Integer { x + __click_binder_0 })(__lambda_0) == __lambda_0 + __click_binder_0 by close(); }",
        ] {
            crate::surface::verify_c_sources(source, &[])
                .unwrap_or_else(|error| panic!("{source}: {}", error.report()));
        }
    }
    #[test]
    fn generated_binders_expand_and_cold_replay_without_search() {
        for source in [
            "theorem check() { ensures answer: forall (value: Integer) { value == value } by { intro(); close(); } }",
            "function every(p: fn(int32) -> Prop, lo: int32, hi: int32) -> Prop { (lo..hi).all(p) } theorem check(lo: int32, hi: int32) { requires lo < hi; ensures answer: every(|i: int32| -> Prop { i < hi }, lo, hi) by { intro(); intro(); close(); } }",
            "theorem check(lo: int32, hi: int32, limit: int32) { let p = |x: int32| -> Prop { x < limit }; requires hi <= limit; ensures answer: (lo..hi).all(p) by { let value = intro(); intro(); close(); } }",
        ] {
            let expanded =
                crate::surface::expand_c_claim_source_by_label(source, &[], "check.answer")
                    .unwrap_or_else(|error| panic!("{source}: {}", error.report()));
            assert!(!expanded.contains("solve("), "{expanded}");
            assert!(!expanded.contains("binder("), "{expanded}");
            crate::surface::without_implicit_solve(|| {
                crate::surface::verify_c_sources(&expanded, &[])
            })
            .unwrap_or_else(|error| panic!("{expanded}: {}", error.report()));
        }
    }
    #[test]
    fn source_cannot_declare_numeric_binder_identities() {
        for source in [
            "theorem check() { ensures binder(7) == binder(7) by close(); }",
            "theorem check() { ensures forall (binder(7): int32) { binder(7) == 0 } by close(); }",
            "theorem check() { ensures forall (x: Integer) { x == x } by { let binder(7) = intro(); close(); } }",
            "theorem check() { ensures (let binder(7): Integer = 0; binder(7)) == 0 by close(); }",
        ] {
            assert!(
                crate::surface::verify_c_sources(source, &[]).is_err(),
                "{source}"
            );
        }
    }
    #[test]
    fn selected_substitutions_include_resource_parameters() {
        let parameter = SurfaceTerm::Resource(Box::new(ResourceSubject::Parameter {
            name: "A".into(),
            index: 0,
        }));
        let replacement = SurfaceTerm::Resource(Box::new(ResourceSubject::Emp));
        let substitutions = BTreeMap::from([("A".to_owned(), replacement.clone())]);
        assert_eq!(
            lowering::substitute_contract_expression(&parameter, &substitutions).unwrap(),
            replacement
        );
    }
    #[test]
    fn cloned_generated_binders_do_not_capture_replacements() {
        let bound = SurfaceBinder::fresh();
        let expression = SurfaceTerm::Lambda {
            parameters: vec![(bound.clone(), ClickType::Integer)],
            result: ClickType::Integer,
            body: Box::new(SurfaceTerm::Add(
                Box::new(bound.reference()),
                Box::new(SurfaceTerm::Binding("input".into())),
            )),
        };
        let changed = lowering::substitute_contract_expression(
            &expression,
            &BTreeMap::from([("input".to_owned(), bound.reference())]),
        )
        .unwrap();
        let SurfaceTerm::Lambda { parameters, .. } = &changed else {
            panic!("lambda")
        };
        assert_ne!(parameters[0].0, bound);
        assert_eq!(
            lowering::contract_expression_referenced_bindings(&changed),
            BTreeSet::from([bound.kernel_name()])
        );
    }
}
#[cfg(test)]
mod scaling_tests {
    include!("../scaling_tests/surface/binders.rs");
}
