use std::collections::BTreeMap;

pub type Symbol = u64;

pub type Record = BTreeMap<Symbol, Object>;

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Object {
    Symbol(Symbol),
    Record(Record),
}
