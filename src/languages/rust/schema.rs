//! Compiler-owned typed Rust source vocabulary. No printed compiler dumps.
use serde::{Deserialize, Serialize};

pub const SCHEMA: u32 = 8;
pub const COMPILER_COMMIT: &str = "01dfd79246f1b2d5f146616deff08223a840a9ae";
pub const TARGET: &str = "x86_64-unknown-linux-gnu";

#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct RustExport {
    pub schema: u32,
    pub compiler_commit: String,
    pub target: String,
    pub edition: String,
    pub overflow_checks: bool,
    pub panic: String,
    pub mir_opt_level: u32,
    pub logical_source: String,
    pub records: Vec<Record>,
    pub functions: Vec<Function>,
}

#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct Span {
    pub line: usize,
    pub column: usize,
}

#[derive(Clone, Debug, PartialEq, Eq, Deserialize, Serialize)]
#[serde(tag = "kind", rename_all = "snake_case", deny_unknown_fields)]
pub enum Type {
    // Named Charon-only shared-byte chunk protocol; not general external ADTs.
    ChunkIterator,
    ChunkOption,
    I32,
    U8,
    U16,
    U32,
    Usize,
    ByteSlice { mutable: bool },
    Array { element: Box<Type>, length: u64 },
    Bool,
    Unit,
    Reference { mutable: bool, pointee: Box<Type> },
    Record { name: String },
}

#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct Record {
    pub name: String,
    pub size: u32,
    pub alignment: u32,
    pub fields: Vec<Field>,
    pub destructor: Option<String>,
}
#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct Field {
    pub name: String,
    pub offset: u32,
    pub value_type: Type,
}
#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct Place {
    pub name: String,
    pub value_type: Type,
    pub span: Span,
}
#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct Function {
    pub name: String,
    pub return_type: Type,
    pub parameters: Vec<Place>,
    pub body: Vec<Statement>,
    pub mir: Option<MirBody>,
    pub span: Span,
}
#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(tag = "kind", rename_all = "snake_case", deny_unknown_fields)]
pub enum Expression {
    IntegerFrom {
        value: Box<Self>,
        source_type: Type,
        value_type: Type,
    },
    ChunkHasNext {
        iterator: String,
    },
    ChunkOptionSlice {
        option: String,
    },
    ChunkOptionTag {
        option: String,
    },
    ChunkRemainder {
        iterator: String,
    },
    ArrayToSlice {
        array: Box<Self>,
        mutable: bool,
    },
    Array {
        elements: Vec<Self>,
    },
    Repeat {
        value: Box<Self>,
        length: u64,
    },
    Integer {
        value: i32,
    },
    UnsignedInteger {
        value: u32,
        value_type: Type,
    },
    UsizeInteger {
        value: u64,
    },
    SliceLength {
        slice: Box<Self>,
    },
    Index {
        slice: Box<Self>,
        index: Box<Self>,
    },
    Boolean {
        value: bool,
    },
    Local {
        name: String,
    },
    Binary {
        operator: String,
        left_type: Type,
        right_type: Type,
        left: Box<Self>,
        right: Box<Self>,
    },
    Not {
        value: Box<Self>,
    },
    BitwiseNot {
        value: Box<Self>,
        value_type: Type,
    },
    Cast {
        value: Box<Self>,
        value_type: Type,
    },
    Borrow {
        place: Box<Self>,
        value_type: Type,
    },
    Deref {
        reference: Box<Self>,
        value_type: Type,
    },
    Field {
        base: Box<Self>,
        record: String,
        field: String,
    },
    Call {
        function: String,
        arguments: Vec<Self>,
    },
}
#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(tag = "kind", rename_all = "snake_case", deny_unknown_fields)]
pub enum Statement {
    ChunkDeclare {
        iterator: String,
        slice: Expression,
        size: Expression,
    },
    ChunkFor {
        iterator: String,
        binding: Place,
        body: Vec<Self>,
    },
    // Compiler-resolved shared slice split, with the tuple destructured locally.
    SliceSplit {
        slice: Expression,
        midpoint: Expression,
        left: Place,
        right: Place,
    },
    // Compiler-resolved slice iterator protocol, not an index-loop rewrite.
    SliceFor {
        iterator: String,
        slice: Expression,
        binding: Place,
        by_reference: bool,
        body: Vec<Self>,
    },
    While {
        condition: Expression,
        body: Vec<Self>,
    },
    Declare {
        place: Place,
        initializer: Expression,
    },
    Assign {
        target: Expression,
        value: Expression,
    },
    If {
        condition: Expression,
        then_body: Vec<Self>,
        else_body: Vec<Self>,
    },
    Return {
        value: Option<Expression>,
    },
    Call {
        function: String,
        arguments: Vec<Expression>,
    },
}

// Drop-elaborated MIR with validated acyclic regions and natural while loops. Ownership events remain explicit in the
// artifact and are checked by live-value assertions in direct lowering.
#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct MirBody {
    pub locals: Vec<Place>,
    pub blocks: Vec<MirBlock>,
}
#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct MirBlock {
    pub statements: Vec<MirStatement>,
    pub terminator: MirTerminator,
}
#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(tag = "kind", rename_all = "snake_case", deny_unknown_fields)]
pub enum MirStatement {
    ChunkInitialize {
        target: String,
        slice: Expression,
        size: Expression,
    },
    ChunkMove {
        target: String,
        source: String,
    },
    ChunkNext {
        iterator: String,
        option: String,
    },
    Assign {
        target: Expression,
        value: Expression,
    },
    Initialize {
        target: String,
        record: String,
        fields: Vec<Expression>,
    },
    Move {
        target: String,
        source: String,
        record: String,
    },
    EndStorage {
        local: String,
    },
}
#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(tag = "kind", rename_all = "snake_case", deny_unknown_fields)]
pub enum MirTerminator {
    Goto {
        target: usize,
    },
    If {
        condition: Expression,
        then_target: usize,
        else_target: usize,
    },
    Drop {
        local: String,
        record: String,
        target: usize,
    },
    Call {
        function: String,
        arguments: Vec<Expression>,
        destination: String,
        target: usize,
    },
    Return,
    Unreachable,
}
