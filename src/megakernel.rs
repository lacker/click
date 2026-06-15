//! Experimental rich kernel for systems-code proofs.
//!
//! This module keeps the LCF shape: `Theorem` is an abstract object whose
//! constructor is not public. The trusted kernel language has native systems
//! concepts instead of encoding them as a tiny general-purpose calculus.

use std::collections::{BTreeMap, BTreeSet};

#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct Var(pub u64);

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum Sort {
    Bool,
    Bv32,
    CType,
    CInt32,
    CBool,
    CPtr,
    CValue,
    CMemory,
    CState,
    CStmtOutcome,
    CFunctionOutcome,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum Bv32Term {
    Const(u32),
    Var(Var),
    Add(Box<Bv32Term>, Box<Bv32Term>),
    Sub(Box<Bv32Term>, Box<Bv32Term>),
    Mul(Box<Bv32Term>, Box<Bv32Term>),
    MemoryLoad(Box<CMemory>, Box<Ptr>),
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum BoolTerm {
    Const(bool),
    Var(Var),
    Bv32Slt(Box<Bv32Term>, Box<Bv32Term>),
    Bv32Sle(Box<Bv32Term>, Box<Bv32Term>),
    Bv32Sgt(Box<Bv32Term>, Box<Bv32Term>),
    Bv32Sge(Box<Bv32Term>, Box<Bv32Term>),
    Bv32Eq(Box<Bv32Term>, Box<Bv32Term>),
    Bv32SignedAddOverflows(Box<Bv32Term>, Box<Bv32Term>),
    Bv32SignedSubOverflows(Box<Bv32Term>, Box<Bv32Term>),
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct Ptr {
    pub block: String,
    pub offset: Bv32Term,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum CValue {
    Int32(Bv32Term),
    Bool(BoolTerm),
    Ptr(Ptr),
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum CType {
    Int32,
    Int32Ptr,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum CExpr {
    Value(CValue),
    Var(String),
    AddressOf(String),
    Lt(Box<CExpr>, Box<CExpr>),
    Le(Box<CExpr>, Box<CExpr>),
    Gt(Box<CExpr>, Box<CExpr>),
    Ge(Box<CExpr>, Box<CExpr>),
    Eq(Box<CExpr>, Box<CExpr>),
    Add(Box<CExpr>, Box<CExpr>),
    Sub(Box<CExpr>, Box<CExpr>),
    Load(Box<CExpr>),
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum CStmt {
    Declare {
        name: String,
        ty: CType,
    },
    Assign {
        name: String,
        expr: CExpr,
    },
    CallAssign {
        target: String,
        function_name: String,
        args: Vec<CExpr>,
    },
    Seq(Box<CStmt>, Box<CStmt>),
    Return(CExpr),
    Store {
        ptr: CExpr,
        value: CExpr,
    },
    If {
        condition: CExpr,
        then_branch: Box<CStmt>,
        else_branch: Box<CStmt>,
    },
    While {
        condition: CExpr,
        invariant: Vec<Prop>,
        body: Box<CStmt>,
    },
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct CParam {
    name: String,
    ty: CType,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct CFunction {
    return_type: CType,
    name: String,
    params: Vec<CParam>,
    body: CStmt,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct CFunctionSpec {
    state: CState,
    args: Vec<CExpr>,
    requires: Vec<Prop>,
    outcome: CFunctionOutcome,
}

#[derive(Clone, Debug, Default, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct CFunctionEnv {
    functions: BTreeMap<String, CFunction>,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum CUndefinedBehavior {
    SignedOverflow,
    InvalidMemory,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum CRuntimeError {
    UnboundVariable(String),
    UnknownFunction(String),
    TypeMismatch,
    WrongArity { expected: usize, actual: usize },
    MissingReturn,
    LoopLimitExceeded,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum CExprOutcome {
    Value(CValue),
    Ub(CUndefinedBehavior),
    RuntimeError(CRuntimeError),
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum CStmtOutcome {
    Normal(CState),
    Return { value: CValue, state: CState },
    Ub(CUndefinedBehavior),
    RuntimeError(CRuntimeError),
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum CFunctionOutcome {
    Return { value: CValue, state: CState },
    Ub(CUndefinedBehavior),
    RuntimeError(CRuntimeError),
}

#[derive(Clone, Debug, Default, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct CLocalEnv {
    bindings: BTreeMap<String, CValue>,
}

#[derive(Clone, Debug, Default, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct CMemory {
    blocks: BTreeMap<String, CBlock>,
    cells: BTreeMap<Ptr, CValue>,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct CBlock {
    size: u32,
}

#[derive(Clone, Debug, Default, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct CState {
    locals: CLocalEnv,
    memory: CMemory,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum Term {
    Bool(BoolTerm),
    Bv32(Bv32Term),
    CValue(CValue),
    CExprOutcome(CExprOutcome),
    CStmtOutcome(CStmtOutcome),
    CFunctionOutcome(CFunctionOutcome),
    CMemory(CMemory),
    CState(CState),
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum Prop {
    Equal(Term, Term),
    BoolIs(BoolTerm, bool),
    CExprEvaluates {
        state: CState,
        expr: CExpr,
        outcome: CExprOutcome,
    },
    CStmtExecutes {
        state: CState,
        stmt: CStmt,
        outcome: CStmtOutcome,
    },
    CFunctionExecutes {
        state: CState,
        function: CFunction,
        args: Vec<CExpr>,
        outcome: CFunctionOutcome,
    },
    CFunctionSatisfiesSpec {
        function: CFunction,
        spec: CFunctionSpec,
    },
    CMemoryLoads {
        memory: CMemory,
        ptr: Ptr,
        outcome: CExprOutcome,
    },
    CMemoryCanLoad {
        memory: CMemory,
        ptr: Ptr,
    },
    CMemoryCanStore {
        memory: CMemory,
        ptr: Ptr,
    },
    Implies(Box<Prop>, Box<Prop>),
    ForAll {
        var: Var,
        sort: Sort,
        body: Box<Prop>,
    },
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Theorem {
    prop: Prop,
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Assumptions {
    bool_facts: BTreeMap<BoolTerm, bool>,
    prop_facts: BTreeSet<Prop>,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct ProofObligation {
    prop: Prop,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct PathFact {
    prop: Prop,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SymbolicCExecution {
    paths: Vec<SymbolicCExecutionPath>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SymbolicCExecutionPath {
    facts: Vec<PathFact>,
    obligations: Vec<ProofObligation>,
    theorem: Theorem,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct CExprPath {
    outcome: CExprOutcome,
    facts: Vec<PathFact>,
    obligations: Vec<ProofObligation>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct CStmtPath {
    outcome: CStmtOutcome,
    facts: Vec<PathFact>,
    obligations: Vec<ProofObligation>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct CFunctionPath {
    outcome: CFunctionOutcome,
    facts: Vec<PathFact>,
    obligations: Vec<ProofObligation>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct CArgsPath {
    values: Vec<CValue>,
    outcome: Option<CFunctionOutcome>,
    facts: Vec<PathFact>,
    obligations: Vec<ProofObligation>,
}

impl Bv32Term {
    pub fn var(var: Var) -> Self {
        Self::Var(var)
    }

    pub fn constant(value: u32) -> Self {
        Self::Const(value)
    }

    fn as_const(&self) -> Option<u32> {
        match self {
            Self::Const(value) => Some(*value),
            Self::Var(_) | Self::MemoryLoad(_, _) => None,
            Self::Add(left, right) => Some(left.as_const()?.wrapping_add(right.as_const()?)),
            Self::Sub(left, right) => Some(left.as_const()?.wrapping_sub(right.as_const()?)),
            Self::Mul(left, right) => Some(left.as_const()?.wrapping_mul(right.as_const()?)),
        }
    }

    fn add(left: Self, right: Self) -> Self {
        match (left.as_const(), right.as_const()) {
            (Some(left), Some(right)) => Self::Const(left.wrapping_add(right)),
            _ => Self::Add(Box::new(left), Box::new(right)),
        }
    }

    fn sub(left: Self, right: Self) -> Self {
        match (left.as_const(), right.as_const()) {
            (Some(left), Some(right)) => Self::Const(left.wrapping_sub(right)),
            _ => Self::Sub(Box::new(left), Box::new(right)),
        }
    }

    fn mul(left: Self, right: Self) -> Self {
        match (left.as_const(), right.as_const()) {
            (Some(left), Some(right)) => Self::Const(left.wrapping_mul(right)),
            _ => Self::Mul(Box::new(left), Box::new(right)),
        }
    }
}

impl BoolTerm {
    fn slt(left: Bv32Term, right: Bv32Term) -> Self {
        match (left.as_const(), right.as_const()) {
            (Some(left), Some(right)) => Self::Const((left as i32) < (right as i32)),
            _ => Self::Bv32Slt(Box::new(left), Box::new(right)),
        }
    }

    fn sle(left: Bv32Term, right: Bv32Term) -> Self {
        match (left.as_const(), right.as_const()) {
            (Some(left), Some(right)) => Self::Const((left as i32) <= (right as i32)),
            _ => Self::Bv32Sle(Box::new(left), Box::new(right)),
        }
    }

    fn sgt(left: Bv32Term, right: Bv32Term) -> Self {
        match (left.as_const(), right.as_const()) {
            (Some(left), Some(right)) => Self::Const((left as i32) > (right as i32)),
            _ => Self::Bv32Sgt(Box::new(left), Box::new(right)),
        }
    }

    fn sge(left: Bv32Term, right: Bv32Term) -> Self {
        match (left.as_const(), right.as_const()) {
            (Some(left), Some(right)) => Self::Const((left as i32) >= (right as i32)),
            _ => Self::Bv32Sge(Box::new(left), Box::new(right)),
        }
    }

    fn eq(left: Bv32Term, right: Bv32Term) -> Self {
        match (left.as_const(), right.as_const()) {
            (Some(left), Some(right)) => Self::Const(left == right),
            _ => Self::Bv32Eq(Box::new(left), Box::new(right)),
        }
    }

    fn signed_add_overflows(left: Bv32Term, right: Bv32Term) -> Self {
        match (left.as_const(), right.as_const()) {
            (Some(left), Some(right)) => Self::Const((left as i32).overflowing_add(right as i32).1),
            _ => Self::Bv32SignedAddOverflows(Box::new(left), Box::new(right)),
        }
    }

    fn signed_sub_overflows(left: Bv32Term, right: Bv32Term) -> Self {
        match (left.as_const(), right.as_const()) {
            (Some(left), Some(right)) => Self::Const((left as i32).overflowing_sub(right as i32).1),
            _ => Self::Bv32SignedSubOverflows(Box::new(left), Box::new(right)),
        }
    }
}

impl CType {
    fn accepts(self, value: &CValue) -> bool {
        matches!(
            (self, value),
            (Self::Int32, CValue::Int32(_)) | (Self::Int32Ptr, CValue::Ptr(_))
        )
    }
}

impl CValue {
    fn byte_width(&self) -> u32 {
        match self {
            Self::Int32(_) => 4,
            Self::Bool(_) => 1,
            Self::Ptr(_) => 8,
        }
    }
}

impl Ptr {
    fn offset_by_int32_elements(&self, elements: Bv32Term) -> Self {
        Self {
            block: self.block.clone(),
            offset: Bv32Term::add(
                self.offset.clone(),
                Bv32Term::mul(elements, Bv32Term::Const(4)),
            ),
        }
    }
}

impl CParam {
    pub fn new(name: impl Into<String>, ty: CType) -> Self {
        Self {
            name: name.into(),
            ty,
        }
    }

    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn ty(&self) -> CType {
        self.ty
    }
}

impl CFunction {
    pub fn new(
        return_type: CType,
        name: impl Into<String>,
        params: Vec<CParam>,
        body: CStmt,
    ) -> Self {
        Self {
            return_type,
            name: name.into(),
            params,
            body,
        }
    }

    pub fn return_type(&self) -> CType {
        self.return_type
    }

    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn params(&self) -> &[CParam] {
        &self.params
    }

    pub fn body(&self) -> &CStmt {
        &self.body
    }
}

impl CFunctionSpec {
    pub fn new(
        state: CState,
        args: Vec<CExpr>,
        requires: Vec<Prop>,
        outcome: CFunctionOutcome,
    ) -> Self {
        Self {
            state,
            args,
            requires,
            outcome,
        }
    }

    pub fn state(&self) -> &CState {
        &self.state
    }

    pub fn args(&self) -> &[CExpr] {
        &self.args
    }

    pub fn requires(&self) -> &[Prop] {
        &self.requires
    }

    pub fn outcome(&self) -> &CFunctionOutcome {
        &self.outcome
    }
}

impl CFunctionEnv {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn with_function(mut self, function: CFunction) -> Self {
        self.functions.insert(function.name().to_string(), function);
        self
    }

    pub fn get_function(&self, name: &str) -> Option<&CFunction> {
        self.functions.get(name)
    }
}

impl CLocalEnv {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn with(mut self, name: impl Into<String>, value: CValue) -> Self {
        self.bindings.insert(name.into(), value);
        self
    }

    pub fn set(&mut self, name: impl Into<String>, value: CValue) {
        self.bindings.insert(name.into(), value);
    }

    pub fn get(&self, name: &str) -> Option<&CValue> {
        self.bindings.get(name)
    }
}

impl CBlock {
    pub fn new(size: u32) -> Self {
        Self { size }
    }

    pub fn size(&self) -> u32 {
        self.size
    }
}

impl CMemory {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn with_block(mut self, block: impl Into<String>, size: u32) -> Self {
        self.blocks.insert(block.into(), CBlock::new(size));
        self
    }

    pub fn store(mut self, ptr: Ptr, value: CValue) -> Self {
        self.cells.insert(ptr, value);
        self
    }

    pub fn load(&self, ptr: &Ptr) -> CExprOutcome {
        match self.cells.get(ptr) {
            Some(value) => CExprOutcome::Value(value.clone()),
            None => CExprOutcome::Ub(CUndefinedBehavior::InvalidMemory),
        }
    }

    fn known_value(&self, ptr: &Ptr) -> Option<CValue> {
        self.cells.get(ptr).cloned()
    }

    fn local_ptr(name: &str) -> Ptr {
        Ptr {
            block: format!("local:{name}"),
            offset: Bv32Term::Const(0),
        }
    }

    fn has_block(&self, block: &str) -> bool {
        self.blocks.contains_key(block)
    }

    fn can_load_concretely(&self, ptr: &Ptr) -> bool {
        self.cells.contains_key(ptr) || self.access_in_bounds(ptr, 4)
    }

    fn can_store_concretely(&self, ptr: &Ptr, value: &CValue) -> bool {
        self.cells.contains_key(ptr) || self.access_in_bounds(ptr, value.byte_width())
    }

    fn access_in_bounds(&self, ptr: &Ptr, byte_width: u32) -> bool {
        let Some(offset) = ptr.offset.as_const() else {
            return false;
        };
        let Some(block) = self.blocks.get(&ptr.block) else {
            return false;
        };
        offset
            .checked_add(byte_width)
            .is_some_and(|end| end <= block.size())
    }

    fn symbolic_int32_load(&self, ptr: &Ptr) -> CValue {
        int32(Bv32Term::MemoryLoad(
            Box::new(self.clone()),
            Box::new(ptr.clone()),
        ))
    }
}

impl CState {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn with_local(mut self, name: impl Into<String>, value: CValue) -> Self {
        self.locals.set(name, value);
        self
    }

    pub fn with_memory(mut self, memory: CMemory) -> Self {
        self.memory = memory;
        self
    }

    pub fn locals(&self) -> &CLocalEnv {
        &self.locals
    }

    pub fn memory(&self) -> &CMemory {
        &self.memory
    }
}

impl Theorem {
    fn new(prop: Prop) -> Self {
        Self { prop }
    }

    pub fn prop(&self) -> &Prop {
        &self.prop
    }
}

impl Assumptions {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn assume_bool(mut self, condition: BoolTerm, value: bool) -> Self {
        self.bool_facts.insert(condition, value);
        self
    }

    pub fn assume_prop(mut self, prop: Prop) -> Self {
        if let Prop::BoolIs(condition, value) = prop {
            self.bool_facts.insert(condition, value);
        } else {
            self.prop_facts.insert(prop);
        }
        self
    }

    fn decide(&self, condition: &BoolTerm) -> Option<bool> {
        match condition {
            BoolTerm::Const(value) => Some(*value),
            _ => self.bool_facts.get(condition).copied(),
        }
    }

    pub fn proves(&self, prop: &Prop) -> bool {
        if solve_builtin_prop(prop) {
            return true;
        }

        match prop {
            Prop::BoolIs(condition, value) => self.decide(condition) == Some(*value),
            _ => self.prop_facts.contains(prop),
        }
    }
}

impl ProofObligation {
    pub fn new(prop: Prop) -> Self {
        Self { prop }
    }

    pub fn bool(condition: BoolTerm, value: bool) -> Self {
        Self::new(Prop::BoolIs(condition, value))
    }

    pub fn memory_can_load(memory: CMemory, ptr: Ptr) -> Self {
        Self::new(Prop::CMemoryCanLoad { memory, ptr })
    }

    pub fn memory_can_store(memory: CMemory, ptr: Ptr) -> Self {
        Self::new(Prop::CMemoryCanStore { memory, ptr })
    }

    pub fn prop(&self) -> &Prop {
        &self.prop
    }
}

impl PathFact {
    pub fn new(prop: Prop) -> Self {
        Self { prop }
    }

    pub fn bool(condition: BoolTerm, value: bool) -> Self {
        Self::new(Prop::BoolIs(condition, value))
    }

    pub fn prop(&self) -> &Prop {
        &self.prop
    }
}

impl SymbolicCExecution {
    pub fn paths(&self) -> &[SymbolicCExecutionPath] {
        &self.paths
    }
}

impl SymbolicCExecutionPath {
    pub fn facts(&self) -> &[PathFact] {
        &self.facts
    }

    pub fn obligations(&self) -> &[ProofObligation] {
        &self.obligations
    }

    pub fn theorem(&self) -> &Theorem {
        &self.theorem
    }
}

pub fn int32(bits: impl Into<Bv32Term>) -> CValue {
    CValue::Int32(bits.into())
}

pub fn c_bool(value: impl Into<BoolTerm>) -> CValue {
    CValue::Bool(value.into())
}

pub fn c_var(name: impl Into<String>) -> CExpr {
    CExpr::Var(name.into())
}

pub fn c_addr_of(name: impl Into<String>) -> CExpr {
    CExpr::AddressOf(name.into())
}

pub fn c_int32_literal(value: u32) -> CExpr {
    CExpr::Value(int32(Bv32Term::Const(value)))
}

pub fn c_ptr_value(ptr: Ptr) -> CExpr {
    CExpr::Value(CValue::Ptr(ptr))
}

pub fn c_lt(left: CExpr, right: CExpr) -> CExpr {
    CExpr::Lt(Box::new(left), Box::new(right))
}

pub fn c_le(left: CExpr, right: CExpr) -> CExpr {
    CExpr::Le(Box::new(left), Box::new(right))
}

pub fn c_gt(left: CExpr, right: CExpr) -> CExpr {
    CExpr::Gt(Box::new(left), Box::new(right))
}

pub fn c_ge(left: CExpr, right: CExpr) -> CExpr {
    CExpr::Ge(Box::new(left), Box::new(right))
}

pub fn c_eq(left: CExpr, right: CExpr) -> CExpr {
    CExpr::Eq(Box::new(left), Box::new(right))
}

pub fn c_add(left: CExpr, right: CExpr) -> CExpr {
    CExpr::Add(Box::new(left), Box::new(right))
}

pub fn c_sub(left: CExpr, right: CExpr) -> CExpr {
    CExpr::Sub(Box::new(left), Box::new(right))
}

pub fn c_load(ptr: CExpr) -> CExpr {
    CExpr::Load(Box::new(ptr))
}

pub fn c_assign(name: impl Into<String>, expr: CExpr) -> CStmt {
    CStmt::Assign {
        name: name.into(),
        expr,
    }
}

pub fn c_call_assign(
    target: impl Into<String>,
    function_name: impl Into<String>,
    args: Vec<CExpr>,
) -> CStmt {
    CStmt::CallAssign {
        target: target.into(),
        function_name: function_name.into(),
        args,
    }
}

pub fn c_declare(name: impl Into<String>, ty: CType) -> CStmt {
    CStmt::Declare {
        name: name.into(),
        ty,
    }
}

pub fn c_seq(first: CStmt, second: CStmt) -> CStmt {
    CStmt::Seq(Box::new(first), Box::new(second))
}

pub fn c_return(expr: CExpr) -> CStmt {
    CStmt::Return(expr)
}

pub fn c_store(ptr: CExpr, value: CExpr) -> CStmt {
    CStmt::Store { ptr, value }
}

pub fn c_if(condition: CExpr, then_branch: CStmt, else_branch: CStmt) -> CStmt {
    CStmt::If {
        condition,
        then_branch: Box::new(then_branch),
        else_branch: Box::new(else_branch),
    }
}

pub fn c_while(condition: CExpr, invariant: Vec<Prop>, body: CStmt) -> CStmt {
    CStmt::While {
        condition,
        invariant,
        body: Box::new(body),
    }
}

pub fn c_param(name: impl Into<String>, ty: CType) -> CParam {
    CParam::new(name, ty)
}

pub fn c_function(
    return_type: CType,
    name: impl Into<String>,
    params: Vec<CParam>,
    body: CStmt,
) -> CFunction {
    CFunction::new(return_type, name, params, body)
}

pub fn c_function_spec(
    state: CState,
    args: Vec<CExpr>,
    requires: Vec<Prop>,
    outcome: CFunctionOutcome,
) -> CFunctionSpec {
    CFunctionSpec::new(state, args, requires, outcome)
}

pub fn c_max_body() -> CStmt {
    c_if(
        c_lt(c_var("a"), c_var("b")),
        c_return(c_var("b")),
        c_return(c_var("a")),
    )
}

pub fn c_max_function() -> CFunction {
    c_function(
        CType::Int32,
        "max",
        vec![c_param("a", CType::Int32), c_param("b", CType::Int32)],
        c_max_body(),
    )
}

pub fn c_max_env(a: CValue, b: CValue) -> CLocalEnv {
    CLocalEnv::new().with("a", a).with("b", b)
}

pub fn c_max_state(a: CValue, b: CValue) -> CState {
    CState::new().with_local("a", a).with_local("b", b)
}

pub fn c_max_lt_condition(a: Bv32Term, b: Bv32Term) -> BoolTerm {
    BoolTerm::slt(a, b)
}

pub fn prove_c_expr_eval(state: CState, expr: CExpr) -> Option<Theorem> {
    let outcome = eval_c_expr(&state, &expr, &Assumptions::new())?;
    Some(Theorem::new(Prop::CExprEvaluates {
        state,
        expr,
        outcome,
    }))
}

pub fn prove_c_stmt_exec(state: CState, stmt: CStmt) -> Option<Theorem> {
    prove_symbolic_c_execution(state, stmt, Assumptions::new())
}

pub fn prove_c_stmt_exec_under_assumptions(
    state: CState,
    stmt: CStmt,
    assumptions: Assumptions,
) -> Option<Theorem> {
    prove_symbolic_c_execution(state, stmt, assumptions)
}

pub fn prove_symbolic_c_execution(
    state: CState,
    stmt: CStmt,
    assumptions: Assumptions,
) -> Option<Theorem> {
    prove_symbolic_c_execution_with_env(state, stmt, assumptions, CFunctionEnv::new())
}

pub fn prove_symbolic_c_execution_with_env(
    state: CState,
    stmt: CStmt,
    assumptions: Assumptions,
    env: CFunctionEnv,
) -> Option<Theorem> {
    let execution = prove_symbolic_c_execution_paths_with_env(state, stmt, assumptions, env);
    let mut paths = execution.paths.into_iter();
    let path = paths.next()?;
    if paths.next().is_some() {
        return None;
    }
    Some(path.theorem)
}

pub fn prove_symbolic_c_execution_paths(
    state: CState,
    stmt: CStmt,
    assumptions: Assumptions,
) -> SymbolicCExecution {
    prove_symbolic_c_execution_paths_with_env(state, stmt, assumptions, CFunctionEnv::new())
}

pub fn prove_symbolic_c_execution_paths_with_env(
    state: CState,
    stmt: CStmt,
    assumptions: Assumptions,
    env: CFunctionEnv,
) -> SymbolicCExecution {
    let paths = exec_c_stmt_paths(&state, &stmt, &assumptions, &env)
        .into_iter()
        .map(|path| {
            let prop = Prop::CStmtExecutes {
                state: state.clone(),
                stmt: stmt.clone(),
                outcome: path.outcome,
            };
            let theorem = Theorem::new(wrap_proof_facts(
                prop,
                &assumptions,
                &path.facts,
                &path.obligations,
            ));
            SymbolicCExecutionPath {
                facts: path.facts,
                obligations: path.obligations,
                theorem,
            }
        })
        .collect();

    SymbolicCExecution { paths }
}

pub fn prove_symbolic_c_function_execution(
    state: CState,
    function: CFunction,
    args: Vec<CExpr>,
    assumptions: Assumptions,
) -> Option<Theorem> {
    prove_symbolic_c_function_execution_with_env(
        state,
        function,
        args,
        assumptions,
        CFunctionEnv::new(),
    )
}

pub fn prove_symbolic_c_function_execution_with_env(
    state: CState,
    function: CFunction,
    args: Vec<CExpr>,
    assumptions: Assumptions,
    env: CFunctionEnv,
) -> Option<Theorem> {
    let execution =
        prove_symbolic_c_function_execution_paths_with_env(state, function, args, assumptions, env);
    let mut paths = execution.paths.into_iter();
    let path = paths.next()?;
    if paths.next().is_some() {
        return None;
    }
    Some(path.theorem)
}

pub fn prove_symbolic_c_function_execution_paths(
    state: CState,
    function: CFunction,
    args: Vec<CExpr>,
    assumptions: Assumptions,
) -> SymbolicCExecution {
    prove_symbolic_c_function_execution_paths_with_env(
        state,
        function,
        args,
        assumptions,
        CFunctionEnv::new(),
    )
}

pub fn prove_symbolic_c_function_execution_paths_with_env(
    state: CState,
    function: CFunction,
    args: Vec<CExpr>,
    assumptions: Assumptions,
    env: CFunctionEnv,
) -> SymbolicCExecution {
    let paths = exec_c_function_paths(&state, &function, &args, &assumptions, &env)
        .into_iter()
        .map(|path| {
            let prop = Prop::CFunctionExecutes {
                state: state.clone(),
                function: function.clone(),
                args: args.clone(),
                outcome: path.outcome,
            };
            let theorem = Theorem::new(wrap_proof_facts(
                prop,
                &assumptions,
                &path.facts,
                &path.obligations,
            ));
            SymbolicCExecutionPath {
                facts: path.facts,
                obligations: path.obligations,
                theorem,
            }
        })
        .collect();

    SymbolicCExecution { paths }
}

pub fn prove_c_function_satisfies_spec(
    function: CFunction,
    spec: CFunctionSpec,
    assumptions: Assumptions,
) -> Option<Theorem> {
    prove_c_function_satisfies_spec_with_env(function, spec, assumptions, CFunctionEnv::new())
}

pub fn prove_c_function_satisfies_spec_with_env(
    function: CFunction,
    spec: CFunctionSpec,
    assumptions: Assumptions,
    env: CFunctionEnv,
) -> Option<Theorem> {
    let spec_assumptions = assumptions_with_props(&assumptions, spec.requires());
    let paths = exec_c_function_paths(
        spec.state(),
        &function,
        spec.args(),
        &spec_assumptions,
        &env,
    );
    let mut paths = paths.into_iter();
    let path = paths.next()?;
    if paths.next().is_some()
        || !path.facts.is_empty()
        || !path.obligations.is_empty()
        || &path.outcome != spec.outcome()
    {
        return None;
    }

    let requires = spec.requires().to_vec();
    let prop = requires.iter().rev().fold(
        Prop::CFunctionSatisfiesSpec { function, spec },
        |body, requirement| Prop::Implies(Box::new(requirement.clone()), Box::new(body)),
    );
    Some(Theorem::new(wrap_proof_facts(prop, &assumptions, &[], &[])))
}

pub fn prove_c_max_lt_returns_right(a: Var, b: Var) -> Option<Theorem> {
    let a_bits = Bv32Term::Var(a);
    let b_bits = Bv32Term::Var(b);
    let a_value = int32(a_bits.clone());
    let b_value = int32(b_bits.clone());
    let condition = c_max_lt_condition(a_bits.clone(), b_bits.clone());
    let state = c_max_state(a_value, b_value.clone());
    let assumptions = Assumptions::new().assume_bool(condition.clone(), true);
    let outcome = exec_c_stmt(&state, &c_max_body(), &assumptions)?;

    if outcome
        != (CStmtOutcome::Return {
            value: b_value,
            state: state.clone(),
        })
    {
        return None;
    }

    Some(Theorem::new(forall_int32(
        a,
        forall_int32(
            b,
            Prop::Implies(
                Box::new(Prop::BoolIs(condition, true)),
                Box::new(Prop::CStmtExecutes {
                    state,
                    stmt: c_max_body(),
                    outcome,
                }),
            ),
        ),
    )))
}

pub fn prove_c_max_not_lt_returns_left(a: Var, b: Var) -> Option<Theorem> {
    let a_bits = Bv32Term::Var(a);
    let b_bits = Bv32Term::Var(b);
    let a_value = int32(a_bits.clone());
    let b_value = int32(b_bits.clone());
    let condition = c_max_lt_condition(a_bits, b_bits);
    let state = c_max_state(a_value.clone(), b_value);
    let assumptions = Assumptions::new().assume_bool(condition.clone(), false);
    let outcome = exec_c_stmt(&state, &c_max_body(), &assumptions)?;

    if outcome
        != (CStmtOutcome::Return {
            value: a_value,
            state: state.clone(),
        })
    {
        return None;
    }

    Some(Theorem::new(forall_int32(
        a,
        forall_int32(
            b,
            Prop::Implies(
                Box::new(Prop::BoolIs(condition, false)),
                Box::new(Prop::CStmtExecutes {
                    state,
                    stmt: c_max_body(),
                    outcome,
                }),
            ),
        ),
    )))
}

pub fn prove_memory_load(memory: CMemory, ptr: Ptr) -> Theorem {
    let outcome = memory.load(&ptr);
    Theorem::new(Prop::CMemoryLoads {
        memory,
        ptr,
        outcome,
    })
}

pub fn prove_memory_load_after_store_same(memory: CMemory, ptr: Ptr, value: CValue) -> Theorem {
    let stored = memory.store(ptr.clone(), value.clone());
    Theorem::new(Prop::CMemoryLoads {
        memory: stored,
        ptr,
        outcome: CExprOutcome::Value(value),
    })
}

fn forall_int32(var: Var, body: Prop) -> Prop {
    Prop::ForAll {
        var,
        sort: Sort::CInt32,
        body: Box::new(body),
    }
}

fn wrap_proof_facts(
    prop: Prop,
    assumptions: &Assumptions,
    facts: &[PathFact],
    obligations: &[ProofObligation],
) -> Prop {
    let prop = obligations.iter().rev().fold(prop, |body, obligation| {
        Prop::Implies(Box::new(obligation.prop().clone()), Box::new(body))
    });

    let prop = facts.iter().rev().fold(prop, |body, fact| {
        Prop::Implies(Box::new(fact.prop().clone()), Box::new(body))
    });

    let prop = assumptions
        .prop_facts
        .iter()
        .rev()
        .fold(prop, |body, prop| {
            Prop::Implies(Box::new(prop.clone()), Box::new(body))
        });

    assumptions
        .bool_facts
        .iter()
        .rev()
        .fold(prop, |body, (condition, value)| {
            Prop::Implies(
                Box::new(Prop::BoolIs(condition.clone(), *value)),
                Box::new(body),
            )
        })
}

fn solve_builtin_prop(prop: &Prop) -> bool {
    match prop {
        Prop::Equal(left, right) => left == right,
        Prop::BoolIs(BoolTerm::Const(actual), expected) => actual == expected,
        Prop::CMemoryCanLoad { memory, ptr } => memory.can_load_concretely(ptr),
        Prop::CMemoryCanStore { memory, ptr } => memory.access_in_bounds(ptr, 4),
        _ => false,
    }
}

fn add_path_fact(facts: &mut Vec<PathFact>, assumptions: &Assumptions, prop: Prop) -> Option<()> {
    if let Prop::BoolIs(condition, value) = prop {
        return add_bool_path_fact(facts, assumptions, condition, value);
    }

    if assumptions.proves(&prop) || facts.iter().any(|fact| fact.prop == prop) {
        return Some(());
    }

    facts.push(PathFact::new(prop));
    Some(())
}

fn add_bool_path_fact(
    facts: &mut Vec<PathFact>,
    assumptions: &Assumptions,
    condition: BoolTerm,
    value: bool,
) -> Option<()> {
    if let Some(known) = assumptions.decide(&condition) {
        return (known == value).then_some(());
    }

    if let Some(existing) = facts
        .iter()
        .filter_map(|fact| match fact.prop() {
            Prop::BoolIs(existing_condition, existing_value)
                if existing_condition == &condition =>
            {
                Some(*existing_value)
            }
            _ => None,
        })
        .next()
    {
        return (existing == value).then_some(());
    }

    facts.push(PathFact::bool(condition, value));
    Some(())
}

fn add_proof_obligation(
    obligations: &mut Vec<ProofObligation>,
    assumptions: &Assumptions,
    prop: Prop,
) -> Option<()> {
    if let Prop::BoolIs(condition, value) = prop {
        return add_bool_obligation(obligations, assumptions, condition, value);
    }

    if assumptions.proves(&prop) || obligations.iter().any(|obligation| obligation.prop == prop) {
        return Some(());
    }

    obligations.push(ProofObligation::new(prop));
    Some(())
}

fn add_bool_obligation(
    obligations: &mut Vec<ProofObligation>,
    assumptions: &Assumptions,
    condition: BoolTerm,
    value: bool,
) -> Option<()> {
    if let Some(known) = assumptions.decide(&condition) {
        return (known == value).then_some(());
    }

    if let Some(existing) = obligations
        .iter()
        .filter_map(|obligation| match obligation.prop() {
            Prop::BoolIs(existing_condition, existing_value)
                if existing_condition == &condition =>
            {
                Some(*existing_value)
            }
            _ => None,
        })
        .next()
    {
        return (existing == value).then_some(());
    }

    obligations.push(ProofObligation::bool(condition, value));
    Some(())
}

fn merge_obligations(
    left: &[ProofObligation],
    right: &[ProofObligation],
    assumptions: &Assumptions,
) -> Option<Vec<ProofObligation>> {
    let mut obligations = left.to_vec();
    for obligation in right {
        add_proof_obligation(&mut obligations, assumptions, obligation.prop().clone())?;
    }
    Some(obligations)
}

fn merge_facts(
    left: &[PathFact],
    right: &[PathFact],
    assumptions: &Assumptions,
) -> Option<Vec<PathFact>> {
    let mut facts = left.to_vec();
    for fact in right {
        add_path_fact(&mut facts, assumptions, fact.prop().clone())?;
    }
    Some(facts)
}

fn merge_path_facts_and_obligations(
    left_facts: &[PathFact],
    left_obligations: &[ProofObligation],
    right_facts: &[PathFact],
    right_obligations: &[ProofObligation],
    assumptions: &Assumptions,
) -> Option<(Vec<PathFact>, Vec<ProofObligation>)> {
    let facts = merge_facts(left_facts, right_facts, assumptions)?;
    let obligations = merge_obligations(left_obligations, right_obligations, assumptions)?;
    Some((facts, obligations))
}

fn decide_with_facts(
    assumptions: &Assumptions,
    facts: &[PathFact],
    condition: &BoolTerm,
) -> Option<bool> {
    assumptions.decide(condition).or_else(|| {
        facts.iter().find_map(|fact| match fact.prop() {
            Prop::BoolIs(existing_condition, value) if existing_condition == condition => {
                Some(*value)
            }
            _ => None,
        })
    })
}

fn assumptions_with_path_context(
    assumptions: &Assumptions,
    facts: &[PathFact],
    obligations: &[ProofObligation],
) -> Assumptions {
    let mut assumptions = assumptions.clone();
    for fact in facts {
        assumptions = assumptions.assume_prop(fact.prop().clone());
    }
    for obligation in obligations {
        assumptions = assumptions.assume_prop(obligation.prop().clone());
    }
    assumptions
}

fn assumptions_with_props(assumptions: &Assumptions, props: &[Prop]) -> Assumptions {
    let mut assumptions = assumptions.clone();
    for prop in props {
        assumptions = assumptions.assume_prop(prop.clone());
    }
    assumptions
}

fn eval_c_expr(state: &CState, expr: &CExpr, assumptions: &Assumptions) -> Option<CExprOutcome> {
    let paths = eval_c_expr_paths(state, expr, assumptions);
    let mut paths = paths.into_iter();
    let path = paths.next()?;
    if paths.next().is_some() || !path.obligations.is_empty() {
        return None;
    }
    Some(path.outcome)
}

fn eval_c_expr_paths(state: &CState, expr: &CExpr, assumptions: &Assumptions) -> Vec<CExprPath> {
    match expr {
        CExpr::Value(value) => vec![CExprPath {
            outcome: CExprOutcome::Value(value.clone()),
            facts: Vec::new(),
            obligations: Vec::new(),
        }],
        CExpr::Var(name) => vec![CExprPath {
            outcome: match state.locals.get(name) {
                Some(value) => CExprOutcome::Value(value.clone()),
                None => CExprOutcome::RuntimeError(CRuntimeError::UnboundVariable(name.clone())),
            },
            facts: Vec::new(),
            obligations: Vec::new(),
        }],
        CExpr::AddressOf(name) => {
            let ptr = CMemory::local_ptr(name);
            vec![CExprPath {
                outcome: if state.memory.has_block(&ptr.block) {
                    CExprOutcome::Value(CValue::Ptr(ptr))
                } else {
                    CExprOutcome::RuntimeError(CRuntimeError::UnboundVariable(name.clone()))
                },
                facts: Vec::new(),
                obligations: Vec::new(),
            }]
        }
        CExpr::Lt(left, right) => eval_c_int32_binary_paths(
            state,
            left,
            right,
            assumptions,
            |left, right, facts, obligations| {
                bool_term_as_c_int32_paths(
                    BoolTerm::slt(left, right),
                    facts,
                    obligations,
                    assumptions,
                )
            },
        ),
        CExpr::Le(left, right) => eval_c_int32_binary_paths(
            state,
            left,
            right,
            assumptions,
            |left, right, facts, obligations| {
                bool_term_as_c_int32_paths(
                    BoolTerm::sle(left, right),
                    facts,
                    obligations,
                    assumptions,
                )
            },
        ),
        CExpr::Gt(left, right) => eval_c_int32_binary_paths(
            state,
            left,
            right,
            assumptions,
            |left, right, facts, obligations| {
                bool_term_as_c_int32_paths(
                    BoolTerm::sgt(left, right),
                    facts,
                    obligations,
                    assumptions,
                )
            },
        ),
        CExpr::Ge(left, right) => eval_c_int32_binary_paths(
            state,
            left,
            right,
            assumptions,
            |left, right, facts, obligations| {
                bool_term_as_c_int32_paths(
                    BoolTerm::sge(left, right),
                    facts,
                    obligations,
                    assumptions,
                )
            },
        ),
        CExpr::Eq(left, right) => eval_c_int32_binary_paths(
            state,
            left,
            right,
            assumptions,
            |left, right, facts, obligations| {
                bool_term_as_c_int32_paths(
                    BoolTerm::eq(left, right),
                    facts,
                    obligations,
                    assumptions,
                )
            },
        ),
        CExpr::Add(left, right) => eval_c_add_paths(state, left, right, assumptions),
        CExpr::Sub(left, right) => eval_c_int32_binary_paths(
            state,
            left,
            right,
            assumptions,
            |left, right, facts, obligations| {
                apply_c_int32_sub(left, right, facts, obligations, assumptions)
            },
        ),
        CExpr::Load(ptr) => eval_c_expr_paths(state, ptr, assumptions)
            .into_iter()
            .flat_map(|path| match path.outcome {
                CExprOutcome::Value(CValue::Ptr(ptr)) => eval_c_memory_load_paths(
                    &state.memory,
                    ptr,
                    path.facts,
                    path.obligations,
                    assumptions,
                ),
                CExprOutcome::Value(_) => vec![CExprPath {
                    outcome: CExprOutcome::RuntimeError(CRuntimeError::TypeMismatch),
                    facts: path.facts,
                    obligations: path.obligations,
                }],
                CExprOutcome::Ub(ub) => vec![CExprPath {
                    outcome: CExprOutcome::Ub(ub),
                    facts: path.facts,
                    obligations: path.obligations,
                }],
                CExprOutcome::RuntimeError(error) => vec![CExprPath {
                    outcome: CExprOutcome::RuntimeError(error),
                    facts: path.facts,
                    obligations: path.obligations,
                }],
            })
            .collect(),
    }
}

fn bool_term_as_c_int32_paths(
    condition: BoolTerm,
    facts: Vec<PathFact>,
    obligations: Vec<ProofObligation>,
    assumptions: &Assumptions,
) -> Vec<CExprPath> {
    match decide_with_facts(assumptions, &facts, &condition) {
        Some(true) => vec![CExprPath {
            outcome: CExprOutcome::Value(int32(1)),
            facts,
            obligations,
        }],
        Some(false) => vec![CExprPath {
            outcome: CExprOutcome::Value(int32(0)),
            facts,
            obligations,
        }],
        None => {
            let mut true_facts = facts.clone();
            add_bool_path_fact(&mut true_facts, assumptions, condition.clone(), true)
                .expect("unknown comparison fact should be consistent");

            let mut false_facts = facts;
            add_bool_path_fact(&mut false_facts, assumptions, condition, false)
                .expect("unknown comparison fact should be consistent");

            vec![
                CExprPath {
                    outcome: CExprOutcome::Value(int32(1)),
                    facts: true_facts,
                    obligations: obligations.clone(),
                },
                CExprPath {
                    outcome: CExprOutcome::Value(int32(0)),
                    facts: false_facts,
                    obligations,
                },
            ]
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct CTruthinessPath {
    is_true: bool,
    facts: Vec<PathFact>,
    obligations: Vec<ProofObligation>,
}

fn c_truthiness_paths(
    value: CValue,
    facts: Vec<PathFact>,
    obligations: Vec<ProofObligation>,
    assumptions: &Assumptions,
) -> Vec<CTruthinessPath> {
    match value {
        CValue::Int32(bits) => {
            let is_zero = BoolTerm::eq(bits, Bv32Term::Const(0));
            match decide_with_facts(assumptions, &facts, &is_zero) {
                Some(true) => vec![CTruthinessPath {
                    is_true: false,
                    facts,
                    obligations,
                }],
                Some(false) => vec![CTruthinessPath {
                    is_true: true,
                    facts,
                    obligations,
                }],
                None => {
                    let mut true_facts = facts.clone();
                    add_bool_path_fact(&mut true_facts, assumptions, is_zero.clone(), false)
                        .expect("unknown truthiness fact should be consistent");

                    let mut false_facts = facts;
                    add_bool_path_fact(&mut false_facts, assumptions, is_zero, true)
                        .expect("unknown truthiness fact should be consistent");

                    vec![
                        CTruthinessPath {
                            is_true: true,
                            facts: true_facts,
                            obligations: obligations.clone(),
                        },
                        CTruthinessPath {
                            is_true: false,
                            facts: false_facts,
                            obligations,
                        },
                    ]
                }
            }
        }
        CValue::Bool(condition) => match decide_with_facts(assumptions, &facts, &condition) {
            Some(value) => vec![CTruthinessPath {
                is_true: value,
                facts,
                obligations,
            }],
            None => {
                let mut true_facts = facts.clone();
                add_bool_path_fact(&mut true_facts, assumptions, condition.clone(), true)
                    .expect("unknown truthiness fact should be consistent");

                let mut false_facts = facts;
                add_bool_path_fact(&mut false_facts, assumptions, condition, false)
                    .expect("unknown truthiness fact should be consistent");

                vec![
                    CTruthinessPath {
                        is_true: true,
                        facts: true_facts,
                        obligations: obligations.clone(),
                    },
                    CTruthinessPath {
                        is_true: false,
                        facts: false_facts,
                        obligations,
                    },
                ]
            }
        },
        CValue::Ptr(ptr) => match (&ptr.block[..], &ptr.offset) {
            ("null", Bv32Term::Const(0)) => vec![CTruthinessPath {
                is_true: false,
                facts,
                obligations,
            }],
            _ => vec![CTruthinessPath {
                is_true: true,
                facts,
                obligations,
            }],
        },
    }
}

fn eval_c_memory_load_paths(
    memory: &CMemory,
    ptr: Ptr,
    facts: Vec<PathFact>,
    mut obligations: Vec<ProofObligation>,
    assumptions: &Assumptions,
) -> Vec<CExprPath> {
    if let Some(value) = memory.known_value(&ptr) {
        return vec![CExprPath {
            outcome: CExprOutcome::Value(value),
            facts,
            obligations,
        }];
    }

    if memory.can_load_concretely(&ptr) {
        return vec![CExprPath {
            outcome: CExprOutcome::Value(memory.symbolic_int32_load(&ptr)),
            facts,
            obligations,
        }];
    }

    let prop = Prop::CMemoryCanLoad {
        memory: memory.clone(),
        ptr: ptr.clone(),
    };
    if add_proof_obligation(&mut obligations, assumptions, prop).is_none() {
        return Vec::new();
    }

    vec![CExprPath {
        outcome: CExprOutcome::Value(memory.symbolic_int32_load(&ptr)),
        facts,
        obligations,
    }]
}

fn eval_c_add_paths(
    state: &CState,
    left: &CExpr,
    right: &CExpr,
    assumptions: &Assumptions,
) -> Vec<CExprPath> {
    let mut paths = Vec::new();
    for left_path in eval_c_expr_paths(state, left, assumptions) {
        let CExprPath {
            outcome: left_outcome,
            facts: left_facts,
            obligations: left_obligations,
        } = left_path;

        let left = match left_outcome {
            CExprOutcome::Value(value) => value,
            CExprOutcome::Ub(ub) => {
                paths.push(CExprPath {
                    outcome: CExprOutcome::Ub(ub),
                    facts: left_facts,
                    obligations: left_obligations,
                });
                continue;
            }
            CExprOutcome::RuntimeError(error) => {
                paths.push(CExprPath {
                    outcome: CExprOutcome::RuntimeError(error),
                    facts: left_facts,
                    obligations: left_obligations,
                });
                continue;
            }
        };

        let right_assumptions =
            assumptions_with_path_context(assumptions, &left_facts, &left_obligations);
        for right_path in eval_c_expr_paths(state, right, &right_assumptions) {
            let Some((facts, obligations)) = merge_path_facts_and_obligations(
                &left_facts,
                &left_obligations,
                &right_path.facts,
                &right_path.obligations,
                assumptions,
            ) else {
                continue;
            };

            let right = match right_path.outcome {
                CExprOutcome::Value(value) => value,
                CExprOutcome::Ub(ub) => {
                    paths.push(CExprPath {
                        outcome: CExprOutcome::Ub(ub),
                        facts,
                        obligations,
                    });
                    continue;
                }
                CExprOutcome::RuntimeError(error) => {
                    paths.push(CExprPath {
                        outcome: CExprOutcome::RuntimeError(error),
                        facts,
                        obligations,
                    });
                    continue;
                }
            };

            paths.extend(apply_c_add(
                left.clone(),
                right,
                facts,
                obligations,
                assumptions,
            ));
        }
    }

    paths
}

fn apply_c_add(
    left: CValue,
    right: CValue,
    facts: Vec<PathFact>,
    obligations: Vec<ProofObligation>,
    assumptions: &Assumptions,
) -> Vec<CExprPath> {
    match (left, right) {
        (CValue::Int32(left), CValue::Int32(right)) => {
            apply_c_int32_add(left, right, facts, obligations, assumptions)
        }
        (CValue::Ptr(ptr), CValue::Int32(offset)) | (CValue::Int32(offset), CValue::Ptr(ptr)) => {
            vec![CExprPath {
                outcome: CExprOutcome::Value(CValue::Ptr(ptr.offset_by_int32_elements(offset))),
                facts,
                obligations,
            }]
        }
        _ => vec![CExprPath {
            outcome: CExprOutcome::RuntimeError(CRuntimeError::TypeMismatch),
            facts,
            obligations,
        }],
    }
}

fn apply_c_int32_add(
    left: Bv32Term,
    right: Bv32Term,
    facts: Vec<PathFact>,
    obligations: Vec<ProofObligation>,
    assumptions: &Assumptions,
) -> Vec<CExprPath> {
    let overflow = BoolTerm::signed_add_overflows(left.clone(), right.clone());
    match decide_with_facts(assumptions, &facts, &overflow) {
        Some(true) => vec![CExprPath {
            outcome: CExprOutcome::Ub(CUndefinedBehavior::SignedOverflow),
            facts,
            obligations,
        }],
        Some(false) => vec![CExprPath {
            outcome: CExprOutcome::Value(int32(Bv32Term::add(left, right))),
            facts,
            obligations,
        }],
        None => {
            let mut normal_facts = facts.clone();
            add_bool_path_fact(&mut normal_facts, assumptions, overflow.clone(), false)
                .expect("unknown overflow fact should be consistent");

            let mut overflow_facts = facts;
            add_bool_path_fact(&mut overflow_facts, assumptions, overflow, true)
                .expect("unknown overflow fact should be consistent");

            vec![
                CExprPath {
                    outcome: CExprOutcome::Value(int32(Bv32Term::add(left, right))),
                    facts: normal_facts,
                    obligations: obligations.clone(),
                },
                CExprPath {
                    outcome: CExprOutcome::Ub(CUndefinedBehavior::SignedOverflow),
                    facts: overflow_facts,
                    obligations,
                },
            ]
        }
    }
}

fn apply_c_int32_sub(
    left: Bv32Term,
    right: Bv32Term,
    facts: Vec<PathFact>,
    obligations: Vec<ProofObligation>,
    assumptions: &Assumptions,
) -> Vec<CExprPath> {
    let overflow = BoolTerm::signed_sub_overflows(left.clone(), right.clone());
    match decide_with_facts(assumptions, &facts, &overflow) {
        Some(true) => vec![CExprPath {
            outcome: CExprOutcome::Ub(CUndefinedBehavior::SignedOverflow),
            facts,
            obligations,
        }],
        Some(false) => vec![CExprPath {
            outcome: CExprOutcome::Value(int32(Bv32Term::sub(left, right))),
            facts,
            obligations,
        }],
        None => {
            let mut normal_facts = facts.clone();
            add_bool_path_fact(&mut normal_facts, assumptions, overflow.clone(), false)
                .expect("unknown overflow fact should be consistent");

            let mut overflow_facts = facts;
            add_bool_path_fact(&mut overflow_facts, assumptions, overflow, true)
                .expect("unknown overflow fact should be consistent");

            vec![
                CExprPath {
                    outcome: CExprOutcome::Value(int32(Bv32Term::sub(left, right))),
                    facts: normal_facts,
                    obligations: obligations.clone(),
                },
                CExprPath {
                    outcome: CExprOutcome::Ub(CUndefinedBehavior::SignedOverflow),
                    facts: overflow_facts,
                    obligations,
                },
            ]
        }
    }
}

fn eval_c_int32_binary_paths(
    state: &CState,
    left: &CExpr,
    right: &CExpr,
    assumptions: &Assumptions,
    apply: impl Fn(Bv32Term, Bv32Term, Vec<PathFact>, Vec<ProofObligation>) -> Vec<CExprPath>,
) -> Vec<CExprPath> {
    let mut paths = Vec::new();
    for left_path in eval_c_expr_paths(state, left, assumptions) {
        let CExprPath {
            outcome: left_outcome,
            facts: left_facts,
            obligations: left_obligations,
        } = left_path;

        let left = match left_outcome {
            CExprOutcome::Value(CValue::Int32(left)) => left,
            CExprOutcome::Value(_) => {
                paths.push(CExprPath {
                    outcome: CExprOutcome::RuntimeError(CRuntimeError::TypeMismatch),
                    facts: left_facts,
                    obligations: left_obligations,
                });
                continue;
            }
            CExprOutcome::Ub(ub) => {
                paths.push(CExprPath {
                    outcome: CExprOutcome::Ub(ub),
                    facts: left_facts,
                    obligations: left_obligations,
                });
                continue;
            }
            CExprOutcome::RuntimeError(error) => {
                paths.push(CExprPath {
                    outcome: CExprOutcome::RuntimeError(error),
                    facts: left_facts,
                    obligations: left_obligations,
                });
                continue;
            }
        };

        let right_assumptions =
            assumptions_with_path_context(assumptions, &left_facts, &left_obligations);
        for right_path in eval_c_expr_paths(state, right, &right_assumptions) {
            let Some((facts, obligations)) = merge_path_facts_and_obligations(
                &left_facts,
                &left_obligations,
                &right_path.facts,
                &right_path.obligations,
                assumptions,
            ) else {
                continue;
            };

            match right_path.outcome {
                CExprOutcome::Value(CValue::Int32(right)) => {
                    paths.extend(apply(left.clone(), right, facts, obligations));
                }
                CExprOutcome::Value(_) => paths.push(CExprPath {
                    outcome: CExprOutcome::RuntimeError(CRuntimeError::TypeMismatch),
                    facts,
                    obligations,
                }),
                CExprOutcome::Ub(ub) => paths.push(CExprPath {
                    outcome: CExprOutcome::Ub(ub),
                    facts,
                    obligations,
                }),
                CExprOutcome::RuntimeError(error) => paths.push(CExprPath {
                    outcome: CExprOutcome::RuntimeError(error),
                    facts,
                    obligations,
                }),
            }
        }
    }

    paths
}

fn exec_c_stmt(state: &CState, stmt: &CStmt, assumptions: &Assumptions) -> Option<CStmtOutcome> {
    let paths = exec_c_stmt_paths(state, stmt, assumptions, &CFunctionEnv::new());
    let mut paths = paths.into_iter();
    let path = paths.next()?;
    if paths.next().is_some() {
        return None;
    }
    Some(path.outcome)
}

fn exec_c_stmt_paths(
    state: &CState,
    stmt: &CStmt,
    assumptions: &Assumptions,
    env: &CFunctionEnv,
) -> Vec<CStmtPath> {
    match stmt {
        CStmt::Declare { name, ty } => vec![CStmtPath {
            outcome: CStmtOutcome::Normal(declare_local(state, name, *ty)),
            facts: Vec::new(),
            obligations: Vec::new(),
        }],
        CStmt::Assign { name, expr } => eval_c_expr_paths(state, expr, assumptions)
            .into_iter()
            .map(|path| CStmtPath {
                outcome: match path.outcome {
                    CExprOutcome::Value(value) => {
                        let mut state = state.clone();
                        sync_stack_local(&mut state, name, &value);
                        state.locals.set(name.clone(), value);
                        CStmtOutcome::Normal(state)
                    }
                    CExprOutcome::Ub(ub) => CStmtOutcome::Ub(ub),
                    CExprOutcome::RuntimeError(error) => CStmtOutcome::RuntimeError(error),
                },
                facts: path.facts,
                obligations: path.obligations,
            })
            .collect(),
        CStmt::CallAssign {
            target,
            function_name,
            args,
        } => exec_c_call_assign_paths(state, target, function_name, args, assumptions, env),
        CStmt::Seq(first, second) => {
            let mut paths = Vec::new();
            for first_path in exec_c_stmt_paths(state, first, assumptions, env) {
                match first_path.outcome {
                    CStmtOutcome::Normal(state) => {
                        paths.extend(exec_c_stmt_paths_with_prefix(
                            &state,
                            second,
                            assumptions,
                            env,
                            &first_path.facts,
                            &first_path.obligations,
                        ));
                    }
                    outcome @ (CStmtOutcome::Return { .. }
                    | CStmtOutcome::Ub(_)
                    | CStmtOutcome::RuntimeError(_)) => paths.push(CStmtPath {
                        outcome,
                        facts: first_path.facts,
                        obligations: first_path.obligations,
                    }),
                }
            }
            paths
        }
        CStmt::Return(expr) => eval_c_expr_paths(state, expr, assumptions)
            .into_iter()
            .map(|path| CStmtPath {
                outcome: match path.outcome {
                    CExprOutcome::Value(value) => CStmtOutcome::Return {
                        value,
                        state: state.clone(),
                    },
                    CExprOutcome::Ub(ub) => CStmtOutcome::Ub(ub),
                    CExprOutcome::RuntimeError(error) => CStmtOutcome::RuntimeError(error),
                },
                facts: path.facts,
                obligations: path.obligations,
            })
            .collect(),
        CStmt::Store { ptr, value } => {
            let mut paths = Vec::new();
            for ptr_path in eval_c_expr_paths(state, ptr, assumptions) {
                let CExprPath {
                    outcome: ptr_outcome,
                    facts: ptr_facts,
                    obligations: ptr_obligations,
                } = ptr_path;

                let ptr = match ptr_outcome {
                    CExprOutcome::Value(CValue::Ptr(ptr)) => ptr,
                    CExprOutcome::Value(_) => {
                        paths.push(CStmtPath {
                            outcome: CStmtOutcome::RuntimeError(CRuntimeError::TypeMismatch),
                            facts: ptr_facts,
                            obligations: ptr_obligations,
                        });
                        continue;
                    }
                    CExprOutcome::Ub(ub) => {
                        paths.push(CStmtPath {
                            outcome: CStmtOutcome::Ub(ub),
                            facts: ptr_facts,
                            obligations: ptr_obligations,
                        });
                        continue;
                    }
                    CExprOutcome::RuntimeError(error) => {
                        paths.push(CStmtPath {
                            outcome: CStmtOutcome::RuntimeError(error),
                            facts: ptr_facts,
                            obligations: ptr_obligations,
                        });
                        continue;
                    }
                };

                let value_assumptions =
                    assumptions_with_path_context(assumptions, &ptr_facts, &ptr_obligations);
                for value_path in eval_c_expr_paths(state, value, &value_assumptions) {
                    let Some((facts, obligations)) = merge_path_facts_and_obligations(
                        &ptr_facts,
                        &ptr_obligations,
                        &value_path.facts,
                        &value_path.obligations,
                        assumptions,
                    ) else {
                        continue;
                    };

                    match value_path.outcome {
                        CExprOutcome::Value(value) => {
                            let Some(obligations) = add_memory_store_obligation(
                                &state.memory,
                                &ptr,
                                &value,
                                obligations,
                                assumptions,
                            ) else {
                                continue;
                            };
                            let mut state = state.clone();
                            state.memory = state.memory.store(ptr.clone(), value);
                            paths.push(CStmtPath {
                                outcome: CStmtOutcome::Normal(state),
                                facts,
                                obligations,
                            });
                        }
                        CExprOutcome::Ub(ub) => paths.push(CStmtPath {
                            outcome: CStmtOutcome::Ub(ub),
                            facts,
                            obligations,
                        }),
                        CExprOutcome::RuntimeError(error) => paths.push(CStmtPath {
                            outcome: CStmtOutcome::RuntimeError(error),
                            facts,
                            obligations,
                        }),
                    }
                }
            }
            paths
        }
        CStmt::If {
            condition,
            then_branch,
            else_branch,
        } => {
            let mut paths = Vec::new();
            for condition_path in eval_c_expr_paths(state, condition, assumptions) {
                let CExprPath {
                    outcome,
                    facts,
                    obligations,
                } = condition_path;
                match outcome {
                    CExprOutcome::Value(value) => {
                        let truthiness_paths =
                            c_truthiness_paths(value, facts, obligations, assumptions);
                        for truthiness_path in truthiness_paths {
                            let branch = if truthiness_path.is_true {
                                then_branch
                            } else {
                                else_branch
                            };
                            paths.extend(exec_c_stmt_paths_with_prefix(
                                state,
                                branch,
                                assumptions,
                                env,
                                &truthiness_path.facts,
                                &truthiness_path.obligations,
                            ));
                        }
                    }
                    CExprOutcome::Ub(ub) => paths.push(CStmtPath {
                        outcome: CStmtOutcome::Ub(ub),
                        facts,
                        obligations,
                    }),
                    CExprOutcome::RuntimeError(error) => paths.push(CStmtPath {
                        outcome: CStmtOutcome::RuntimeError(error),
                        facts,
                        obligations,
                    }),
                }
            }
            paths
        }
        CStmt::While {
            condition,
            invariant,
            body,
        } => exec_c_while_paths(state, condition, invariant, body, assumptions, env, 256),
    }
}

fn exec_c_while_paths(
    state: &CState,
    condition: &CExpr,
    invariant: &[Prop],
    body: &CStmt,
    assumptions: &Assumptions,
    env: &CFunctionEnv,
    fuel: usize,
) -> Vec<CStmtPath> {
    if fuel == 0 {
        return vec![CStmtPath {
            outcome: CStmtOutcome::RuntimeError(CRuntimeError::LoopLimitExceeded),
            facts: Vec::new(),
            obligations: Vec::new(),
        }];
    }

    let mut base_obligations = Vec::new();
    for prop in invariant {
        if add_proof_obligation(&mut base_obligations, assumptions, prop.clone()).is_none() {
            return Vec::new();
        }
    }
    let loop_assumptions = assumptions_with_props(assumptions, invariant);
    let mut paths = Vec::new();

    for condition_path in eval_c_expr_paths(state, condition, &loop_assumptions) {
        let Some((condition_facts, condition_obligations)) = merge_path_facts_and_obligations(
            &[],
            &base_obligations,
            &condition_path.facts,
            &condition_path.obligations,
            assumptions,
        ) else {
            continue;
        };

        match condition_path.outcome {
            CExprOutcome::Value(value) => {
                let truthiness_paths =
                    c_truthiness_paths(value, condition_facts, condition_obligations, assumptions);
                for truthiness_path in truthiness_paths {
                    if truthiness_path.is_true {
                        paths.extend(exec_c_while_body_paths(
                            state,
                            condition,
                            invariant,
                            body,
                            assumptions,
                            env,
                            fuel,
                            truthiness_path.facts,
                            truthiness_path.obligations,
                        ));
                    } else {
                        paths.push(CStmtPath {
                            outcome: CStmtOutcome::Normal(state.clone()),
                            facts: truthiness_path.facts,
                            obligations: truthiness_path.obligations,
                        });
                    }
                }
            }
            CExprOutcome::Ub(ub) => paths.push(CStmtPath {
                outcome: CStmtOutcome::Ub(ub),
                facts: condition_facts,
                obligations: condition_obligations,
            }),
            CExprOutcome::RuntimeError(error) => paths.push(CStmtPath {
                outcome: CStmtOutcome::RuntimeError(error),
                facts: condition_facts,
                obligations: condition_obligations,
            }),
        }
    }

    paths
}

fn exec_c_while_body_paths(
    state: &CState,
    condition: &CExpr,
    invariant: &[Prop],
    body: &CStmt,
    assumptions: &Assumptions,
    env: &CFunctionEnv,
    fuel: usize,
    facts: Vec<PathFact>,
    obligations: Vec<ProofObligation>,
) -> Vec<CStmtPath> {
    let body_assumptions = assumptions_with_path_context(assumptions, &facts, &obligations);
    exec_c_stmt_paths(state, body, &body_assumptions, env)
        .into_iter()
        .flat_map(|body_path| {
            let Some((facts, obligations)) = merge_path_facts_and_obligations(
                &facts,
                &obligations,
                &body_path.facts,
                &body_path.obligations,
                assumptions,
            ) else {
                return Vec::new();
            };

            match body_path.outcome {
                CStmtOutcome::Normal(next_state) => {
                    let next_assumptions =
                        assumptions_with_path_context(assumptions, &facts, &obligations);
                    exec_c_while_paths(
                        &next_state,
                        condition,
                        invariant,
                        body,
                        &next_assumptions,
                        env,
                        fuel - 1,
                    )
                    .into_iter()
                    .filter_map(|path| {
                        let (facts, obligations) = merge_path_facts_and_obligations(
                            &facts,
                            &obligations,
                            &path.facts,
                            &path.obligations,
                            assumptions,
                        )?;
                        Some(CStmtPath {
                            outcome: path.outcome,
                            facts,
                            obligations,
                        })
                    })
                    .collect()
                }
                outcome @ (CStmtOutcome::Return { .. }
                | CStmtOutcome::Ub(_)
                | CStmtOutcome::RuntimeError(_)) => vec![CStmtPath {
                    outcome,
                    facts,
                    obligations,
                }],
            }
        })
        .collect()
}

fn declare_local(state: &CState, name: &str, ty: CType) -> CState {
    let mut state = state.clone();
    let (initial_value, byte_width) = match ty {
        CType::Int32 => (int32(0), 4),
        CType::Int32Ptr => (
            CValue::Ptr(Ptr {
                block: "null".to_string(),
                offset: Bv32Term::Const(0),
            }),
            8,
        ),
    };
    let ptr = CMemory::local_ptr(name);
    state.memory = state
        .memory
        .with_block(ptr.block.clone(), byte_width)
        .store(ptr, initial_value.clone());
    state.locals.set(name.to_string(), initial_value);
    state
}

fn sync_stack_local(state: &mut CState, name: &str, value: &CValue) {
    let ptr = CMemory::local_ptr(name);
    if state.memory.has_block(&ptr.block) {
        state.memory = state.memory.clone().store(ptr, value.clone());
    }
}

fn exec_c_call_assign_paths(
    state: &CState,
    target: &str,
    function_name: &str,
    args: &[CExpr],
    assumptions: &Assumptions,
    env: &CFunctionEnv,
) -> Vec<CStmtPath> {
    let Some(function) = env.get_function(function_name) else {
        return vec![CStmtPath {
            outcome: CStmtOutcome::RuntimeError(CRuntimeError::UnknownFunction(
                function_name.to_string(),
            )),
            facts: Vec::new(),
            obligations: Vec::new(),
        }];
    };

    exec_c_function_paths(state, function, args, assumptions, env)
        .into_iter()
        .map(|path| {
            let outcome = match path.outcome {
                CFunctionOutcome::Return { value, mut state } => {
                    sync_stack_local(&mut state, target, &value);
                    state.locals.set(target.to_string(), value);
                    CStmtOutcome::Normal(state)
                }
                CFunctionOutcome::Ub(ub) => CStmtOutcome::Ub(ub),
                CFunctionOutcome::RuntimeError(error) => CStmtOutcome::RuntimeError(error),
            };

            CStmtPath {
                outcome,
                facts: path.facts,
                obligations: path.obligations,
            }
        })
        .collect()
}

fn exec_c_stmt_paths_with_prefix(
    state: &CState,
    stmt: &CStmt,
    assumptions: &Assumptions,
    env: &CFunctionEnv,
    prefix_facts: &[PathFact],
    prefix_obligations: &[ProofObligation],
) -> Vec<CStmtPath> {
    let effective_assumptions =
        assumptions_with_path_context(assumptions, prefix_facts, prefix_obligations);
    exec_c_stmt_paths(state, stmt, &effective_assumptions, env)
        .into_iter()
        .filter_map(|path| {
            let (facts, obligations) = merge_path_facts_and_obligations(
                prefix_facts,
                prefix_obligations,
                &path.facts,
                &path.obligations,
                assumptions,
            )?;
            Some(CStmtPath {
                outcome: path.outcome,
                facts,
                obligations,
            })
        })
        .collect()
}

fn exec_c_function_paths(
    caller_state: &CState,
    function: &CFunction,
    args: &[CExpr],
    assumptions: &Assumptions,
    env: &CFunctionEnv,
) -> Vec<CFunctionPath> {
    if args.len() != function.params.len() {
        return vec![CFunctionPath {
            outcome: CFunctionOutcome::RuntimeError(CRuntimeError::WrongArity {
                expected: function.params.len(),
                actual: args.len(),
            }),
            facts: Vec::new(),
            obligations: Vec::new(),
        }];
    }

    let mut paths = Vec::new();
    for args_path in eval_c_args_paths(caller_state, args, assumptions) {
        if let Some(outcome) = args_path.outcome {
            paths.push(CFunctionPath {
                outcome,
                facts: args_path.facts,
                obligations: args_path.obligations,
            });
            continue;
        }

        let Some(callee_state) = bind_c_function_args(caller_state, function, &args_path.values)
        else {
            paths.push(CFunctionPath {
                outcome: CFunctionOutcome::RuntimeError(CRuntimeError::TypeMismatch),
                facts: args_path.facts,
                obligations: args_path.obligations,
            });
            continue;
        };

        let body_assumptions =
            assumptions_with_path_context(assumptions, &args_path.facts, &args_path.obligations);
        for body_path in exec_c_stmt_paths(&callee_state, function.body(), &body_assumptions, env) {
            let Some((facts, obligations)) = merge_path_facts_and_obligations(
                &args_path.facts,
                &args_path.obligations,
                &body_path.facts,
                &body_path.obligations,
                assumptions,
            ) else {
                continue;
            };

            paths.push(CFunctionPath {
                outcome: function_outcome_from_body(caller_state, function, body_path.outcome),
                facts,
                obligations,
            });
        }
    }

    paths
}

fn add_memory_store_obligation(
    memory: &CMemory,
    ptr: &Ptr,
    value: &CValue,
    mut obligations: Vec<ProofObligation>,
    assumptions: &Assumptions,
) -> Option<Vec<ProofObligation>> {
    if memory.can_store_concretely(ptr, value) {
        return Some(obligations);
    }

    add_proof_obligation(
        &mut obligations,
        assumptions,
        Prop::CMemoryCanStore {
            memory: memory.clone(),
            ptr: ptr.clone(),
        },
    )?;
    Some(obligations)
}

fn eval_c_args_paths(state: &CState, args: &[CExpr], assumptions: &Assumptions) -> Vec<CArgsPath> {
    let mut paths = vec![CArgsPath {
        values: Vec::new(),
        outcome: None,
        facts: Vec::new(),
        obligations: Vec::new(),
    }];

    for arg in args {
        let mut next_paths = Vec::new();
        for path in paths {
            if path.outcome.is_some() {
                next_paths.push(path);
                continue;
            }

            let arg_assumptions =
                assumptions_with_path_context(assumptions, &path.facts, &path.obligations);
            for arg_path in eval_c_expr_paths(state, arg, &arg_assumptions) {
                let Some((facts, obligations)) = merge_path_facts_and_obligations(
                    &path.facts,
                    &path.obligations,
                    &arg_path.facts,
                    &arg_path.obligations,
                    assumptions,
                ) else {
                    continue;
                };

                match arg_path.outcome {
                    CExprOutcome::Value(value) => {
                        let mut values = path.values.clone();
                        values.push(value);
                        next_paths.push(CArgsPath {
                            values,
                            outcome: None,
                            facts,
                            obligations,
                        });
                    }
                    CExprOutcome::Ub(ub) => next_paths.push(CArgsPath {
                        values: path.values.clone(),
                        outcome: Some(CFunctionOutcome::Ub(ub)),
                        facts,
                        obligations,
                    }),
                    CExprOutcome::RuntimeError(error) => next_paths.push(CArgsPath {
                        values: path.values.clone(),
                        outcome: Some(CFunctionOutcome::RuntimeError(error)),
                        facts,
                        obligations,
                    }),
                }
            }
        }
        paths = next_paths;
    }

    paths
}

fn bind_c_function_args(
    caller_state: &CState,
    function: &CFunction,
    values: &[CValue],
) -> Option<CState> {
    let mut callee_state = CState::new().with_memory(caller_state.memory.clone());
    for (param, value) in function.params().iter().zip(values) {
        if !param.ty().accepts(value) {
            return None;
        }
        callee_state
            .locals
            .set(param.name().to_string(), value.clone());
    }
    Some(callee_state)
}

fn function_outcome_from_body(
    caller_state: &CState,
    function: &CFunction,
    outcome: CStmtOutcome,
) -> CFunctionOutcome {
    match outcome {
        CStmtOutcome::Return { value, state } => {
            if !function.return_type().accepts(&value) {
                return CFunctionOutcome::RuntimeError(CRuntimeError::TypeMismatch);
            }

            let mut caller_state = caller_state.clone();
            caller_state.memory = state.memory;
            CFunctionOutcome::Return {
                value,
                state: caller_state,
            }
        }
        CStmtOutcome::Normal(_) => CFunctionOutcome::RuntimeError(CRuntimeError::MissingReturn),
        CStmtOutcome::Ub(ub) => CFunctionOutcome::Ub(ub),
        CStmtOutcome::RuntimeError(error) => CFunctionOutcome::RuntimeError(error),
    }
}

impl From<u32> for Bv32Term {
    fn from(value: u32) -> Self {
        Self::Const(value)
    }
}

impl From<bool> for BoolTerm {
    fn from(value: bool) -> Self {
        Self::Const(value)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn concrete_max_executes_without_list_encoding() {
        let state = c_max_state(int32(0), int32(1));
        let theorem = prove_c_stmt_exec(state.clone(), c_max_body()).expect("max should execute");

        assert_eq!(
            theorem.prop(),
            &Prop::CStmtExecutes {
                state: state.clone(),
                stmt: c_max_body(),
                outcome: CStmtOutcome::Return {
                    value: int32(1),
                    state,
                },
            }
        );
    }

    #[test]
    fn concrete_max_function_call_preserves_caller_locals() {
        let state = CState::new().with_local("caller", int32(99));
        let function = c_max_function();
        let args = vec![c_int32_literal(0), c_int32_literal(1)];
        let theorem = prove_symbolic_c_function_execution(
            state.clone(),
            function.clone(),
            args.clone(),
            Assumptions::new(),
        )
        .expect("max function call should execute");

        assert_eq!(
            theorem.prop(),
            &Prop::CFunctionExecutes {
                state: state.clone(),
                function,
                args,
                outcome: CFunctionOutcome::Return {
                    value: int32(1),
                    state,
                },
            }
        );
    }

    #[test]
    fn symbolic_max_function_call_reports_branch_facts() {
        let a = Var(14);
        let b = Var(15);
        let a_bits = Bv32Term::Var(a);
        let b_bits = Bv32Term::Var(b);
        let condition = c_max_lt_condition(a_bits.clone(), b_bits.clone());
        let state = CState::new();
        let function = c_max_function();
        let args = vec![
            CExpr::Value(int32(a_bits.clone())),
            CExpr::Value(int32(b_bits.clone())),
        ];
        let execution = prove_symbolic_c_function_execution_paths(
            state.clone(),
            function.clone(),
            args.clone(),
            Assumptions::new(),
        );

        assert_eq!(execution.paths().len(), 2);
        assert_eq!(
            execution.paths()[0].facts(),
            &[PathFact::bool(condition.clone(), true)]
        );
        assert_eq!(
            execution.paths()[0].obligations(),
            &[] as &[ProofObligation]
        );
        assert_eq!(
            execution.paths()[0].theorem().prop(),
            &Prop::Implies(
                Box::new(Prop::BoolIs(condition.clone(), true)),
                Box::new(Prop::CFunctionExecutes {
                    state: state.clone(),
                    function: function.clone(),
                    args: args.clone(),
                    outcome: CFunctionOutcome::Return {
                        value: int32(b_bits),
                        state: state.clone(),
                    },
                }),
            )
        );

        assert_eq!(
            execution.paths()[1].facts(),
            &[PathFact::bool(condition.clone(), false)]
        );
        assert_eq!(
            execution.paths()[1].obligations(),
            &[] as &[ProofObligation]
        );
        assert_eq!(
            execution.paths()[1].theorem().prop(),
            &Prop::Implies(
                Box::new(Prop::BoolIs(condition, false)),
                Box::new(Prop::CFunctionExecutes {
                    state: state.clone(),
                    function,
                    args,
                    outcome: CFunctionOutcome::Return {
                        value: int32(a_bits),
                        state,
                    },
                }),
            )
        );
    }

    #[test]
    fn function_call_threads_memory_but_discards_callee_locals() {
        let ptr = Ptr {
            block: "block".to_string(),
            offset: Bv32Term::Const(0),
        };
        let state = CState::new().with_local("caller", int32(42));
        let function = c_function(
            CType::Int32,
            "store_and_load",
            vec![c_param("p", CType::Int32Ptr)],
            c_seq(
                c_store(c_var("p"), c_int32_literal(9)),
                c_return(c_load(c_var("p"))),
            ),
        );
        let args = vec![c_ptr_value(ptr.clone())];
        let final_state = CState::new()
            .with_local("caller", int32(42))
            .with_memory(CMemory::new().store(ptr.clone(), int32(9)));
        let store_obligation = Prop::CMemoryCanStore {
            memory: CMemory::new(),
            ptr,
        };
        let theorem = prove_symbolic_c_function_execution(
            state.clone(),
            function.clone(),
            args.clone(),
            Assumptions::new(),
        )
        .expect("store/load function call should execute");

        assert_eq!(
            theorem.prop(),
            &Prop::Implies(
                Box::new(store_obligation),
                Box::new(Prop::CFunctionExecutes {
                    state,
                    function,
                    args,
                    outcome: CFunctionOutcome::Return {
                        value: int32(9),
                        state: final_state,
                    },
                }),
            )
        );
    }

    #[test]
    fn concrete_function_spec_is_native_theorem() {
        let function = c_max_function();
        let spec = c_function_spec(
            CState::new(),
            vec![c_int32_literal(0), c_int32_literal(1)],
            Vec::new(),
            CFunctionOutcome::Return {
                value: int32(1),
                state: CState::new(),
            },
        );
        let theorem =
            prove_c_function_satisfies_spec(function.clone(), spec.clone(), Assumptions::new())
                .expect("concrete max spec should prove");

        assert_eq!(
            theorem.prop(),
            &Prop::CFunctionSatisfiesSpec { function, spec }
        );
    }

    #[test]
    fn symbolic_function_spec_uses_requirements_as_path_facts() {
        let a = Var(16);
        let b = Var(17);
        let a_bits = Bv32Term::Var(a);
        let b_bits = Bv32Term::Var(b);
        let condition = c_max_lt_condition(a_bits.clone(), b_bits.clone());
        let function = c_max_function();
        let spec = c_function_spec(
            CState::new(),
            vec![CExpr::Value(int32(a_bits)), CExpr::Value(int32(b_bits))],
            vec![Prop::BoolIs(condition.clone(), true)],
            CFunctionOutcome::Return {
                value: int32(Bv32Term::Var(b)),
                state: CState::new(),
            },
        );
        let theorem =
            prove_c_function_satisfies_spec(function.clone(), spec.clone(), Assumptions::new())
                .expect("symbolic branch spec should prove under condition");

        assert_eq!(
            theorem.prop(),
            &Prop::Implies(
                Box::new(Prop::BoolIs(condition, true)),
                Box::new(Prop::CFunctionSatisfiesSpec { function, spec }),
            )
        );
    }

    #[test]
    fn incomplete_symbolic_function_spec_does_not_prove() {
        let a = Var(18);
        let b = Var(19);
        let function = c_max_function();
        let spec = c_function_spec(
            CState::new(),
            vec![
                CExpr::Value(int32(Bv32Term::Var(a))),
                CExpr::Value(int32(Bv32Term::Var(b))),
            ],
            Vec::new(),
            CFunctionOutcome::Return {
                value: int32(Bv32Term::Var(b)),
                state: CState::new(),
            },
        );

        assert!(prove_c_function_satisfies_spec(function, spec, Assumptions::new()).is_none());
    }

    #[test]
    fn call_assign_uses_function_environment() {
        let increment = c_function(
            CType::Int32,
            "increment",
            vec![c_param("x", CType::Int32)],
            c_return(c_add(c_var("x"), c_int32_literal(1))),
        );
        let env = CFunctionEnv::new().with_function(increment);
        let state = CState::new();
        let stmt = c_seq(
            c_call_assign("result", "increment", vec![c_int32_literal(41)]),
            c_return(c_var("result")),
        );
        let final_state = CState::new().with_local("result", int32(42));
        let theorem = prove_symbolic_c_execution_with_env(
            state.clone(),
            stmt.clone(),
            Assumptions::new(),
            env,
        )
        .expect("known function call should execute");

        assert_eq!(
            theorem.prop(),
            &Prop::CStmtExecutes {
                state,
                stmt,
                outcome: CStmtOutcome::Return {
                    value: int32(42),
                    state: final_state,
                },
            }
        );
    }

    #[test]
    fn unknown_call_assign_is_runtime_error() {
        let state = CState::new();
        let stmt = c_call_assign("result", "missing", Vec::new());
        let theorem = prove_symbolic_c_execution_with_env(
            state.clone(),
            stmt.clone(),
            Assumptions::new(),
            CFunctionEnv::new(),
        )
        .expect("unknown function should produce a single runtime-error path");

        assert_eq!(
            theorem.prop(),
            &Prop::CStmtExecutes {
                state,
                stmt,
                outcome: CStmtOutcome::RuntimeError(CRuntimeError::UnknownFunction(
                    "missing".to_string(),
                )),
            }
        );
    }

    #[test]
    fn while_loop_executes_concrete_countdown() {
        let state = CState::new().with_local("x", int32(3));
        let loop_stmt = c_while(
            c_gt(c_var("x"), c_int32_literal(0)),
            Vec::new(),
            c_assign("x", c_sub(c_var("x"), c_int32_literal(1))),
        );
        let stmt = c_seq(loop_stmt, c_return(c_var("x")));
        let final_state = CState::new().with_local("x", int32(0));
        let theorem = prove_symbolic_c_execution(state.clone(), stmt.clone(), Assumptions::new())
            .expect("concrete countdown loop should execute");

        assert_eq!(
            theorem.prop(),
            &Prop::CStmtExecutes {
                state,
                stmt,
                outcome: CStmtOutcome::Return {
                    value: int32(0),
                    state: final_state,
                },
            }
        );
    }

    #[test]
    fn while_invariant_is_proof_obligation() {
        let ptr = Ptr {
            block: "block".to_string(),
            offset: Bv32Term::Const(0),
        };
        let invariant = Prop::CMemoryCanLoad {
            memory: CMemory::new(),
            ptr,
        };
        let state = CState::new().with_local("x", int32(0));
        let stmt = c_while(
            c_gt(c_var("x"), c_int32_literal(0)),
            vec![invariant.clone()],
            c_assign("x", c_sub(c_var("x"), c_int32_literal(1))),
        );
        let theorem = prove_symbolic_c_execution(state.clone(), stmt.clone(), Assumptions::new())
            .expect("false loop should execute under invariant obligation");

        assert_eq!(
            theorem.prop(),
            &Prop::Implies(
                Box::new(invariant),
                Box::new(Prop::CStmtExecutes {
                    state: state.clone(),
                    stmt,
                    outcome: CStmtOutcome::Normal(state),
                }),
            )
        );
    }

    #[test]
    fn builtin_obligation_solver_proves_trivial_props() {
        let assumptions = Assumptions::new();
        let memory = CMemory::new().with_block("block", 8);
        let ptr = Ptr {
            block: "block".to_string(),
            offset: Bv32Term::Const(4),
        };

        assert!(assumptions.proves(&Prop::Equal(
            Term::Bv32(Bv32Term::Const(7)),
            Term::Bv32(Bv32Term::Const(7)),
        )));
        assert!(assumptions.proves(&Prop::BoolIs(BoolTerm::Const(true), true)));
        assert!(assumptions.proves(&Prop::CMemoryCanLoad {
            memory: memory.clone(),
            ptr: ptr.clone(),
        }));
        assert!(assumptions.proves(&Prop::CMemoryCanStore { memory, ptr }));
    }

    #[test]
    fn builtin_obligation_solver_discharges_concrete_invariant() {
        let ptr = Ptr {
            block: "block".to_string(),
            offset: Bv32Term::Const(0),
        };
        let memory = CMemory::new().with_block("block", 4);
        let invariant = Prop::CMemoryCanLoad {
            memory: memory.clone(),
            ptr,
        };
        let state = CState::new().with_local("x", int32(0)).with_memory(memory);
        let stmt = c_while(
            c_gt(c_var("x"), c_int32_literal(0)),
            vec![invariant],
            c_assign("x", c_sub(c_var("x"), c_int32_literal(1))),
        );
        let theorem = prove_symbolic_c_execution(state.clone(), stmt.clone(), Assumptions::new())
            .expect("concrete invariant should be solved");

        assert_eq!(
            theorem.prop(),
            &Prop::CStmtExecutes {
                state: state.clone(),
                stmt,
                outcome: CStmtOutcome::Normal(state),
            }
        );
    }

    #[test]
    fn symbolic_max_lt_branch_is_native_theorem() {
        let a = Var(10);
        let b = Var(11);
        let theorem = prove_c_max_lt_returns_right(a, b).expect("lt branch should prove");
        let condition = BoolTerm::Bv32Slt(Box::new(Bv32Term::Var(a)), Box::new(Bv32Term::Var(b)));
        let state = c_max_state(int32(Bv32Term::Var(a)), int32(Bv32Term::Var(b)));

        assert_eq!(
            theorem.prop(),
            &forall_int32(
                a,
                forall_int32(
                    b,
                    Prop::Implies(
                        Box::new(Prop::BoolIs(condition, true)),
                        Box::new(Prop::CStmtExecutes {
                            state: state.clone(),
                            stmt: c_max_body(),
                            outcome: CStmtOutcome::Return {
                                value: int32(Bv32Term::Var(b)),
                                state,
                            },
                        }),
                    ),
                ),
            )
        );
    }

    #[test]
    fn symbolic_max_not_lt_branch_is_native_theorem() {
        let a = Var(12);
        let b = Var(13);
        let theorem = prove_c_max_not_lt_returns_left(a, b).expect("false branch should prove");
        let condition = BoolTerm::Bv32Slt(Box::new(Bv32Term::Var(a)), Box::new(Bv32Term::Var(b)));
        let state = c_max_state(int32(Bv32Term::Var(a)), int32(Bv32Term::Var(b)));

        assert_eq!(
            theorem.prop(),
            &forall_int32(
                a,
                forall_int32(
                    b,
                    Prop::Implies(
                        Box::new(Prop::BoolIs(condition, false)),
                        Box::new(Prop::CStmtExecutes {
                            state: state.clone(),
                            stmt: c_max_body(),
                            outcome: CStmtOutcome::Return {
                                value: int32(Bv32Term::Var(a)),
                                state,
                            },
                        }),
                    ),
                ),
            )
        );
    }

    #[test]
    fn signed_add_overflow_is_native_ub() {
        let state = CState::new();
        let theorem = prove_c_expr_eval(
            state.clone(),
            c_add(c_int32_literal(2_147_483_647), c_int32_literal(1)),
        )
        .expect("concrete add should evaluate");

        assert_eq!(
            theorem.prop(),
            &Prop::CExprEvaluates {
                state,
                expr: c_add(c_int32_literal(2_147_483_647), c_int32_literal(1)),
                outcome: CExprOutcome::Ub(CUndefinedBehavior::SignedOverflow),
            }
        );
    }

    #[test]
    fn int32_subtraction_is_native() {
        let state = CState::new();
        let stmt = c_return(c_sub(c_int32_literal(7), c_int32_literal(2)));
        let theorem = prove_symbolic_c_execution(state.clone(), stmt.clone(), Assumptions::new())
            .expect("concrete subtraction should execute");

        assert_eq!(
            theorem.prop(),
            &Prop::CStmtExecutes {
                state: state.clone(),
                stmt,
                outcome: CStmtOutcome::Return {
                    value: int32(5),
                    state,
                },
            }
        );
    }

    #[test]
    fn signed_sub_overflow_is_native_ub() {
        let state = CState::new();
        let theorem = prove_c_expr_eval(
            state.clone(),
            c_sub(c_int32_literal(2_147_483_648), c_int32_literal(1)),
        )
        .expect("concrete sub should evaluate");

        assert_eq!(
            theorem.prop(),
            &Prop::CExprEvaluates {
                state,
                expr: c_sub(c_int32_literal(2_147_483_648), c_int32_literal(1)),
                outcome: CExprOutcome::Ub(CUndefinedBehavior::SignedOverflow),
            }
        );
    }

    #[test]
    fn int32_comparisons_return_c_int32_zero_or_one() {
        let state = CState::new();
        let examples = [
            (c_le(c_int32_literal(2), c_int32_literal(2)), int32(1)),
            (c_gt(c_int32_literal(3), c_int32_literal(2)), int32(1)),
            (c_ge(c_int32_literal(2), c_int32_literal(3)), int32(0)),
            (c_eq(c_int32_literal(4), c_int32_literal(4)), int32(1)),
        ];

        for (expr, expected) in examples {
            let theorem =
                prove_c_expr_eval(state.clone(), expr.clone()).expect("comparison should evaluate");
            assert_eq!(
                theorem.prop(),
                &Prop::CExprEvaluates {
                    state: state.clone(),
                    expr,
                    outcome: CExprOutcome::Value(expected),
                }
            );
        }
    }

    #[test]
    fn if_uses_c_int32_truthiness() {
        let state = CState::new();
        let stmt = c_if(
            c_int32_literal(7),
            c_return(c_int32_literal(1)),
            c_return(c_int32_literal(0)),
        );
        let theorem = prove_symbolic_c_execution(state.clone(), stmt.clone(), Assumptions::new())
            .expect("nonzero int32 condition should take then branch");

        assert_eq!(
            theorem.prop(),
            &Prop::CStmtExecutes {
                state: state.clone(),
                stmt,
                outcome: CStmtOutcome::Return {
                    value: int32(1),
                    state,
                },
            }
        );

        let state = CState::new();
        let stmt = c_if(
            c_int32_literal(0),
            c_return(c_int32_literal(1)),
            c_return(c_int32_literal(0)),
        );
        let theorem = prove_symbolic_c_execution(state.clone(), stmt.clone(), Assumptions::new())
            .expect("zero int32 condition should take else branch");

        assert_eq!(
            theorem.prop(),
            &Prop::CStmtExecutes {
                state: state.clone(),
                stmt,
                outcome: CStmtOutcome::Return {
                    value: int32(0),
                    state,
                },
            }
        );
    }

    #[test]
    fn assignment_and_sequence_update_native_state() {
        let state = CState::new();
        let stmt = c_seq(c_assign("x", c_int32_literal(2)), c_return(c_var("x")));
        let final_state = CState::new().with_local("x", int32(2));
        let theorem = prove_symbolic_c_execution(state.clone(), stmt.clone(), Assumptions::new())
            .expect("assignment sequence should execute");

        assert_eq!(
            theorem.prop(),
            &Prop::CStmtExecutes {
                state,
                stmt,
                outcome: CStmtOutcome::Return {
                    value: int32(2),
                    state: final_state,
                },
            }
        );
    }

    #[test]
    fn store_then_load_threads_native_memory() {
        let ptr = Ptr {
            block: "block".to_string(),
            offset: Bv32Term::Const(0),
        };
        let state = CState::new();
        let stmt = c_seq(
            c_store(c_ptr_value(ptr.clone()), c_int32_literal(9)),
            c_return(c_load(c_ptr_value(ptr.clone()))),
        );
        let final_state = CState::new().with_memory(CMemory::new().store(ptr.clone(), int32(9)));
        let store_obligation = Prop::CMemoryCanStore {
            memory: CMemory::new(),
            ptr,
        };
        let theorem = prove_symbolic_c_execution(state.clone(), stmt.clone(), Assumptions::new())
            .expect("store then load should execute");

        assert_eq!(
            theorem.prop(),
            &Prop::Implies(
                Box::new(store_obligation),
                Box::new(Prop::CStmtExecutes {
                    state,
                    stmt,
                    outcome: CStmtOutcome::Return {
                        value: int32(9),
                        state: final_state,
                    },
                }),
            )
        );
    }

    #[test]
    fn symbolic_load_from_incomplete_memory_reports_validity_obligation() {
        let ptr = Ptr {
            block: "block".to_string(),
            offset: Bv32Term::Const(4),
        };
        let state = CState::new().with_local("p", CValue::Ptr(ptr.clone()));
        let stmt = c_return(c_load(c_var("p")));
        let execution =
            prove_symbolic_c_execution_paths(state.clone(), stmt.clone(), Assumptions::new());

        assert_eq!(execution.paths().len(), 1);
        assert_eq!(
            execution.paths()[0].obligations(),
            &[ProofObligation::memory_can_load(
                CMemory::new(),
                ptr.clone()
            )]
        );
        assert_eq!(
            execution.paths()[0].theorem().prop(),
            &Prop::Implies(
                Box::new(Prop::CMemoryCanLoad {
                    memory: CMemory::new(),
                    ptr: ptr.clone(),
                }),
                Box::new(Prop::CStmtExecutes {
                    state: state.clone(),
                    stmt,
                    outcome: CStmtOutcome::Return {
                        value: int32(Bv32Term::MemoryLoad(
                            Box::new(CMemory::new()),
                            Box::new(ptr),
                        )),
                        state,
                    },
                }),
            )
        );
    }

    #[test]
    fn block_backed_store_then_load_needs_no_memory_obligation() {
        let ptr = Ptr {
            block: "block".to_string(),
            offset: Bv32Term::Const(0),
        };
        let memory = CMemory::new().with_block("block", 16);
        let state = CState::new().with_memory(memory.clone());
        let stmt = c_seq(
            c_store(c_ptr_value(ptr.clone()), c_int32_literal(9)),
            c_return(c_load(c_ptr_value(ptr.clone()))),
        );
        let final_state = CState::new().with_memory(memory.store(ptr, int32(9)));
        let theorem = prove_symbolic_c_execution(state.clone(), stmt.clone(), Assumptions::new())
            .expect("in-range block store/load should execute");

        assert_eq!(
            theorem.prop(),
            &Prop::CStmtExecutes {
                state,
                stmt,
                outcome: CStmtOutcome::Return {
                    value: int32(9),
                    state: final_state,
                },
            }
        );
    }

    #[test]
    fn block_backed_missing_load_returns_symbolic_value_without_obligation() {
        let ptr = Ptr {
            block: "block".to_string(),
            offset: Bv32Term::Const(4),
        };
        let memory = CMemory::new().with_block("block", 16);
        let state = CState::new()
            .with_local("p", CValue::Ptr(ptr.clone()))
            .with_memory(memory.clone());
        let stmt = c_return(c_load(c_var("p")));
        let theorem = prove_symbolic_c_execution(state.clone(), stmt.clone(), Assumptions::new())
            .expect("in-range missing load should produce symbolic value");

        assert_eq!(
            theorem.prop(),
            &Prop::CStmtExecutes {
                state: state.clone(),
                stmt,
                outcome: CStmtOutcome::Return {
                    value: int32(Bv32Term::MemoryLoad(Box::new(memory), Box::new(ptr))),
                    state,
                },
            }
        );
    }

    #[test]
    fn pointer_addition_scales_int32_offsets_for_loads() {
        let base = Ptr {
            block: "block".to_string(),
            offset: Bv32Term::Const(0),
        };
        let second = Ptr {
            block: "block".to_string(),
            offset: Bv32Term::Const(4),
        };
        let memory = CMemory::new()
            .with_block("block", 16)
            .store(second, int32(23));
        let state = CState::new()
            .with_local("p", CValue::Ptr(base))
            .with_memory(memory);
        let stmt = c_return(c_load(c_add(c_var("p"), c_int32_literal(1))));
        let theorem = prove_symbolic_c_execution(state.clone(), stmt.clone(), Assumptions::new())
            .expect("pointer arithmetic load should execute");

        assert_eq!(
            theorem.prop(),
            &Prop::CStmtExecutes {
                state,
                stmt,
                outcome: CStmtOutcome::Return {
                    value: int32(23),
                    state: CState::new()
                        .with_local(
                            "p",
                            CValue::Ptr(Ptr {
                                block: "block".to_string(),
                                offset: Bv32Term::Const(0),
                            }),
                        )
                        .with_memory(CMemory::new().with_block("block", 16).store(
                            Ptr {
                                block: "block".to_string(),
                                offset: Bv32Term::Const(4),
                            },
                            int32(23),
                        ),),
                },
            }
        );
    }

    #[test]
    fn pointer_addition_out_of_range_load_reports_validity_obligation() {
        let base = Ptr {
            block: "block".to_string(),
            offset: Bv32Term::Const(0),
        };
        let derived = Ptr {
            block: "block".to_string(),
            offset: Bv32Term::Const(4),
        };
        let memory = CMemory::new().with_block("block", 4);
        let state = CState::new()
            .with_local("p", CValue::Ptr(base))
            .with_memory(memory.clone());
        let stmt = c_return(c_load(c_add(c_var("p"), c_int32_literal(1))));
        let execution =
            prove_symbolic_c_execution_paths(state.clone(), stmt.clone(), Assumptions::new());

        assert_eq!(execution.paths().len(), 1);
        assert_eq!(
            execution.paths()[0].obligations(),
            &[ProofObligation::memory_can_load(
                memory.clone(),
                derived.clone()
            )]
        );
        assert_eq!(
            execution.paths()[0].theorem().prop(),
            &Prop::Implies(
                Box::new(Prop::CMemoryCanLoad {
                    memory: memory.clone(),
                    ptr: derived.clone(),
                }),
                Box::new(Prop::CStmtExecutes {
                    state: state.clone(),
                    stmt,
                    outcome: CStmtOutcome::Return {
                        value: int32(Bv32Term::MemoryLoad(Box::new(memory), Box::new(derived),)),
                        state,
                    },
                }),
            )
        );
    }

    #[test]
    fn local_declaration_allocates_stack_object_for_address_of() {
        let local_ptr = Ptr {
            block: "local:x".to_string(),
            offset: Bv32Term::Const(0),
        };
        let state = CState::new();
        let stmt = c_seq(
            c_declare("x", CType::Int32),
            c_seq(
                c_assign("x", c_int32_literal(5)),
                c_return(c_load(c_addr_of("x"))),
            ),
        );
        let final_state = CState::new().with_local("x", int32(5)).with_memory(
            CMemory::new()
                .with_block("local:x", 4)
                .store(local_ptr, int32(5)),
        );
        let theorem = prove_symbolic_c_execution(state.clone(), stmt.clone(), Assumptions::new())
            .expect("local declaration/address-of should execute");

        assert_eq!(
            theorem.prop(),
            &Prop::CStmtExecutes {
                state,
                stmt,
                outcome: CStmtOutcome::Return {
                    value: int32(5),
                    state: final_state,
                },
            }
        );
    }

    #[test]
    fn symbolic_execution_stops_without_needed_overflow_fact() {
        let left = Var(20);
        let right = Var(21);
        let state = CState::new()
            .with_local("left", int32(Bv32Term::Var(left)))
            .with_local("right", int32(Bv32Term::Var(right)));
        let stmt = c_return(c_add(c_var("left"), c_var("right")));

        assert!(prove_symbolic_c_execution(state, stmt, Assumptions::new()).is_none());
    }

    #[test]
    fn symbolic_execution_reports_branch_facts() {
        let a = Var(24);
        let b = Var(25);
        let a_bits = Bv32Term::Var(a);
        let b_bits = Bv32Term::Var(b);
        let condition = c_max_lt_condition(a_bits.clone(), b_bits.clone());
        let state = c_max_state(int32(a_bits), int32(b_bits));
        let execution =
            prove_symbolic_c_execution_paths(state.clone(), c_max_body(), Assumptions::new());

        assert_eq!(execution.paths().len(), 2);
        assert_eq!(
            execution.paths()[0].facts(),
            &[PathFact::bool(condition.clone(), true)]
        );
        assert_eq!(
            execution.paths()[0].obligations(),
            &[] as &[ProofObligation]
        );
        assert_eq!(
            execution.paths()[0].theorem().prop(),
            &Prop::Implies(
                Box::new(Prop::BoolIs(condition.clone(), true)),
                Box::new(Prop::CStmtExecutes {
                    state: state.clone(),
                    stmt: c_max_body(),
                    outcome: CStmtOutcome::Return {
                        value: int32(Bv32Term::Var(b)),
                        state: state.clone(),
                    },
                }),
            )
        );

        assert_eq!(
            execution.paths()[1].facts(),
            &[PathFact::bool(condition.clone(), false)]
        );
        assert_eq!(
            execution.paths()[1].obligations(),
            &[] as &[ProofObligation]
        );
        assert_eq!(
            execution.paths()[1].theorem().prop(),
            &Prop::Implies(
                Box::new(Prop::BoolIs(condition, false)),
                Box::new(Prop::CStmtExecutes {
                    state: state.clone(),
                    stmt: c_max_body(),
                    outcome: CStmtOutcome::Return {
                        value: int32(Bv32Term::Var(a)),
                        state,
                    },
                }),
            )
        );
    }

    #[test]
    fn symbolic_execution_reports_overflow_facts() {
        let left = Var(26);
        let right = Var(27);
        let left_bits = Bv32Term::Var(left);
        let right_bits = Bv32Term::Var(right);
        let state = CState::new()
            .with_local("left", int32(left_bits.clone()))
            .with_local("right", int32(right_bits.clone()));
        let stmt = c_return(c_add(c_var("left"), c_var("right")));
        let overflow = BoolTerm::signed_add_overflows(left_bits.clone(), right_bits.clone());
        let execution =
            prove_symbolic_c_execution_paths(state.clone(), stmt.clone(), Assumptions::new());

        assert_eq!(execution.paths().len(), 2);
        assert_eq!(
            execution.paths()[0].facts(),
            &[PathFact::bool(overflow.clone(), false)]
        );
        assert_eq!(
            execution.paths()[0].obligations(),
            &[] as &[ProofObligation]
        );
        assert_eq!(
            execution.paths()[0].theorem().prop(),
            &Prop::Implies(
                Box::new(Prop::BoolIs(overflow.clone(), false)),
                Box::new(Prop::CStmtExecutes {
                    state: state.clone(),
                    stmt: stmt.clone(),
                    outcome: CStmtOutcome::Return {
                        value: int32(Bv32Term::Add(Box::new(left_bits), Box::new(right_bits))),
                        state: state.clone(),
                    },
                }),
            )
        );

        assert_eq!(
            execution.paths()[1].facts(),
            &[PathFact::bool(overflow.clone(), true)]
        );
        assert_eq!(
            execution.paths()[1].obligations(),
            &[] as &[ProofObligation]
        );
        assert_eq!(
            execution.paths()[1].theorem().prop(),
            &Prop::Implies(
                Box::new(Prop::BoolIs(overflow, true)),
                Box::new(Prop::CStmtExecutes {
                    state: state.clone(),
                    stmt,
                    outcome: CStmtOutcome::Ub(CUndefinedBehavior::SignedOverflow),
                }),
            )
        );
    }

    #[test]
    fn symbolic_execution_uses_no_overflow_fact() {
        let left = Var(22);
        let right = Var(23);
        let left_bits = Bv32Term::Var(left);
        let right_bits = Bv32Term::Var(right);
        let state = CState::new()
            .with_local("left", int32(left_bits.clone()))
            .with_local("right", int32(right_bits.clone()));
        let stmt = c_return(c_add(c_var("left"), c_var("right")));
        let no_overflow = BoolTerm::signed_add_overflows(left_bits.clone(), right_bits.clone());
        let assumptions = Assumptions::new().assume_bool(no_overflow.clone(), false);
        let theorem = prove_symbolic_c_execution(state.clone(), stmt.clone(), assumptions)
            .expect("no-overflow fact should let symbolic add execute");

        assert_eq!(
            theorem.prop(),
            &Prop::Implies(
                Box::new(Prop::BoolIs(no_overflow, false)),
                Box::new(Prop::CStmtExecutes {
                    state: state.clone(),
                    stmt,
                    outcome: CStmtOutcome::Return {
                        value: int32(Bv32Term::Add(Box::new(left_bits), Box::new(right_bits))),
                        state,
                    },
                }),
            )
        );
    }

    #[test]
    fn memory_load_store_are_native_theorems() {
        let ptr = Ptr {
            block: "block".to_string(),
            offset: Bv32Term::Const(0),
        };
        let value = int32(7);
        let theorem =
            prove_memory_load_after_store_same(CMemory::new(), ptr.clone(), value.clone());

        assert_eq!(
            theorem.prop(),
            &Prop::CMemoryLoads {
                memory: CMemory::new().store(ptr.clone(), value.clone()),
                ptr,
                outcome: CExprOutcome::Value(value),
            }
        );
    }

    #[test]
    fn missing_memory_load_is_native_ub() {
        let ptr = Ptr {
            block: "block".to_string(),
            offset: Bv32Term::Const(4),
        };
        let theorem = prove_memory_load(CMemory::new(), ptr.clone());

        assert_eq!(
            theorem.prop(),
            &Prop::CMemoryLoads {
                memory: CMemory::new(),
                ptr,
                outcome: CExprOutcome::Ub(CUndefinedBehavior::InvalidMemory),
            }
        );
    }
}
