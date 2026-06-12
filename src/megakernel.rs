//! Experimental rich kernel for systems-code proofs.
//!
//! This module is intentionally parallel to the current list-based kernel. It
//! keeps the LCF shape: `Theorem` is an abstract object whose constructor is not
//! public. The difference is that the trusted kernel language has native
//! systems concepts instead of encoding them all as Lisp-style lists.

use std::collections::BTreeMap;

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
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum BoolTerm {
    Const(bool),
    Var(Var),
    Bv32Slt(Box<Bv32Term>, Box<Bv32Term>),
    Bv32Eq(Box<Bv32Term>, Box<Bv32Term>),
    Bv32SignedAddOverflows(Box<Bv32Term>, Box<Bv32Term>),
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
    Lt(Box<CExpr>, Box<CExpr>),
    Add(Box<CExpr>, Box<CExpr>),
    Load(Box<CExpr>),
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum CStmt {
    Assign {
        name: String,
        expr: CExpr,
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
pub enum CUndefinedBehavior {
    SignedOverflow,
    InvalidMemory,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum CRuntimeError {
    UnboundVariable(String),
    TypeMismatch,
    WrongArity { expected: usize, actual: usize },
    MissingReturn,
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
    cells: BTreeMap<Ptr, CValue>,
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
    CMemoryLoads {
        memory: CMemory,
        ptr: Ptr,
        outcome: CExprOutcome,
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
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct BoolObligation {
    condition: BoolTerm,
    value: bool,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SymbolicCExecution {
    paths: Vec<SymbolicCExecutionPath>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SymbolicCExecutionPath {
    obligations: Vec<BoolObligation>,
    theorem: Theorem,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct CExprPath {
    outcome: CExprOutcome,
    obligations: Vec<BoolObligation>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct CStmtPath {
    outcome: CStmtOutcome,
    obligations: Vec<BoolObligation>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct CFunctionPath {
    outcome: CFunctionOutcome,
    obligations: Vec<BoolObligation>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct CArgsPath {
    values: Vec<CValue>,
    outcome: Option<CFunctionOutcome>,
    obligations: Vec<BoolObligation>,
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
            Self::Var(_) | Self::Add(_, _) => None,
        }
    }

    fn add(left: Self, right: Self) -> Self {
        match (left.as_const(), right.as_const()) {
            (Some(left), Some(right)) => Self::Const(left.wrapping_add(right)),
            _ => Self::Add(Box::new(left), Box::new(right)),
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

    fn signed_add_overflows(left: Bv32Term, right: Bv32Term) -> Self {
        match (left.as_const(), right.as_const()) {
            (Some(left), Some(right)) => Self::Const((left as i32).overflowing_add(right as i32).1),
            _ => Self::Bv32SignedAddOverflows(Box::new(left), Box::new(right)),
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

impl CMemory {
    pub fn new() -> Self {
        Self::default()
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

    fn decide(&self, condition: &BoolTerm) -> Option<bool> {
        match condition {
            BoolTerm::Const(value) => Some(*value),
            _ => self.bool_facts.get(condition).copied(),
        }
    }
}

impl BoolObligation {
    pub fn new(condition: BoolTerm, value: bool) -> Self {
        Self { condition, value }
    }

    pub fn condition(&self) -> &BoolTerm {
        &self.condition
    }

    pub fn value(&self) -> bool {
        self.value
    }

    pub fn prop(&self) -> Prop {
        Prop::BoolIs(self.condition.clone(), self.value)
    }
}

impl SymbolicCExecution {
    pub fn paths(&self) -> &[SymbolicCExecutionPath] {
        &self.paths
    }
}

impl SymbolicCExecutionPath {
    pub fn obligations(&self) -> &[BoolObligation] {
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

pub fn c_int32_literal(value: u32) -> CExpr {
    CExpr::Value(int32(Bv32Term::Const(value)))
}

pub fn c_ptr_value(ptr: Ptr) -> CExpr {
    CExpr::Value(CValue::Ptr(ptr))
}

pub fn c_lt(left: CExpr, right: CExpr) -> CExpr {
    CExpr::Lt(Box::new(left), Box::new(right))
}

pub fn c_add(left: CExpr, right: CExpr) -> CExpr {
    CExpr::Add(Box::new(left), Box::new(right))
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
    let execution = prove_symbolic_c_execution_with_obligations(state, stmt, assumptions);
    let mut paths = execution.paths.into_iter();
    let path = paths.next()?;
    if paths.next().is_some() {
        return None;
    }
    Some(path.theorem)
}

pub fn prove_symbolic_c_execution_with_obligations(
    state: CState,
    stmt: CStmt,
    assumptions: Assumptions,
) -> SymbolicCExecution {
    let paths = exec_c_stmt_paths(&state, &stmt, &assumptions)
        .into_iter()
        .map(|path| {
            let prop = Prop::CStmtExecutes {
                state: state.clone(),
                stmt: stmt.clone(),
                outcome: path.outcome,
            };
            let theorem = Theorem::new(wrap_bool_facts(prop, &assumptions, &path.obligations));
            SymbolicCExecutionPath {
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
    let execution =
        prove_symbolic_c_function_execution_with_obligations(state, function, args, assumptions);
    let mut paths = execution.paths.into_iter();
    let path = paths.next()?;
    if paths.next().is_some() {
        return None;
    }
    Some(path.theorem)
}

pub fn prove_symbolic_c_function_execution_with_obligations(
    state: CState,
    function: CFunction,
    args: Vec<CExpr>,
    assumptions: Assumptions,
) -> SymbolicCExecution {
    let paths = exec_c_function_paths(&state, &function, &args, &assumptions)
        .into_iter()
        .map(|path| {
            let prop = Prop::CFunctionExecutes {
                state: state.clone(),
                function: function.clone(),
                args: args.clone(),
                outcome: path.outcome,
            };
            let theorem = Theorem::new(wrap_bool_facts(prop, &assumptions, &path.obligations));
            SymbolicCExecutionPath {
                obligations: path.obligations,
                theorem,
            }
        })
        .collect();

    SymbolicCExecution { paths }
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

fn wrap_bool_facts(prop: Prop, assumptions: &Assumptions, obligations: &[BoolObligation]) -> Prop {
    let prop = obligations.iter().rev().fold(prop, |body, obligation| {
        Prop::Implies(Box::new(obligation.prop()), Box::new(body))
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

fn add_bool_obligation(
    obligations: &mut Vec<BoolObligation>,
    assumptions: &Assumptions,
    condition: BoolTerm,
    value: bool,
) -> Option<()> {
    if let Some(known) = assumptions.decide(&condition) {
        return (known == value).then_some(());
    }

    if let Some(existing) = obligations
        .iter()
        .find(|obligation| obligation.condition == condition)
    {
        return (existing.value == value).then_some(());
    }

    obligations.push(BoolObligation::new(condition, value));
    Some(())
}

fn merge_obligations(
    left: &[BoolObligation],
    right: &[BoolObligation],
    assumptions: &Assumptions,
) -> Option<Vec<BoolObligation>> {
    let mut obligations = left.to_vec();
    for obligation in right {
        add_bool_obligation(
            &mut obligations,
            assumptions,
            obligation.condition.clone(),
            obligation.value,
        )?;
    }
    Some(obligations)
}

fn decide_with_obligations(
    assumptions: &Assumptions,
    obligations: &[BoolObligation],
    condition: &BoolTerm,
) -> Option<bool> {
    assumptions.decide(condition).or_else(|| {
        obligations
            .iter()
            .find(|obligation| &obligation.condition == condition)
            .map(|obligation| obligation.value)
    })
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
            obligations: Vec::new(),
        }],
        CExpr::Var(name) => vec![CExprPath {
            outcome: match state.locals.get(name) {
                Some(value) => CExprOutcome::Value(value.clone()),
                None => CExprOutcome::RuntimeError(CRuntimeError::UnboundVariable(name.clone())),
            },
            obligations: Vec::new(),
        }],
        CExpr::Lt(left, right) => eval_c_int32_binary_paths(
            state,
            left,
            right,
            assumptions,
            |left, right, obligations| {
                vec![CExprPath {
                    outcome: CExprOutcome::Value(c_bool(BoolTerm::slt(left, right))),
                    obligations,
                }]
            },
        ),
        CExpr::Add(left, right) => eval_c_int32_binary_paths(
            state,
            left,
            right,
            assumptions,
            |left, right, obligations| {
                let overflow = BoolTerm::signed_add_overflows(left.clone(), right.clone());
                match decide_with_obligations(assumptions, &obligations, &overflow) {
                    Some(true) => vec![CExprPath {
                        outcome: CExprOutcome::Ub(CUndefinedBehavior::SignedOverflow),
                        obligations,
                    }],
                    Some(false) => vec![CExprPath {
                        outcome: CExprOutcome::Value(int32(Bv32Term::add(left, right))),
                        obligations,
                    }],
                    None => {
                        let mut normal_obligations = obligations.clone();
                        add_bool_obligation(
                            &mut normal_obligations,
                            assumptions,
                            overflow.clone(),
                            false,
                        )
                        .expect("unknown overflow fact should be consistent");

                        let mut overflow_obligations = obligations;
                        add_bool_obligation(&mut overflow_obligations, assumptions, overflow, true)
                            .expect("unknown overflow fact should be consistent");

                        vec![
                            CExprPath {
                                outcome: CExprOutcome::Value(int32(Bv32Term::add(left, right))),
                                obligations: normal_obligations,
                            },
                            CExprPath {
                                outcome: CExprOutcome::Ub(CUndefinedBehavior::SignedOverflow),
                                obligations: overflow_obligations,
                            },
                        ]
                    }
                }
            },
        ),
        CExpr::Load(ptr) => eval_c_expr_paths(state, ptr, assumptions)
            .into_iter()
            .map(|path| CExprPath {
                outcome: match path.outcome {
                    CExprOutcome::Value(CValue::Ptr(ptr)) => state.memory.load(&ptr),
                    CExprOutcome::Value(_) => {
                        CExprOutcome::RuntimeError(CRuntimeError::TypeMismatch)
                    }
                    CExprOutcome::Ub(ub) => CExprOutcome::Ub(ub),
                    CExprOutcome::RuntimeError(error) => CExprOutcome::RuntimeError(error),
                },
                obligations: path.obligations,
            })
            .collect(),
    }
}

fn eval_c_int32_binary_paths(
    state: &CState,
    left: &CExpr,
    right: &CExpr,
    assumptions: &Assumptions,
    apply: impl Fn(Bv32Term, Bv32Term, Vec<BoolObligation>) -> Vec<CExprPath>,
) -> Vec<CExprPath> {
    let mut paths = Vec::new();
    for left_path in eval_c_expr_paths(state, left, assumptions) {
        let CExprPath {
            outcome: left_outcome,
            obligations: left_obligations,
        } = left_path;

        let left = match left_outcome {
            CExprOutcome::Value(CValue::Int32(left)) => left,
            CExprOutcome::Value(_) => {
                paths.push(CExprPath {
                    outcome: CExprOutcome::RuntimeError(CRuntimeError::TypeMismatch),
                    obligations: left_obligations,
                });
                continue;
            }
            CExprOutcome::Ub(ub) => {
                paths.push(CExprPath {
                    outcome: CExprOutcome::Ub(ub),
                    obligations: left_obligations,
                });
                continue;
            }
            CExprOutcome::RuntimeError(error) => {
                paths.push(CExprPath {
                    outcome: CExprOutcome::RuntimeError(error),
                    obligations: left_obligations,
                });
                continue;
            }
        };

        for right_path in eval_c_expr_paths(state, right, assumptions) {
            let Some(obligations) =
                merge_obligations(&left_obligations, &right_path.obligations, assumptions)
            else {
                continue;
            };

            match right_path.outcome {
                CExprOutcome::Value(CValue::Int32(right)) => {
                    paths.extend(apply(left.clone(), right, obligations));
                }
                CExprOutcome::Value(_) => paths.push(CExprPath {
                    outcome: CExprOutcome::RuntimeError(CRuntimeError::TypeMismatch),
                    obligations,
                }),
                CExprOutcome::Ub(ub) => paths.push(CExprPath {
                    outcome: CExprOutcome::Ub(ub),
                    obligations,
                }),
                CExprOutcome::RuntimeError(error) => paths.push(CExprPath {
                    outcome: CExprOutcome::RuntimeError(error),
                    obligations,
                }),
            }
        }
    }

    paths
}

fn exec_c_stmt(state: &CState, stmt: &CStmt, assumptions: &Assumptions) -> Option<CStmtOutcome> {
    let paths = exec_c_stmt_paths(state, stmt, assumptions);
    let mut paths = paths.into_iter();
    let path = paths.next()?;
    if paths.next().is_some() {
        return None;
    }
    Some(path.outcome)
}

fn exec_c_stmt_paths(state: &CState, stmt: &CStmt, assumptions: &Assumptions) -> Vec<CStmtPath> {
    match stmt {
        CStmt::Assign { name, expr } => eval_c_expr_paths(state, expr, assumptions)
            .into_iter()
            .map(|path| CStmtPath {
                outcome: match path.outcome {
                    CExprOutcome::Value(value) => {
                        let mut state = state.clone();
                        state.locals.set(name.clone(), value);
                        CStmtOutcome::Normal(state)
                    }
                    CExprOutcome::Ub(ub) => CStmtOutcome::Ub(ub),
                    CExprOutcome::RuntimeError(error) => CStmtOutcome::RuntimeError(error),
                },
                obligations: path.obligations,
            })
            .collect(),
        CStmt::Seq(first, second) => {
            let mut paths = Vec::new();
            for first_path in exec_c_stmt_paths(state, first, assumptions) {
                match first_path.outcome {
                    CStmtOutcome::Normal(state) => {
                        paths.extend(exec_c_stmt_paths_with_prefix(
                            &state,
                            second,
                            assumptions,
                            &first_path.obligations,
                        ));
                    }
                    outcome @ (CStmtOutcome::Return { .. }
                    | CStmtOutcome::Ub(_)
                    | CStmtOutcome::RuntimeError(_)) => paths.push(CStmtPath {
                        outcome,
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
                obligations: path.obligations,
            })
            .collect(),
        CStmt::Store { ptr, value } => {
            let mut paths = Vec::new();
            for ptr_path in eval_c_expr_paths(state, ptr, assumptions) {
                let CExprPath {
                    outcome: ptr_outcome,
                    obligations: ptr_obligations,
                } = ptr_path;

                let ptr = match ptr_outcome {
                    CExprOutcome::Value(CValue::Ptr(ptr)) => ptr,
                    CExprOutcome::Value(_) => {
                        paths.push(CStmtPath {
                            outcome: CStmtOutcome::RuntimeError(CRuntimeError::TypeMismatch),
                            obligations: ptr_obligations,
                        });
                        continue;
                    }
                    CExprOutcome::Ub(ub) => {
                        paths.push(CStmtPath {
                            outcome: CStmtOutcome::Ub(ub),
                            obligations: ptr_obligations,
                        });
                        continue;
                    }
                    CExprOutcome::RuntimeError(error) => {
                        paths.push(CStmtPath {
                            outcome: CStmtOutcome::RuntimeError(error),
                            obligations: ptr_obligations,
                        });
                        continue;
                    }
                };

                for value_path in eval_c_expr_paths(state, value, assumptions) {
                    let Some(obligations) =
                        merge_obligations(&ptr_obligations, &value_path.obligations, assumptions)
                    else {
                        continue;
                    };

                    paths.push(CStmtPath {
                        outcome: match value_path.outcome {
                            CExprOutcome::Value(value) => {
                                let mut state = state.clone();
                                state.memory = state.memory.store(ptr.clone(), value);
                                CStmtOutcome::Normal(state)
                            }
                            CExprOutcome::Ub(ub) => CStmtOutcome::Ub(ub),
                            CExprOutcome::RuntimeError(error) => CStmtOutcome::RuntimeError(error),
                        },
                        obligations,
                    });
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
                match condition_path.outcome {
                    CExprOutcome::Value(CValue::Bool(condition)) => {
                        match decide_with_obligations(
                            assumptions,
                            &condition_path.obligations,
                            &condition,
                        ) {
                            Some(true) => paths.extend(exec_c_stmt_paths_with_prefix(
                                state,
                                then_branch,
                                assumptions,
                                &condition_path.obligations,
                            )),
                            Some(false) => paths.extend(exec_c_stmt_paths_with_prefix(
                                state,
                                else_branch,
                                assumptions,
                                &condition_path.obligations,
                            )),
                            None => {
                                let mut true_obligations = condition_path.obligations.clone();
                                add_bool_obligation(
                                    &mut true_obligations,
                                    assumptions,
                                    condition.clone(),
                                    true,
                                )
                                .expect("unknown branch fact should be consistent");
                                paths.extend(exec_c_stmt_paths_with_prefix(
                                    state,
                                    then_branch,
                                    assumptions,
                                    &true_obligations,
                                ));

                                let mut false_obligations = condition_path.obligations;
                                add_bool_obligation(
                                    &mut false_obligations,
                                    assumptions,
                                    condition,
                                    false,
                                )
                                .expect("unknown branch fact should be consistent");
                                paths.extend(exec_c_stmt_paths_with_prefix(
                                    state,
                                    else_branch,
                                    assumptions,
                                    &false_obligations,
                                ));
                            }
                        }
                    }
                    CExprOutcome::Value(_) => paths.push(CStmtPath {
                        outcome: CStmtOutcome::RuntimeError(CRuntimeError::TypeMismatch),
                        obligations: condition_path.obligations,
                    }),
                    CExprOutcome::Ub(ub) => paths.push(CStmtPath {
                        outcome: CStmtOutcome::Ub(ub),
                        obligations: condition_path.obligations,
                    }),
                    CExprOutcome::RuntimeError(error) => paths.push(CStmtPath {
                        outcome: CStmtOutcome::RuntimeError(error),
                        obligations: condition_path.obligations,
                    }),
                }
            }
            paths
        }
    }
}

fn exec_c_stmt_paths_with_prefix(
    state: &CState,
    stmt: &CStmt,
    assumptions: &Assumptions,
    prefix: &[BoolObligation],
) -> Vec<CStmtPath> {
    exec_c_stmt_paths(state, stmt, assumptions)
        .into_iter()
        .filter_map(|path| {
            let obligations = merge_obligations(prefix, &path.obligations, assumptions)?;
            Some(CStmtPath {
                outcome: path.outcome,
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
) -> Vec<CFunctionPath> {
    if args.len() != function.params.len() {
        return vec![CFunctionPath {
            outcome: CFunctionOutcome::RuntimeError(CRuntimeError::WrongArity {
                expected: function.params.len(),
                actual: args.len(),
            }),
            obligations: Vec::new(),
        }];
    }

    let mut paths = Vec::new();
    for args_path in eval_c_args_paths(caller_state, args, assumptions) {
        if let Some(outcome) = args_path.outcome {
            paths.push(CFunctionPath {
                outcome,
                obligations: args_path.obligations,
            });
            continue;
        }

        let Some(callee_state) = bind_c_function_args(caller_state, function, &args_path.values)
        else {
            paths.push(CFunctionPath {
                outcome: CFunctionOutcome::RuntimeError(CRuntimeError::TypeMismatch),
                obligations: args_path.obligations,
            });
            continue;
        };

        for body_path in exec_c_stmt_paths(&callee_state, function.body(), assumptions) {
            let Some(obligations) =
                merge_obligations(&args_path.obligations, &body_path.obligations, assumptions)
            else {
                continue;
            };

            paths.push(CFunctionPath {
                outcome: function_outcome_from_body(caller_state, function, body_path.outcome),
                obligations,
            });
        }
    }

    paths
}

fn eval_c_args_paths(state: &CState, args: &[CExpr], assumptions: &Assumptions) -> Vec<CArgsPath> {
    let mut paths = vec![CArgsPath {
        values: Vec::new(),
        outcome: None,
        obligations: Vec::new(),
    }];

    for arg in args {
        let mut next_paths = Vec::new();
        for path in paths {
            if path.outcome.is_some() {
                next_paths.push(path);
                continue;
            }

            for arg_path in eval_c_expr_paths(state, arg, assumptions) {
                let Some(obligations) =
                    merge_obligations(&path.obligations, &arg_path.obligations, assumptions)
                else {
                    continue;
                };

                match arg_path.outcome {
                    CExprOutcome::Value(value) => {
                        let mut values = path.values.clone();
                        values.push(value);
                        next_paths.push(CArgsPath {
                            values,
                            outcome: None,
                            obligations,
                        });
                    }
                    CExprOutcome::Ub(ub) => next_paths.push(CArgsPath {
                        values: path.values.clone(),
                        outcome: Some(CFunctionOutcome::Ub(ub)),
                        obligations,
                    }),
                    CExprOutcome::RuntimeError(error) => next_paths.push(CArgsPath {
                        values: path.values.clone(),
                        outcome: Some(CFunctionOutcome::RuntimeError(error)),
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
    fn symbolic_max_function_call_reports_branch_obligations() {
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
        let execution = prove_symbolic_c_function_execution_with_obligations(
            state.clone(),
            function.clone(),
            args.clone(),
            Assumptions::new(),
        );

        assert_eq!(execution.paths().len(), 2);
        assert_eq!(
            execution.paths()[0].obligations(),
            &[BoolObligation::new(condition.clone(), true)]
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
            execution.paths()[1].obligations(),
            &[BoolObligation::new(condition.clone(), false)]
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
            .with_memory(CMemory::new().store(ptr, int32(9)));
        let theorem = prove_symbolic_c_function_execution(
            state.clone(),
            function.clone(),
            args.clone(),
            Assumptions::new(),
        )
        .expect("store/load function call should execute");

        assert_eq!(
            theorem.prop(),
            &Prop::CFunctionExecutes {
                state,
                function,
                args,
                outcome: CFunctionOutcome::Return {
                    value: int32(9),
                    state: final_state,
                },
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
        let final_state = CState::new().with_memory(CMemory::new().store(ptr, int32(9)));
        let theorem = prove_symbolic_c_execution(state.clone(), stmt.clone(), Assumptions::new())
            .expect("store then load should execute");

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
    fn symbolic_execution_reports_branch_obligations() {
        let a = Var(24);
        let b = Var(25);
        let a_bits = Bv32Term::Var(a);
        let b_bits = Bv32Term::Var(b);
        let condition = c_max_lt_condition(a_bits.clone(), b_bits.clone());
        let state = c_max_state(int32(a_bits), int32(b_bits));
        let execution = prove_symbolic_c_execution_with_obligations(
            state.clone(),
            c_max_body(),
            Assumptions::new(),
        );

        assert_eq!(execution.paths().len(), 2);
        assert_eq!(
            execution.paths()[0].obligations(),
            &[BoolObligation::new(condition.clone(), true)]
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
            execution.paths()[1].obligations(),
            &[BoolObligation::new(condition.clone(), false)]
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
    fn symbolic_execution_reports_overflow_obligations() {
        let left = Var(26);
        let right = Var(27);
        let left_bits = Bv32Term::Var(left);
        let right_bits = Bv32Term::Var(right);
        let state = CState::new()
            .with_local("left", int32(left_bits.clone()))
            .with_local("right", int32(right_bits.clone()));
        let stmt = c_return(c_add(c_var("left"), c_var("right")));
        let overflow = BoolTerm::signed_add_overflows(left_bits.clone(), right_bits.clone());
        let execution = prove_symbolic_c_execution_with_obligations(
            state.clone(),
            stmt.clone(),
            Assumptions::new(),
        );

        assert_eq!(execution.paths().len(), 2);
        assert_eq!(
            execution.paths()[0].obligations(),
            &[BoolObligation::new(overflow.clone(), false)]
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
            execution.paths()[1].obligations(),
            &[BoolObligation::new(overflow.clone(), true)]
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
