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
    CInt32,
    CBool,
    CPtr,
    CValue,
    CMemory,
    CState,
    CStmtOutcome,
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
pub enum CUndefinedBehavior {
    SignedOverflow,
    InvalidMemory,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum CRuntimeError {
    UnboundVariable(String),
    TypeMismatch,
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

pub fn c_max_body() -> CStmt {
    c_if(
        c_lt(c_var("a"), c_var("b")),
        c_return(c_var("b")),
        c_return(c_var("a")),
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
    let outcome = exec_c_stmt(&state, &stmt, &assumptions)?;
    let prop = Prop::CStmtExecutes {
        state,
        stmt,
        outcome,
    };
    Some(Theorem::new(wrap_assumptions(prop, &assumptions)))
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

fn wrap_assumptions(prop: Prop, assumptions: &Assumptions) -> Prop {
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

fn eval_c_expr(state: &CState, expr: &CExpr, assumptions: &Assumptions) -> Option<CExprOutcome> {
    match expr {
        CExpr::Value(value) => Some(CExprOutcome::Value(value.clone())),
        CExpr::Var(name) => Some(match state.locals.get(name) {
            Some(value) => CExprOutcome::Value(value.clone()),
            None => CExprOutcome::RuntimeError(CRuntimeError::UnboundVariable(name.clone())),
        }),
        CExpr::Lt(left, right) => {
            eval_c_int32_binary(state, left, right, assumptions, |left, right| {
                Some(CExprOutcome::Value(c_bool(BoolTerm::slt(left, right))))
            })
        }
        CExpr::Add(left, right) => eval_c_int32_binary(
            state,
            left,
            right,
            assumptions,
            |left, right| match assumptions
                .decide(&BoolTerm::signed_add_overflows(left.clone(), right.clone()))
            {
                Some(true) => Some(CExprOutcome::Ub(CUndefinedBehavior::SignedOverflow)),
                Some(false) => Some(CExprOutcome::Value(int32(Bv32Term::add(left, right)))),
                None => None,
            },
        ),
        CExpr::Load(ptr) => Some(match eval_c_expr(state, ptr, assumptions)? {
            CExprOutcome::Value(CValue::Ptr(ptr)) => state.memory.load(&ptr),
            CExprOutcome::Value(_) => CExprOutcome::RuntimeError(CRuntimeError::TypeMismatch),
            CExprOutcome::Ub(ub) => CExprOutcome::Ub(ub),
            CExprOutcome::RuntimeError(error) => CExprOutcome::RuntimeError(error),
        }),
    }
}

fn eval_c_int32_binary(
    state: &CState,
    left: &CExpr,
    right: &CExpr,
    assumptions: &Assumptions,
    apply: impl FnOnce(Bv32Term, Bv32Term) -> Option<CExprOutcome>,
) -> Option<CExprOutcome> {
    let left = eval_c_expr(state, left, assumptions)?;
    let right = eval_c_expr(state, right, assumptions)?;
    match (left, right) {
        (CExprOutcome::Value(CValue::Int32(left)), CExprOutcome::Value(CValue::Int32(right))) => {
            apply(left, right)
        }
        (CExprOutcome::Ub(ub), _) | (_, CExprOutcome::Ub(ub)) => Some(CExprOutcome::Ub(ub)),
        (CExprOutcome::RuntimeError(error), _) | (_, CExprOutcome::RuntimeError(error)) => {
            Some(CExprOutcome::RuntimeError(error))
        }
        _ => Some(CExprOutcome::RuntimeError(CRuntimeError::TypeMismatch)),
    }
}

fn exec_c_stmt(state: &CState, stmt: &CStmt, assumptions: &Assumptions) -> Option<CStmtOutcome> {
    match stmt {
        CStmt::Assign { name, expr } => Some(match eval_c_expr(state, expr, assumptions)? {
            CExprOutcome::Value(value) => {
                let mut state = state.clone();
                state.locals.set(name.clone(), value);
                CStmtOutcome::Normal(state)
            }
            CExprOutcome::Ub(ub) => CStmtOutcome::Ub(ub),
            CExprOutcome::RuntimeError(error) => CStmtOutcome::RuntimeError(error),
        }),
        CStmt::Seq(first, second) => match exec_c_stmt(state, first, assumptions)? {
            CStmtOutcome::Normal(state) => exec_c_stmt(&state, second, assumptions),
            outcome @ (CStmtOutcome::Return { .. }
            | CStmtOutcome::Ub(_)
            | CStmtOutcome::RuntimeError(_)) => Some(outcome),
        },
        CStmt::Return(expr) => Some(match eval_c_expr(state, expr, assumptions)? {
            CExprOutcome::Value(value) => CStmtOutcome::Return {
                value,
                state: state.clone(),
            },
            CExprOutcome::Ub(ub) => CStmtOutcome::Ub(ub),
            CExprOutcome::RuntimeError(error) => CStmtOutcome::RuntimeError(error),
        }),
        CStmt::Store { ptr, value } => Some(match eval_c_expr(state, ptr, assumptions)? {
            CExprOutcome::Value(CValue::Ptr(ptr)) => {
                match eval_c_expr(state, value, assumptions)? {
                    CExprOutcome::Value(value) => {
                        let mut state = state.clone();
                        state.memory = state.memory.store(ptr, value);
                        CStmtOutcome::Normal(state)
                    }
                    CExprOutcome::Ub(ub) => CStmtOutcome::Ub(ub),
                    CExprOutcome::RuntimeError(error) => CStmtOutcome::RuntimeError(error),
                }
            }
            CExprOutcome::Value(_) => CStmtOutcome::RuntimeError(CRuntimeError::TypeMismatch),
            CExprOutcome::Ub(ub) => CStmtOutcome::Ub(ub),
            CExprOutcome::RuntimeError(error) => CStmtOutcome::RuntimeError(error),
        }),
        CStmt::If {
            condition,
            then_branch,
            else_branch,
        } => match eval_c_expr(state, condition, assumptions)? {
            CExprOutcome::Value(CValue::Bool(condition)) => {
                let branch = if assumptions.decide(&condition)? {
                    then_branch
                } else {
                    else_branch
                };
                exec_c_stmt(state, branch, assumptions)
            }
            CExprOutcome::Value(_) => Some(CStmtOutcome::RuntimeError(CRuntimeError::TypeMismatch)),
            CExprOutcome::Ub(ub) => Some(CStmtOutcome::Ub(ub)),
            CExprOutcome::RuntimeError(error) => Some(CStmtOutcome::RuntimeError(error)),
        },
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
