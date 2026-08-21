//! Tiny C0 syntax import for the executable C model.

use std::collections::BTreeMap;

use crate::lang::{SourcePosition, character_positions};

/// Stable documentation IDs for the accepted C0 surface. This registry
/// describes source forms rather than the lowered enum variants because some
/// forms are syntax sugar and several forms share a representation.
pub const C0_PUBLIC_FORMS: &[&str] = &[
    "type.void",
    "type.int32",
    "type.uint8",
    "type.pointer",
    "type.array-parameter",
    "type.local-array",
    "type.struct-pointer",
    "declaration.function",
    "declaration.struct",
    "declaration.local",
    "statement.empty",
    "statement.block",
    "statement.assignment",
    "statement.initializer",
    "statement.call",
    "statement.call-assignment",
    "statement.return",
    "statement.if",
    "statement.while",
    "statement.for",
    "statement.store",
    "statement.malloc",
    "statement.free",
    "statement.increment",
    "statement.decrement",
    "statement.add-assign",
    "statement.subtract-assign",
    "statement.multiply-assign",
    "statement.xor-assign",
    "expression.variable",
    "expression.int-literal",
    "expression.char-literal",
    "expression.null-pointer",
    "expression.address-of",
    "expression.sizeof-struct",
    "expression.call",
    "expression.index",
    "expression.field",
    "expression.dereference",
    "expression.pointer-arithmetic",
    "operator.logical-not",
    "operator.logical-and",
    "operator.logical-or",
    "operator.equal",
    "operator.not-equal",
    "operator.less-than",
    "operator.less-equal",
    "operator.greater-than",
    "operator.greater-equal",
    "operator.add",
    "operator.subtract",
    "operator.multiply",
    "operator.divide",
    "operator.remainder",
    "operator.shift-left",
    "operator.shift-right",
    "operator.bitwise-and",
    "operator.bitwise-or",
    "operator.bitwise-xor",
    "operator.bitwise-not",
];

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct C0Function {
    return_type: C0Type,
    name: String,
    parameters: Vec<C0Parameter>,
    body: C0Statement,
    structs: BTreeMap<String, C0StructLayout>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct C0Parameter {
    c_type: C0Type,
    name: String,
    struct_name: Option<String>,
    struct_layout: Option<C0StructLayout>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct ParsedType {
    c_type: C0Type,
    struct_name: Option<String>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct C0StructLayout {
    fields: BTreeMap<String, C0StructField>,
    size_bytes: u32,
    alignment_bytes: u32,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct C0StructField {
    c_type: C0Type,
    struct_name: Option<String>,
    offset_bytes: u32,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum C0Type {
    Void,
    Int32,
    UInt8,
    Int32Pointer,
    UInt8Pointer,
    Int32Array(u32),
    UInt8Array(u32),
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum CAbi {
    Lp64,
}

impl CAbi {
    pub const SUPPORTED: Self = Self::Lp64;

    fn size_and_alignment(self, c_type: C0Type) -> (u32, u32) {
        match (self, c_type) {
            (Self::Lp64, C0Type::Void) => (0, 1),
            (Self::Lp64, C0Type::Int32) => (4, 4),
            (Self::Lp64, C0Type::UInt8) => (1, 1),
            (Self::Lp64, C0Type::Int32Pointer | C0Type::UInt8Pointer) => (8, 8),
            (Self::Lp64, C0Type::Int32Array(length)) => (length.saturating_mul(4), 4),
            (Self::Lp64, C0Type::UInt8Array(length)) => (length, 1),
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum C0Statement {
    Skip,
    Declare {
        c_type: C0Type,
        name: String,
    },
    Assign {
        name: String,
        expression: C0Expression,
    },
    CallAssign {
        target: String,
        function_name: String,
        arguments: Vec<C0Expression>,
    },
    Call {
        function_name: String,
        arguments: Vec<C0Expression>,
    },
    HeapAllocate {
        target: String,
        bytes: C0Expression,
    },
    HeapFree {
        pointer: C0Expression,
    },
    Seq(Box<C0Statement>, Box<C0Statement>),
    Return(C0Expression),
    Store {
        pointer: C0Expression,
        value: C0Expression,
        value_type: Option<C0Type>,
    },
    If {
        condition: C0Expression,
        then_branch: Box<C0Statement>,
        else_branch: Box<C0Statement>,
    },
    While {
        condition: C0Expression,
        body: Box<C0Statement>,
    },
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum C0Expression {
    Void,
    Variable(String),
    AddressOf(Box<C0Expression>),
    PointerOffsetBytes {
        pointer: Box<C0Expression>,
        bytes: u32,
    },
    Int32Literal(u32),
    UInt8Literal(u8),
    SizeOfStruct {
        name: String,
        bytes: u32,
    },
    LessThan(Box<C0Expression>, Box<C0Expression>),
    LessEqual(Box<C0Expression>, Box<C0Expression>),
    GreaterThan(Box<C0Expression>, Box<C0Expression>),
    GreaterEqual(Box<C0Expression>, Box<C0Expression>),
    Equal(Box<C0Expression>, Box<C0Expression>),
    NotEqual(Box<C0Expression>, Box<C0Expression>),
    Not(Box<C0Expression>),
    And(Box<C0Expression>, Box<C0Expression>),
    Or(Box<C0Expression>, Box<C0Expression>),
    Add(Box<C0Expression>, Box<C0Expression>),
    Subtract(Box<C0Expression>, Box<C0Expression>),
    Multiply(Box<C0Expression>, Box<C0Expression>),
    Divide(Box<C0Expression>, Box<C0Expression>),
    Remainder(Box<C0Expression>, Box<C0Expression>),
    ShiftLeft(Box<C0Expression>, Box<C0Expression>),
    ShiftRight(Box<C0Expression>, Box<C0Expression>),
    BitwiseAnd(Box<C0Expression>, Box<C0Expression>),
    BitwiseOr(Box<C0Expression>, Box<C0Expression>),
    BitwiseXor(Box<C0Expression>, Box<C0Expression>),
    BitwiseNot(Box<C0Expression>),
    Load(Box<C0Expression>),
    Field {
        pointer: Box<C0Expression>,
        field_type: C0Type,
        field_struct_name: Option<String>,
    },
    Index(Box<C0Expression>, Box<C0Expression>),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct C0SyntaxError {
    message: String,
    position: Option<SourcePosition>,
}

impl C0Function {
    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn parameters(&self) -> &[C0Parameter] {
        &self.parameters
    }

    pub fn return_type(&self) -> C0Type {
        self.return_type
    }

    pub fn body(&self) -> &C0Statement {
        &self.body
    }

    pub fn structs(&self) -> &BTreeMap<String, C0StructLayout> {
        &self.structs
    }

    pub fn body_kernel_statement(&self) -> crate::kernel::CStatement {
        self.body.to_kernel_statement()
    }

    pub fn to_kernel_function(&self) -> crate::kernel::CFunction {
        crate::kernel::c_function(
            self.return_type.to_kernel_type(),
            self.name.clone(),
            self.parameters
                .iter()
                .map(C0Parameter::to_kernel_parameter)
                .collect(),
            self.body.to_kernel_statement(),
        )
    }
}

impl C0StructLayout {
    pub fn fields(&self) -> &BTreeMap<String, C0StructField> {
        &self.fields
    }

    pub fn field(&self, name: &str) -> Option<&C0StructField> {
        self.fields.get(name)
    }

    pub fn size_bytes(&self) -> u32 {
        self.size_bytes
    }

    pub fn alignment_bytes(&self) -> u32 {
        self.alignment_bytes
    }
}

impl C0StructField {
    pub fn c_type(&self) -> C0Type {
        self.c_type
    }

    pub fn offset_bytes(&self) -> u32 {
        self.offset_bytes
    }

    pub fn struct_name(&self) -> Option<&str> {
        self.struct_name.as_deref()
    }

    pub fn byte_width(&self) -> u32 {
        self.c_type.to_kernel_type().byte_width()
    }
}

impl C0Parameter {
    pub(crate) fn new(c_type: C0Type, name: String, struct_name: Option<String>) -> Self {
        Self {
            c_type,
            name,
            struct_name,
            struct_layout: None,
        }
    }

    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn c_type(&self) -> C0Type {
        self.c_type
    }

    pub fn struct_name(&self) -> Option<&str> {
        self.struct_name.as_deref()
    }

    pub fn struct_layout(&self) -> Option<&C0StructLayout> {
        self.struct_layout.as_ref()
    }

    pub fn to_kernel_parameter(&self) -> crate::kernel::CParameter {
        crate::kernel::c_parameter(self.name.clone(), self.c_type.to_kernel_type())
    }
}

impl C0Type {
    pub fn to_kernel_type(self) -> crate::kernel::CType {
        match self {
            Self::Void => crate::kernel::CType::Void,
            Self::Int32 => crate::kernel::CType::Int32,
            Self::UInt8 => crate::kernel::CType::UInt8,
            Self::Int32Pointer => crate::kernel::CType::Int32Pointer,
            Self::UInt8Pointer => crate::kernel::CType::UInt8Pointer,
            Self::Int32Array(length) => crate::kernel::CType::Int32Array(length),
            Self::UInt8Array(length) => crate::kernel::CType::UInt8Array(length),
        }
    }
}

impl C0Statement {
    pub fn to_kernel_statement(&self) -> crate::kernel::CStatement {
        match self {
            Self::Skip => crate::kernel::c_skip(),
            Self::Declare { c_type, name } => {
                crate::kernel::c_declare(name.clone(), c_type.to_kernel_type())
            }
            Self::Assign { name, expression } => {
                crate::kernel::c_assign(name.clone(), expression.to_kernel_expression())
            }
            Self::CallAssign {
                target,
                function_name,
                arguments,
            } => crate::kernel::c_call_assign(
                target.clone(),
                function_name.clone(),
                arguments
                    .iter()
                    .map(C0Expression::to_kernel_expression)
                    .collect(),
            ),
            Self::Call {
                function_name,
                arguments,
            } => crate::kernel::c_call(
                function_name.clone(),
                arguments
                    .iter()
                    .map(C0Expression::to_kernel_expression)
                    .collect(),
            ),
            Self::HeapAllocate { target, bytes } => {
                crate::kernel::c_heap_allocate_sized(target.clone(), bytes.to_kernel_expression())
            }
            Self::HeapFree { pointer } => {
                crate::kernel::c_heap_free(pointer.to_kernel_expression())
            }
            Self::Seq(first, second) => {
                crate::kernel::c_seq(first.to_kernel_statement(), second.to_kernel_statement())
            }
            Self::Return(expression) => crate::kernel::c_return(expression.to_kernel_expression()),
            Self::Store {
                pointer,
                value,
                value_type,
            } => match value_type {
                Some(value_type) => crate::kernel::c_typed_store(
                    pointer.to_kernel_expression(),
                    value.to_kernel_expression(),
                    value_type.to_kernel_type(),
                ),
                None => crate::kernel::c_store(
                    pointer.to_kernel_expression(),
                    value.to_kernel_expression(),
                ),
            },
            Self::If {
                condition,
                then_branch,
                else_branch,
            } => crate::kernel::c_if(
                condition.to_kernel_expression(),
                then_branch.to_kernel_statement(),
                else_branch.to_kernel_statement(),
            ),
            Self::While { condition, body } => crate::kernel::c_while(
                condition.to_kernel_expression(),
                Vec::new(),
                body.to_kernel_statement(),
            ),
        }
    }
}

impl C0Expression {
    pub fn to_kernel_expression(&self) -> crate::kernel::CExpression {
        match self {
            Self::Void => crate::kernel::c_void_value(),
            Self::Variable(name) => crate::kernel::c_variable(name.clone()),
            Self::AddressOf(target) => {
                crate::kernel::CExpression::AddressOf(Box::new(target.to_kernel_expression()))
            }
            Self::PointerOffsetBytes { pointer, bytes } => {
                crate::kernel::c_pointer_offset_bytes(pointer.to_kernel_expression(), *bytes)
            }
            Self::Int32Literal(value) => crate::kernel::c_int32_literal(*value),
            Self::UInt8Literal(value) => crate::kernel::c_uint8_literal(*value),
            Self::SizeOfStruct { bytes, .. } => crate::kernel::c_int32_literal(*bytes),
            Self::LessThan(left, right) => crate::kernel::c_less_than(
                left.to_kernel_expression(),
                right.to_kernel_expression(),
            ),
            Self::LessEqual(left, right) => crate::kernel::c_less_equal(
                left.to_kernel_expression(),
                right.to_kernel_expression(),
            ),
            Self::GreaterThan(left, right) => crate::kernel::c_greater_than(
                left.to_kernel_expression(),
                right.to_kernel_expression(),
            ),
            Self::GreaterEqual(left, right) => crate::kernel::c_greater_equal(
                left.to_kernel_expression(),
                right.to_kernel_expression(),
            ),
            Self::Equal(left, right) => {
                crate::kernel::c_equal(left.to_kernel_expression(), right.to_kernel_expression())
            }
            Self::NotEqual(left, right) => crate::kernel::c_not_equal(
                left.to_kernel_expression(),
                right.to_kernel_expression(),
            ),
            Self::Not(expression) => crate::kernel::c_not(expression.to_kernel_expression()),
            Self::And(left, right) => {
                crate::kernel::c_and(left.to_kernel_expression(), right.to_kernel_expression())
            }
            Self::Or(left, right) => {
                crate::kernel::c_or(left.to_kernel_expression(), right.to_kernel_expression())
            }
            Self::Add(left, right) => {
                crate::kernel::c_add(left.to_kernel_expression(), right.to_kernel_expression())
            }
            Self::Subtract(left, right) => {
                crate::kernel::c_subtract(left.to_kernel_expression(), right.to_kernel_expression())
            }
            Self::Multiply(left, right) => {
                crate::kernel::c_multiply(left.to_kernel_expression(), right.to_kernel_expression())
            }
            Self::Divide(left, right) => {
                crate::kernel::c_divide(left.to_kernel_expression(), right.to_kernel_expression())
            }
            Self::Remainder(left, right) => crate::kernel::c_remainder(
                left.to_kernel_expression(),
                right.to_kernel_expression(),
            ),
            Self::ShiftLeft(left, right) => crate::kernel::c_shift_left(
                left.to_kernel_expression(),
                right.to_kernel_expression(),
            ),
            Self::ShiftRight(left, right) => crate::kernel::c_shift_right(
                left.to_kernel_expression(),
                right.to_kernel_expression(),
            ),
            Self::BitwiseAnd(left, right) => crate::kernel::c_bitwise_and(
                left.to_kernel_expression(),
                right.to_kernel_expression(),
            ),
            Self::BitwiseOr(left, right) => crate::kernel::c_bitwise_or(
                left.to_kernel_expression(),
                right.to_kernel_expression(),
            ),
            Self::BitwiseXor(left, right) => crate::kernel::c_bitwise_xor(
                left.to_kernel_expression(),
                right.to_kernel_expression(),
            ),
            Self::BitwiseNot(expression) => {
                crate::kernel::c_bitwise_not(expression.to_kernel_expression())
            }
            Self::Load(pointer) => crate::kernel::c_load(pointer.to_kernel_expression()),
            Self::Field {
                pointer,
                field_type,
                field_struct_name: _,
            } => crate::kernel::c_typed_load(
                pointer.to_kernel_expression(),
                field_type.to_kernel_type(),
            ),
            Self::Index(base, index) => {
                crate::kernel::c_index(base.to_kernel_expression(), index.to_kernel_expression())
            }
        }
    }
}

impl C0SyntaxError {
    fn new(message: impl Into<String>) -> Self {
        Self {
            message: message.into(),
            position: None,
        }
    }

    fn at(position: SourcePosition, message: impl Into<String>) -> Self {
        Self {
            message: message.into(),
            position: Some(position),
        }
    }

    /// Attaches `position` if the error does not already carry one.
    fn with_position(mut self, position: SourcePosition) -> Self {
        self.position.get_or_insert(position);
        self
    }

    pub fn message(&self) -> &str {
        &self.message
    }

    pub fn position(&self) -> Option<SourcePosition> {
        self.position
    }
}

impl std::fmt::Display for C0SyntaxError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.position {
            Some(position) => write!(f, "{position}: {}", self.message),
            None => write!(f, "{}", self.message),
        }
    }
}

pub fn parse_function(source: &str) -> Result<C0Function, C0SyntaxError> {
    parse_function_for_abi(source, CAbi::SUPPORTED)
}

pub fn parse_function_for_abi(source: &str, abi: CAbi) -> Result<C0Function, C0SyntaxError> {
    Parser::new(source, abi)?.parse_function()
}

fn validate_function_returns(
    statement: &C0Statement,
    return_type: C0Type,
) -> Result<(), C0SyntaxError> {
    match statement {
        C0Statement::Return(C0Expression::Void) if return_type != C0Type::Void => {
            Err(C0SyntaxError::new("non-void functions must return a value"))
        }
        C0Statement::Return(C0Expression::Void) => Ok(()),
        C0Statement::Return(_) if return_type == C0Type::Void => {
            Err(C0SyntaxError::new("void functions cannot return a value"))
        }
        C0Statement::Seq(first, second) => {
            validate_function_returns(first, return_type)?;
            validate_function_returns(second, return_type)
        }
        C0Statement::If {
            then_branch,
            else_branch,
            ..
        } => {
            validate_function_returns(then_branch, return_type)?;
            validate_function_returns(else_branch, return_type)
        }
        C0Statement::While { body, .. } => validate_function_returns(body, return_type),
        C0Statement::Skip
        | C0Statement::Declare { .. }
        | C0Statement::Assign { .. }
        | C0Statement::CallAssign { .. }
        | C0Statement::Call { .. }
        | C0Statement::HeapAllocate { .. }
        | C0Statement::HeapFree { .. }
        | C0Statement::Return(_)
        | C0Statement::Store { .. } => Ok(()),
    }
}

fn align_up(offset: u32, alignment: u32) -> Option<u32> {
    debug_assert!(alignment.is_power_of_two());
    offset
        .checked_add(alignment - 1)
        .map(|value| value & !(alignment - 1))
}

fn offset_field_pointer(base: C0Expression, offset_bytes: u32) -> C0Expression {
    if offset_bytes == 0 {
        return base;
    }
    C0Expression::PointerOffsetBytes {
        pointer: Box::new(base),
        bytes: offset_bytes,
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum Token {
    Ident(String),
    Number(String),
    CharLiteral(u8),
    LParen,
    RParen,
    LBracket,
    RBracket,
    LBrace,
    RBrace,
    Comma,
    Semicolon,
    Plus,
    PlusPlus,
    PlusEqual,
    Minus,
    Arrow,
    MinusMinus,
    MinusEqual,
    LessThan,
    LessEqual,
    ShiftLeft,
    GreaterThan,
    GreaterEqual,
    ShiftRight,
    EqualEqual,
    BangEqual,
    Bang,
    AmpAmp,
    PipePipe,
    Star,
    StarEqual,
    CaretEqual,
    Slash,
    Percent,
    Amp,
    Pipe,
    Caret,
    Tilde,
    Equal,
}

impl Token {
    /// A human-readable rendering for diagnostics, such as `` identifier `x` ``
    /// or `` `;` ``.
    fn describe(&self) -> String {
        match self {
            Self::Ident(name) => format!("identifier `{name}`"),
            Self::Number(number) => format!("number `{number}`"),
            Self::CharLiteral(value) => {
                format!("character literal `{}`", (*value as char).escape_default())
            }
            other => format!("`{}`", other.spelling()),
        }
    }

    fn spelling(&self) -> &'static str {
        match self {
            Self::Ident(_) | Self::Number(_) | Self::CharLiteral(_) => "",
            Self::LParen => "(",
            Self::RParen => ")",
            Self::LBracket => "[",
            Self::RBracket => "]",
            Self::LBrace => "{",
            Self::RBrace => "}",
            Self::Comma => ",",
            Self::Semicolon => ";",
            Self::Plus => "+",
            Self::PlusPlus => "++",
            Self::PlusEqual => "+=",
            Self::Minus => "-",
            Self::Arrow => "->",
            Self::MinusMinus => "--",
            Self::MinusEqual => "-=",
            Self::LessThan => "<",
            Self::LessEqual => "<=",
            Self::ShiftLeft => "<<",
            Self::GreaterThan => ">",
            Self::GreaterEqual => ">=",
            Self::ShiftRight => ">>",
            Self::EqualEqual => "==",
            Self::BangEqual => "!=",
            Self::Bang => "!",
            Self::AmpAmp => "&&",
            Self::PipePipe => "||",
            Self::Star => "*",
            Self::StarEqual => "*=",
            Self::CaretEqual => "^=",
            Self::Slash => "/",
            Self::Percent => "%",
            Self::Amp => "&",
            Self::Pipe => "|",
            Self::Caret => "^",
            Self::Tilde => "~",
            Self::Equal => "=",
        }
    }

    fn is_scalar_update(&self) -> bool {
        matches!(
            self,
            Self::Equal
                | Self::PlusPlus
                | Self::MinusMinus
                | Self::PlusEqual
                | Self::MinusEqual
                | Self::StarEqual
                | Self::CaretEqual
        )
    }
}

/// A captured error position; see [`Parser::error_context`].
struct ErrorContext {
    position: Option<SourcePosition>,
}

impl ErrorContext {
    fn error(&self, message: impl Into<String>) -> C0SyntaxError {
        match self.position {
            Some(position) => C0SyntaxError::at(position, message),
            None => C0SyntaxError::new(message),
        }
    }
}

struct Parser {
    tokens: Vec<Token>,
    positions: Vec<SourcePosition>,
    position: usize,
    structs: BTreeMap<String, C0StructLayout>,
    variable_structs: BTreeMap<String, String>,
    abi: CAbi,
}

impl Parser {
    fn new(source: &str, abi: CAbi) -> Result<Self, C0SyntaxError> {
        let (tokens, positions) = tokenize(source)?;
        Ok(Self {
            tokens,
            positions,
            position: 0,
            structs: BTreeMap::new(),
            variable_structs: BTreeMap::new(),
            abi,
        })
    }

    /// The source position of the next unconsumed token, or of the end of
    /// input when every token has been consumed.
    fn here(&self) -> Option<SourcePosition> {
        self.positions
            .get(self.position)
            .or_else(|| self.positions.last())
            .copied()
    }

    /// An error at the next unconsumed token.
    fn error_here(&self, message: impl Into<String>) -> C0SyntaxError {
        match self.here() {
            Some(position) => C0SyntaxError::at(position, message),
            None => C0SyntaxError::new(message),
        }
    }

    /// An error at the most recently consumed token; use after `next()` has
    /// already advanced past the offending token.
    fn error_at_previous(&self, message: impl Into<String>) -> C0SyntaxError {
        let index = self.position.saturating_sub(1);
        match self.positions.get(index).or_else(|| self.positions.last()) {
            Some(position) => C0SyntaxError::at(*position, message),
            None => C0SyntaxError::new(message),
        }
    }

    fn parse_function(mut self) -> Result<C0Function, C0SyntaxError> {
        self.parse_struct_declarations()?;
        let return_type = self.parse_type()?.c_type;
        let name = self.expect_ident("function name")?;
        self.expect(Token::LParen)?;
        let parameters = self.parse_parameters()?;
        self.expect(Token::RParen)?;
        let mut body = self.parse_block_statement()?;
        validate_function_returns(&body, return_type)?;
        if return_type == C0Type::Void {
            body = C0Statement::Seq(
                Box::new(body),
                Box::new(C0Statement::Return(C0Expression::Void)),
            );
        }
        self.expect_end(&name)?;

        Ok(C0Function {
            return_type,
            name,
            parameters,
            body,
            structs: self.structs,
        })
    }

    fn parse_struct_declarations(&mut self) -> Result<(), C0SyntaxError> {
        while self.peek_ident() == Some("struct") && self.peek_n(2) == Some(&Token::LBrace) {
            self.expect_ident_spelling("struct")?;
            let _name = self.expect_ident("struct name")?;
            let name = _name;
            self.expect(Token::LBrace)?;

            let mut fields = BTreeMap::new();
            let mut offset_bytes = 0u32;
            let mut struct_alignment = 1u32;
            while self.peek() != Some(&Token::RBrace) {
                if self.peek().is_none() {
                    return Err(self.error_here("expected struct field or `}`, got end of input"));
                }
                let field_type = self.parse_type()?;
                if !matches!(
                    field_type.c_type,
                    C0Type::Int32 | C0Type::Int32Pointer | C0Type::UInt8Pointer
                ) {
                    return Err(
                        self.error_here("struct fields currently support int32 and pointer fields")
                    );
                }
                let field_name = self.expect_ident("struct field name")?;
                self.expect(Token::Semicolon)?;
                let (field_size, field_alignment) = self.abi.size_and_alignment(field_type.c_type);
                offset_bytes = align_up(offset_bytes, field_alignment).ok_or_else(|| {
                    self.error_here(format!("struct `{name}` layout is too large"))
                })?;
                if fields
                    .insert(
                        field_name.clone(),
                        C0StructField {
                            c_type: field_type.c_type,
                            struct_name: field_type.struct_name,
                            offset_bytes,
                        },
                    )
                    .is_some()
                {
                    return Err(self
                        .error_here(format!("duplicate field `{field_name}` in struct `{name}`")));
                }
                offset_bytes = offset_bytes.checked_add(field_size).ok_or_else(|| {
                    self.error_here(format!("struct `{name}` layout is too large"))
                })?;
                struct_alignment = struct_alignment.max(field_alignment);
            }

            self.expect(Token::RBrace)?;
            self.expect(Token::Semicolon)?;

            if fields.is_empty() {
                return Err(self.error_here("struct declarations must contain at least one field"));
            }
            let size_bytes = align_up(offset_bytes, struct_alignment)
                .ok_or_else(|| self.error_here(format!("struct `{name}` layout is too large")))?;
            if self
                .structs
                .insert(
                    name.clone(),
                    C0StructLayout {
                        fields,
                        size_bytes,
                        alignment_bytes: struct_alignment,
                    },
                )
                .is_some()
            {
                return Err(self.error_here(format!("duplicate struct declaration `{name}`")));
            }
        }

        Ok(())
    }

    fn parse_parameters(&mut self) -> Result<Vec<C0Parameter>, C0SyntaxError> {
        let mut parameters = Vec::new();
        if self.peek() == Some(&Token::RParen) {
            return Ok(parameters);
        }

        loop {
            let parsed_type = self.parse_type()?;
            if parsed_type.c_type == C0Type::Void {
                return Err(self.error_here("function parameters cannot have type `void`"));
            }
            let name = self.expect_ident("parameter name")?;
            let c_type = self.parse_parameter_array_suffix(parsed_type.c_type)?;
            let struct_name = parsed_type.struct_name;
            if struct_name.is_some() {
                if c_type != parsed_type.c_type {
                    return Err(
                        self.error_here("array parameters of struct type are not supported")
                    );
                }
                self.variable_structs.insert(
                    name.clone(),
                    struct_name.clone().expect("struct_name checked above"),
                );
            }
            parameters.push(C0Parameter {
                c_type,
                name,
                struct_layout: struct_name
                    .as_ref()
                    .and_then(|name| self.structs.get(name))
                    .cloned(),
                struct_name,
            });

            if self.peek() != Some(&Token::Comma) {
                return Ok(parameters);
            }
            self.position += 1;
        }
    }

    fn parse_type(&mut self) -> Result<ParsedType, C0SyntaxError> {
        match self.next() {
            Some(Token::Ident(name)) if name == "struct" => {
                let struct_name = self.expect_ident("struct name")?;
                if self.peek() == Some(&Token::Star) {
                    self.position += 1;
                    Ok(ParsedType {
                        c_type: C0Type::Int32Pointer,
                        struct_name: Some(struct_name),
                    })
                } else {
                    Err(self.error_here("only pointer-to-struct types are supported"))
                }
            }
            Some(Token::Ident(name)) if name == "void" || name == "int32" || name == "uint8" => {
                let scalar_type = match name.as_str() {
                    "void" => C0Type::Void,
                    "int32" => C0Type::Int32,
                    "uint8" => C0Type::UInt8,
                    _ => unreachable!(),
                };
                if self.peek() == Some(&Token::Star) {
                    if scalar_type == C0Type::Void {
                        return Err(self.error_here("`void *` is not supported yet"));
                    }
                    self.position += 1;
                    Ok(ParsedType {
                        c_type: match scalar_type {
                            C0Type::Int32 => C0Type::Int32Pointer,
                            C0Type::UInt8 => C0Type::UInt8Pointer,
                            _ => unreachable!("scalar type should not be aggregate"),
                        },
                        struct_name: None,
                    })
                } else {
                    Ok(ParsedType {
                        c_type: scalar_type,
                        struct_name: None,
                    })
                }
            }
            Some(token) => Err(self.error_at_previous(format!(
                "expected type `void`, `int32`, `uint8`, or `struct`, got {}",
                token.describe()
            ))),
            None => Err(self.error_here(
                "expected type `void`, `int32`, `uint8`, or `struct`, got end of input",
            )),
        }
    }

    fn parse_parameter_array_suffix(&mut self, c_type: C0Type) -> Result<C0Type, C0SyntaxError> {
        if self.peek() != Some(&Token::LBracket) {
            return Ok(c_type);
        }
        let pointer_type = match c_type {
            C0Type::Int32 => C0Type::Int32Pointer,
            C0Type::UInt8 => C0Type::UInt8Pointer,
            _ => {
                return Err(self.error_here("only scalar array parameters are supported"));
            }
        };

        if !matches!(c_type, C0Type::Int32 | C0Type::UInt8) {
            return Err(self.error_here("only scalar array parameters are supported"));
        }

        self.position += 1;
        if matches!(self.peek(), Some(Token::Number(_))) {
            self.position += 1;
        }
        self.expect(Token::RBracket)?;
        Ok(pointer_type)
    }

    fn parse_local_array_suffix(&mut self, c_type: C0Type) -> Result<C0Type, C0SyntaxError> {
        if self.peek() != Some(&Token::LBracket) {
            return Ok(c_type);
        }
        let (array_type, element_width, element_name): (fn(u32) -> C0Type, u32, &str) = match c_type
        {
            C0Type::Int32 => (C0Type::Int32Array, 4u32, "int32"),
            C0Type::UInt8 => (C0Type::UInt8Array, 1u32, "uint8"),
            _ => return Err(self.error_here("only scalar local arrays are supported")),
        };

        self.position += 1;
        let length = match self.next() {
            Some(Token::Number(number)) => {
                let length = number.parse::<u32>().map_err(|_| {
                    self.error_here(format!("array length `{number}` is out of range"))
                })?;
                if length == 0 {
                    return Err(self.error_here("local arrays must have positive length"));
                }
                if length.checked_mul(element_width).is_none() {
                    return Err(self.error_here(format!(
                        "array length `{number}` is too large for {element_name} elements"
                    )));
                }
                length
            }
            Some(token) => {
                return Err(self.error_at_previous(format!(
                    "expected local array length, got {}",
                    token.describe()
                )));
            }
            None => {
                return Err(self.error_here("expected local array length, got end of input"));
            }
        };
        self.expect(Token::RBracket)?;
        Ok(array_type(length))
    }

    fn parse_block_statement(&mut self) -> Result<C0Statement, C0SyntaxError> {
        self.expect(Token::LBrace)?;
        let mut statements = Vec::new();
        while self.peek() != Some(&Token::RBrace) {
            if self.peek().is_none() {
                return Err(self.error_here("expected statement or `}`, got end of input"));
            }
            statements.push(self.parse_statement()?);
        }
        self.expect(Token::RBrace)?;

        let mut statements = statements.into_iter();
        let Some(mut statement) = statements.next() else {
            return Ok(C0Statement::Skip);
        };
        for next in statements {
            statement = C0Statement::Seq(Box::new(statement), Box::new(next));
        }

        Ok(statement)
    }

    fn parse_statement(&mut self) -> Result<C0Statement, C0SyntaxError> {
        match self.peek() {
            Some(Token::Semicolon) => {
                self.position += 1;
                Ok(C0Statement::Skip)
            }
            Some(Token::Star) => {
                self.position += 1;
                let pointer = self.parse_unary()?;
                self.expect(Token::Equal)?;
                let value = self.parse_expression()?;
                self.expect(Token::Semicolon)?;
                Ok(C0Statement::Store {
                    pointer,
                    value,
                    value_type: None,
                })
            }
            Some(Token::Ident(_)) if self.peek_next() == Some(&Token::LBracket) => {
                let pointer = self.parse_indexed_lvalue_pointer()?;
                self.expect(Token::Equal)?;
                let value = self.parse_expression()?;
                self.expect(Token::Semicolon)?;
                Ok(C0Statement::Store {
                    pointer,
                    value,
                    value_type: None,
                })
            }
            Some(Token::Ident(_)) if self.peek_next() == Some(&Token::Arrow) => {
                let (pointer, value_type) = self.parse_postfix_lvalue_pointer()?;
                self.expect(Token::Equal)?;
                let value = self.parse_expression()?;
                self.expect(Token::Semicolon)?;
                Ok(C0Statement::Store {
                    pointer,
                    value,
                    value_type,
                })
            }
            Some(Token::Ident(_)) if self.peek_next().is_some_and(Token::is_scalar_update) => {
                let statement = self.parse_scalar_update_statement("statement")?;
                self.expect(Token::Semicolon)?;
                Ok(statement)
            }
            Some(Token::Ident(name)) if name == "int32" || name == "uint8" || name == "struct" => {
                let parsed_type = self.parse_type()?;
                let name = self.expect_ident("local name")?;
                let c_type = self.parse_local_array_suffix(parsed_type.c_type)?;
                if parsed_type.struct_name.is_some() {
                    if c_type != parsed_type.c_type {
                        return Err(
                            self.error_here("local arrays of struct type are not supported")
                        );
                    }
                    self.variable_structs.insert(
                        name.clone(),
                        parsed_type.struct_name.expect("struct_name checked above"),
                    );
                }
                let declaration = C0Statement::Declare {
                    c_type,
                    name: name.clone(),
                };
                if self.peek() == Some(&Token::Equal) {
                    if matches!(c_type, C0Type::Int32Array(_) | C0Type::UInt8Array(_)) {
                        return Err(self.error_here("local array initializers are not supported"));
                    }
                    self.position += 1;
                    if matches!(self.peek(), Some(Token::Ident(_)))
                        && self.peek_next() == Some(&Token::LParen)
                    {
                        let function_name = self.expect_ident("function name")?;
                        let arguments = self.parse_call_arguments()?;
                        let call =
                            self.call_assignment_statement(name.clone(), function_name, arguments)?;
                        self.expect(Token::Semicolon)?;
                        return Ok(C0Statement::Seq(Box::new(declaration), Box::new(call)));
                    }
                    let expression = self.parse_expression()?;
                    self.expect(Token::Semicolon)?;
                    return Ok(C0Statement::Seq(
                        Box::new(declaration),
                        Box::new(C0Statement::Assign { name, expression }),
                    ));
                }
                self.expect(Token::Semicolon)?;
                Ok(declaration)
            }
            Some(Token::Ident(_)) => match self.peek_ident() {
                Some("return") => {
                    self.position += 1;
                    let expression = if self.peek() == Some(&Token::Semicolon) {
                        C0Expression::Void
                    } else {
                        self.parse_expression()?
                    };
                    self.expect(Token::Semicolon)?;
                    Ok(C0Statement::Return(expression))
                }
                Some("if") => {
                    self.position += 1;
                    self.expect(Token::LParen)?;
                    let condition = self.parse_expression()?;
                    self.expect(Token::RParen)?;
                    let then_branch = Box::new(self.parse_block_statement()?);
                    let else_branch = if self.peek_ident() == Some("else") {
                        self.position += 1;
                        Box::new(self.parse_block_statement()?)
                    } else {
                        Box::new(C0Statement::Skip)
                    };
                    Ok(C0Statement::If {
                        condition,
                        then_branch,
                        else_branch,
                    })
                }
                Some("while") => {
                    self.position += 1;
                    self.expect(Token::LParen)?;
                    let condition = self.parse_expression()?;
                    self.expect(Token::RParen)?;
                    let body = Box::new(self.parse_block_statement()?);
                    Ok(C0Statement::While { condition, body })
                }
                Some("for") => {
                    self.position += 1;
                    self.expect(Token::LParen)?;
                    let init = self.parse_for_initializer()?;
                    self.expect(Token::Semicolon)?;
                    let condition = self.parse_expression()?;
                    self.expect(Token::Semicolon)?;
                    let step = self.parse_scalar_update_statement("for-loop step")?;
                    self.expect(Token::RParen)?;
                    let body = self.parse_block_statement()?;
                    let body = C0Statement::Seq(Box::new(body), Box::new(step));
                    Ok(C0Statement::Seq(
                        Box::new(init),
                        Box::new(C0Statement::While {
                            condition,
                            body: Box::new(body),
                        }),
                    ))
                }
                Some(other) => {
                    if other == "free" && self.peek_next() == Some(&Token::LParen) {
                        self.position += 1;
                        let arguments = self.parse_call_arguments()?;
                        self.expect(Token::Semicolon)?;
                        let [pointer] = arguments.as_slice() else {
                            return Err(self.error_here(format!(
                                "`free` expects one pointer argument, got {}",
                                arguments.len()
                            )));
                        };
                        Ok(C0Statement::HeapFree {
                            pointer: pointer.clone(),
                        })
                    } else if self.peek_next() == Some(&Token::LParen) {
                        let function_name = self.expect_ident("function name")?;
                        if function_name == "malloc" {
                            return Err(self.error_here(
                                "the fixed-size `malloc` result may not be discarded",
                            ));
                        }
                        let arguments = self.parse_call_arguments()?;
                        self.expect(Token::Semicolon)?;
                        Ok(C0Statement::Call {
                            function_name,
                            arguments,
                        })
                    } else {
                        Err(self
                            .error_here(format!("expected statement, got identifier `{other}`")))
                    }
                }
                None => unreachable!("identifier token should have identifier spelling"),
            },
            Some(token) => {
                Err(self.error_here(format!("expected statement, got {}", token.describe())))
            }
            None => Err(self.error_here("expected statement, got end of input")),
        }
    }

    fn parse_for_initializer(&mut self) -> Result<C0Statement, C0SyntaxError> {
        if matches!(self.peek_ident(), Some("int32" | "uint8")) {
            let parsed_type = self.parse_type()?;
            let name = self.expect_ident("for-loop local name")?;
            if self.peek() != Some(&Token::Equal) {
                return Err(self.error_here("for-loop declarations require an initializer"));
            }
            self.position += 1;
            let expression = self.parse_expression()?;
            return Ok(C0Statement::Seq(
                Box::new(C0Statement::Declare {
                    c_type: parsed_type.c_type,
                    name: name.clone(),
                }),
                Box::new(C0Statement::Assign { name, expression }),
            ));
        }
        let Some(Token::Ident(name)) = self.next() else {
            return Err(
                self.error_here("expected assignment target in for-loop initializer".to_string())
            );
        };
        self.expect(Token::Equal)?;
        let expression = self.parse_expression()?;
        Ok(C0Statement::Assign { name, expression })
    }

    fn parse_scalar_update_statement(
        &mut self,
        context: &str,
    ) -> Result<C0Statement, C0SyntaxError> {
        let name = match self.next() {
            Some(Token::Ident(name)) if name != "int32" && name != "uint8" => name,
            Some(Token::Ident(name)) => {
                return Err(self.error_here(format!(
                    "expected scalar update target in {context}, got `{name}`"
                )));
            }
            Some(token) => {
                return Err(self.error_at_previous(format!(
                    "expected scalar update target in {context}, got {}",
                    token.describe()
                )));
            }
            None => {
                return Err(self.error_here(format!(
                    "expected scalar update target in {context}, got end of input"
                )));
            }
        };
        let operator = self.next().ok_or_else(|| {
            self.error_here(format!(
                "expected scalar update operator in {context}, got end of input"
            ))
        })?;
        let expression = match operator {
            Token::Equal => {
                if matches!(self.peek(), Some(Token::Ident(_)))
                    && self.peek_next() == Some(&Token::LParen)
                {
                    let function_name = self.expect_ident("function name")?;
                    let arguments = self.parse_call_arguments()?;
                    return self.call_assignment_statement(name, function_name, arguments);
                }
                self.parse_expression()?
            }
            Token::PlusPlus => C0Expression::Add(
                Box::new(C0Expression::Variable(name.clone())),
                Box::new(C0Expression::Int32Literal(1)),
            ),
            Token::MinusMinus => C0Expression::Subtract(
                Box::new(C0Expression::Variable(name.clone())),
                Box::new(C0Expression::Int32Literal(1)),
            ),
            Token::PlusEqual => C0Expression::Add(
                Box::new(C0Expression::Variable(name.clone())),
                Box::new(self.parse_expression()?),
            ),
            Token::MinusEqual => C0Expression::Subtract(
                Box::new(C0Expression::Variable(name.clone())),
                Box::new(self.parse_expression()?),
            ),
            Token::StarEqual => C0Expression::Multiply(
                Box::new(C0Expression::Variable(name.clone())),
                Box::new(self.parse_expression()?),
            ),
            Token::CaretEqual => C0Expression::BitwiseXor(
                Box::new(C0Expression::Variable(name.clone())),
                Box::new(self.parse_expression()?),
            ),
            token => {
                return Err(self.error_here(format!(
                    "expected scalar update operator in {context}, got {}",
                    token.describe()
                )));
            }
        };
        Ok(C0Statement::Assign { name, expression })
    }

    fn call_assignment_statement(
        &self,
        target: String,
        function_name: String,
        arguments: Vec<C0Expression>,
    ) -> Result<C0Statement, C0SyntaxError> {
        if function_name != "malloc" {
            return Ok(C0Statement::CallAssign {
                target,
                function_name,
                arguments,
            });
        }
        let [bytes] = arguments.as_slice() else {
            return Err(self.error_here(format!(
                "`malloc` expects one byte-count argument, got {}",
                arguments.len()
            )));
        };
        if let Some(target_struct) = self.variable_structs.get(&target) {
            let C0Expression::SizeOfStruct { name, .. } = bytes else {
                return Err(self.error_here(format!(
                    "allocation of `struct {target_struct}` currently requires `sizeof(struct {target_struct})`"
                )));
            };
            if name != target_struct {
                return Err(self.error_here(format!(
                    "`malloc(sizeof(struct {name}))` does not match target type `struct {target_struct} *`"
                )));
            }
        }
        Ok(C0Statement::HeapAllocate {
            target,
            bytes: bytes.clone(),
        })
    }

    fn parse_expression(&mut self) -> Result<C0Expression, C0SyntaxError> {
        self.parse_logical_or()
    }

    fn parse_call_arguments(&mut self) -> Result<Vec<C0Expression>, C0SyntaxError> {
        self.expect(Token::LParen)?;
        let mut arguments = Vec::new();
        if self.peek() == Some(&Token::RParen) {
            self.position += 1;
            return Ok(arguments);
        }

        loop {
            arguments.push(self.parse_expression()?);
            match self.peek() {
                Some(Token::Comma) => {
                    self.position += 1;
                }
                Some(Token::RParen) => {
                    self.position += 1;
                    return Ok(arguments);
                }
                Some(token) => {
                    return Err(self.error_at_previous(format!(
                        "expected `,` or `)`, got {}",
                        token.describe()
                    )));
                }
                None => {
                    return Err(self.error_here("expected `,` or `)`, got end of input"));
                }
            }
        }
    }

    fn parse_logical_or(&mut self) -> Result<C0Expression, C0SyntaxError> {
        let mut expression = self.parse_logical_and()?;
        loop {
            expression = match self.peek() {
                Some(Token::PipePipe) => {
                    self.position += 1;
                    let right = self.parse_logical_and()?;
                    C0Expression::Or(Box::new(expression), Box::new(right))
                }
                _ => return Ok(expression),
            };
        }
    }

    fn parse_logical_and(&mut self) -> Result<C0Expression, C0SyntaxError> {
        let mut expression = self.parse_bitwise_or()?;
        loop {
            expression = match self.peek() {
                Some(Token::AmpAmp) => {
                    self.position += 1;
                    let right = self.parse_bitwise_or()?;
                    C0Expression::And(Box::new(expression), Box::new(right))
                }
                _ => return Ok(expression),
            };
        }
    }

    fn parse_bitwise_or(&mut self) -> Result<C0Expression, C0SyntaxError> {
        let mut expression = self.parse_bitwise_xor()?;
        while self.peek() == Some(&Token::Pipe) {
            self.position += 1;
            let right = self.parse_bitwise_xor()?;
            expression = C0Expression::BitwiseOr(Box::new(expression), Box::new(right));
        }
        Ok(expression)
    }

    fn parse_bitwise_xor(&mut self) -> Result<C0Expression, C0SyntaxError> {
        let mut expression = self.parse_bitwise_and()?;
        while self.peek() == Some(&Token::Caret) {
            self.position += 1;
            let right = self.parse_bitwise_and()?;
            expression = C0Expression::BitwiseXor(Box::new(expression), Box::new(right));
        }
        Ok(expression)
    }

    fn parse_bitwise_and(&mut self) -> Result<C0Expression, C0SyntaxError> {
        let mut expression = self.parse_compare()?;
        while self.peek() == Some(&Token::Amp) {
            self.position += 1;
            let right = self.parse_compare()?;
            expression = C0Expression::BitwiseAnd(Box::new(expression), Box::new(right));
        }
        Ok(expression)
    }

    fn parse_compare(&mut self) -> Result<C0Expression, C0SyntaxError> {
        let mut expression = self.parse_shift()?;
        loop {
            expression = match self.peek() {
                Some(Token::LessThan) => {
                    self.position += 1;
                    let right = self.parse_shift()?;
                    C0Expression::LessThan(Box::new(expression), Box::new(right))
                }
                Some(Token::LessEqual) => {
                    self.position += 1;
                    let right = self.parse_shift()?;
                    C0Expression::LessEqual(Box::new(expression), Box::new(right))
                }
                Some(Token::GreaterThan) => {
                    self.position += 1;
                    let right = self.parse_shift()?;
                    C0Expression::GreaterThan(Box::new(expression), Box::new(right))
                }
                Some(Token::GreaterEqual) => {
                    self.position += 1;
                    let right = self.parse_shift()?;
                    C0Expression::GreaterEqual(Box::new(expression), Box::new(right))
                }
                Some(Token::EqualEqual) => {
                    self.position += 1;
                    let right = self.parse_shift()?;
                    C0Expression::Equal(Box::new(expression), Box::new(right))
                }
                Some(Token::BangEqual) => {
                    self.position += 1;
                    let right = self.parse_shift()?;
                    C0Expression::NotEqual(Box::new(expression), Box::new(right))
                }
                _ => return Ok(expression),
            };
        }
    }

    fn parse_shift(&mut self) -> Result<C0Expression, C0SyntaxError> {
        let mut expression = self.parse_add()?;
        loop {
            expression = match self.peek() {
                Some(Token::ShiftLeft) => {
                    self.position += 1;
                    let right = self.parse_add()?;
                    C0Expression::ShiftLeft(Box::new(expression), Box::new(right))
                }
                Some(Token::ShiftRight) => {
                    self.position += 1;
                    let right = self.parse_add()?;
                    C0Expression::ShiftRight(Box::new(expression), Box::new(right))
                }
                _ => return Ok(expression),
            };
        }
    }

    fn parse_add(&mut self) -> Result<C0Expression, C0SyntaxError> {
        let mut expression = self.parse_multiply()?;
        loop {
            expression = match self.peek() {
                Some(Token::Plus) => {
                    self.position += 1;
                    let right = self.parse_multiply()?;
                    C0Expression::Add(Box::new(expression), Box::new(right))
                }
                Some(Token::Minus) => {
                    self.position += 1;
                    let right = self.parse_multiply()?;
                    C0Expression::Subtract(Box::new(expression), Box::new(right))
                }
                _ => return Ok(expression),
            };
        }
    }

    fn parse_multiply(&mut self) -> Result<C0Expression, C0SyntaxError> {
        let mut expression = self.parse_unary()?;
        loop {
            let Some(operator) = self.peek() else {
                break;
            };
            let constructor = match operator {
                Token::Star => C0Expression::Multiply,
                Token::Slash => C0Expression::Divide,
                Token::Percent => C0Expression::Remainder,
                _ => break,
            };
            self.position += 1;
            let right = self.parse_unary()?;
            expression = constructor(Box::new(expression), Box::new(right));
        }
        Ok(expression)
    }

    fn parse_unary(&mut self) -> Result<C0Expression, C0SyntaxError> {
        if self.peek() == Some(&Token::Minus) {
            self.position += 1;
            if let Some(Token::Number(number)) = self.peek().cloned() {
                self.position += 1;
                let magnitude = number.parse::<u64>().map_err(|_| {
                    self.error_here(format!(
                        "negative int32 literal `-{number}` is out of range"
                    ))
                })?;
                if magnitude > (i32::MAX as u64) + 1 {
                    return Err(self.error_here(format!(
                        "negative int32 literal `-{number}` is out of range"
                    )));
                }
                let value = (-(magnitude as i64) as i32) as u32;
                return Ok(C0Expression::Int32Literal(value));
            }
            return Ok(C0Expression::Subtract(
                Box::new(C0Expression::Int32Literal(0)),
                Box::new(self.parse_unary()?),
            ));
        }

        if self.peek() == Some(&Token::Star) {
            self.position += 1;
            return Ok(C0Expression::Load(Box::new(self.parse_unary()?)));
        }

        if self.peek() == Some(&Token::Amp) {
            self.position += 1;
            return Ok(C0Expression::AddressOf(Box::new(self.parse_unary()?)));
        }

        if self.peek() == Some(&Token::Bang) {
            self.position += 1;
            return Ok(C0Expression::Not(Box::new(self.parse_unary()?)));
        }

        if self.peek() == Some(&Token::Tilde) {
            self.position += 1;
            return Ok(C0Expression::BitwiseNot(Box::new(self.parse_unary()?)));
        }

        self.parse_postfix()
    }

    fn parse_postfix(&mut self) -> Result<C0Expression, C0SyntaxError> {
        let mut expression = self.parse_primary()?;
        loop {
            match self.peek() {
                Some(Token::LBracket) => {
                    self.position += 1;
                    let index = self.parse_expression()?;
                    self.expect(Token::RBracket)?;
                    expression = C0Expression::Index(Box::new(expression), Box::new(index));
                }
                Some(Token::Arrow) => {
                    self.position += 1;
                    let field_name = self.expect_ident("field name")?;
                    let (pointer, field_type, field_struct_name) =
                        self.resolve_field_access(&expression, &field_name)?;
                    expression = C0Expression::Field {
                        pointer: Box::new(pointer),
                        field_type,
                        field_struct_name,
                    };
                }
                _ => return Ok(expression),
            }
        }
    }

    fn parse_indexed_lvalue_pointer(&mut self) -> Result<C0Expression, C0SyntaxError> {
        let mut base = self.parse_primary()?;
        loop {
            self.expect(Token::LBracket)?;
            let index = self.parse_expression()?;
            self.expect(Token::RBracket)?;
            if self.peek() != Some(&Token::LBracket) {
                return Ok(C0Expression::Add(Box::new(base), Box::new(index)));
            }
            base = C0Expression::Index(Box::new(base), Box::new(index));
        }
    }

    fn parse_postfix_lvalue_pointer(
        &mut self,
    ) -> Result<(C0Expression, Option<C0Type>), C0SyntaxError> {
        match self.parse_postfix()? {
            C0Expression::Field {
                pointer,
                field_type,
                ..
            } => Ok((*pointer, Some(field_type))),
            C0Expression::Index(base, index) => Ok((C0Expression::Add(base, index), None)),
            expression => Err(self.error_here(format!(
                "expected field or indexed assignment target, got {expression:?}"
            ))),
        }
    }

    fn resolve_field_access(
        &self,
        base: &C0Expression,
        field_name: &str,
    ) -> Result<(C0Expression, C0Type, Option<String>), C0SyntaxError> {
        let struct_name = match base {
            C0Expression::Variable(base_name) => self.variable_structs.get(base_name),
            C0Expression::Field {
                field_struct_name, ..
            } => field_struct_name.as_ref(),
            _ => None,
        };
        let struct_name = struct_name.ok_or_else(|| {
            self.error_here(format!(
                "cannot access field `{field_name}` through a non-struct-pointer expression"
            ))
        })?;
        let layout = self.structs.get(struct_name).ok_or_else(|| {
            self.error_here(format!("unknown struct declaration `{struct_name}`"))
        })?;
        let field = layout.fields.get(field_name).ok_or_else(|| {
            self.error_here(format!(
                "struct `{struct_name}` has no field `{field_name}`"
            ))
        })?;
        Ok((
            offset_field_pointer(base.clone(), field.offset_bytes),
            field.c_type,
            field.struct_name.clone(),
        ))
    }

    fn parse_primary(&mut self) -> Result<C0Expression, C0SyntaxError> {
        if self.peek_ident() == Some("sizeof") && self.peek_next() == Some(&Token::LParen) {
            self.position += 2;
            self.expect_ident_spelling("struct")?;
            let name = self.expect_ident("struct name")?;
            self.expect(Token::RParen)?;
            let bytes = self
                .structs
                .get(&name)
                .ok_or_else(|| self.error_here(format!("unknown struct declaration `{name}`")))?
                .size_bytes;
            return Ok(C0Expression::SizeOfStruct { name, bytes });
        }
        let at = self.error_context();
        match self.next() {
            Some(Token::Ident(name)) => Ok(C0Expression::Variable(name)),
            Some(Token::Number(number)) => {
                let value = number
                    .parse::<u32>()
                    .map_err(|_| at.error(format!("int32 literal `{number}` is out of range")))?;
                if value > i32::MAX as u32 {
                    return Err(at.error(format!("int32 literal `{number}` is out of range")));
                }
                Ok(C0Expression::Int32Literal(value))
            }
            Some(Token::CharLiteral(value)) => Ok(C0Expression::UInt8Literal(value)),
            Some(Token::LParen) => {
                let expression = self.parse_expression()?;
                self.expect(Token::RParen)?;
                Ok(expression)
            }
            Some(token) => Err(at.error(format!("expected expression, got {}", token.describe()))),
            None => Err(at.error("expected expression, got end of input")),
        }
    }

    fn expect(&mut self, expected: Token) -> Result<(), C0SyntaxError> {
        let at = self.error_context();
        match self.next() {
            Some(token) if token == expected => Ok(()),
            Some(token) => Err(at.error(format!(
                "expected {}, got {}",
                expected.describe(),
                token.describe()
            ))),
            None => Err(at.error(format!(
                "expected {}, got end of input",
                expected.describe()
            ))),
        }
    }

    fn expect_ident(&mut self, label: &str) -> Result<String, C0SyntaxError> {
        let at = self.error_context();
        match self.next() {
            Some(Token::Ident(name)) => Ok(name),
            Some(token) => Err(at.error(format!("expected {label}, got {}", token.describe()))),
            None => Err(at.error(format!("expected {label}, got end of input"))),
        }
    }

    fn expect_ident_spelling(&mut self, expected: &str) -> Result<(), C0SyntaxError> {
        let at = self.error_context();
        match self.next() {
            Some(Token::Ident(name)) if name == expected => Ok(()),
            Some(token) => {
                Err(at.error(format!("expected `{expected}`, got {}", token.describe())))
            }
            None => Err(at.error(format!("expected `{expected}`, got end of input"))),
        }
    }

    /// Captures the position of the next unconsumed token so an error can
    /// still point at it after the token is consumed.
    fn error_context(&self) -> ErrorContext {
        ErrorContext {
            position: self.here(),
        }
    }

    /// `function_name` is the function just parsed, used to point at where the
    /// trailing tokens begin.
    fn expect_end(&self, function_name: &str) -> Result<(), C0SyntaxError> {
        if self.position == self.tokens.len() {
            Ok(())
        } else {
            // Trailing tokens after a complete function almost always mean a
            // second function definition: name that restriction instead of
            // reporting a bare "expected end of input".
            Err(self.error_here(format!(
                "each C source file holds exactly one function; \
                 put the next definition in its own file and add another \
                 `verifying` line (got {} after the end of `{function_name}`)",
                self.tokens[self.position].describe(),
            )))
        }
    }

    fn peek(&self) -> Option<&Token> {
        self.tokens.get(self.position)
    }

    fn peek_next(&self) -> Option<&Token> {
        self.tokens.get(self.position + 1)
    }

    fn peek_n(&self, offset: usize) -> Option<&Token> {
        self.tokens.get(self.position + offset)
    }

    fn peek_ident(&self) -> Option<&str> {
        match self.peek() {
            Some(Token::Ident(name)) => Some(name),
            _ => None,
        }
    }

    fn next(&mut self) -> Option<Token> {
        let token = self.tokens.get(self.position).cloned();
        if token.is_some() {
            self.position += 1;
        }
        token
    }
}

fn tokenize(source: &str) -> Result<(Vec<Token>, Vec<SourcePosition>), C0SyntaxError> {
    let chars = source.chars().collect::<Vec<_>>();
    let char_positions = character_positions(source);
    let mut tokens = Vec::new();
    let mut positions = Vec::new();
    let mut index = 0;

    while index < chars.len() {
        let ch = chars[index];
        let position = char_positions[index];
        if ch.is_whitespace() {
            index += 1;
            continue;
        }

        if ch == '/' && chars.get(index + 1) == Some(&'/') {
            index += 2;
            while index < chars.len() && chars[index] != '\n' {
                index += 1;
            }
            continue;
        }

        if ch == '/' && chars.get(index + 1) == Some(&'*') {
            index += 2;
            while index + 1 < chars.len() && !(chars[index] == '*' && chars[index + 1] == '/') {
                index += 1;
            }
            if index + 1 == chars.len() {
                return Err(C0SyntaxError::at(position, "unterminated block comment"));
            }
            index += 2;
            continue;
        }

        if is_ident_start(ch) {
            let start = index;
            index += 1;
            while index < chars.len() && is_ident_continue(chars[index]) {
                index += 1;
            }
            tokens.push(Token::Ident(chars[start..index].iter().collect()));
            positions.push(position);
            continue;
        }

        if ch.is_ascii_digit() {
            let start = index;
            index += 1;
            while index < chars.len() && chars[index].is_ascii_digit() {
                index += 1;
            }
            tokens.push(Token::Number(chars[start..index].iter().collect()));
            positions.push(position);
            continue;
        }

        if ch == '\'' {
            let (value, next_index) =
                parse_char_literal(&chars, index).map_err(|error| error.with_position(position))?;
            tokens.push(Token::CharLiteral(value));
            positions.push(position);
            index = next_index;
            continue;
        }

        if index + 1 < chars.len() {
            let token = match (ch, chars[index + 1]) {
                ('=', '=') => Some(Token::EqualEqual),
                ('!', '=') => Some(Token::BangEqual),
                ('&', '&') => Some(Token::AmpAmp),
                ('|', '|') => Some(Token::PipePipe),
                ('<', '<') => Some(Token::ShiftLeft),
                ('>', '>') => Some(Token::ShiftRight),
                ('<', '=') => Some(Token::LessEqual),
                ('>', '=') => Some(Token::GreaterEqual),
                ('-', '>') => Some(Token::Arrow),
                ('+', '+') => Some(Token::PlusPlus),
                ('+', '=') => Some(Token::PlusEqual),
                ('-', '-') => Some(Token::MinusMinus),
                ('-', '=') => Some(Token::MinusEqual),
                ('*', '=') => Some(Token::StarEqual),
                ('^', '=') => Some(Token::CaretEqual),
                _ => None,
            };
            if let Some(token) = token {
                tokens.push(token);
                positions.push(position);
                index += 2;
                continue;
            }
        }

        let token = match ch {
            '(' => Token::LParen,
            ')' => Token::RParen,
            '[' => Token::LBracket,
            ']' => Token::RBracket,
            '{' => Token::LBrace,
            '}' => Token::RBrace,
            ',' => Token::Comma,
            ';' => Token::Semicolon,
            '+' => Token::Plus,
            '-' => Token::Minus,
            '<' => Token::LessThan,
            '>' => Token::GreaterThan,
            '*' => Token::Star,
            '/' => Token::Slash,
            '%' => Token::Percent,
            '&' => Token::Amp,
            '|' => Token::Pipe,
            '^' => Token::Caret,
            '~' => Token::Tilde,
            '!' => Token::Bang,
            '=' => Token::Equal,
            _ => {
                return Err(C0SyntaxError::at(
                    position,
                    format!("unexpected character `{ch}`"),
                ));
            }
        };
        tokens.push(token);
        positions.push(position);
        index += 1;
    }

    Ok((tokens, positions))
}

fn parse_char_literal(chars: &[char], start: usize) -> Result<(u8, usize), C0SyntaxError> {
    let Some(first) = chars.get(start + 1).copied() else {
        return Err(C0SyntaxError::new("unterminated character literal"));
    };
    let (value, end) = if first == '\\' {
        let Some(escaped) = chars.get(start + 2).copied() else {
            return Err(C0SyntaxError::new("unterminated character literal"));
        };
        let value = match escaped {
            'n' => b'\n',
            'r' => b'\r',
            't' => b'\t',
            '0' => b'\0',
            '\\' => b'\\',
            '\'' => b'\'',
            '"' => b'"',
            other => {
                return Err(C0SyntaxError::new(format!(
                    "unsupported character escape `\\{other}`"
                )));
            }
        };
        (value, start + 3)
    } else {
        if !first.is_ascii() {
            return Err(C0SyntaxError::new(
                "only ASCII character literals are supported",
            ));
        }
        (first as u8, start + 2)
    };

    if chars.get(end) != Some(&'\'') {
        return Err(C0SyntaxError::new(
            "character literals must contain exactly one byte",
        ));
    }

    Ok((value, end + 1))
}

fn is_ident_start(ch: char) -> bool {
    ch.is_ascii_alphabetic() || ch == '_'
}

fn is_ident_continue(ch: char) -> bool {
    ch.is_ascii_alphanumeric() || ch == '_'
}
