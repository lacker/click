//! Tiny C0 syntax import for the executable C model.

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct C0Function {
    return_type: C0Type,
    name: String,
    parameters: Vec<C0Parameter>,
    body: C0Statement,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct C0Parameter {
    c_type: C0Type,
    name: String,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum C0Type {
    Int32,
    UInt8,
    Int32Pointer,
    UInt8Pointer,
    Int32Array(u32),
    UInt8Array(u32),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum C0Statement {
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
    Seq(Box<C0Statement>, Box<C0Statement>),
    Return(C0Expression),
    Store {
        pointer: C0Expression,
        value: C0Expression,
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
    Variable(String),
    AddressOf(Box<C0Expression>),
    Int32Literal(u32),
    UInt8Literal(u8),
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
    Index(Box<C0Expression>, Box<C0Expression>),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct C0SyntaxError {
    message: String,
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

impl C0Parameter {
    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn c_type(&self) -> C0Type {
        self.c_type
    }

    pub fn to_kernel_parameter(&self) -> crate::kernel::CParameter {
        crate::kernel::c_parameter(self.name.clone(), self.c_type.to_kernel_type())
    }
}

impl C0Type {
    pub fn to_kernel_type(self) -> crate::kernel::CType {
        match self {
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
            Self::Seq(first, second) => {
                crate::kernel::c_seq(first.to_kernel_statement(), second.to_kernel_statement())
            }
            Self::Return(expression) => crate::kernel::c_return(expression.to_kernel_expression()),
            Self::Store { pointer, value } => {
                crate::kernel::c_store(pointer.to_kernel_expression(), value.to_kernel_expression())
            }
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
            Self::Variable(name) => crate::kernel::c_variable(name.clone()),
            Self::AddressOf(target) => {
                crate::kernel::CExpression::AddressOf(Box::new(target.to_kernel_expression()))
            }
            Self::Int32Literal(value) => crate::kernel::c_int32_literal(*value),
            Self::UInt8Literal(value) => crate::kernel::c_uint8_literal(*value),
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
        }
    }

    pub fn message(&self) -> &str {
        &self.message
    }
}

pub fn parse_function(source: &str) -> Result<C0Function, C0SyntaxError> {
    Parser::new(source)?.parse_function()
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
    Slash,
    Percent,
    Amp,
    Pipe,
    Caret,
    Tilde,
    Equal,
}

impl Token {
    fn is_scalar_update(&self) -> bool {
        matches!(
            self,
            Self::Equal
                | Self::PlusPlus
                | Self::MinusMinus
                | Self::PlusEqual
                | Self::MinusEqual
                | Self::StarEqual
        )
    }
}

struct Parser {
    tokens: Vec<Token>,
    position: usize,
}

impl Parser {
    fn new(source: &str) -> Result<Self, C0SyntaxError> {
        Ok(Self {
            tokens: tokenize(source)?,
            position: 0,
        })
    }

    fn parse_function(mut self) -> Result<C0Function, C0SyntaxError> {
        self.parse_struct_declarations()?;
        let return_type = self.parse_type()?;
        let name = self.expect_ident("function name")?;
        self.expect(Token::LParen)?;
        let parameters = self.parse_parameters()?;
        self.expect(Token::RParen)?;
        let body = self.parse_block_statement()?;
        self.expect_end()?;

        Ok(C0Function {
            return_type,
            name,
            parameters,
            body,
        })
    }

    fn parse_struct_declarations(&mut self) -> Result<(), C0SyntaxError> {
        while self.peek_ident() == Some("struct") && self.peek_n(2) == Some(&Token::LBrace) {
            self.expect_ident_spelling("struct")?;
            let _name = self.expect_ident("struct name")?;
            self.expect(Token::LBrace)?;

            let mut field_count = 0;
            while self.peek() != Some(&Token::RBrace) {
                if self.peek().is_none() {
                    return Err(C0SyntaxError::new(
                        "expected struct field or `}`, got end of input",
                    ));
                }
                let field_type = self.parse_type()?;
                if field_type != C0Type::Int32 {
                    return Err(C0SyntaxError::new(
                        "only single-int32-field structs are supported",
                    ));
                }
                let _field_name = self.expect_ident("struct field name")?;
                self.expect(Token::Semicolon)?;
                field_count += 1;
            }

            self.expect(Token::RBrace)?;
            self.expect(Token::Semicolon)?;

            if field_count != 1 {
                return Err(C0SyntaxError::new(
                    "only single-int32-field structs are supported",
                ));
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
            let c_type = self.parse_type()?;
            let name = self.expect_ident("parameter name")?;
            let c_type = self.parse_parameter_array_suffix(c_type)?;
            parameters.push(C0Parameter { c_type, name });

            if self.peek() != Some(&Token::Comma) {
                return Ok(parameters);
            }
            self.position += 1;
        }
    }

    fn parse_type(&mut self) -> Result<C0Type, C0SyntaxError> {
        match self.next() {
            Some(Token::Ident(name)) if name == "struct" => {
                let _struct_name = self.expect_ident("struct name")?;
                if self.peek() == Some(&Token::Star) {
                    self.position += 1;
                    Ok(C0Type::Int32Pointer)
                } else {
                    Err(C0SyntaxError::new(
                        "only pointer-to-struct types are supported",
                    ))
                }
            }
            Some(Token::Ident(name)) if name == "int32" || name == "uint8" => {
                let scalar_type = if name == "int32" {
                    C0Type::Int32
                } else {
                    C0Type::UInt8
                };
                if self.peek() == Some(&Token::Star) {
                    self.position += 1;
                    Ok(match scalar_type {
                        C0Type::Int32 => C0Type::Int32Pointer,
                        C0Type::UInt8 => C0Type::UInt8Pointer,
                        _ => unreachable!("scalar type should not be aggregate"),
                    })
                } else {
                    Ok(scalar_type)
                }
            }
            Some(token) => Err(C0SyntaxError::new(format!(
                "expected type `int32` or `uint8`, got {token:?}"
            ))),
            None => Err(C0SyntaxError::new(
                "expected type `int32` or `uint8`, got end of input",
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
                return Err(C0SyntaxError::new(
                    "only scalar array parameters are supported",
                ));
            }
        };

        if !matches!(c_type, C0Type::Int32 | C0Type::UInt8) {
            return Err(C0SyntaxError::new(
                "only scalar array parameters are supported",
            ));
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
            _ => return Err(C0SyntaxError::new("only scalar local arrays are supported")),
        };

        self.position += 1;
        let length = match self.next() {
            Some(Token::Number(number)) => {
                let length = number.parse::<u32>().map_err(|_| {
                    C0SyntaxError::new(format!("array length `{number}` is out of range"))
                })?;
                if length == 0 {
                    return Err(C0SyntaxError::new("local arrays must have positive length"));
                }
                if length.checked_mul(element_width).is_none() {
                    return Err(C0SyntaxError::new(format!(
                        "array length `{number}` is too large for {element_name} elements"
                    )));
                }
                length
            }
            Some(token) => {
                return Err(C0SyntaxError::new(format!(
                    "expected local array length, got {token:?}"
                )));
            }
            None => {
                return Err(C0SyntaxError::new(
                    "expected local array length, got end of input",
                ));
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
                return Err(C0SyntaxError::new(
                    "expected statement or `}`, got end of input",
                ));
            }
            statements.push(self.parse_statement()?);
        }
        self.expect(Token::RBrace)?;

        let mut statements = statements.into_iter();
        let Some(mut statement) = statements.next() else {
            return Err(C0SyntaxError::new(
                "expected at least one statement in block",
            ));
        };
        for next in statements {
            statement = C0Statement::Seq(Box::new(statement), Box::new(next));
        }

        Ok(statement)
    }

    fn parse_statement(&mut self) -> Result<C0Statement, C0SyntaxError> {
        match self.peek() {
            Some(Token::Star) => {
                self.position += 1;
                let pointer = self.parse_unary()?;
                self.expect(Token::Equal)?;
                let value = self.parse_expression()?;
                self.expect(Token::Semicolon)?;
                Ok(C0Statement::Store { pointer, value })
            }
            Some(Token::Ident(_)) if self.peek_next() == Some(&Token::LBracket) => {
                let pointer = self.parse_indexed_lvalue_pointer()?;
                self.expect(Token::Equal)?;
                let value = self.parse_expression()?;
                self.expect(Token::Semicolon)?;
                Ok(C0Statement::Store { pointer, value })
            }
            Some(Token::Ident(_)) if self.peek_next() == Some(&Token::Arrow) => {
                let pointer = self.parse_field_lvalue_pointer()?;
                self.expect(Token::Equal)?;
                let value = self.parse_expression()?;
                self.expect(Token::Semicolon)?;
                Ok(C0Statement::Store { pointer, value })
            }
            Some(Token::Ident(_)) if self.peek_next().is_some_and(Token::is_scalar_update) => {
                let statement = self.parse_scalar_update_statement("statement")?;
                self.expect(Token::Semicolon)?;
                Ok(statement)
            }
            Some(Token::Ident(name)) if name == "int32" || name == "uint8" => {
                let c_type = self.parse_type()?;
                let name = self.expect_ident("local name")?;
                let c_type = self.parse_local_array_suffix(c_type)?;
                self.expect(Token::Semicolon)?;
                Ok(C0Statement::Declare { c_type, name })
            }
            Some(Token::Ident(_)) => match self.peek_ident() {
                Some("return") => {
                    self.position += 1;
                    let expression = self.parse_expression()?;
                    self.expect(Token::Semicolon)?;
                    Ok(C0Statement::Return(expression))
                }
                Some("if") => {
                    self.position += 1;
                    self.expect(Token::LParen)?;
                    let condition = self.parse_expression()?;
                    self.expect(Token::RParen)?;
                    let then_branch = Box::new(self.parse_block_statement()?);
                    self.expect_ident_spelling("else")?;
                    let else_branch = Box::new(self.parse_block_statement()?);
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
                Some(other) => Err(C0SyntaxError::new(format!(
                    "expected statement, got identifier `{other}`"
                ))),
                None => unreachable!("identifier token should have identifier spelling"),
            },
            Some(token) => Err(C0SyntaxError::new(format!(
                "expected statement, got {token:?}"
            ))),
            None => Err(C0SyntaxError::new("expected statement, got end of input")),
        }
    }

    fn parse_for_initializer(&mut self) -> Result<C0Statement, C0SyntaxError> {
        let Some(Token::Ident(name)) = self.next() else {
            return Err(C0SyntaxError::new(format!(
                "expected assignment target in for-loop initializer"
            )));
        };
        if name == "int32" || name == "uint8" {
            return Err(C0SyntaxError::new(
                "declarations are not supported in for-loop initializer",
            ));
        }
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
                return Err(C0SyntaxError::new(format!(
                    "expected scalar update target in {context}, got `{name}`"
                )));
            }
            Some(token) => {
                return Err(C0SyntaxError::new(format!(
                    "expected scalar update target in {context}, got {token:?}"
                )));
            }
            None => {
                return Err(C0SyntaxError::new(format!(
                    "expected scalar update target in {context}, got end of input"
                )));
            }
        };
        let operator = self.next().ok_or_else(|| {
            C0SyntaxError::new(format!(
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
                    return Ok(C0Statement::CallAssign {
                        target: name,
                        function_name,
                        arguments,
                    });
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
            token => {
                return Err(C0SyntaxError::new(format!(
                    "expected scalar update operator in {context}, got {token:?}"
                )));
            }
        };
        Ok(C0Statement::Assign { name, expression })
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
                    return Err(C0SyntaxError::new(format!(
                        "expected `,` or `)`, got {token:?}"
                    )));
                }
                None => {
                    return Err(C0SyntaxError::new("expected `,` or `)`, got end of input"));
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
                    let _field_name = self.expect_ident("field name")?;
                    expression = C0Expression::Load(Box::new(expression));
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

    fn parse_field_lvalue_pointer(&mut self) -> Result<C0Expression, C0SyntaxError> {
        let base = self.parse_primary()?;
        self.expect(Token::Arrow)?;
        let _field_name = self.expect_ident("field name")?;
        Ok(base)
    }

    fn parse_primary(&mut self) -> Result<C0Expression, C0SyntaxError> {
        match self.next() {
            Some(Token::Ident(name)) => Ok(C0Expression::Variable(name)),
            Some(Token::Number(number)) => {
                let value = number.parse::<u32>().map_err(|_| {
                    C0SyntaxError::new(format!("int32 literal `{number}` is out of range"))
                })?;
                if value > i32::MAX as u32 {
                    return Err(C0SyntaxError::new(format!(
                        "int32 literal `{number}` is out of range"
                    )));
                }
                Ok(C0Expression::Int32Literal(value))
            }
            Some(Token::CharLiteral(value)) => Ok(C0Expression::UInt8Literal(value)),
            Some(Token::LParen) => {
                let expression = self.parse_expression()?;
                self.expect(Token::RParen)?;
                Ok(expression)
            }
            Some(token) => Err(C0SyntaxError::new(format!(
                "expected expression, got {token:?}"
            ))),
            None => Err(C0SyntaxError::new("expected expression, got end of input")),
        }
    }

    fn expect(&mut self, expected: Token) -> Result<(), C0SyntaxError> {
        match self.next() {
            Some(token) if token == expected => Ok(()),
            Some(token) => Err(C0SyntaxError::new(format!(
                "expected {expected:?}, got {token:?}"
            ))),
            None => Err(C0SyntaxError::new(format!(
                "expected {expected:?}, got end of input"
            ))),
        }
    }

    fn expect_ident(&mut self, label: &str) -> Result<String, C0SyntaxError> {
        match self.next() {
            Some(Token::Ident(name)) => Ok(name),
            Some(token) => Err(C0SyntaxError::new(format!(
                "expected {label}, got {token:?}"
            ))),
            None => Err(C0SyntaxError::new(format!(
                "expected {label}, got end of input"
            ))),
        }
    }

    fn expect_ident_spelling(&mut self, expected: &str) -> Result<(), C0SyntaxError> {
        match self.next() {
            Some(Token::Ident(name)) if name == expected => Ok(()),
            Some(Token::Ident(name)) => Err(C0SyntaxError::new(format!(
                "expected `{expected}`, got `{name}`"
            ))),
            Some(token) => Err(C0SyntaxError::new(format!(
                "expected `{expected}`, got {token:?}"
            ))),
            None => Err(C0SyntaxError::new(format!(
                "expected `{expected}`, got end of input"
            ))),
        }
    }

    fn expect_end(&self) -> Result<(), C0SyntaxError> {
        if self.position == self.tokens.len() {
            Ok(())
        } else {
            Err(C0SyntaxError::new(format!(
                "expected end of input, got {:?}",
                self.tokens[self.position]
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

fn tokenize(source: &str) -> Result<Vec<Token>, C0SyntaxError> {
    let chars = source.chars().collect::<Vec<_>>();
    let mut tokens = Vec::new();
    let mut index = 0;

    while index < chars.len() {
        let ch = chars[index];
        if ch.is_whitespace() {
            index += 1;
            continue;
        }

        if is_ident_start(ch) {
            let start = index;
            index += 1;
            while index < chars.len() && is_ident_continue(chars[index]) {
                index += 1;
            }
            tokens.push(Token::Ident(chars[start..index].iter().collect()));
            continue;
        }

        if ch.is_ascii_digit() {
            let start = index;
            index += 1;
            while index < chars.len() && chars[index].is_ascii_digit() {
                index += 1;
            }
            tokens.push(Token::Number(chars[start..index].iter().collect()));
            continue;
        }

        if ch == '\'' {
            let (value, next_index) = parse_char_literal(&chars, index)?;
            tokens.push(Token::CharLiteral(value));
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
                _ => None,
            };
            if let Some(token) = token {
                tokens.push(token);
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
                return Err(C0SyntaxError::new(format!("unexpected character `{ch}`")));
            }
        };
        tokens.push(token);
        index += 1;
    }

    Ok(tokens)
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
