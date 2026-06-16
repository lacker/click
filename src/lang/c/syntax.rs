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
    Int32Pointer,
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

    pub fn body_megakernel_statement(&self) -> crate::megakernel::CStatement {
        self.body.to_megakernel_statement()
    }

    pub fn to_megakernel_function(&self) -> crate::megakernel::CFunction {
        crate::megakernel::c_function(
            self.return_type.to_megakernel_type(),
            self.name.clone(),
            self.parameters
                .iter()
                .map(C0Parameter::to_megakernel_parameter)
                .collect(),
            self.body.to_megakernel_statement(),
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

    pub fn to_megakernel_parameter(&self) -> crate::megakernel::CParameter {
        crate::megakernel::c_parameter(self.name.clone(), self.c_type.to_megakernel_type())
    }
}

impl C0Type {
    pub fn to_megakernel_type(self) -> crate::megakernel::CType {
        match self {
            Self::Int32 => crate::megakernel::CType::Int32,
            Self::Int32Pointer => crate::megakernel::CType::Int32Pointer,
        }
    }
}

impl C0Statement {
    pub fn to_megakernel_statement(&self) -> crate::megakernel::CStatement {
        match self {
            Self::Declare { c_type, name } => {
                crate::megakernel::c_declare(name.clone(), c_type.to_megakernel_type())
            }
            Self::Assign { name, expression } => {
                crate::megakernel::c_assign(name.clone(), expression.to_megakernel_expression())
            }
            Self::CallAssign {
                target,
                function_name,
                arguments,
            } => crate::megakernel::c_call_assign(
                target.clone(),
                function_name.clone(),
                arguments
                    .iter()
                    .map(C0Expression::to_megakernel_expression)
                    .collect(),
            ),
            Self::Seq(first, second) => crate::megakernel::c_seq(
                first.to_megakernel_statement(),
                second.to_megakernel_statement(),
            ),
            Self::Return(expression) => {
                crate::megakernel::c_return(expression.to_megakernel_expression())
            }
            Self::Store { pointer, value } => crate::megakernel::c_store(
                pointer.to_megakernel_expression(),
                value.to_megakernel_expression(),
            ),
            Self::If {
                condition,
                then_branch,
                else_branch,
            } => crate::megakernel::c_if(
                condition.to_megakernel_expression(),
                then_branch.to_megakernel_statement(),
                else_branch.to_megakernel_statement(),
            ),
            Self::While { condition, body } => crate::megakernel::c_while(
                condition.to_megakernel_expression(),
                Vec::new(),
                body.to_megakernel_statement(),
            ),
        }
    }
}

impl C0Expression {
    pub fn to_megakernel_expression(&self) -> crate::megakernel::CExpression {
        match self {
            Self::Variable(name) => crate::megakernel::c_variable(name.clone()),
            Self::AddressOf(target) => crate::megakernel::CExpression::AddressOf(Box::new(
                target.to_megakernel_expression(),
            )),
            Self::Int32Literal(value) => crate::megakernel::c_int32_literal(*value),
            Self::LessThan(left, right) => crate::megakernel::c_less_than(
                left.to_megakernel_expression(),
                right.to_megakernel_expression(),
            ),
            Self::LessEqual(left, right) => crate::megakernel::c_less_equal(
                left.to_megakernel_expression(),
                right.to_megakernel_expression(),
            ),
            Self::GreaterThan(left, right) => crate::megakernel::c_greater_than(
                left.to_megakernel_expression(),
                right.to_megakernel_expression(),
            ),
            Self::GreaterEqual(left, right) => crate::megakernel::c_greater_equal(
                left.to_megakernel_expression(),
                right.to_megakernel_expression(),
            ),
            Self::Equal(left, right) => crate::megakernel::c_equal(
                left.to_megakernel_expression(),
                right.to_megakernel_expression(),
            ),
            Self::NotEqual(left, right) => crate::megakernel::c_not_equal(
                left.to_megakernel_expression(),
                right.to_megakernel_expression(),
            ),
            Self::Not(expression) => {
                crate::megakernel::c_not(expression.to_megakernel_expression())
            }
            Self::And(left, right) => crate::megakernel::c_and(
                left.to_megakernel_expression(),
                right.to_megakernel_expression(),
            ),
            Self::Or(left, right) => crate::megakernel::c_or(
                left.to_megakernel_expression(),
                right.to_megakernel_expression(),
            ),
            Self::Add(left, right) => crate::megakernel::c_add(
                left.to_megakernel_expression(),
                right.to_megakernel_expression(),
            ),
            Self::Subtract(left, right) => crate::megakernel::c_subtract(
                left.to_megakernel_expression(),
                right.to_megakernel_expression(),
            ),
            Self::Load(pointer) => crate::megakernel::c_load(pointer.to_megakernel_expression()),
            Self::Index(base, index) => crate::megakernel::c_index(
                base.to_megakernel_expression(),
                index.to_megakernel_expression(),
            ),
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
    LParen,
    RParen,
    LBracket,
    RBracket,
    LBrace,
    RBrace,
    Comma,
    Semicolon,
    Plus,
    Minus,
    LessThan,
    LessEqual,
    GreaterThan,
    GreaterEqual,
    EqualEqual,
    BangEqual,
    Bang,
    AmpAmp,
    PipePipe,
    Star,
    Amp,
    Equal,
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
            Some(Token::Ident(name)) if name == "int32" => {
                if self.peek() == Some(&Token::Star) {
                    self.position += 1;
                    Ok(C0Type::Int32Pointer)
                } else {
                    Ok(C0Type::Int32)
                }
            }
            Some(token) => Err(C0SyntaxError::new(format!(
                "expected type `int32`, got {token:?}"
            ))),
            None => Err(C0SyntaxError::new(
                "expected type `int32`, got end of input",
            )),
        }
    }

    fn parse_parameter_array_suffix(&mut self, c_type: C0Type) -> Result<C0Type, C0SyntaxError> {
        if self.peek() != Some(&Token::LBracket) {
            return Ok(c_type);
        }
        if c_type != C0Type::Int32 {
            return Err(C0SyntaxError::new(
                "only `int32 name[]` array parameters are supported",
            ));
        }

        self.position += 1;
        if matches!(self.peek(), Some(Token::Number(_))) {
            self.position += 1;
        }
        self.expect(Token::RBracket)?;
        Ok(C0Type::Int32Pointer)
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
            Some(Token::Ident(name)) if self.peek_next() == Some(&Token::Equal) => {
                let name = name.clone();
                self.position += 2;
                if matches!(self.peek(), Some(Token::Ident(_)))
                    && self.peek_next() == Some(&Token::LParen)
                {
                    let function_name = self.expect_ident("function name")?;
                    let arguments = self.parse_call_arguments()?;
                    self.expect(Token::Semicolon)?;
                    return Ok(C0Statement::CallAssign {
                        target: name,
                        function_name,
                        arguments,
                    });
                }
                let expression = self.parse_expression()?;
                self.expect(Token::Semicolon)?;
                Ok(C0Statement::Assign { name, expression })
            }
            Some(Token::Ident(name)) if name == "int32" => {
                let c_type = self.parse_type()?;
                let name = self.expect_ident("local name")?;
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
        let mut expression = self.parse_compare()?;
        loop {
            expression = match self.peek() {
                Some(Token::AmpAmp) => {
                    self.position += 1;
                    let right = self.parse_compare()?;
                    C0Expression::And(Box::new(expression), Box::new(right))
                }
                _ => return Ok(expression),
            };
        }
    }

    fn parse_compare(&mut self) -> Result<C0Expression, C0SyntaxError> {
        let mut expression = self.parse_add()?;
        loop {
            expression = match self.peek() {
                Some(Token::LessThan) => {
                    self.position += 1;
                    let right = self.parse_add()?;
                    C0Expression::LessThan(Box::new(expression), Box::new(right))
                }
                Some(Token::LessEqual) => {
                    self.position += 1;
                    let right = self.parse_add()?;
                    C0Expression::LessEqual(Box::new(expression), Box::new(right))
                }
                Some(Token::GreaterThan) => {
                    self.position += 1;
                    let right = self.parse_add()?;
                    C0Expression::GreaterThan(Box::new(expression), Box::new(right))
                }
                Some(Token::GreaterEqual) => {
                    self.position += 1;
                    let right = self.parse_add()?;
                    C0Expression::GreaterEqual(Box::new(expression), Box::new(right))
                }
                Some(Token::EqualEqual) => {
                    self.position += 1;
                    let right = self.parse_add()?;
                    C0Expression::Equal(Box::new(expression), Box::new(right))
                }
                Some(Token::BangEqual) => {
                    self.position += 1;
                    let right = self.parse_add()?;
                    C0Expression::NotEqual(Box::new(expression), Box::new(right))
                }
                _ => return Ok(expression),
            };
        }
    }

    fn parse_add(&mut self) -> Result<C0Expression, C0SyntaxError> {
        let mut expression = self.parse_unary()?;
        loop {
            expression = match self.peek() {
                Some(Token::Plus) => {
                    self.position += 1;
                    let right = self.parse_unary()?;
                    C0Expression::Add(Box::new(expression), Box::new(right))
                }
                Some(Token::Minus) => {
                    self.position += 1;
                    let right = self.parse_unary()?;
                    C0Expression::Subtract(Box::new(expression), Box::new(right))
                }
                _ => return Ok(expression),
            };
        }
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

        self.parse_postfix()
    }

    fn parse_postfix(&mut self) -> Result<C0Expression, C0SyntaxError> {
        let mut expression = self.parse_primary()?;
        while self.peek() == Some(&Token::LBracket) {
            self.position += 1;
            let index = self.parse_expression()?;
            self.expect(Token::RBracket)?;
            expression = C0Expression::Index(Box::new(expression), Box::new(index));
        }
        Ok(expression)
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

        if index + 1 < chars.len() {
            let token = match (ch, chars[index + 1]) {
                ('=', '=') => Some(Token::EqualEqual),
                ('!', '=') => Some(Token::BangEqual),
                ('&', '&') => Some(Token::AmpAmp),
                ('|', '|') => Some(Token::PipePipe),
                ('<', '=') => Some(Token::LessEqual),
                ('>', '=') => Some(Token::GreaterEqual),
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
            '&' => Token::Amp,
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

fn is_ident_start(ch: char) -> bool {
    ch.is_ascii_alphabetic() || ch == '_'
}

fn is_ident_continue(ch: char) -> bool {
    ch.is_ascii_alphanumeric() || ch == '_'
}
