//! Tiny C0 syntax import for the executable C model.

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct C0Function {
    return_type: C0Type,
    name: String,
    params: Vec<C0Param>,
    body: C0Stmt,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct C0Param {
    ty: C0Type,
    name: String,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum C0Type {
    Int32,
    Int32Ptr,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum C0Stmt {
    Declare {
        ty: C0Type,
        name: String,
    },
    Assign {
        name: String,
        expr: C0Expr,
    },
    CallAssign {
        target: String,
        function_name: String,
        args: Vec<C0Expr>,
    },
    Seq(Box<C0Stmt>, Box<C0Stmt>),
    Return(C0Expr),
    Store {
        ptr: C0Expr,
        value: C0Expr,
    },
    If {
        condition: C0Expr,
        then_branch: Box<C0Stmt>,
        else_branch: Box<C0Stmt>,
    },
    While {
        condition: C0Expr,
        body: Box<C0Stmt>,
    },
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum C0Expr {
    Var(String),
    AddressOf(String),
    Int32Literal(u32),
    Lt(Box<C0Expr>, Box<C0Expr>),
    Le(Box<C0Expr>, Box<C0Expr>),
    Gt(Box<C0Expr>, Box<C0Expr>),
    Ge(Box<C0Expr>, Box<C0Expr>),
    Eq(Box<C0Expr>, Box<C0Expr>),
    Ne(Box<C0Expr>, Box<C0Expr>),
    Not(Box<C0Expr>),
    And(Box<C0Expr>, Box<C0Expr>),
    Or(Box<C0Expr>, Box<C0Expr>),
    Add(Box<C0Expr>, Box<C0Expr>),
    Sub(Box<C0Expr>, Box<C0Expr>),
    Load(Box<C0Expr>),
    Index(Box<C0Expr>, Box<C0Expr>),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct C0SyntaxError {
    message: String,
}

impl C0Function {
    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn params(&self) -> &[C0Param] {
        &self.params
    }

    pub fn return_type(&self) -> C0Type {
        self.return_type
    }

    pub fn body(&self) -> &C0Stmt {
        &self.body
    }

    pub fn body_megakernel_stmt(&self) -> crate::megakernel::CStmt {
        self.body.to_megakernel_stmt()
    }

    pub fn to_megakernel_function(&self) -> crate::megakernel::CFunction {
        crate::megakernel::c_function(
            self.return_type.to_megakernel_type(),
            self.name.clone(),
            self.params
                .iter()
                .map(C0Param::to_megakernel_param)
                .collect(),
            self.body.to_megakernel_stmt(),
        )
    }
}

impl C0Param {
    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn ty(&self) -> C0Type {
        self.ty
    }

    pub fn to_megakernel_param(&self) -> crate::megakernel::CParam {
        crate::megakernel::c_param(self.name.clone(), self.ty.to_megakernel_type())
    }
}

impl C0Type {
    pub fn to_megakernel_type(self) -> crate::megakernel::CType {
        match self {
            Self::Int32 => crate::megakernel::CType::Int32,
            Self::Int32Ptr => crate::megakernel::CType::Int32Ptr,
        }
    }
}

impl C0Stmt {
    pub fn to_megakernel_stmt(&self) -> crate::megakernel::CStmt {
        match self {
            Self::Declare { ty, name } => {
                crate::megakernel::c_declare(name.clone(), ty.to_megakernel_type())
            }
            Self::Assign { name, expr } => {
                crate::megakernel::c_assign(name.clone(), expr.to_megakernel_expr())
            }
            Self::CallAssign {
                target,
                function_name,
                args,
            } => crate::megakernel::c_call_assign(
                target.clone(),
                function_name.clone(),
                args.iter().map(C0Expr::to_megakernel_expr).collect(),
            ),
            Self::Seq(first, second) => {
                crate::megakernel::c_seq(first.to_megakernel_stmt(), second.to_megakernel_stmt())
            }
            Self::Return(expr) => crate::megakernel::c_return(expr.to_megakernel_expr()),
            Self::Store { ptr, value } => {
                crate::megakernel::c_store(ptr.to_megakernel_expr(), value.to_megakernel_expr())
            }
            Self::If {
                condition,
                then_branch,
                else_branch,
            } => crate::megakernel::c_if(
                condition.to_megakernel_expr(),
                then_branch.to_megakernel_stmt(),
                else_branch.to_megakernel_stmt(),
            ),
            Self::While { condition, body } => crate::megakernel::c_while(
                condition.to_megakernel_expr(),
                Vec::new(),
                body.to_megakernel_stmt(),
            ),
        }
    }
}

impl C0Expr {
    pub fn to_megakernel_expr(&self) -> crate::megakernel::CExpr {
        match self {
            Self::Var(name) => crate::megakernel::c_var(name.clone()),
            Self::AddressOf(name) => crate::megakernel::c_addr_of(name.clone()),
            Self::Int32Literal(value) => crate::megakernel::c_int32_literal(*value),
            Self::Lt(left, right) => {
                crate::megakernel::c_lt(left.to_megakernel_expr(), right.to_megakernel_expr())
            }
            Self::Le(left, right) => {
                crate::megakernel::c_le(left.to_megakernel_expr(), right.to_megakernel_expr())
            }
            Self::Gt(left, right) => {
                crate::megakernel::c_gt(left.to_megakernel_expr(), right.to_megakernel_expr())
            }
            Self::Ge(left, right) => {
                crate::megakernel::c_ge(left.to_megakernel_expr(), right.to_megakernel_expr())
            }
            Self::Eq(left, right) => {
                crate::megakernel::c_eq(left.to_megakernel_expr(), right.to_megakernel_expr())
            }
            Self::Ne(left, right) => {
                crate::megakernel::c_ne(left.to_megakernel_expr(), right.to_megakernel_expr())
            }
            Self::Not(expr) => crate::megakernel::c_not(expr.to_megakernel_expr()),
            Self::And(left, right) => {
                crate::megakernel::c_and(left.to_megakernel_expr(), right.to_megakernel_expr())
            }
            Self::Or(left, right) => {
                crate::megakernel::c_or(left.to_megakernel_expr(), right.to_megakernel_expr())
            }
            Self::Add(left, right) => {
                crate::megakernel::c_add(left.to_megakernel_expr(), right.to_megakernel_expr())
            }
            Self::Sub(left, right) => {
                crate::megakernel::c_sub(left.to_megakernel_expr(), right.to_megakernel_expr())
            }
            Self::Load(ptr) => crate::megakernel::c_load(ptr.to_megakernel_expr()),
            Self::Index(base, index) => crate::megakernel::c_load(crate::megakernel::c_add(
                base.to_megakernel_expr(),
                index.to_megakernel_expr(),
            )),
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
    Lt,
    Le,
    Gt,
    Ge,
    EqEq,
    BangEq,
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
        let params = self.parse_params()?;
        self.expect(Token::RParen)?;
        let body = self.parse_block_stmt()?;
        self.expect_end()?;

        Ok(C0Function {
            return_type,
            name,
            params,
            body,
        })
    }

    fn parse_params(&mut self) -> Result<Vec<C0Param>, C0SyntaxError> {
        let mut params = Vec::new();
        if self.peek() == Some(&Token::RParen) {
            return Ok(params);
        }

        loop {
            let ty = self.parse_type()?;
            let name = self.expect_ident("parameter name")?;
            params.push(C0Param { ty, name });

            if self.peek() != Some(&Token::Comma) {
                return Ok(params);
            }
            self.position += 1;
        }
    }

    fn parse_type(&mut self) -> Result<C0Type, C0SyntaxError> {
        match self.next() {
            Some(Token::Ident(name)) if name == "int32" => {
                if self.peek() == Some(&Token::Star) {
                    self.position += 1;
                    Ok(C0Type::Int32Ptr)
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

    fn parse_block_stmt(&mut self) -> Result<C0Stmt, C0SyntaxError> {
        self.expect(Token::LBrace)?;
        let mut statements = Vec::new();
        while self.peek() != Some(&Token::RBrace) {
            if self.peek().is_none() {
                return Err(C0SyntaxError::new(
                    "expected statement or `}`, got end of input",
                ));
            }
            statements.push(self.parse_stmt()?);
        }
        self.expect(Token::RBrace)?;

        let mut statements = statements.into_iter();
        let Some(mut statement) = statements.next() else {
            return Err(C0SyntaxError::new(
                "expected at least one statement in block",
            ));
        };
        for next in statements {
            statement = C0Stmt::Seq(Box::new(statement), Box::new(next));
        }

        Ok(statement)
    }

    fn parse_stmt(&mut self) -> Result<C0Stmt, C0SyntaxError> {
        match self.peek() {
            Some(Token::Star) => {
                self.position += 1;
                let ptr = self.parse_unary()?;
                self.expect(Token::Equal)?;
                let value = self.parse_expr()?;
                self.expect(Token::Semicolon)?;
                Ok(C0Stmt::Store { ptr, value })
            }
            Some(Token::Ident(_)) if self.peek_next() == Some(&Token::LBracket) => {
                let ptr = self.parse_indexed_lvalue_ptr()?;
                self.expect(Token::Equal)?;
                let value = self.parse_expr()?;
                self.expect(Token::Semicolon)?;
                Ok(C0Stmt::Store { ptr, value })
            }
            Some(Token::Ident(name)) if self.peek_next() == Some(&Token::Equal) => {
                let name = name.clone();
                self.position += 2;
                if matches!(self.peek(), Some(Token::Ident(_)))
                    && self.peek_next() == Some(&Token::LParen)
                {
                    let function_name = self.expect_ident("function name")?;
                    let args = self.parse_call_args()?;
                    self.expect(Token::Semicolon)?;
                    return Ok(C0Stmt::CallAssign {
                        target: name,
                        function_name,
                        args,
                    });
                }
                let expr = self.parse_expr()?;
                self.expect(Token::Semicolon)?;
                Ok(C0Stmt::Assign { name, expr })
            }
            Some(Token::Ident(name)) if name == "int32" => {
                let ty = self.parse_type()?;
                let name = self.expect_ident("local name")?;
                self.expect(Token::Semicolon)?;
                Ok(C0Stmt::Declare { ty, name })
            }
            Some(Token::Ident(_)) => match self.peek_ident() {
                Some("return") => {
                    self.position += 1;
                    let expr = self.parse_expr()?;
                    self.expect(Token::Semicolon)?;
                    Ok(C0Stmt::Return(expr))
                }
                Some("if") => {
                    self.position += 1;
                    self.expect(Token::LParen)?;
                    let condition = self.parse_expr()?;
                    self.expect(Token::RParen)?;
                    let then_branch = Box::new(self.parse_block_stmt()?);
                    self.expect_ident_spelling("else")?;
                    let else_branch = Box::new(self.parse_block_stmt()?);
                    Ok(C0Stmt::If {
                        condition,
                        then_branch,
                        else_branch,
                    })
                }
                Some("while") => {
                    self.position += 1;
                    self.expect(Token::LParen)?;
                    let condition = self.parse_expr()?;
                    self.expect(Token::RParen)?;
                    let body = Box::new(self.parse_block_stmt()?);
                    Ok(C0Stmt::While { condition, body })
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

    fn parse_expr(&mut self) -> Result<C0Expr, C0SyntaxError> {
        self.parse_logical_or()
    }

    fn parse_call_args(&mut self) -> Result<Vec<C0Expr>, C0SyntaxError> {
        self.expect(Token::LParen)?;
        let mut args = Vec::new();
        if self.peek() == Some(&Token::RParen) {
            self.position += 1;
            return Ok(args);
        }

        loop {
            args.push(self.parse_expr()?);
            match self.peek() {
                Some(Token::Comma) => {
                    self.position += 1;
                }
                Some(Token::RParen) => {
                    self.position += 1;
                    return Ok(args);
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

    fn parse_logical_or(&mut self) -> Result<C0Expr, C0SyntaxError> {
        let mut expr = self.parse_logical_and()?;
        loop {
            expr = match self.peek() {
                Some(Token::PipePipe) => {
                    self.position += 1;
                    let right = self.parse_logical_and()?;
                    C0Expr::Or(Box::new(expr), Box::new(right))
                }
                _ => return Ok(expr),
            };
        }
    }

    fn parse_logical_and(&mut self) -> Result<C0Expr, C0SyntaxError> {
        let mut expr = self.parse_compare()?;
        loop {
            expr = match self.peek() {
                Some(Token::AmpAmp) => {
                    self.position += 1;
                    let right = self.parse_compare()?;
                    C0Expr::And(Box::new(expr), Box::new(right))
                }
                _ => return Ok(expr),
            };
        }
    }

    fn parse_compare(&mut self) -> Result<C0Expr, C0SyntaxError> {
        let mut expr = self.parse_add()?;
        loop {
            expr = match self.peek() {
                Some(Token::Lt) => {
                    self.position += 1;
                    let right = self.parse_add()?;
                    C0Expr::Lt(Box::new(expr), Box::new(right))
                }
                Some(Token::Le) => {
                    self.position += 1;
                    let right = self.parse_add()?;
                    C0Expr::Le(Box::new(expr), Box::new(right))
                }
                Some(Token::Gt) => {
                    self.position += 1;
                    let right = self.parse_add()?;
                    C0Expr::Gt(Box::new(expr), Box::new(right))
                }
                Some(Token::Ge) => {
                    self.position += 1;
                    let right = self.parse_add()?;
                    C0Expr::Ge(Box::new(expr), Box::new(right))
                }
                Some(Token::EqEq) => {
                    self.position += 1;
                    let right = self.parse_add()?;
                    C0Expr::Eq(Box::new(expr), Box::new(right))
                }
                Some(Token::BangEq) => {
                    self.position += 1;
                    let right = self.parse_add()?;
                    C0Expr::Ne(Box::new(expr), Box::new(right))
                }
                _ => return Ok(expr),
            };
        }
    }

    fn parse_add(&mut self) -> Result<C0Expr, C0SyntaxError> {
        let mut expr = self.parse_unary()?;
        loop {
            expr = match self.peek() {
                Some(Token::Plus) => {
                    self.position += 1;
                    let right = self.parse_unary()?;
                    C0Expr::Add(Box::new(expr), Box::new(right))
                }
                Some(Token::Minus) => {
                    self.position += 1;
                    let right = self.parse_unary()?;
                    C0Expr::Sub(Box::new(expr), Box::new(right))
                }
                _ => return Ok(expr),
            };
        }
    }

    fn parse_unary(&mut self) -> Result<C0Expr, C0SyntaxError> {
        if self.peek() == Some(&Token::Star) {
            self.position += 1;
            return Ok(C0Expr::Load(Box::new(self.parse_unary()?)));
        }

        if self.peek() == Some(&Token::Amp) {
            self.position += 1;
            let name = self.expect_ident("address-of target")?;
            return Ok(C0Expr::AddressOf(name));
        }

        if self.peek() == Some(&Token::Bang) {
            self.position += 1;
            return Ok(C0Expr::Not(Box::new(self.parse_unary()?)));
        }

        self.parse_postfix()
    }

    fn parse_postfix(&mut self) -> Result<C0Expr, C0SyntaxError> {
        let mut expr = self.parse_primary()?;
        while self.peek() == Some(&Token::LBracket) {
            self.position += 1;
            let index = self.parse_expr()?;
            self.expect(Token::RBracket)?;
            expr = C0Expr::Index(Box::new(expr), Box::new(index));
        }
        Ok(expr)
    }

    fn parse_indexed_lvalue_ptr(&mut self) -> Result<C0Expr, C0SyntaxError> {
        let mut base = self.parse_primary()?;
        loop {
            self.expect(Token::LBracket)?;
            let index = self.parse_expr()?;
            self.expect(Token::RBracket)?;
            if self.peek() != Some(&Token::LBracket) {
                return Ok(C0Expr::Add(Box::new(base), Box::new(index)));
            }
            base = C0Expr::Index(Box::new(base), Box::new(index));
        }
    }

    fn parse_primary(&mut self) -> Result<C0Expr, C0SyntaxError> {
        match self.next() {
            Some(Token::Ident(name)) => Ok(C0Expr::Var(name)),
            Some(Token::Number(number)) => {
                let value = number.parse::<u32>().map_err(|_| {
                    C0SyntaxError::new(format!("int32 literal `{number}` is out of range"))
                })?;
                if value > i32::MAX as u32 {
                    return Err(C0SyntaxError::new(format!(
                        "int32 literal `{number}` is out of range"
                    )));
                }
                Ok(C0Expr::Int32Literal(value))
            }
            Some(Token::LParen) => {
                let expr = self.parse_expr()?;
                self.expect(Token::RParen)?;
                Ok(expr)
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
                ('=', '=') => Some(Token::EqEq),
                ('!', '=') => Some(Token::BangEq),
                ('&', '&') => Some(Token::AmpAmp),
                ('|', '|') => Some(Token::PipePipe),
                ('<', '=') => Some(Token::Le),
                ('>', '=') => Some(Token::Ge),
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
            '<' => Token::Lt,
            '>' => Token::Gt,
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
