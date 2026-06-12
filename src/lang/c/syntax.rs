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
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum C0Stmt {
    Return(C0Expr),
    If {
        condition: C0Expr,
        then_branch: Box<C0Stmt>,
        else_branch: Box<C0Stmt>,
    },
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum C0Expr {
    Var(String),
    Int32Literal(u32),
    Lt(Box<C0Expr>, Box<C0Expr>),
    Add(Box<C0Expr>, Box<C0Expr>),
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

    pub fn body_click_source(&self) -> String {
        self.body.to_click_source()
    }
}

impl C0Param {
    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn ty(&self) -> C0Type {
        self.ty
    }
}

impl C0Stmt {
    pub fn to_click_source(&self) -> String {
        match self {
            Self::Return(expr) => format!("(c-return-stmt {})", expr.to_click_source()),
            Self::If {
                condition,
                then_branch,
                else_branch,
            } => format!(
                "(c-if-stmt {} {} {})",
                condition.to_click_source(),
                then_branch.to_click_source(),
                else_branch.to_click_source()
            ),
        }
    }
}

impl C0Expr {
    pub fn to_click_source(&self) -> String {
        match self {
            Self::Var(name) => format!("(c-var-expr (quote {name}))"),
            Self::Int32Literal(value) => format!("(c-int32-expr (c-int32 (bv32 {value})))"),
            Self::Lt(left, right) => format!(
                "(c-lt-expr {} {})",
                left.to_click_source(),
                right.to_click_source()
            ),
            Self::Add(left, right) => format!(
                "(c-add-expr {} {})",
                left.to_click_source(),
                right.to_click_source()
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
    LBrace,
    RBrace,
    Comma,
    Semicolon,
    Plus,
    Lt,
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
            Some(Token::Ident(name)) if name == "int32" => Ok(C0Type::Int32),
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
        let statement = self.parse_stmt()?;
        self.expect(Token::RBrace)?;
        Ok(statement)
    }

    fn parse_stmt(&mut self) -> Result<C0Stmt, C0SyntaxError> {
        match self.peek_ident() {
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
            Some(other) => Err(C0SyntaxError::new(format!(
                "expected statement, got identifier `{other}`"
            ))),
            None => Err(C0SyntaxError::new("expected statement, got end of input")),
        }
    }

    fn parse_expr(&mut self) -> Result<C0Expr, C0SyntaxError> {
        self.parse_lt()
    }

    fn parse_lt(&mut self) -> Result<C0Expr, C0SyntaxError> {
        let mut expr = self.parse_add()?;
        while self.peek() == Some(&Token::Lt) {
            self.position += 1;
            let right = self.parse_add()?;
            expr = C0Expr::Lt(Box::new(expr), Box::new(right));
        }
        Ok(expr)
    }

    fn parse_add(&mut self) -> Result<C0Expr, C0SyntaxError> {
        let mut expr = self.parse_primary()?;
        while self.peek() == Some(&Token::Plus) {
            self.position += 1;
            let right = self.parse_primary()?;
            expr = C0Expr::Add(Box::new(expr), Box::new(right));
        }
        Ok(expr)
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

        let token = match ch {
            '(' => Token::LParen,
            ')' => Token::RParen,
            '{' => Token::LBrace,
            '}' => Token::RBrace,
            ',' => Token::Comma,
            ';' => Token::Semicolon,
            '+' => Token::Plus,
            '<' => Token::Lt,
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
