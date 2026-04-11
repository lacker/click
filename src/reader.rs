use crate::kernel::{ClickResult, Symbol};

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum SExpr {
    Symbol(Symbol),
    List(Vec<SExpr>),
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum Token {
    LParen,
    RParen,
    Quote,
    Symbol(Symbol),
}

pub(crate) fn read(source: &str) -> ClickResult<Vec<SExpr>> {
    let source = strip_shebang(source);
    let tokens = tokenize(source)?;
    Parser::new(tokens).parse_program()
}

fn strip_shebang(source: &str) -> &str {
    if !source.starts_with("#!") {
        return source;
    }

    match source.find('\n') {
        Some(index) => &source[index + 1..],
        None => "",
    }
}

fn tokenize(source: &str) -> ClickResult<Vec<Token>> {
    let mut tokens = Vec::new();
    let mut chars = source.chars().peekable();

    while let Some(ch) = chars.next() {
        match ch {
            '(' => tokens.push(Token::LParen),
            ')' => tokens.push(Token::RParen),
            '\'' => tokens.push(Token::Quote),
            ';' => {
                for next in chars.by_ref() {
                    if next == '\n' {
                        break;
                    }
                }
            }
            c if c.is_whitespace() => {}
            _ => {
                let mut symbol = String::from(ch);
                while let Some(next) = chars.peek() {
                    if next.is_whitespace() || matches!(next, '(' | ')' | '\'' | ';') {
                        break;
                    }
                    symbol.push(*next);
                    chars.next();
                }
                tokens.push(Token::Symbol(symbol.into()));
            }
        }
    }

    Ok(tokens)
}

struct Parser {
    tokens: Vec<Token>,
    index: usize,
}

impl Parser {
    fn new(tokens: Vec<Token>) -> Self {
        Self { tokens, index: 0 }
    }

    fn parse_program(mut self) -> ClickResult<Vec<SExpr>> {
        let mut sexprs = Vec::new();
        while self.index < self.tokens.len() {
            sexprs.push(self.parse_expr()?);
        }
        Ok(sexprs)
    }

    fn parse_expr(&mut self) -> ClickResult<SExpr> {
        let token = self
            .tokens
            .get(self.index)
            .ok_or_else(|| "unexpected end of input".to_string())?
            .clone();
        self.index += 1;

        match token {
            Token::LParen => {
                let mut items = Vec::new();
                loop {
                    match self.tokens.get(self.index) {
                        Some(Token::RParen) => {
                            self.index += 1;
                            return Ok(SExpr::List(items));
                        }
                        Some(_) => items.push(self.parse_expr()?),
                        None => return Err("unterminated list".to_string()),
                    }
                }
            }
            Token::RParen => Err("unexpected ')'".to_string()),
            Token::Quote => Err("quote syntax is no longer supported".to_string()),
            Token::Symbol(symbol) => Ok(SExpr::Symbol(symbol)),
        }
    }
}
