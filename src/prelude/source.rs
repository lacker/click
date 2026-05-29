use std::collections::{HashMap, HashSet};

use crate::{Lambda, ListCase, Name, Symbol, Term};

#[derive(Clone, Copy)]
pub(super) struct NameBinding {
    pub spelling: &'static str,
    pub name: Name,
}

#[derive(Clone, Copy)]
pub(super) struct SymbolBinding {
    pub spelling: &'static str,
    pub symbol: Symbol,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct ParseError {
    message: String,
}

impl ParseError {
    fn new(message: impl Into<String>) -> Self {
        Self {
            message: message.into(),
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum Token {
    LParen,
    RParen,
    Atom(String),
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum Expr {
    Atom(String),
    List(Vec<Expr>),
}

pub(super) fn parse_term_definitions(
    source: &str,
    definitions: &[NameBinding],
    symbols: &[SymbolBinding],
) -> Result<Vec<(Name, Term)>, ParseError> {
    let tokens = tokenize(source);
    let expressions = parse_expressions(&tokens)?;
    let mut parser = TermParser::new(definitions, symbols)?;
    let mut defined = HashSet::new();
    let mut terms = Vec::new();

    for expression in expressions {
        let Expr::List(items) = expression else {
            return Err(ParseError::new("top-level form must be a list"));
        };
        if items.len() != 3 || atom(&items[0])? != "def" {
            return Err(ParseError::new(
                "top-level form must be (def <name> <term>)",
            ));
        }

        let spelling = atom(&items[1])?;
        let Some(name) = parser.definition(spelling) else {
            return Err(ParseError::new(format!("unknown definition `{spelling}`")));
        };
        if !defined.insert(name) {
            return Err(ParseError::new(format!(
                "duplicate definition `{spelling}`"
            )));
        }

        let term = parser.term(&items[2])?;
        terms.push((name, term));
    }

    for binding in definitions {
        if !defined.contains(&binding.name) {
            return Err(ParseError::new(format!(
                "missing definition `{}`",
                binding.spelling
            )));
        }
    }

    Ok(terms)
}

fn tokenize(source: &str) -> Vec<Token> {
    let mut tokens = Vec::new();
    let mut chars = source.chars().peekable();

    while let Some(ch) = chars.next() {
        match ch {
            ';' => {
                for ch in chars.by_ref() {
                    if ch == '\n' {
                        break;
                    }
                }
            }
            '(' => tokens.push(Token::LParen),
            ')' => tokens.push(Token::RParen),
            ch if ch.is_whitespace() => {}
            ch => {
                let mut atom = String::from(ch);
                while let Some(&ch) = chars.peek() {
                    if ch.is_whitespace() || ch == '(' || ch == ')' || ch == ';' {
                        break;
                    }
                    atom.push(ch);
                    chars.next();
                }
                tokens.push(Token::Atom(atom));
            }
        }
    }

    tokens
}

fn parse_expressions(tokens: &[Token]) -> Result<Vec<Expr>, ParseError> {
    let mut index = 0;
    let mut expressions = Vec::new();

    while index < tokens.len() {
        expressions.push(parse_expression(tokens, &mut index)?);
    }

    Ok(expressions)
}

fn parse_expression(tokens: &[Token], index: &mut usize) -> Result<Expr, ParseError> {
    let Some(token) = tokens.get(*index) else {
        return Err(ParseError::new("unexpected end of input"));
    };
    *index += 1;

    match token {
        Token::Atom(atom) => Ok(Expr::Atom(atom.clone())),
        Token::RParen => Err(ParseError::new("unexpected `)`")),
        Token::LParen => {
            let mut items = Vec::new();
            loop {
                match tokens.get(*index) {
                    Some(Token::RParen) => {
                        *index += 1;
                        return Ok(Expr::List(items));
                    }
                    Some(_) => items.push(parse_expression(tokens, index)?),
                    None => return Err(ParseError::new("unclosed `(`")),
                }
            }
        }
    }
}

fn atom(expression: &Expr) -> Result<&str, ParseError> {
    match expression {
        Expr::Atom(atom) => Ok(atom),
        Expr::List(_) => Err(ParseError::new("expected atom")),
    }
}

struct TermParser<'a> {
    definitions: HashMap<&'a str, Name>,
    symbols: HashMap<&'a str, Symbol>,
    scopes: Vec<HashMap<String, Symbol>>,
}

impl<'a> TermParser<'a> {
    fn new(
        definitions: &'a [NameBinding],
        symbols: &'a [SymbolBinding],
    ) -> Result<Self, ParseError> {
        let mut definition_map = HashMap::new();
        for binding in definitions {
            if definition_map
                .insert(binding.spelling, binding.name)
                .is_some()
            {
                return Err(ParseError::new(format!(
                    "duplicate definition binding `{}`",
                    binding.spelling
                )));
            }
        }

        let mut symbol_map = HashMap::new();
        for binding in symbols {
            if symbol_map
                .insert(binding.spelling, binding.symbol)
                .is_some()
            {
                return Err(ParseError::new(format!(
                    "duplicate symbol binding `{}`",
                    binding.spelling
                )));
            }
        }

        Ok(Self {
            definitions: definition_map,
            symbols: symbol_map,
            scopes: Vec::new(),
        })
    }

    fn definition(&self, spelling: &str) -> Option<Name> {
        self.definitions.get(spelling).copied()
    }

    fn term(&mut self, expression: &Expr) -> Result<Term, ParseError> {
        match expression {
            Expr::Atom(atom) => self.atom_term(atom),
            Expr::List(items) => self.list_term(items),
        }
    }

    fn atom_term(&self, spelling: &str) -> Result<Term, ParseError> {
        match spelling {
            "nil" => Ok(Term::Nil),
            "diverge" => Ok(Term::Diverge),
            _ => {
                if let Some(symbol) = self.variable(spelling) {
                    return Ok(Term::Var(symbol));
                }
                if let Some(name) = self.definition(spelling) {
                    return Ok(Term::Const(name));
                }

                Err(ParseError::new(format!("unknown identifier `{spelling}`")))
            }
        }
    }

    fn list_term(&mut self, items: &[Expr]) -> Result<Term, ParseError> {
        let Some(head) = items.first() else {
            return Err(ParseError::new("empty application"));
        };

        if let Expr::Atom(form) = head {
            match form.as_str() {
                "lambda" => return self.lambda(items),
                "list-case" => return self.list_case(items),
                "cons" => return self.cons(items),
                "head" => return self.head(items),
                "tail" => return self.tail(items),
                "error" => return self.error(items),
                "quote" => return self.quote(items),
                _ => {}
            }
        }

        self.application(items)
    }

    fn lambda(&mut self, items: &[Expr]) -> Result<Term, ParseError> {
        expect_len("lambda", items, 3)?;
        let parameter = atom(&items[1])?;
        let symbol = self.symbol(parameter)?;
        self.push_variable(parameter, symbol);
        let body = self.term(&items[2])?;
        self.pop_variable();

        Ok(Term::Lambda(Lambda {
            parameter: symbol,
            body: Box::new(body),
        }))
    }

    fn list_case(&mut self, items: &[Expr]) -> Result<Term, ParseError> {
        expect_len("list-case", items, 5)?;
        let list = self.term(&items[1])?;
        let nil = self.term(&items[2])?;
        let cons = atom(&items[3])?;
        let cons_symbol = self.symbol(cons)?;

        self.push_variable(cons, cons_symbol);
        let cons_case = self.term(&items[4])?;
        self.pop_variable();

        Ok(Term::ListCase(ListCase {
            list: Box::new(list),
            nil: Box::new(nil),
            cons: cons_symbol,
            cons_case: Box::new(cons_case),
        }))
    }

    fn cons(&mut self, items: &[Expr]) -> Result<Term, ParseError> {
        expect_len("cons", items, 3)?;
        Ok(Term::Cons {
            head: Box::new(self.term(&items[1])?),
            tail: Box::new(self.term(&items[2])?),
        })
    }

    fn head(&mut self, items: &[Expr]) -> Result<Term, ParseError> {
        expect_len("head", items, 2)?;
        Ok(Term::Head(Box::new(self.term(&items[1])?)))
    }

    fn tail(&mut self, items: &[Expr]) -> Result<Term, ParseError> {
        expect_len("tail", items, 2)?;
        Ok(Term::Tail(Box::new(self.term(&items[1])?)))
    }

    fn error(&mut self, items: &[Expr]) -> Result<Term, ParseError> {
        expect_len("error", items, 2)?;
        Ok(Term::Error(Box::new(self.term(&items[1])?)))
    }

    fn quote(&mut self, items: &[Expr]) -> Result<Term, ParseError> {
        expect_len("quote", items, 2)?;
        Ok(Term::Quote(self.symbol(atom(&items[1])?)?))
    }

    fn application(&mut self, items: &[Expr]) -> Result<Term, ParseError> {
        let mut terms = items
            .iter()
            .map(|item| self.term(item))
            .collect::<Result<Vec<_>, _>>()?
            .into_iter();
        let Some(mut term) = terms.next() else {
            return Err(ParseError::new("empty application"));
        };

        for argument in terms {
            term = Term::Apply {
                function: Box::new(term),
                argument: Box::new(argument),
            };
        }

        Ok(term)
    }

    fn symbol(&self, spelling: &str) -> Result<Symbol, ParseError> {
        self.symbols
            .get(spelling)
            .copied()
            .ok_or_else(|| ParseError::new(format!("unknown symbol `{spelling}`")))
    }

    fn variable(&self, spelling: &str) -> Option<Symbol> {
        self.scopes
            .iter()
            .rev()
            .find_map(|scope| scope.get(spelling).copied())
    }

    fn push_variable(&mut self, spelling: &str, symbol: Symbol) {
        self.scopes
            .push(HashMap::from([(spelling.to_owned(), symbol)]));
    }

    fn pop_variable(&mut self) {
        self.scopes.pop();
    }
}

fn expect_len(form: &str, items: &[Expr], len: usize) -> Result<(), ParseError> {
    if items.len() == len {
        Ok(())
    } else {
        Err(ParseError::new(format!(
            "`{form}` expects {} arguments, got {}",
            len - 1,
            items.len().saturating_sub(1)
        )))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_term_definitions() {
        let definitions = [
            NameBinding {
                spelling: "id",
                name: Name(1),
            },
            NameBinding {
                spelling: "use_id",
                name: Name(2),
            },
        ];
        let symbols = [SymbolBinding {
            spelling: "x",
            symbol: Symbol(1),
        }];

        assert_eq!(
            parse_term_definitions(
                "
                ; comments are ignored
                (def id (lambda x x))
                (def use_id (id nil))
                ",
                &definitions,
                &symbols,
            ),
            Ok(vec![
                (
                    Name(1),
                    Term::Lambda(Lambda {
                        parameter: Symbol(1),
                        body: Box::new(Term::Var(Symbol(1))),
                    }),
                ),
                (
                    Name(2),
                    Term::Apply {
                        function: Box::new(Term::Const(Name(1))),
                        argument: Box::new(Term::Nil),
                    },
                ),
            ])
        );
    }

    #[test]
    fn rejects_unbound_identifiers() {
        let definitions = [NameBinding {
            spelling: "bad",
            name: Name(1),
        }];

        let error = parse_term_definitions("(def bad x)", &definitions, &[])
            .expect_err("free identifier should fail");

        assert_eq!(error.message, "unknown identifier `x`");
    }
}
