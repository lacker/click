use std::collections::{HashMap, HashSet};

use crate::{
    Lambda, ListCase, Name, Prop, Symbol, Term, and, computes_to, computes_to_list, diverges,
    equal, errors, exists, forall, implies, is_list, is_value, or,
};

const FIRST_THEOREM_SYMBOL: Symbol = Symbol(2_000);

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
pub(super) struct LocalSymbol {
    spelling: String,
    symbol: Symbol,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct ParsedTheorem {
    pub name: Name,
    pub prop: Prop,
    local_symbols: Vec<LocalSymbol>,
}

impl ParsedTheorem {
    pub(super) fn symbol(&self, spelling: &str) -> Option<Symbol> {
        let mut matches = self
            .local_symbols
            .iter()
            .filter(|symbol| symbol.spelling == spelling);
        let symbol = matches.next()?.symbol;

        matches.next().is_none().then_some(symbol)
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct ParsedModule {
    pub terms: Vec<(Name, Term)>,
    pub theorems: Vec<ParsedTheorem>,
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

pub(super) fn parse_module(
    source: &str,
    term_definitions: &[NameBinding],
    theorem_definitions: &[NameBinding],
    symbols: &[SymbolBinding],
) -> Result<ParsedModule, ParseError> {
    let tokens = tokenize(source);
    let expressions = parse_expressions(&tokens)?;
    let mut term_parser = TermParser::new(term_definitions, symbols)?;
    let theorem_names = name_map(theorem_definitions, "theorem")?;
    let mut defined_terms = HashSet::new();
    let mut defined_theorems = HashSet::new();
    let mut terms = Vec::new();
    let mut theorems = Vec::new();

    for expression in expressions {
        let form = top_level_form(&expression)?;

        match form.kind {
            "def" => {
                let Some(name) = term_parser.definition(form.name) else {
                    return Err(ParseError::new(format!(
                        "unknown definition `{}`",
                        form.name
                    )));
                };
                if !defined_terms.insert(name) {
                    return Err(ParseError::new(format!(
                        "duplicate definition `{}`",
                        form.name
                    )));
                }

                let term = term_parser.term(form.body)?;
                terms.push((name, term));
            }
            "theorem" => {
                let Some(name) = theorem_names.get(form.name).copied() else {
                    return Err(ParseError::new(format!("unknown theorem `{}`", form.name)));
                };
                if !defined_theorems.insert(name) {
                    return Err(ParseError::new(format!(
                        "duplicate theorem `{}`",
                        form.name
                    )));
                }

                let mut theorem_parser = TermParser::new_with_local_symbols(
                    term_definitions,
                    symbols,
                    FIRST_THEOREM_SYMBOL,
                )?;
                let prop = theorem_parser.prop(form.body)?;
                theorems.push(ParsedTheorem {
                    name,
                    prop,
                    local_symbols: theorem_parser.into_local_symbols(),
                });
            }
            _ => unreachable!("top_level_form only returns known form kinds"),
        }
    }

    for binding in term_definitions {
        if !defined_terms.contains(&binding.name) {
            return Err(ParseError::new(format!(
                "missing definition `{}`",
                binding.spelling
            )));
        }
    }

    for binding in theorem_definitions {
        if !defined_theorems.contains(&binding.name) {
            return Err(ParseError::new(format!(
                "missing theorem `{}`",
                binding.spelling
            )));
        }
    }

    Ok(ParsedModule { terms, theorems })
}

struct TopLevelForm<'a> {
    kind: &'a str,
    name: &'a str,
    body: &'a Expr,
}

fn top_level_form(expression: &Expr) -> Result<TopLevelForm<'_>, ParseError> {
    let Expr::List(items) = expression else {
        return Err(ParseError::new("top-level form must be a list"));
    };
    if items.len() != 3 {
        return Err(ParseError::new(
            "top-level form must be (def <name> <term>) or (theorem <name> <prop>)",
        ));
    }

    let kind = atom(&items[0])?;
    match kind {
        "def" | "theorem" => Ok(TopLevelForm {
            kind,
            name: atom(&items[1])?,
            body: &items[2],
        }),
        _ => Err(ParseError::new(format!("unknown top-level form `{kind}`"))),
    }
}

fn name_map<'a>(
    bindings: &'a [NameBinding],
    kind: &str,
) -> Result<HashMap<&'a str, Name>, ParseError> {
    let mut names = HashMap::new();
    for binding in bindings {
        if names.insert(binding.spelling, binding.name).is_some() {
            return Err(ParseError::new(format!(
                "duplicate {kind} binding `{}`",
                binding.spelling
            )));
        }
    }

    Ok(names)
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
    local_symbols: Vec<LocalSymbol>,
    next_local_symbol: Option<u64>,
    used_symbols: HashSet<Symbol>,
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

        let used_symbols = symbol_map.values().copied().collect();

        Ok(Self {
            definitions: definition_map,
            symbols: symbol_map,
            scopes: Vec::new(),
            local_symbols: Vec::new(),
            next_local_symbol: None,
            used_symbols,
        })
    }

    fn new_with_local_symbols(
        definitions: &'a [NameBinding],
        symbols: &'a [SymbolBinding],
        first_local_symbol: Symbol,
    ) -> Result<Self, ParseError> {
        let mut parser = Self::new(definitions, symbols)?;
        parser.next_local_symbol = Some(first_local_symbol.0);
        Ok(parser)
    }

    fn into_local_symbols(self) -> Vec<LocalSymbol> {
        self.local_symbols
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
        let symbol = self.binder_symbol(parameter)?;
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
        let cons_symbol = self.binder_symbol(cons)?;

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
        Ok(Term::Quote(self.static_symbol(atom(&items[1])?)?))
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

    fn prop(&mut self, expression: &Expr) -> Result<Prop, ParseError> {
        let Expr::List(items) = expression else {
            return Err(ParseError::new("expected proposition"));
        };
        let Some(head) = items.first() else {
            return Err(ParseError::new("empty proposition"));
        };
        let form = atom(head)?;

        match form {
            "equal" => self.equal(items),
            "computes-to" => self.computes_to(items),
            "is-value" => self.is_value(items),
            "is-list" => self.is_list(items),
            "implies" => self.implies(items),
            "forall" => self.forall(items),
            "exists" => self.exists(items),
            "and" => self.and(items),
            "or" => self.or(items),
            "computes-to-list" => self.computes_to_list(items),
            "errors" => self.errors(items),
            "diverges" => self.diverges(items),
            _ => Err(ParseError::new(format!("unknown proposition `{form}`"))),
        }
    }

    fn equal(&mut self, items: &[Expr]) -> Result<Prop, ParseError> {
        expect_len("equal", items, 3)?;
        Ok(equal(self.term(&items[1])?, self.term(&items[2])?))
    }

    fn computes_to(&mut self, items: &[Expr]) -> Result<Prop, ParseError> {
        expect_len("computes-to", items, 3)?;
        Ok(computes_to(self.term(&items[1])?, self.term(&items[2])?))
    }

    fn is_value(&mut self, items: &[Expr]) -> Result<Prop, ParseError> {
        expect_len("is-value", items, 2)?;
        Ok(is_value(self.term(&items[1])?))
    }

    fn is_list(&mut self, items: &[Expr]) -> Result<Prop, ParseError> {
        expect_len("is-list", items, 2)?;
        Ok(is_list(self.term(&items[1])?))
    }

    fn implies(&mut self, items: &[Expr]) -> Result<Prop, ParseError> {
        expect_len("implies", items, 3)?;
        Ok(implies(self.prop(&items[1])?, self.prop(&items[2])?))
    }

    fn forall(&mut self, items: &[Expr]) -> Result<Prop, ParseError> {
        expect_len("forall", items, 3)?;
        let variable = atom(&items[1])?;
        let symbol = self.binder_symbol(variable)?;
        self.push_variable(variable, symbol);
        let body = self.prop(&items[2])?;
        self.pop_variable();

        Ok(forall(symbol, body))
    }

    fn exists(&mut self, items: &[Expr]) -> Result<Prop, ParseError> {
        expect_len("exists", items, 3)?;
        let variable = atom(&items[1])?;
        let symbol = self.binder_symbol(variable)?;
        self.push_variable(variable, symbol);
        let body = self.prop(&items[2])?;
        self.pop_variable();

        Ok(exists(symbol, body))
    }

    fn and(&mut self, items: &[Expr]) -> Result<Prop, ParseError> {
        expect_len("and", items, 3)?;
        Ok(and(self.prop(&items[1])?, self.prop(&items[2])?))
    }

    fn or(&mut self, items: &[Expr]) -> Result<Prop, ParseError> {
        expect_len("or", items, 3)?;
        Ok(or(self.prop(&items[1])?, self.prop(&items[2])?))
    }

    fn computes_to_list(&mut self, items: &[Expr]) -> Result<Prop, ParseError> {
        expect_len("computes-to-list", items, 3)?;
        Ok(computes_to_list(
            self.binder_symbol(atom(&items[1])?)?,
            self.term(&items[2])?,
        ))
    }

    fn errors(&mut self, items: &[Expr]) -> Result<Prop, ParseError> {
        expect_len("errors", items, 3)?;
        Ok(errors(
            self.binder_symbol(atom(&items[1])?)?,
            self.term(&items[2])?,
        ))
    }

    fn diverges(&mut self, items: &[Expr]) -> Result<Prop, ParseError> {
        expect_len("diverges", items, 2)?;
        Ok(diverges(self.term(&items[1])?))
    }

    fn static_symbol(&self, spelling: &str) -> Result<Symbol, ParseError> {
        self.symbols
            .get(spelling)
            .copied()
            .ok_or_else(|| ParseError::new(format!("unknown symbol `{spelling}`")))
    }

    fn binder_symbol(&mut self, spelling: &str) -> Result<Symbol, ParseError> {
        if self.next_local_symbol.is_some() {
            return self.allocate_local_symbol(spelling);
        }

        self.static_symbol(spelling)
    }

    fn allocate_local_symbol(&mut self, spelling: &str) -> Result<Symbol, ParseError> {
        let Some(mut next) = self.next_local_symbol else {
            return Err(ParseError::new(format!("unknown symbol `{spelling}`")));
        };

        loop {
            let symbol = Symbol(next);
            next += 1;
            self.next_local_symbol = Some(next);

            if self.used_symbols.insert(symbol) {
                self.local_symbols.push(LocalSymbol {
                    spelling: spelling.to_owned(),
                    symbol,
                });
                return Ok(symbol);
            }
        }
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
    fn parses_module_terms_and_theorems() {
        let terms = [
            NameBinding {
                spelling: "id",
                name: Name(1),
            },
            NameBinding {
                spelling: "use_id",
                name: Name(2),
            },
        ];
        let theorems = [NameBinding {
            spelling: "use_id_computes",
            name: Name(3),
        }];
        let symbols = [SymbolBinding {
            spelling: "x",
            symbol: Symbol(1),
        }];

        assert_eq!(
            parse_module(
                "
                ; comments are ignored
                (def id (lambda x x))
                (def use_id (id nil))
                (theorem use_id_computes
                  (forall value
                    (computes-to (use_id value) value)))
                ",
                &terms,
                &theorems,
                &symbols,
            ),
            Ok(ParsedModule {
                terms: vec![
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
                ],
                theorems: vec![ParsedTheorem {
                    name: Name(3),
                    prop: forall(
                        Symbol(2_000),
                        computes_to(
                            Term::Apply {
                                function: Box::new(Term::Const(Name(2))),
                                argument: Box::new(Term::Var(Symbol(2_000))),
                            },
                            Term::Var(Symbol(2_000)),
                        ),
                    ),
                    local_symbols: vec![LocalSymbol {
                        spelling: "value".to_owned(),
                        symbol: Symbol(2_000),
                    }],
                }],
            })
        );
    }

    #[test]
    fn rejects_unbound_identifiers() {
        let definitions = [NameBinding {
            spelling: "bad",
            name: Name(1),
        }];

        let error = parse_module("(def bad x)", &definitions, &[], &[])
            .expect_err("free identifier should fail");

        assert_eq!(error.message, "unknown identifier `x`");
    }

    #[test]
    fn allocates_theorem_local_symbols() {
        let theorems = [NameBinding {
            spelling: "use_id_computes_to_list",
            name: Name(3),
        }];
        let terms = [NameBinding {
            spelling: "use_id",
            name: Name(2),
        }];

        assert_eq!(
            parse_module(
                "
                (def use_id nil)
                (theorem use_id_computes_to_list
                  (forall x
                    (implies
                      (is-list x)
                      (computes-to-list result (use_id x)))))
                ",
                &terms,
                &theorems,
                &[],
            ),
            Ok(ParsedModule {
                terms: vec![(Name(2), Term::Nil)],
                theorems: vec![ParsedTheorem {
                    name: Name(3),
                    prop: forall(
                        Symbol(2_000),
                        implies(
                            is_list(Term::Var(Symbol(2_000))),
                            computes_to_list(
                                Symbol(2_001),
                                Term::Apply {
                                    function: Box::new(Term::Const(Name(2))),
                                    argument: Box::new(Term::Var(Symbol(2_000))),
                                },
                            ),
                        ),
                    ),
                    local_symbols: vec![
                        LocalSymbol {
                            spelling: "x".to_owned(),
                            symbol: Symbol(2_000),
                        },
                        LocalSymbol {
                            spelling: "result".to_owned(),
                            symbol: Symbol(2_001),
                        },
                    ],
                }],
            })
        );
    }
}
