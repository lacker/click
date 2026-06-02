//! S-expression source parsing and elaboration into kernel syntax.

use std::collections::{HashMap, HashSet};

use crate::{
    Computation, ErrorName, Lambda, ListCase, Name, Prop, Symbol, and, computes_to,
    computes_to_list, diverges, equal, errors_with, exists, exists_where, forall, forall_where,
    implies, is_effect, is_list, is_outcome, is_value, or,
};

const FIRST_THEOREM_SYMBOL: Symbol = Symbol(2_000);

#[derive(Clone, Copy)]
#[cfg(test)]
pub(crate) struct NameBinding {
    pub spelling: &'static str,
    pub name: Name,
}

#[derive(Clone, Copy)]
#[cfg(test)]
pub(crate) struct SymbolBinding {
    pub spelling: &'static str,
    pub symbol: Symbol,
}

#[derive(Clone, Copy)]
pub(crate) struct ModuleSpec {
    pub source: &'static str,
}

impl ModuleSpec {
    pub(crate) fn parse(&self, env: &mut ElabEnv) -> Result<ParsedModule, ParseError> {
        env.parse_module(self.source)
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ElabEnv {
    computations: HashMap<String, Name>,
    theorems: HashMap<String, Name>,
    symbols: HashMap<String, Symbol>,
    next_name: u64,
    next_symbol: u64,
}

impl Default for ElabEnv {
    fn default() -> Self {
        Self::new()
    }
}

impl ElabEnv {
    pub fn new() -> Self {
        Self {
            computations: HashMap::new(),
            theorems: HashMap::new(),
            symbols: HashMap::new(),
            next_name: 1,
            next_symbol: 1,
        }
    }

    pub(crate) fn parse_module(&mut self, source: &str) -> Result<ParsedModule, ParseError> {
        let tokens = tokenize(source);
        let expressions = parse_expressions(&tokens)?;
        self.register_top_level_names(&expressions)?;

        let mut symbols = SymbolTable::allocating(self.symbols.clone(), self.next_symbol);
        let module = parse_module_expressions(
            &expressions,
            &self.computations,
            &self.theorems,
            &mut symbols,
        )?;
        let (symbol_map, next_symbol) = symbols.into_parts();
        self.symbols = symbol_map;
        self.next_symbol = next_symbol.expect("allocating symbol tables track the next symbol");

        Ok(module)
    }

    #[allow(dead_code)]
    pub fn computation(&self, spelling: &str) -> Option<Name> {
        self.computations.get(spelling).copied()
    }

    #[allow(dead_code)]
    pub fn theorem(&self, spelling: &str) -> Option<Name> {
        self.theorems.get(spelling).copied()
    }

    pub fn symbol(&self, spelling: &str) -> Option<Symbol> {
        self.symbols.get(spelling).copied()
    }

    pub fn intern_symbol(&mut self, spelling: &str) -> Symbol {
        if let Some(symbol) = self.symbol(spelling) {
            return symbol;
        }

        let symbol = loop {
            let symbol = Symbol(self.next_symbol);
            self.next_symbol += 1;
            if !self.symbols.values().any(|used| *used == symbol) {
                break symbol;
            }
        };
        self.symbols.insert(spelling.to_owned(), symbol);

        symbol
    }

    fn register_top_level_names(&mut self, expressions: &[Expr]) -> Result<(), ParseError> {
        for expression in expressions {
            let form = top_level_form(expression)?;
            match form.kind {
                "def" => {
                    if self.computations.contains_key(form.name)
                        || self.theorems.contains_key(form.name)
                    {
                        return Err(ParseError::new(format!(
                            "duplicate top-level name `{}`",
                            form.name
                        )));
                    }
                    let name = self.allocate_name();
                    self.computations.insert(form.name.to_owned(), name);
                }
                "theorem" => {
                    if self.computations.contains_key(form.name)
                        || self.theorems.contains_key(form.name)
                    {
                        return Err(ParseError::new(format!(
                            "duplicate top-level name `{}`",
                            form.name
                        )));
                    }
                    let name = self.allocate_name();
                    self.theorems.insert(form.name.to_owned(), name);
                }
                _ => unreachable!("top_level_form only returns known form kinds"),
            }
        }

        Ok(())
    }

    fn allocate_name(&mut self) -> Name {
        let name = Name(self.next_name);
        self.next_name += 1;
        name
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct LocalSymbol {
    spelling: String,
    symbol: Symbol,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct ParsedTheorem {
    pub name: Name,
    pub prop: Prop,
    pub proof: ProofScript,
    local_symbols: Vec<LocalSymbol>,
}

impl ParsedTheorem {
    #[cfg(test)]
    pub(crate) fn symbol(&self, spelling: &str) -> Option<Symbol> {
        let mut matches = self
            .local_symbols
            .iter()
            .filter(|symbol| symbol.spelling == spelling);
        let symbol = matches.next()?.symbol;

        matches.next().is_none().then_some(symbol)
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum ProofScript {
    Proof(ProofExpr),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum ProofExpr {
    Known(Name),
    Assume(Symbol),
    Symm(Box<ProofExpr>),
    Trans(Box<ProofExpr>, Box<ProofExpr>),
    EvalTo {
        computation: Computation,
        expected: Computation,
        limit: usize,
    },
    EvalSame {
        left: Computation,
        right: Computation,
        limit: usize,
    },
    Rewrite {
        equality: Box<ProofExpr>,
        proof: Box<ProofExpr>,
        variable: Symbol,
        template: Prop,
    },
    ImpliesIntro {
        assumption: Symbol,
        premise: Prop,
        proof: Box<ProofExpr>,
    },
    ImpliesElim {
        implication: Box<ProofExpr>,
        premise: Box<ProofExpr>,
    },
    ExistsIntro {
        variable: Symbol,
        guard: Option<Prop>,
        body: Prop,
        witness: Computation,
        proof: Box<ProofExpr>,
    },
    ExistsElim {
        existential: Box<ProofExpr>,
        witness: Symbol,
        assumption: Symbol,
        proof: Box<ProofExpr>,
    },
    AndIntro(Box<ProofExpr>, Box<ProofExpr>),
    AndElimLeft(Box<ProofExpr>),
    AndElimRight(Box<ProofExpr>),
    ListInduction {
        variable: Symbol,
        property: Prop,
        base: Box<ProofExpr>,
        head: Symbol,
        tail: Symbol,
        induction_hypothesis_assumption: Symbol,
        step: Box<ProofExpr>,
    },
    ForAllIntro {
        variable: Symbol,
        guard: Option<Prop>,
        proof: Box<ProofExpr>,
    },
    ForAllElim {
        forall: Box<ProofExpr>,
        argument: Computation,
    },
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct ParsedModule {
    pub computations: Vec<(Name, Computation)>,
    pub theorems: Vec<ParsedTheorem>,
}

impl ParsedModule {
    pub(crate) fn computation(&self, name: Name) -> Option<&Computation> {
        self.computations
            .iter()
            .find_map(|(computation_name, computation)| {
                (*computation_name == name).then_some(computation)
            })
    }

    pub(crate) fn theorem(&self, name: Name) -> Option<&ParsedTheorem> {
        self.theorems.iter().find(|theorem| theorem.name == name)
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ParseError {
    message: String,
}

impl ParseError {
    fn new(message: impl Into<String>) -> Self {
        Self {
            message: message.into(),
        }
    }

    pub fn message(&self) -> &str {
        &self.message
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

#[cfg(test)]
pub(crate) fn parse_module(
    source: &str,
    computation_definitions: &[NameBinding],
    theorem_definitions: &[NameBinding],
    symbols: &[SymbolBinding],
) -> Result<ParsedModule, ParseError> {
    let tokens = tokenize(source);
    let expressions = parse_expressions(&tokens)?;

    let computation_names = name_map(computation_definitions, "definition")?;
    let theorem_names = name_map(theorem_definitions, "theorem")?;
    let mut symbols = SymbolTable::fixed(symbols)?;

    let module = parse_module_expressions(
        &expressions,
        &computation_names,
        &theorem_names,
        &mut symbols,
    )?;

    for binding in computation_definitions {
        if module.computation(binding.name).is_none() {
            return Err(ParseError::new(format!(
                "missing definition `{}`",
                binding.spelling
            )));
        }
    }

    for binding in theorem_definitions {
        if module.theorem(binding.name).is_none() {
            return Err(ParseError::new(format!(
                "missing theorem `{}`",
                binding.spelling
            )));
        }
    }

    Ok(module)
}

fn parse_module_expressions(
    expressions: &[Expr],
    computation_names: &HashMap<String, Name>,
    theorem_names: &HashMap<String, Name>,
    symbols: &mut SymbolTable,
) -> Result<ParsedModule, ParseError> {
    let mut defined_computations = HashSet::new();
    let mut defined_theorems = HashSet::new();
    let mut computations = Vec::new();
    let mut theorems = Vec::new();

    for expression in expressions {
        let form = top_level_form(&expression)?;

        match form.kind {
            "def" => {
                let Some(name) = computation_names.get(form.name).copied() else {
                    return Err(ParseError::new(format!(
                        "unknown definition `{}`",
                        form.name
                    )));
                };
                if !defined_computations.insert(name) {
                    return Err(ParseError::new(format!(
                        "duplicate definition `{}`",
                        form.name
                    )));
                }

                let mut source_parser =
                    SourceParser::new(computation_names, theorem_names, symbols);
                let computation = source_parser.computation(form.body)?;
                computations.push((name, computation));
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

                let Some(proof_expr) = form.proof else {
                    return Err(ParseError::new(format!(
                        "theorem `{}` is missing a proof script",
                        form.name
                    )));
                };

                let mut theorem_parser = SourceParser::new_with_local_symbols(
                    symbols,
                    computation_names,
                    theorem_names,
                    FIRST_THEOREM_SYMBOL,
                );
                let prop = theorem_parser.prop(form.body)?;
                let proof = theorem_parser.proof_script(proof_expr)?;
                theorems.push(ParsedTheorem {
                    name,
                    prop,
                    proof,
                    local_symbols: theorem_parser.into_local_symbols(),
                });
            }
            _ => unreachable!("top_level_form only returns known form kinds"),
        }
    }

    Ok(ParsedModule {
        computations,
        theorems,
    })
}

struct TopLevelForm<'a> {
    kind: &'a str,
    name: &'a str,
    body: &'a Expr,
    proof: Option<&'a Expr>,
}

fn top_level_form(expression: &Expr) -> Result<TopLevelForm<'_>, ParseError> {
    let Expr::List(items) = expression else {
        return Err(ParseError::new("top-level form must be a list"));
    };
    let kind = atom(&items[0])?;
    match kind {
        "def" if items.len() == 3 => Ok(TopLevelForm {
            kind,
            name: atom(&items[1])?,
            body: &items[2],
            proof: None,
        }),
        "theorem" if items.len() == 4 => Ok(TopLevelForm {
            kind,
            name: atom(&items[1])?,
            body: &items[2],
            proof: Some(&items[3]),
        }),
        "def" | "theorem" => Err(ParseError::new(
            "top-level form must be (def <name> <computation>) or (theorem <name> <prop> <proof>)",
        )),
        _ => Err(ParseError::new(format!("unknown top-level form `{kind}`"))),
    }
}

#[cfg(test)]
fn name_map(bindings: &[NameBinding], kind: &str) -> Result<HashMap<String, Name>, ParseError> {
    let mut names = HashMap::new();
    for binding in bindings {
        if names
            .insert(binding.spelling.to_owned(), binding.name)
            .is_some()
        {
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

fn error_name(expression: &Expr) -> Result<ErrorName, ParseError> {
    Ok(ErrorName(parse_u64(atom(expression)?)?))
}

struct SymbolTable {
    symbols: HashMap<String, Symbol>,
    used_symbols: HashSet<Symbol>,
    next_static_symbol: Option<u64>,
}

impl SymbolTable {
    #[cfg(test)]
    fn fixed(bindings: &[SymbolBinding]) -> Result<Self, ParseError> {
        let mut symbols = HashMap::new();
        for binding in bindings {
            if symbols
                .insert(binding.spelling.to_owned(), binding.symbol)
                .is_some()
            {
                return Err(ParseError::new(format!(
                    "duplicate symbol binding `{}`",
                    binding.spelling
                )));
            }
        }

        let used_symbols = symbols.values().copied().collect();

        Ok(Self {
            symbols,
            used_symbols,
            next_static_symbol: None,
        })
    }

    fn allocating(symbols: HashMap<String, Symbol>, next_static_symbol: u64) -> Self {
        let used_symbols = symbols.values().copied().collect();

        Self {
            symbols,
            used_symbols,
            next_static_symbol: Some(next_static_symbol),
        }
    }

    fn into_parts(self) -> (HashMap<String, Symbol>, Option<u64>) {
        (self.symbols, self.next_static_symbol)
    }

    fn static_symbol(&mut self, spelling: &str) -> Result<Symbol, ParseError> {
        if let Some(symbol) = self.symbols.get(spelling).copied() {
            return Ok(symbol);
        }

        let Some(mut next) = self.next_static_symbol else {
            return Err(ParseError::new(format!("unknown symbol `{spelling}`")));
        };

        let symbol = loop {
            let symbol = Symbol(next);
            next += 1;
            if self.used_symbols.insert(symbol) {
                break symbol;
            }
        };
        self.next_static_symbol = Some(next);
        self.symbols.insert(spelling.to_owned(), symbol);

        Ok(symbol)
    }

    fn allocate_local_symbol(&mut self, next_local: &mut u64) -> Symbol {
        loop {
            let symbol = Symbol(*next_local);
            *next_local += 1;

            if self.used_symbols.insert(symbol) {
                return symbol;
            }
        }
    }
}

struct SourceParser<'a> {
    definitions: &'a HashMap<String, Name>,
    theorems: &'a HashMap<String, Name>,
    symbols: &'a mut SymbolTable,
    scopes: Vec<HashMap<String, Symbol>>,
    local_symbols: Vec<LocalSymbol>,
    next_local_symbol: Option<u64>,
}

#[derive(Clone, Copy)]
enum PropSymbolMode {
    Declare,
    Reference,
}

impl<'a> SourceParser<'a> {
    fn new(
        definitions: &'a HashMap<String, Name>,
        theorems: &'a HashMap<String, Name>,
        symbols: &'a mut SymbolTable,
    ) -> Self {
        Self {
            definitions,
            theorems,
            symbols,
            scopes: Vec::new(),
            local_symbols: Vec::new(),
            next_local_symbol: None,
        }
    }

    fn new_with_local_symbols(
        symbols: &'a mut SymbolTable,
        definitions: &'a HashMap<String, Name>,
        theorems: &'a HashMap<String, Name>,
        first_local_symbol: Symbol,
    ) -> Self {
        let mut parser = Self::new(definitions, theorems, symbols);
        parser.next_local_symbol = Some(first_local_symbol.0);
        parser
    }

    fn into_local_symbols(self) -> Vec<LocalSymbol> {
        self.local_symbols
    }

    fn definition(&self, spelling: &str) -> Option<Name> {
        self.definitions.get(spelling).copied()
    }

    fn theorem(&self, spelling: &str) -> Option<Name> {
        self.theorems.get(spelling).copied()
    }

    fn computation(&mut self, expression: &Expr) -> Result<Computation, ParseError> {
        match expression {
            Expr::Atom(atom) => self.atom_computation(atom),
            Expr::List(items) => self.list_computation(items),
        }
    }

    fn atom_computation(&self, spelling: &str) -> Result<Computation, ParseError> {
        match spelling {
            "nil" => Ok(Computation::Nil),
            "diverge" => Ok(Computation::Diverge),
            _ => {
                if let Some(symbol) = self.variable(spelling) {
                    return Ok(Computation::Var(symbol));
                }
                if let Some(symbol) = self.local_symbol(spelling) {
                    return Ok(Computation::Var(symbol));
                }
                if let Some(name) = self.definition(spelling) {
                    return Ok(Computation::Ref(name));
                }

                Err(ParseError::new(format!("unknown identifier `{spelling}`")))
            }
        }
    }

    fn list_computation(&mut self, items: &[Expr]) -> Result<Computation, ParseError> {
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

    fn lambda(&mut self, items: &[Expr]) -> Result<Computation, ParseError> {
        expect_len("lambda", items, 3)?;
        let parameter = atom(&items[1])?;
        let symbol = self.binder_symbol(parameter)?;
        self.push_variable(parameter, symbol);
        let body = self.computation(&items[2])?;
        self.pop_variable();

        Ok(Computation::Lambda(Lambda {
            parameter: symbol,
            body: Box::new(body),
        }))
    }

    fn list_case(&mut self, items: &[Expr]) -> Result<Computation, ParseError> {
        expect_len("list-case", items, 5)?;
        let list = self.computation(&items[1])?;
        let nil = self.computation(&items[2])?;
        let cons = atom(&items[3])?;
        let cons_symbol = self.binder_symbol(cons)?;

        self.push_variable(cons, cons_symbol);
        let cons_case = self.computation(&items[4])?;
        self.pop_variable();

        Ok(Computation::ListCase(ListCase {
            list: Box::new(list),
            nil: Box::new(nil),
            cons: cons_symbol,
            cons_case: Box::new(cons_case),
        }))
    }

    fn cons(&mut self, items: &[Expr]) -> Result<Computation, ParseError> {
        expect_len("cons", items, 3)?;
        Ok(Computation::Cons {
            head: Box::new(self.computation(&items[1])?),
            tail: Box::new(self.computation(&items[2])?),
        })
    }

    fn head(&mut self, items: &[Expr]) -> Result<Computation, ParseError> {
        expect_len("head", items, 2)?;
        Ok(Computation::Head(Box::new(self.computation(&items[1])?)))
    }

    fn tail(&mut self, items: &[Expr]) -> Result<Computation, ParseError> {
        expect_len("tail", items, 2)?;
        Ok(Computation::Tail(Box::new(self.computation(&items[1])?)))
    }

    fn error(&mut self, items: &[Expr]) -> Result<Computation, ParseError> {
        expect_len("error", items, 2)?;
        Ok(Computation::Error(error_name(&items[1])?))
    }

    fn quote(&mut self, items: &[Expr]) -> Result<Computation, ParseError> {
        expect_len("quote", items, 2)?;
        Ok(Computation::Quote(self.static_symbol(atom(&items[1])?)?))
    }

    fn application(&mut self, items: &[Expr]) -> Result<Computation, ParseError> {
        let mut computations = items
            .iter()
            .map(|item| self.computation(item))
            .collect::<Result<Vec<_>, _>>()?
            .into_iter();
        let Some(mut computation) = computations.next() else {
            return Err(ParseError::new("empty application"));
        };

        for argument in computations {
            computation = Computation::Apply {
                function: Box::new(computation),
                argument: Box::new(argument),
            };
        }

        Ok(computation)
    }

    fn prop(&mut self, expression: &Expr) -> Result<Prop, ParseError> {
        self.prop_with_symbols(expression, PropSymbolMode::Declare)
    }

    fn proof_prop(&mut self, expression: &Expr) -> Result<Prop, ParseError> {
        self.prop_with_symbols(expression, PropSymbolMode::Reference)
    }

    fn prop_with_symbols(
        &mut self,
        expression: &Expr,
        symbol_mode: PropSymbolMode,
    ) -> Result<Prop, ParseError> {
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
            "implies" => self.implies(items, symbol_mode),
            "forall" => self.forall(items, symbol_mode),
            "exists" => self.exists(items, symbol_mode),
            "and" => self.and(items, symbol_mode),
            "or" => self.or(items, symbol_mode),
            "computes-to-list" => self.computes_to_list(items, symbol_mode),
            "errors-with" => self.errors_with(items),
            "diverges" => self.diverges(items),
            "is-value" => self.is_value(items),
            "is-list" => self.is_list(items),
            "is-effect" => self.is_effect(items),
            "is-outcome" => self.is_outcome(items),
            _ => Err(ParseError::new(format!("unknown proposition `{form}`"))),
        }
    }

    fn equal(&mut self, items: &[Expr]) -> Result<Prop, ParseError> {
        expect_len("equal", items, 3)?;
        Ok(equal(
            self.computation(&items[1])?,
            self.computation(&items[2])?,
        ))
    }

    fn computes_to(&mut self, items: &[Expr]) -> Result<Prop, ParseError> {
        expect_len("computes-to", items, 3)?;
        Ok(computes_to(
            self.computation(&items[1])?,
            self.computation(&items[2])?,
        ))
    }

    fn implies(&mut self, items: &[Expr], symbol_mode: PropSymbolMode) -> Result<Prop, ParseError> {
        expect_len("implies", items, 3)?;
        Ok(implies(
            self.prop_with_symbols(&items[1], symbol_mode)?,
            self.prop_with_symbols(&items[2], symbol_mode)?,
        ))
    }

    fn forall(&mut self, items: &[Expr], symbol_mode: PropSymbolMode) -> Result<Prop, ParseError> {
        let (variable, guard, body) = match items.len() {
            3 => (atom(&items[1])?, None, &items[2]),
            4 => (atom(&items[1])?, Some(&items[2]), &items[3]),
            _ => {
                return Err(ParseError::new(format!(
                    "`forall` expects 2 or 3 arguments, got {}",
                    items.len().saturating_sub(1)
                )));
            }
        };
        let symbol = self.prop_symbol(variable, symbol_mode)?;
        self.push_variable(variable, symbol);
        let guard = self.quantifier_guard(guard, symbol_mode)?;
        let body = self.prop_with_symbols(body, symbol_mode)?;
        self.pop_variable();

        match guard {
            Some(guard) => Ok(forall_where(symbol, guard, body)),
            None => Ok(forall(symbol, body)),
        }
    }

    fn exists(&mut self, items: &[Expr], symbol_mode: PropSymbolMode) -> Result<Prop, ParseError> {
        let (variable, guard, body) = match items.len() {
            3 => (atom(&items[1])?, None, &items[2]),
            4 => (atom(&items[1])?, Some(&items[2]), &items[3]),
            _ => {
                return Err(ParseError::new(format!(
                    "`exists` expects 2 or 3 arguments, got {}",
                    items.len().saturating_sub(1)
                )));
            }
        };
        let symbol = self.prop_symbol(variable, symbol_mode)?;
        self.push_variable(variable, symbol);
        let guard = self.quantifier_guard(guard, symbol_mode)?;
        let body = self.prop_with_symbols(body, symbol_mode)?;
        self.pop_variable();

        match guard {
            Some(guard) => Ok(exists_where(symbol, guard, body)),
            None => Ok(exists(symbol, body)),
        }
    }

    fn and(&mut self, items: &[Expr], symbol_mode: PropSymbolMode) -> Result<Prop, ParseError> {
        expect_len("and", items, 3)?;
        Ok(and(
            self.prop_with_symbols(&items[1], symbol_mode)?,
            self.prop_with_symbols(&items[2], symbol_mode)?,
        ))
    }

    fn or(&mut self, items: &[Expr], symbol_mode: PropSymbolMode) -> Result<Prop, ParseError> {
        expect_len("or", items, 3)?;
        Ok(or(
            self.prop_with_symbols(&items[1], symbol_mode)?,
            self.prop_with_symbols(&items[2], symbol_mode)?,
        ))
    }

    fn computes_to_list(
        &mut self,
        items: &[Expr],
        symbol_mode: PropSymbolMode,
    ) -> Result<Prop, ParseError> {
        expect_len("computes-to-list", items, 3)?;
        Ok(computes_to_list(
            self.prop_symbol(atom(&items[1])?, symbol_mode)?,
            self.computation(&items[2])?,
        ))
    }

    fn errors_with(&mut self, items: &[Expr]) -> Result<Prop, ParseError> {
        expect_len("errors-with", items, 3)?;
        Ok(errors_with(
            self.computation(&items[1])?,
            error_name(&items[2])?,
        ))
    }

    fn diverges(&mut self, items: &[Expr]) -> Result<Prop, ParseError> {
        expect_len("diverges", items, 2)?;
        Ok(diverges(self.computation(&items[1])?))
    }

    fn is_value(&mut self, items: &[Expr]) -> Result<Prop, ParseError> {
        expect_len("is-value", items, 2)?;
        Ok(is_value(self.computation(&items[1])?))
    }

    fn is_list(&mut self, items: &[Expr]) -> Result<Prop, ParseError> {
        expect_len("is-list", items, 2)?;
        Ok(is_list(self.computation(&items[1])?))
    }

    fn is_effect(&mut self, items: &[Expr]) -> Result<Prop, ParseError> {
        expect_len("is-effect", items, 2)?;
        Ok(is_effect(self.computation(&items[1])?))
    }

    fn is_outcome(&mut self, items: &[Expr]) -> Result<Prop, ParseError> {
        expect_len("is-outcome", items, 2)?;
        Ok(is_outcome(self.computation(&items[1])?))
    }

    fn quantifier_guard(
        &mut self,
        guard: Option<&Expr>,
        symbol_mode: PropSymbolMode,
    ) -> Result<Option<Prop>, ParseError> {
        match guard {
            Some(prop) => Ok(Some(self.prop_with_symbols(prop, symbol_mode)?)),
            None => Ok(None),
        }
    }

    fn proof_script(&mut self, expression: &Expr) -> Result<ProofScript, ParseError> {
        let Expr::List(items) = expression else {
            return Err(ParseError::new("expected proof script"));
        };
        let Some(head) = items.first() else {
            return Err(ParseError::new("empty proof script"));
        };
        let form = atom(head)?;

        match form {
            "proof" => {
                expect_len("proof", items, 2)?;
                Ok(ProofScript::Proof(self.proof_expr(&items[1])?))
            }
            _ => Err(ParseError::new(format!("unknown proof script `{form}`"))),
        }
    }

    fn proof_expr(&mut self, expression: &Expr) -> Result<ProofExpr, ParseError> {
        let Expr::List(items) = expression else {
            return Err(ParseError::new("expected proof expression"));
        };
        let Some(head) = items.first() else {
            return Err(ParseError::new("empty proof expression"));
        };
        let form = atom(head)?;

        match form {
            "known" => self.proof_known(items),
            "assume" => self.proof_assume(items),
            "symm" => self.proof_symm(items),
            "trans" => self.proof_trans(items),
            "eval-to" => self.proof_eval_to(items),
            "eval-same" => self.proof_eval_same(items),
            "rewrite" => self.proof_rewrite(items),
            "list-induction" => self.proof_list_induction(items),
            "implies-intro" => self.proof_implies_intro(items),
            "implies-elim" => self.proof_implies_elim(items),
            "exists-intro" => self.proof_exists_intro(items),
            "exists-elim" => self.proof_exists_elim(items),
            "and-intro" => self.proof_and_intro(items),
            "and-elim-left" => self.proof_and_elim_left(items),
            "and-elim-right" => self.proof_and_elim_right(items),
            "forall-intro" => self.proof_forall_intro(items),
            "forall-elim" => self.proof_forall_elim(items),
            _ => Err(ParseError::new(format!(
                "unknown proof expression `{form}`"
            ))),
        }
    }

    fn proof_known(&self, items: &[Expr]) -> Result<ProofExpr, ParseError> {
        expect_len("known", items, 2)?;
        let theorem = atom(&items[1])?;
        let Some(name) = self.theorem(theorem) else {
            return Err(ParseError::new(format!("unknown theorem `{theorem}`")));
        };

        Ok(ProofExpr::Known(name))
    }

    fn proof_assume(&self, items: &[Expr]) -> Result<ProofExpr, ParseError> {
        expect_len("assume", items, 2)?;
        Ok(ProofExpr::Assume(
            self.existing_local_symbol(atom(&items[1])?)?,
        ))
    }

    fn proof_symm(&mut self, items: &[Expr]) -> Result<ProofExpr, ParseError> {
        expect_len("symm", items, 2)?;
        Ok(ProofExpr::Symm(Box::new(self.proof_expr(&items[1])?)))
    }

    fn proof_trans(&mut self, items: &[Expr]) -> Result<ProofExpr, ParseError> {
        expect_len("trans", items, 3)?;
        Ok(ProofExpr::Trans(
            Box::new(self.proof_expr(&items[1])?),
            Box::new(self.proof_expr(&items[2])?),
        ))
    }

    fn proof_eval_to(&mut self, items: &[Expr]) -> Result<ProofExpr, ParseError> {
        match items.len() {
            3 => Ok(ProofExpr::EvalTo {
                computation: self.computation(&items[1])?,
                expected: self.computation(&items[2])?,
                limit: 128,
            }),
            4 => Ok(ProofExpr::EvalTo {
                computation: self.computation(&items[1])?,
                expected: self.computation(&items[2])?,
                limit: parse_usize(atom(&items[3])?)?,
            }),
            _ => Err(ParseError::new(format!(
                "`eval-to` expects 2 or 3 arguments, got {}",
                items.len().saturating_sub(1)
            ))),
        }
    }

    fn proof_eval_same(&mut self, items: &[Expr]) -> Result<ProofExpr, ParseError> {
        match items.len() {
            3 => Ok(ProofExpr::EvalSame {
                left: self.computation(&items[1])?,
                right: self.computation(&items[2])?,
                limit: 128,
            }),
            4 => Ok(ProofExpr::EvalSame {
                left: self.computation(&items[1])?,
                right: self.computation(&items[2])?,
                limit: parse_usize(atom(&items[3])?)?,
            }),
            _ => Err(ParseError::new(format!(
                "`eval-same` expects 2 or 3 arguments, got {}",
                items.len().saturating_sub(1)
            ))),
        }
    }

    fn proof_rewrite(&mut self, items: &[Expr]) -> Result<ProofExpr, ParseError> {
        expect_len("rewrite", items, 5)?;
        Ok(ProofExpr::Rewrite {
            equality: Box::new(self.proof_expr(&items[1])?),
            proof: Box::new(self.proof_expr(&items[2])?),
            variable: self.proof_symbol(atom(&items[3])?)?,
            template: self.proof_prop(&items[4])?,
        })
    }

    fn proof_list_induction(&mut self, items: &[Expr]) -> Result<ProofExpr, ParseError> {
        expect_len("list-induction", items, 8)?;
        Ok(ProofExpr::ListInduction {
            variable: self.proof_symbol(atom(&items[1])?)?,
            property: self.proof_prop(&items[2])?,
            base: Box::new(self.proof_expr(&items[3])?),
            head: self.proof_symbol(atom(&items[4])?)?,
            tail: self.proof_symbol(atom(&items[5])?)?,
            induction_hypothesis_assumption: self.proof_symbol(atom(&items[6])?)?,
            step: Box::new(self.proof_expr(&items[7])?),
        })
    }

    fn proof_implies_intro(&mut self, items: &[Expr]) -> Result<ProofExpr, ParseError> {
        expect_len("implies-intro", items, 4)?;
        Ok(ProofExpr::ImpliesIntro {
            assumption: self.proof_symbol(atom(&items[1])?)?,
            premise: self.proof_prop(&items[2])?,
            proof: Box::new(self.proof_expr(&items[3])?),
        })
    }

    fn proof_implies_elim(&mut self, items: &[Expr]) -> Result<ProofExpr, ParseError> {
        expect_len("implies-elim", items, 3)?;
        Ok(ProofExpr::ImpliesElim {
            implication: Box::new(self.proof_expr(&items[1])?),
            premise: Box::new(self.proof_expr(&items[2])?),
        })
    }

    fn proof_exists_intro(&mut self, items: &[Expr]) -> Result<ProofExpr, ParseError> {
        let (variable, guard, body, witness, proof) = match items.len() {
            5 => (&items[1], None, &items[2], &items[3], &items[4]),
            6 => (&items[1], Some(&items[2]), &items[3], &items[4], &items[5]),
            _ => {
                return Err(ParseError::new(format!(
                    "`exists-intro` expects 4 or 5 arguments, got {}",
                    items.len().saturating_sub(1)
                )));
            }
        };
        let variable = self.proof_symbol(atom(variable)?)?;
        Ok(ProofExpr::ExistsIntro {
            variable,
            guard: self.quantifier_guard(guard, PropSymbolMode::Reference)?,
            body: self.proof_prop(body)?,
            witness: self.computation(witness)?,
            proof: Box::new(self.proof_expr(proof)?),
        })
    }

    fn proof_exists_elim(&mut self, items: &[Expr]) -> Result<ProofExpr, ParseError> {
        expect_len("exists-elim", items, 5)?;
        Ok(ProofExpr::ExistsElim {
            existential: Box::new(self.proof_expr(&items[1])?),
            witness: self.proof_symbol(atom(&items[2])?)?,
            assumption: self.proof_symbol(atom(&items[3])?)?,
            proof: Box::new(self.proof_expr(&items[4])?),
        })
    }

    fn proof_and_intro(&mut self, items: &[Expr]) -> Result<ProofExpr, ParseError> {
        expect_len("and-intro", items, 3)?;
        Ok(ProofExpr::AndIntro(
            Box::new(self.proof_expr(&items[1])?),
            Box::new(self.proof_expr(&items[2])?),
        ))
    }

    fn proof_and_elim_left(&mut self, items: &[Expr]) -> Result<ProofExpr, ParseError> {
        expect_len("and-elim-left", items, 2)?;
        Ok(ProofExpr::AndElimLeft(Box::new(
            self.proof_expr(&items[1])?,
        )))
    }

    fn proof_and_elim_right(&mut self, items: &[Expr]) -> Result<ProofExpr, ParseError> {
        expect_len("and-elim-right", items, 2)?;
        Ok(ProofExpr::AndElimRight(Box::new(
            self.proof_expr(&items[1])?,
        )))
    }

    fn proof_forall_intro(&mut self, items: &[Expr]) -> Result<ProofExpr, ParseError> {
        let (variable, guard, proof) = match items.len() {
            3 => (&items[1], None, &items[2]),
            4 => (&items[1], Some(&items[2]), &items[3]),
            _ => {
                return Err(ParseError::new(format!(
                    "`forall-intro` expects 2 or 3 arguments, got {}",
                    items.len().saturating_sub(1)
                )));
            }
        };
        let variable = self.proof_symbol(atom(variable)?)?;
        Ok(ProofExpr::ForAllIntro {
            variable,
            guard: self.quantifier_guard(guard, PropSymbolMode::Reference)?,
            proof: Box::new(self.proof_expr(proof)?),
        })
    }

    fn proof_forall_elim(&mut self, items: &[Expr]) -> Result<ProofExpr, ParseError> {
        expect_len("forall-elim", items, 3)?;
        Ok(ProofExpr::ForAllElim {
            forall: Box::new(self.proof_expr(&items[1])?),
            argument: self.computation(&items[2])?,
        })
    }

    fn static_symbol(&mut self, spelling: &str) -> Result<Symbol, ParseError> {
        self.symbols.static_symbol(spelling)
    }

    fn binder_symbol(&mut self, spelling: &str) -> Result<Symbol, ParseError> {
        if self.next_local_symbol.is_some() {
            return self.allocate_local_symbol(spelling);
        }

        self.static_symbol(spelling)
    }

    fn prop_symbol(&mut self, spelling: &str, mode: PropSymbolMode) -> Result<Symbol, ParseError> {
        match mode {
            PropSymbolMode::Declare => self.binder_symbol(spelling),
            PropSymbolMode::Reference => self.proof_symbol(spelling),
        }
    }

    fn proof_symbol(&mut self, spelling: &str) -> Result<Symbol, ParseError> {
        if let Some(symbol) = self.local_symbol(spelling) {
            return Ok(symbol);
        }

        self.binder_symbol(spelling)
    }

    fn existing_local_symbol(&self, spelling: &str) -> Result<Symbol, ParseError> {
        self.local_symbol(spelling)
            .ok_or_else(|| ParseError::new(format!("unknown proof symbol `{spelling}`")))
    }

    fn allocate_local_symbol(&mut self, spelling: &str) -> Result<Symbol, ParseError> {
        let Some(mut next) = self.next_local_symbol.take() else {
            return Err(ParseError::new(format!("unknown symbol `{spelling}`")));
        };

        let symbol = self.symbols.allocate_local_symbol(&mut next);
        self.next_local_symbol = Some(next);
        self.local_symbols.push(LocalSymbol {
            spelling: spelling.to_owned(),
            symbol,
        });

        Ok(symbol)
    }

    fn local_symbol(&self, spelling: &str) -> Option<Symbol> {
        let mut matches = self
            .local_symbols
            .iter()
            .filter(|symbol| symbol.spelling == spelling);
        let symbol = matches.next()?.symbol;

        matches.next().is_none().then_some(symbol)
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

fn parse_usize(atom: &str) -> Result<usize, ParseError> {
    atom.parse()
        .map_err(|_| ParseError::new(format!("expected natural number, got `{atom}`")))
}

fn parse_u64(atom: &str) -> Result<u64, ParseError> {
    atom.parse()
        .map_err(|_| ParseError::new(format!("expected natural number, got `{atom}`")))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn elab_env_allocates_names_and_symbols_from_source() {
        let mut env = ElabEnv::new();
        assert_eq!(env.intern_symbol(":true"), Symbol(1));

        let module = env
            .parse_module(
                "
                (def id (lambda x (quote :true)))
                (theorem id_computes
                  (computes-to (id nil) (quote :true))
                  (proof (eval-to (id nil) (quote :true))))
                ",
            )
            .expect("source should parse through environment");

        assert_eq!(env.computation("id"), Some(Name(1)));
        assert_eq!(env.theorem("id_computes"), Some(Name(2)));
        assert_eq!(env.symbol(":true"), Some(Symbol(1)));
        assert_eq!(env.symbol("x"), Some(Symbol(2)));
        assert!(module.computation(Name(1)).is_some());
        assert!(module.theorem(Name(2)).is_some());
    }

    #[test]
    fn parses_module_computations_and_theorems() {
        let computations = [
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
                    (computes-to (use_id value) value))
                  (proof
                    (forall-intro value
                      (eval-to (use_id value) value))))
                ",
                &computations,
                &theorems,
                &symbols,
            ),
            Ok(ParsedModule {
                computations: vec![
                    (
                        Name(1),
                        Computation::Lambda(Lambda {
                            parameter: Symbol(1),
                            body: Box::new(Computation::Var(Symbol(1))),
                        }),
                    ),
                    (
                        Name(2),
                        Computation::Apply {
                            function: Box::new(Computation::Ref(Name(1))),
                            argument: Box::new(Computation::Nil),
                        },
                    ),
                ],
                theorems: vec![ParsedTheorem {
                    name: Name(3),
                    prop: forall(
                        Symbol(2_000),
                        computes_to(
                            Computation::Apply {
                                function: Box::new(Computation::Ref(Name(2))),
                                argument: Box::new(Computation::Var(Symbol(2_000))),
                            },
                            Computation::Var(Symbol(2_000)),
                        ),
                    ),
                    proof: ProofScript::Proof(ProofExpr::ForAllIntro {
                        variable: Symbol(2_000),
                        guard: None,
                        proof: Box::new(ProofExpr::EvalTo {
                            computation: Computation::Apply {
                                function: Box::new(Computation::Ref(Name(2))),
                                argument: Box::new(Computation::Var(Symbol(2_000))),
                            },
                            expected: Computation::Var(Symbol(2_000)),
                            limit: 128,
                        }),
                    }),
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

        assert_eq!(error.message(), "unknown identifier `x`");
    }

    #[test]
    fn parses_named_errors() {
        let computations = [NameBinding {
            spelling: "bad",
            name: Name(1),
        }];
        let theorems = [NameBinding {
            spelling: "bad_errors",
            name: Name(2),
        }];

        assert_eq!(
            parse_module(
                "
                (def bad (error 7))
                (theorem bad_errors
                  (errors-with bad 7)
                  (proof (eval-to bad (error 7))))
                ",
                &computations,
                &theorems,
                &[],
            ),
            Ok(ParsedModule {
                computations: vec![(Name(1), Computation::Error(ErrorName(7)))],
                theorems: vec![ParsedTheorem {
                    name: Name(2),
                    prop: errors_with(Computation::Ref(Name(1)), ErrorName(7)),
                    proof: ProofScript::Proof(ProofExpr::EvalTo {
                        computation: Computation::Ref(Name(1)),
                        expected: Computation::Error(ErrorName(7)),
                        limit: 128,
                    }),
                    local_symbols: vec![],
                }],
            })
        );
    }

    #[test]
    fn allocates_theorem_local_symbols() {
        let theorems = [NameBinding {
            spelling: "use_id_computes_to_list",
            name: Name(3),
        }];
        let computations = [NameBinding {
            spelling: "use_id",
            name: Name(2),
        }];

        assert_eq!(
            parse_module(
                "
                (def use_id nil)
                (theorem use_id_computes_to_list
                  (forall x (is-list x)
                    (computes-to-list result (use_id x)))
                  (proof
                    (forall-intro x (is-list x)
                      (exists-intro result (is-list result)
                        (computes-to (use_id x) result)
                        x
                        (eval-to (use_id x) x)))))
                ",
                &computations,
                &theorems,
                &[],
            ),
            Ok(ParsedModule {
                computations: vec![(Name(2), Computation::Nil)],
                theorems: vec![ParsedTheorem {
                    name: Name(3),
                    prop: forall_where(
                        Symbol(2_000),
                        is_list(Computation::Var(Symbol(2_000))),
                        computes_to_list(
                            Symbol(2_001),
                            Computation::Apply {
                                function: Box::new(Computation::Ref(Name(2))),
                                argument: Box::new(Computation::Var(Symbol(2_000))),
                            },
                        ),
                    ),
                    proof: ProofScript::Proof(ProofExpr::ForAllIntro {
                        variable: Symbol(2_000),
                        guard: Some(is_list(Computation::Var(Symbol(2_000)))),
                        proof: Box::new(ProofExpr::ExistsIntro {
                            variable: Symbol(2_001),
                            guard: Some(is_list(Computation::Var(Symbol(2_001)))),
                            body: computes_to(
                                Computation::Apply {
                                    function: Box::new(Computation::Ref(Name(2))),
                                    argument: Box::new(Computation::Var(Symbol(2_000))),
                                },
                                Computation::Var(Symbol(2_001)),
                            ),
                            witness: Computation::Var(Symbol(2_000)),
                            proof: Box::new(ProofExpr::EvalTo {
                                computation: Computation::Apply {
                                    function: Box::new(Computation::Ref(Name(2))),
                                    argument: Box::new(Computation::Var(Symbol(2_000))),
                                },
                                expected: Computation::Var(Symbol(2_000)),
                                limit: 128,
                            }),
                        }),
                    }),
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

    #[test]
    fn rejects_legacy_guard_form() {
        let theorems = [NameBinding {
            spelling: "old_guard",
            name: Name(1),
        }];

        let error = parse_module(
            "
            (theorem old_guard
              (forall list x
                (equal x x))
              (proof
                (forall-intro list x
                  (eval-to x x))))
            ",
            &[],
            &theorems,
            &[],
        )
        .expect_err("legacy guard form should not parse");

        assert_eq!(error.message(), "expected proposition");
    }

    #[test]
    fn parses_existential_and_conjunction_eliminators() {
        let theorems = [NameBinding {
            spelling: "use_elims",
            name: Name(1),
        }];

        let module = parse_module(
            "
            (theorem use_elims
              (equal nil nil)
              (proof
                (exists-elim
                  (exists-intro witness
                    (and
                      (equal witness witness)
                      (equal nil nil))
                    nil
                    (and-intro
                      (eval-to nil nil)
                      (eval-to nil nil)))
                  unpacked
                  unpacked_proof
                  (and-intro
                    (and-elim-left
                      (assume unpacked_proof))
                    (and-elim-right
                      (assume unpacked_proof))))))
            ",
            &[],
            &theorems,
            &[],
        )
        .expect("source proof eliminators should parse");

        let ProofScript::Proof(ProofExpr::ExistsElim {
            existential,
            witness,
            assumption,
            proof,
        }) = &module.theorems[0].proof
        else {
            panic!("expected an exists-elim proof expression");
        };

        assert_eq!(*witness, Symbol(2_001));
        assert_eq!(*assumption, Symbol(2_002));
        assert!(matches!(
            existential.as_ref(),
            ProofExpr::ExistsIntro { variable, .. } if *variable == Symbol(2_000)
        ));

        let ProofExpr::AndIntro(left, right) = proof.as_ref() else {
            panic!("expected both conjunction eliminators under an and-intro");
        };
        assert!(matches!(left.as_ref(), ProofExpr::AndElimLeft(_)));
        assert!(matches!(right.as_ref(), ProofExpr::AndElimRight(_)));
    }
}
