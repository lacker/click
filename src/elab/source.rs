//! S-expression source parsing and elaboration into kernel syntax.

use std::collections::{HashMap, HashSet};

use crate::{
    Computation, ErrorName, FALSE_SYMBOL, LAMBDA_KIND_SYMBOL, LIST_KIND_SYMBOL, Lambda, ListCase,
    Name, Prop, SYMBOL_KIND_SYMBOL, Symbol, TRUE_SYMBOL, absurd, and, computes_to,
    computes_to_list, diverges, equal, errors_with, exists, exists_where, forall, forall_where,
    if_then_else, implies, is_bool, is_effect, is_list, is_outcome, is_value, or, substitute_prop,
    symbol_eq, value_kind,
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
        let symbols = HashMap::from([
            (":true".to_owned(), TRUE_SYMBOL),
            (":false".to_owned(), FALSE_SYMBOL),
            (":symbol".to_owned(), SYMBOL_KIND_SYMBOL),
            (":lambda".to_owned(), LAMBDA_KIND_SYMBOL),
            (":list".to_owned(), LIST_KIND_SYMBOL),
        ]);
        let max_reserved_symbol = [
            TRUE_SYMBOL,
            FALSE_SYMBOL,
            SYMBOL_KIND_SYMBOL,
            LAMBDA_KIND_SYMBOL,
            LIST_KIND_SYMBOL,
        ]
        .into_iter()
        .map(|symbol| symbol.0)
        .max()
        .expect("reserved symbol set should be nonempty");
        let next_symbol = max_reserved_symbol + 1;

        Self {
            computations: HashMap::new(),
            theorems: HashMap::new(),
            symbols,
            next_name: 1,
            next_symbol,
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

    pub fn computation(&self, spelling: &str) -> Option<Name> {
        self.computations.get(spelling).copied()
    }

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
    By(TacticScript),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum ProofExpr {
    Known(Name),
    Assume(Symbol),
    Primitive(Prop),
    Symm(Box<ProofExpr>),
    Trans(Box<ProofExpr>, Box<ProofExpr>),
    SymbolEqTrue(Box<ProofExpr>),
    IfTrueCondition(Box<ProofExpr>),
    IfTrueThen(Box<ProofExpr>),
    IfEffectThenConditionFalse(Box<ProofExpr>),
    IfEffectThenElse(Box<ProofExpr>),
    IfValueConditionBool(Box<ProofExpr>),
    DistinctOutcomes(Box<ProofExpr>),
    ValueNonSymbolNonLambdaIsList {
        value: Box<ProofExpr>,
        not_symbol: Box<ProofExpr>,
        not_lambda: Box<ProofExpr>,
    },
    AbsurdElim {
        absurd: Box<ProofExpr>,
        prop: Prop,
    },
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
    OrIntroLeft {
        proof: Box<ProofExpr>,
        right: Prop,
    },
    OrIntroRight {
        left: Prop,
        proof: Box<ProofExpr>,
    },
    OrElim {
        disjunction: Box<ProofExpr>,
        left_assumption: Symbol,
        left_proof: Box<ProofExpr>,
        right_assumption: Symbol,
        right_proof: Box<ProofExpr>,
    },
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
        proof: Box<ProofExpr>,
    },
    ForAllElim {
        forall: Box<ProofExpr>,
        argument: Computation,
    },
    Apply {
        proof: Box<ProofExpr>,
        arguments: Vec<Computation>,
    },
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct TacticScript {
    pub tactics: Vec<TacticExpr>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum TacticExpr {
    Intro(Symbol),
    Exact(Box<ProofExpr>),
    Assumption,
    Have {
        assumption: Symbol,
        prop: Prop,
        proof: ProofScript,
        body: Option<TacticScript>,
    },
    Eval {
        limit: usize,
    },
    Simp {
        rules: Vec<ProofExpr>,
    },
    Simpa {
        rules: Vec<ProofExpr>,
        proof: Option<Box<ProofExpr>>,
    },
    Fold {
        definition: Name,
    },
    Apply {
        theorem: Name,
        arguments: Vec<Computation>,
    },
    Specialize {
        assumption: Symbol,
        proof: Box<ProofExpr>,
        arguments: Vec<Computation>,
        body: Option<TacticScript>,
    },
    Split {
        left: TacticScript,
        right: TacticScript,
    },
    Exists {
        witness: Computation,
        proof: TacticScript,
    },
    Obtain {
        existential: Box<ProofExpr>,
        witness: Symbol,
        assumption: Symbol,
        body: Option<TacticScript>,
    },
    Cases {
        conjunction: Box<ProofExpr>,
        left_assumption: Symbol,
        right_assumption: Symbol,
        body: Option<TacticScript>,
    },
    OrElim {
        disjunction: Box<ProofExpr>,
        left_assumption: Symbol,
        left: TacticScript,
        right_assumption: Symbol,
        right: TacticScript,
    },
    Left(TacticScript),
    Right(TacticScript),
    Rewrite {
        equality: Box<ProofExpr>,
    },
    ListInduction {
        variable: Symbol,
        base: TacticScript,
        head: Symbol,
        tail: Symbol,
        induction_hypothesis_assumption: Symbol,
        step: TacticScript,
    },
    ValueInduction {
        variable: Symbol,
        symbol_assumption: Symbol,
        symbol_case: TacticScript,
        lambda_assumption: Symbol,
        lambda_case: TacticScript,
        nil_case: TacticScript,
        head: Symbol,
        tail: Symbol,
        head_induction_hypothesis_assumption: Symbol,
        tail_induction_hypothesis_assumption: Symbol,
        cons_case: TacticScript,
    },
    Calc {
        start: Computation,
        steps: Vec<CalcStep>,
    },
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct CalcStep {
    pub target: Computation,
    pub proof: ProofScript,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct ParsedModule {
    pub computations: Vec<(Name, Computation)>,
    pub theorems: Vec<ParsedTheorem>,
}

impl ParsedModule {
    #[cfg(test)]
    pub(crate) fn computation(&self, name: Name) -> Option<&Computation> {
        self.computations
            .iter()
            .find_map(|(computation_name, computation)| {
                (*computation_name == name).then_some(computation)
            })
    }

    #[cfg(test)]
    pub(crate) fn theorem(&self, name: Name) -> Option<&ParsedTheorem> {
        self.theorems.iter().find(|theorem| theorem.name == name)
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SourceSection {
    name: String,
}

impl SourceSection {
    pub fn new(name: impl Into<String>) -> Self {
        Self { name: name.into() }
    }

    pub fn name(&self) -> &str {
        &self.name
    }
}

impl From<&str> for SourceSection {
    fn from(name: &str) -> Self {
        Self::new(name)
    }
}

impl From<String> for SourceSection {
    fn from(name: String) -> Self {
        Self::new(name)
    }
}

impl std::fmt::Display for SourceSection {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.name.fmt(f)
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
                "if" => return self.if_computation(items),
                "symbol-eq" => return self.symbol_eq(items),
                "value-kind" => return self.value_kind(items),
                "is-symbol" if self.variable(form).is_none() => {
                    return self.value_kind_test(items, SYMBOL_KIND_SYMBOL);
                }
                "is-lambda" if self.variable(form).is_none() => {
                    return self.value_kind_test(items, LAMBDA_KIND_SYMBOL);
                }
                "is-list-value" if self.variable(form).is_none() => {
                    return self.value_kind_test(items, LIST_KIND_SYMBOL);
                }
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

    fn if_computation(&mut self, items: &[Expr]) -> Result<Computation, ParseError> {
        expect_len("if", items, 4)?;
        Ok(if_then_else(
            self.computation(&items[1])?,
            self.computation(&items[2])?,
            self.computation(&items[3])?,
        ))
    }

    fn symbol_eq(&mut self, items: &[Expr]) -> Result<Computation, ParseError> {
        expect_len("symbol-eq", items, 3)?;
        Ok(symbol_eq(
            self.computation(&items[1])?,
            self.computation(&items[2])?,
        ))
    }

    fn value_kind(&mut self, items: &[Expr]) -> Result<Computation, ParseError> {
        expect_len("value-kind", items, 2)?;
        Ok(value_kind(self.computation(&items[1])?))
    }

    fn value_kind_test(&mut self, items: &[Expr], kind: Symbol) -> Result<Computation, ParseError> {
        expect_len(atom(&items[0])?, items, 2)?;
        Ok(symbol_eq(
            value_kind(self.computation(&items[1])?),
            Computation::Quote(kind),
        ))
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
            "absurd" => self.absurd(items),
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
            "is-bool" => self.is_bool(items),
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

    fn absurd(&mut self, items: &[Expr]) -> Result<Prop, ParseError> {
        expect_len("absurd", items, 1)?;
        Ok(absurd())
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
        let (variable, predicate, body) = match items.len() {
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
        let predicate = self.quantifier_predicate(predicate, symbol_mode)?;
        let body = self.prop_with_symbols(body, symbol_mode)?;
        self.pop_variable();

        match predicate {
            Some(predicate) => Ok(forall_where(symbol, predicate, body)),
            None => Ok(forall(symbol, body)),
        }
    }

    fn exists(&mut self, items: &[Expr], symbol_mode: PropSymbolMode) -> Result<Prop, ParseError> {
        let (variable, predicate, body) = match items.len() {
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
        let predicate = self.quantifier_predicate(predicate, symbol_mode)?;
        let body = self.prop_with_symbols(body, symbol_mode)?;
        self.pop_variable();

        match predicate {
            Some(predicate) => Ok(exists_where(symbol, predicate, body)),
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

    fn is_bool(&mut self, items: &[Expr]) -> Result<Prop, ParseError> {
        expect_len("is-bool", items, 2)?;
        Ok(is_bool(self.computation(&items[1])?))
    }

    fn quantifier_predicate(
        &mut self,
        predicate: Option<&Expr>,
        symbol_mode: PropSymbolMode,
    ) -> Result<Option<Prop>, ParseError> {
        match predicate {
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
            "by" => Ok(ProofScript::By(self.tactic_script(items)?)),
            _ => Err(ParseError::new(format!("unknown proof script `{form}`"))),
        }
    }

    fn tactic_script(&mut self, items: &[Expr]) -> Result<TacticScript, ParseError> {
        if items.first().and_then(|head| atom(head).ok()) != Some("by") {
            return Err(ParseError::new("expected tactic script"));
        }

        Ok(TacticScript {
            tactics: items[1..]
                .iter()
                .map(|item| self.tactic_expr(item))
                .collect::<Result<Vec<_>, _>>()?,
        })
    }

    fn nested_tactic_script(&mut self, expression: &Expr) -> Result<TacticScript, ParseError> {
        let Expr::List(items) = expression else {
            return Err(ParseError::new("expected tactic script"));
        };
        self.tactic_script(items)
    }

    fn tactic_expr(&mut self, expression: &Expr) -> Result<TacticExpr, ParseError> {
        let Expr::List(items) = expression else {
            return Err(ParseError::new("expected tactic expression"));
        };
        let Some(head) = items.first() else {
            return Err(ParseError::new("empty tactic expression"));
        };
        let form = atom(head)?;

        match form {
            "intro" => self.tactic_intro(items),
            "exact" => self.tactic_exact(items),
            "assumption" => self.tactic_assumption(items),
            "have" => self.tactic_have(items),
            "eval" => self.tactic_eval(items),
            "simp" => self.tactic_simp(items),
            "simpa" => self.tactic_simpa(items),
            "fold" => self.tactic_fold(items),
            "apply" => self.tactic_apply(items),
            "specialize" => self.tactic_specialize(items),
            "split" | "constructor" => self.tactic_split(form, items),
            "exists" => self.tactic_exists(items),
            "obtain" => self.tactic_obtain(items),
            "cases" => self.tactic_cases(items),
            "or-elim" => self.tactic_or_elim(items),
            "left" => self.tactic_left(items),
            "right" => self.tactic_right(items),
            "rewrite" => self.tactic_rewrite(items),
            "induction" | "list-induction" => self.tactic_list_induction(form, items),
            "value-induction" => self.tactic_value_induction(items),
            "calc" => self.tactic_calc(items),
            _ => Err(ParseError::new(format!("unknown tactic `{form}`"))),
        }
    }

    fn tactic_intro(&mut self, items: &[Expr]) -> Result<TacticExpr, ParseError> {
        expect_len("intro", items, 2)?;
        Ok(TacticExpr::Intro(self.proof_symbol(atom(&items[1])?)?))
    }

    fn tactic_exact(&mut self, items: &[Expr]) -> Result<TacticExpr, ParseError> {
        if items.len() < 2 {
            return Err(ParseError::new(format!(
                "`exact` expects at least 1 argument, got {}",
                items.len().saturating_sub(1)
            )));
        }

        Ok(TacticExpr::Exact(Box::new(
            self.proof_expr_or_ref_with_arguments(&items[1], &items[2..])?,
        )))
    }

    fn tactic_assumption(&mut self, items: &[Expr]) -> Result<TacticExpr, ParseError> {
        expect_len("assumption", items, 1)?;
        Ok(TacticExpr::Assumption)
    }

    fn tactic_have(&mut self, items: &[Expr]) -> Result<TacticExpr, ParseError> {
        if !(4..=5).contains(&items.len()) {
            return Err(ParseError::new(format!(
                "`have` expects a name, proposition, proof script, and optional `(by ...)` body; got {} arguments",
                items.len().saturating_sub(1)
            )));
        }

        let assumption = self.proof_symbol(atom(&items[1])?)?;
        let prop = self.proof_prop(&items[2])?;
        let proof = self.proof_script(&items[3])?;
        let body = if items.len() == 5 {
            let Expr::List(body_items) = &items[4] else {
                return Err(ParseError::new(
                    "`have` body must be a `(by ...)` tactic script",
                ));
            };
            if body_items.first().and_then(|head| atom(head).ok()) != Some("by") {
                return Err(ParseError::new(
                    "`have` got an extra argument that is not a `(by ...)` body; if this is the next tactic, close the `(have ...)` form before it",
                ));
            }
            Some(self.tactic_script(body_items)?)
        } else {
            None
        };

        Ok(TacticExpr::Have {
            assumption,
            prop,
            proof,
            body,
        })
    }

    fn tactic_eval(&mut self, items: &[Expr]) -> Result<TacticExpr, ParseError> {
        match items.len() {
            1 => Ok(TacticExpr::Eval { limit: 128 }),
            2 => Ok(TacticExpr::Eval {
                limit: parse_usize(atom(&items[1])?)?,
            }),
            _ => Err(ParseError::new(format!(
                "`eval` expects 0 or 1 arguments, got {}",
                items.len().saturating_sub(1)
            ))),
        }
    }

    fn tactic_simp(&mut self, items: &[Expr]) -> Result<TacticExpr, ParseError> {
        if items.len() < 2 {
            return Err(ParseError::new(
                "`simp` currently expects `only` followed by zero or more theorem names",
            ));
        }
        let mode = atom(&items[1])?;
        if mode != "only" {
            return Err(ParseError::new(format!(
                "`simp` currently supports only explicit rules: expected `only`, got `{mode}`"
            )));
        }

        let mut rules = Vec::new();
        for item in &items[2..] {
            rules.push(self.proof_expr_or_ref(item)?);
        }

        Ok(TacticExpr::Simp { rules })
    }

    fn tactic_simpa(&mut self, items: &[Expr]) -> Result<TacticExpr, ParseError> {
        if items.len() < 2 {
            return Err(ParseError::new(
                "`simpa` currently expects `only` followed by zero or more rules and optional `using <proof>`",
            ));
        }
        let mode = atom(&items[1])?;
        if mode != "only" {
            return Err(ParseError::new(format!(
                "`simpa` currently supports only explicit rules: expected `only`, got `{mode}`"
            )));
        }

        let mut using_index = None;
        for (index, item) in items.iter().enumerate().skip(2) {
            if atom(item).ok() == Some("using") {
                if using_index.is_some() {
                    return Err(ParseError::new("`simpa` got more than one `using`"));
                }
                using_index = Some(index);
            }
        }

        let (rule_items, proof) = match using_index {
            Some(index) => {
                if items.len() != index + 2 {
                    return Err(ParseError::new(
                        "`simpa using` expects exactly one proof expression after `using`",
                    ));
                }
                (
                    &items[2..index],
                    Some(Box::new(self.proof_expr_or_ref(&items[index + 1])?)),
                )
            }
            None => (&items[2..], None),
        };

        let mut rules = Vec::new();
        for item in rule_items {
            rules.push(self.proof_expr_or_ref(item)?);
        }

        Ok(TacticExpr::Simpa { rules, proof })
    }

    fn tactic_fold(&mut self, items: &[Expr]) -> Result<TacticExpr, ParseError> {
        expect_len("fold", items, 2)?;
        let spelling = atom(&items[1])?;
        let Some(definition) = self.definition(spelling) else {
            return Err(ParseError::new(format!(
                "`fold` expected a computation definition, got `{spelling}`"
            )));
        };

        Ok(TacticExpr::Fold { definition })
    }

    fn tactic_apply(&mut self, items: &[Expr]) -> Result<TacticExpr, ParseError> {
        if items.len() < 2 {
            return Err(ParseError::new(format!(
                "`apply` expects at least 1 argument, got {}",
                items.len().saturating_sub(1)
            )));
        }

        let theorem = atom(&items[1])?;
        let Some(theorem) = self.theorem(theorem) else {
            return Err(ParseError::new(format!("unknown theorem `{theorem}`")));
        };

        Ok(TacticExpr::Apply {
            theorem,
            arguments: items[2..]
                .iter()
                .map(|item| self.computation(item))
                .collect::<Result<Vec<_>, _>>()?,
        })
    }

    fn tactic_specialize(&mut self, items: &[Expr]) -> Result<TacticExpr, ParseError> {
        if items.len() < 3 {
            return Err(ParseError::new(format!(
                "`specialize` expects a name, proof, zero or more arguments, and optional `(by ...)` body; got {} arguments",
                items.len().saturating_sub(1)
            )));
        }

        let assumption = self.proof_symbol(atom(&items[1])?)?;
        let proof = self.proof_expr_or_ref(&items[2])?;
        let (arguments, body) = self.split_optional_final_tactic_body(&items[3..])?;
        Ok(TacticExpr::Specialize {
            assumption,
            proof: Box::new(proof),
            arguments: arguments
                .iter()
                .map(|item| self.computation(item))
                .collect::<Result<Vec<_>, _>>()?,
            body,
        })
    }

    fn tactic_split(&mut self, form: &str, items: &[Expr]) -> Result<TacticExpr, ParseError> {
        expect_len(form, items, 3)?;
        Ok(TacticExpr::Split {
            left: self.nested_tactic_script(&items[1])?,
            right: self.nested_tactic_script(&items[2])?,
        })
    }

    fn tactic_exists(&mut self, items: &[Expr]) -> Result<TacticExpr, ParseError> {
        expect_len("exists", items, 3)?;
        Ok(TacticExpr::Exists {
            witness: self.computation(&items[1])?,
            proof: self.nested_tactic_script(&items[2])?,
        })
    }

    fn tactic_obtain(&mut self, items: &[Expr]) -> Result<TacticExpr, ParseError> {
        if !(4..=5).contains(&items.len()) {
            return Err(ParseError::new(format!(
                "`obtain` expects a witness name, proof name, existential proof, and optional `(by ...)` body; got {} arguments",
                items.len().saturating_sub(1)
            )));
        }

        let witness = self.proof_symbol(atom(&items[1])?)?;
        let assumption = self.proof_symbol(atom(&items[2])?)?;
        let existential = Box::new(self.proof_expr_or_ref(&items[3])?);
        let body = self.optional_tactic_body("obtain", items.get(4))?;

        Ok(TacticExpr::Obtain {
            existential,
            witness,
            assumption,
            body,
        })
    }

    fn optional_tactic_body(
        &mut self,
        form: &str,
        body: Option<&Expr>,
    ) -> Result<Option<TacticScript>, ParseError> {
        let Some(body) = body else {
            return Ok(None);
        };

        let Expr::List(body_items) = body else {
            return Err(ParseError::new(format!(
                "`{form}` body must be a `(by ...)` tactic script"
            )));
        };
        if body_items.first().and_then(|head| atom(head).ok()) != Some("by") {
            return Err(ParseError::new(format!(
                "`{form}` got an extra argument that is not a `(by ...)` body; if this is the next tactic, close the `({form} ...)` form before it"
            )));
        }

        Ok(Some(self.tactic_script(body_items)?))
    }

    fn split_optional_final_tactic_body<'b>(
        &mut self,
        items: &'b [Expr],
    ) -> Result<(&'b [Expr], Option<TacticScript>), ParseError> {
        let Some(Expr::List(body_items)) = items.last() else {
            return Ok((items, None));
        };
        if body_items.first().and_then(|head| atom(head).ok()) != Some("by") {
            return Ok((items, None));
        }

        Ok((
            &items[..items.len() - 1],
            Some(self.tactic_script(body_items)?),
        ))
    }

    fn tactic_cases(&mut self, items: &[Expr]) -> Result<TacticExpr, ParseError> {
        if !(4..=5).contains(&items.len()) {
            return Err(ParseError::new(format!(
                "`cases` expects a conjunction proof, left proof name, right proof name, and optional `(by ...)` body; got {} arguments",
                items.len().saturating_sub(1)
            )));
        }

        Ok(TacticExpr::Cases {
            conjunction: Box::new(self.proof_expr_or_ref(&items[1])?),
            left_assumption: self.proof_symbol(atom(&items[2])?)?,
            right_assumption: self.proof_symbol(atom(&items[3])?)?,
            body: self.optional_tactic_body("cases", items.get(4))?,
        })
    }

    fn tactic_or_elim(&mut self, items: &[Expr]) -> Result<TacticExpr, ParseError> {
        expect_len("or-elim", items, 6)?;
        Ok(TacticExpr::OrElim {
            disjunction: Box::new(self.proof_expr_or_ref(&items[1])?),
            left_assumption: self.proof_symbol(atom(&items[2])?)?,
            left: self.nested_tactic_script(&items[3])?,
            right_assumption: self.proof_symbol(atom(&items[4])?)?,
            right: self.nested_tactic_script(&items[5])?,
        })
    }

    fn tactic_left(&mut self, items: &[Expr]) -> Result<TacticExpr, ParseError> {
        expect_len("left", items, 2)?;
        Ok(TacticExpr::Left(self.nested_tactic_script(&items[1])?))
    }

    fn tactic_right(&mut self, items: &[Expr]) -> Result<TacticExpr, ParseError> {
        expect_len("right", items, 2)?;
        Ok(TacticExpr::Right(self.nested_tactic_script(&items[1])?))
    }

    fn tactic_rewrite(&mut self, items: &[Expr]) -> Result<TacticExpr, ParseError> {
        if items.len() < 2 {
            return Err(ParseError::new(format!(
                "`rewrite` expects at least 1 argument, got {}",
                items.len().saturating_sub(1)
            )));
        }
        Ok(TacticExpr::Rewrite {
            equality: Box::new(self.proof_expr_or_ref_with_arguments(&items[1], &items[2..])?),
        })
    }

    fn tactic_list_induction(
        &mut self,
        form: &str,
        items: &[Expr],
    ) -> Result<TacticExpr, ParseError> {
        expect_len(form, items, 7)?;
        Ok(TacticExpr::ListInduction {
            variable: self.proof_symbol(atom(&items[1])?)?,
            base: self.nested_tactic_script(&items[2])?,
            head: self.proof_symbol(atom(&items[3])?)?,
            tail: self.proof_symbol(atom(&items[4])?)?,
            induction_hypothesis_assumption: self.proof_symbol(atom(&items[5])?)?,
            step: self.nested_tactic_script(&items[6])?,
        })
    }

    fn tactic_value_induction(&mut self, items: &[Expr]) -> Result<TacticExpr, ParseError> {
        expect_len("value-induction", items, 12)?;
        Ok(TacticExpr::ValueInduction {
            variable: self.proof_symbol(atom(&items[1])?)?,
            symbol_assumption: self.proof_symbol(atom(&items[2])?)?,
            symbol_case: self.nested_tactic_script(&items[3])?,
            lambda_assumption: self.proof_symbol(atom(&items[4])?)?,
            lambda_case: self.nested_tactic_script(&items[5])?,
            nil_case: self.nested_tactic_script(&items[6])?,
            head: self.proof_symbol(atom(&items[7])?)?,
            tail: self.proof_symbol(atom(&items[8])?)?,
            head_induction_hypothesis_assumption: self.proof_symbol(atom(&items[9])?)?,
            tail_induction_hypothesis_assumption: self.proof_symbol(atom(&items[10])?)?,
            cons_case: self.nested_tactic_script(&items[11])?,
        })
    }

    fn tactic_calc(&mut self, items: &[Expr]) -> Result<TacticExpr, ParseError> {
        if items.len() < 3 {
            return Err(ParseError::new(format!(
                "`calc` expects a start expression and at least one step, got {}",
                items.len().saturating_sub(1)
            )));
        }

        Ok(TacticExpr::Calc {
            start: self.computation(&items[1])?,
            steps: items[2..]
                .iter()
                .map(|item| self.calc_step(item))
                .collect::<Result<Vec<_>, _>>()?,
        })
    }

    fn calc_step(&mut self, expression: &Expr) -> Result<CalcStep, ParseError> {
        let Expr::List(items) = expression else {
            return Err(ParseError::new("expected calc step"));
        };
        expect_len("==", items, 3)?;
        let form = atom(&items[0])?;
        if form != "==" {
            return Err(ParseError::new(format!(
                "expected calc step form `==`, got `{form}`"
            )));
        }

        Ok(CalcStep {
            target: self.computation(&items[1])?,
            proof: self.proof_script(&items[2])?,
        })
    }

    fn proof_expr_or_ref(&mut self, expression: &Expr) -> Result<ProofExpr, ParseError> {
        match expression {
            Expr::Atom(spelling) => {
                if let Some(symbol) = self.local_symbol(spelling) {
                    return Ok(ProofExpr::Assume(symbol));
                }
                if let Some(theorem) = self.theorem(spelling) {
                    return Ok(ProofExpr::Known(theorem));
                }

                Err(ParseError::new(format!("unknown proof `{spelling}`")))
            }
            Expr::List(items) => {
                let Some(head) = items.first() else {
                    return Err(ParseError::new("empty proof expression"));
                };
                if let Ok(spelling) = atom(head) {
                    if self.local_symbol(spelling).is_some() || self.theorem(spelling).is_some() {
                        return self.proof_expr_or_ref_with_arguments(head, &items[1..]);
                    }
                }

                self.proof_expr(expression)
            }
        }
    }

    fn proof_expr_or_ref_with_arguments(
        &mut self,
        expression: &Expr,
        arguments: &[Expr],
    ) -> Result<ProofExpr, ParseError> {
        let proof = self.proof_expr_or_ref(expression)?;
        self.apply_proof_arguments(proof, arguments)
    }

    fn apply_proof_arguments(
        &mut self,
        proof: ProofExpr,
        arguments: &[Expr],
    ) -> Result<ProofExpr, ParseError> {
        if arguments.is_empty() {
            return Ok(proof);
        }

        Ok(ProofExpr::Apply {
            proof: Box::new(proof),
            arguments: arguments
                .iter()
                .map(|argument| self.computation(argument))
                .collect::<Result<_, _>>()?,
        })
    }

    fn proof_expr(&mut self, expression: &Expr) -> Result<ProofExpr, ParseError> {
        let Expr::List(items) = expression else {
            return Err(ParseError::new("expected proof expression"));
        };
        let Some(head) = items.first() else {
            return Err(ParseError::new("empty proof expression"));
        };
        let form = atom(head)?;

        // These raw proof-expression forms map directly to kernel proof rules.
        // Goal-directed source should normally prefer `(by ...)` tactics.
        match form {
            "known" => self.proof_known(items),
            "assume" => self.proof_assume(items),
            "primitive" => self.proof_primitive(items),
            "symm" => self.proof_symm(items),
            "trans" => self.proof_trans(items),
            "symbol-eq-true" => self.proof_symbol_eq_true(items),
            "if-true-condition" => self.proof_if_true_condition(items),
            "if-true-then" => self.proof_if_true_then(items),
            "if-effect-then-condition-false" => self.proof_if_effect_then_condition_false(items),
            "if-effect-then-else" => self.proof_if_effect_then_else(items),
            "if-value-condition-bool" => self.proof_if_value_condition_bool(items),
            "distinct-outcomes" => self.proof_distinct_outcomes(items),
            "value-non-symbol-non-lambda-is-list" => {
                self.proof_value_non_symbol_non_lambda_is_list(items)
            }
            "absurd-elim" => self.proof_absurd_elim(items),
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
            "or-intro-left" => self.proof_or_intro_left(items),
            "or-intro-right" => self.proof_or_intro_right(items),
            "or-elim" => self.proof_or_elim(items),
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

    fn proof_primitive(&mut self, items: &[Expr]) -> Result<ProofExpr, ParseError> {
        expect_len("primitive", items, 2)?;
        Ok(ProofExpr::Primitive(self.proof_prop(&items[1])?))
    }

    fn proof_symm(&mut self, items: &[Expr]) -> Result<ProofExpr, ParseError> {
        expect_len("symm", items, 2)?;
        Ok(ProofExpr::Symm(Box::new(
            self.proof_expr_or_ref(&items[1])?,
        )))
    }

    fn proof_trans(&mut self, items: &[Expr]) -> Result<ProofExpr, ParseError> {
        expect_len("trans", items, 3)?;
        Ok(ProofExpr::Trans(
            Box::new(self.proof_expr(&items[1])?),
            Box::new(self.proof_expr(&items[2])?),
        ))
    }

    fn proof_symbol_eq_true(&mut self, items: &[Expr]) -> Result<ProofExpr, ParseError> {
        expect_len("symbol-eq-true", items, 2)?;
        Ok(ProofExpr::SymbolEqTrue(Box::new(
            self.proof_expr_or_ref(&items[1])?,
        )))
    }

    fn proof_if_true_condition(&mut self, items: &[Expr]) -> Result<ProofExpr, ParseError> {
        expect_len("if-true-condition", items, 2)?;
        Ok(ProofExpr::IfTrueCondition(Box::new(
            self.proof_expr_or_ref(&items[1])?,
        )))
    }

    fn proof_if_true_then(&mut self, items: &[Expr]) -> Result<ProofExpr, ParseError> {
        expect_len("if-true-then", items, 2)?;
        Ok(ProofExpr::IfTrueThen(Box::new(
            self.proof_expr_or_ref(&items[1])?,
        )))
    }

    fn proof_if_effect_then_condition_false(
        &mut self,
        items: &[Expr],
    ) -> Result<ProofExpr, ParseError> {
        expect_len("if-effect-then-condition-false", items, 2)?;
        Ok(ProofExpr::IfEffectThenConditionFalse(Box::new(
            self.proof_expr_or_ref(&items[1])?,
        )))
    }

    fn proof_if_effect_then_else(&mut self, items: &[Expr]) -> Result<ProofExpr, ParseError> {
        expect_len("if-effect-then-else", items, 2)?;
        Ok(ProofExpr::IfEffectThenElse(Box::new(
            self.proof_expr_or_ref(&items[1])?,
        )))
    }

    fn proof_if_value_condition_bool(&mut self, items: &[Expr]) -> Result<ProofExpr, ParseError> {
        expect_len("if-value-condition-bool", items, 2)?;
        Ok(ProofExpr::IfValueConditionBool(Box::new(
            self.proof_expr_or_ref(&items[1])?,
        )))
    }

    fn proof_distinct_outcomes(&mut self, items: &[Expr]) -> Result<ProofExpr, ParseError> {
        expect_len("distinct-outcomes", items, 2)?;
        Ok(ProofExpr::DistinctOutcomes(Box::new(
            self.proof_expr_or_ref(&items[1])?,
        )))
    }

    fn proof_value_non_symbol_non_lambda_is_list(
        &mut self,
        items: &[Expr],
    ) -> Result<ProofExpr, ParseError> {
        expect_len("value-non-symbol-non-lambda-is-list", items, 4)?;
        Ok(ProofExpr::ValueNonSymbolNonLambdaIsList {
            value: Box::new(self.proof_expr_or_ref(&items[1])?),
            not_symbol: Box::new(self.proof_expr_or_ref(&items[2])?),
            not_lambda: Box::new(self.proof_expr_or_ref(&items[3])?),
        })
    }

    fn proof_absurd_elim(&mut self, items: &[Expr]) -> Result<ProofExpr, ParseError> {
        expect_len("absurd-elim", items, 3)?;
        Ok(ProofExpr::AbsurdElim {
            absurd: Box::new(self.proof_expr_or_ref(&items[1])?),
            prop: self.proof_prop(&items[2])?,
        })
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
        let (variable, predicate, body, witness, proof) = match items.len() {
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
        let predicate = self.quantifier_predicate(predicate, PropSymbolMode::Reference)?;
        let body = self.proof_prop(body)?;
        let witness = self.computation(witness)?;
        let proof = self.proof_expr(proof)?;

        let (body, proof) = if let Some(predicate) = predicate {
            let witness_predicate = substitute_prop(&predicate, variable, &witness);
            (
                and(predicate, body),
                ProofExpr::AndIntro(
                    Box::new(ProofExpr::Primitive(witness_predicate)),
                    Box::new(proof),
                ),
            )
        } else {
            (body, proof)
        };

        Ok(ProofExpr::ExistsIntro {
            variable,
            body,
            witness,
            proof: Box::new(proof),
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

    fn proof_or_intro_left(&mut self, items: &[Expr]) -> Result<ProofExpr, ParseError> {
        expect_len("or-intro-left", items, 3)?;
        Ok(ProofExpr::OrIntroLeft {
            proof: Box::new(self.proof_expr(&items[1])?),
            right: self.proof_prop(&items[2])?,
        })
    }

    fn proof_or_intro_right(&mut self, items: &[Expr]) -> Result<ProofExpr, ParseError> {
        expect_len("or-intro-right", items, 3)?;
        Ok(ProofExpr::OrIntroRight {
            left: self.proof_prop(&items[1])?,
            proof: Box::new(self.proof_expr(&items[2])?),
        })
    }

    fn proof_or_elim(&mut self, items: &[Expr]) -> Result<ProofExpr, ParseError> {
        expect_len("or-elim", items, 6)?;
        Ok(ProofExpr::OrElim {
            disjunction: Box::new(self.proof_expr(&items[1])?),
            left_assumption: self.proof_symbol(atom(&items[2])?)?,
            left_proof: Box::new(self.proof_expr(&items[3])?),
            right_assumption: self.proof_symbol(atom(&items[4])?)?,
            right_proof: Box::new(self.proof_expr(&items[5])?),
        })
    }

    fn proof_forall_intro(&mut self, items: &[Expr]) -> Result<ProofExpr, ParseError> {
        let (variable, predicate, proof) = match items.len() {
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
        let proof = self.proof_expr(proof)?;
        let proof = if let Some(predicate) =
            self.quantifier_predicate(predicate, PropSymbolMode::Reference)?
        {
            ProofExpr::ImpliesIntro {
                assumption: variable,
                premise: predicate,
                proof: Box::new(proof),
            }
        } else {
            proof
        };

        Ok(ProofExpr::ForAllIntro {
            variable,
            proof: Box::new(proof),
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
        assert_eq!(env.symbol(":false"), Some(Symbol(2)));

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
        assert_eq!(env.symbol("x"), Some(Symbol(LIST_KIND_SYMBOL.0 + 1)));
        assert!(module.computation(Name(1)).is_some());
        assert!(module.theorem(Name(2)).is_some());
    }

    #[test]
    fn parses_if_computation() {
        let mut env = ElabEnv::new();

        let module = env
            .parse_module("(def choose (if (quote :true) nil diverge))")
            .expect("source if expression should parse");

        assert_eq!(
            module.computation(Name(1)),
            Some(&if_then_else(
                Computation::Quote(TRUE_SYMBOL),
                Computation::Nil,
                Computation::Diverge,
            ))
        );
        assert_eq!(env.symbol(":true"), Some(TRUE_SYMBOL));
        assert_eq!(env.symbol(":false"), Some(FALSE_SYMBOL));
    }

    #[test]
    fn parses_symbol_eq_computation_and_is_bool_prop() {
        let mut env = ElabEnv::new();

        let module = env
            .parse_module(
                "
                (def same (symbol-eq (quote :true) (quote :false)))
                (theorem same_is_bool
                  (is-bool same)
                  (proof
                    (or-intro-right
                      (computes-to same (quote :true))
                      (eval-to same (quote :false)))))
                ",
            )
            .expect("symbol-eq and is-bool source should parse");

        assert_eq!(
            module.computation(Name(1)),
            Some(&symbol_eq(
                Computation::Quote(TRUE_SYMBOL),
                Computation::Quote(FALSE_SYMBOL),
            ))
        );
        assert_eq!(
            module.theorem(Name(2)).map(|theorem| &theorem.prop),
            Some(&is_bool(Computation::Ref(Name(1))))
        );
    }

    #[test]
    fn parses_value_kind_computation_and_reserved_kind_symbols() {
        let mut env = ElabEnv::new();

        let module = env
            .parse_module("(def kind (value-kind (quote :true)))")
            .expect("source value-kind expression should parse");

        assert_eq!(
            module.computation(Name(1)),
            Some(&value_kind(Computation::Quote(TRUE_SYMBOL)))
        );
        assert_eq!(env.symbol(":symbol"), Some(SYMBOL_KIND_SYMBOL));
        assert_eq!(env.symbol(":lambda"), Some(LAMBDA_KIND_SYMBOL));
        assert_eq!(env.symbol(":list"), Some(LIST_KIND_SYMBOL));
    }

    #[test]
    fn parses_direct_value_kind_test_aliases() {
        let mut env = ElabEnv::new();

        let module = env
            .parse_module(
                "
                (def is-symbol (lambda value value))
                (def symbol_predicate is-symbol)
                (def symbol_test (is-symbol (quote :true)))
                (def lambda_test (is-lambda (lambda value value)))
                (def list_test (is-list-value nil))
                (def shadowed (lambda is-symbol (is-symbol (quote :true))))
                ",
            )
            .expect("source value-kind test aliases should parse");
        let value = env
            .symbol("value")
            .expect("lambda parameter should be interned");
        let shadowed_is_symbol = env
            .symbol("is-symbol")
            .expect("shadowing lambda parameter should be interned");

        assert_eq!(
            module.computation(Name(2)),
            Some(&Computation::Ref(Name(1)))
        );
        assert_eq!(
            module.computation(Name(3)),
            Some(&symbol_eq(
                value_kind(Computation::Quote(TRUE_SYMBOL)),
                Computation::Quote(SYMBOL_KIND_SYMBOL),
            ))
        );
        assert_eq!(
            module.computation(Name(4)),
            Some(&symbol_eq(
                value_kind(Computation::Lambda(Lambda {
                    parameter: value,
                    body: Box::new(Computation::Var(value)),
                })),
                Computation::Quote(LAMBDA_KIND_SYMBOL),
            ))
        );
        assert_eq!(
            module.computation(Name(5)),
            Some(&symbol_eq(
                value_kind(Computation::Nil),
                Computation::Quote(LIST_KIND_SYMBOL),
            ))
        );
        assert_eq!(
            module.computation(Name(6)),
            Some(&Computation::Lambda(Lambda {
                parameter: shadowed_is_symbol,
                body: Box::new(Computation::Apply {
                    function: Box::new(Computation::Var(shadowed_is_symbol)),
                    argument: Box::new(Computation::Quote(TRUE_SYMBOL)),
                }),
            }))
        );
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
    fn parses_by_tactic_scripts() {
        let computations = [NameBinding {
            spelling: "id",
            name: Name(1),
        }];
        let theorems = [NameBinding {
            spelling: "id_computes",
            name: Name(2),
        }];
        let symbols = [SymbolBinding {
            spelling: "x",
            symbol: Symbol(1),
        }];

        assert_eq!(
            parse_module(
                "
                (def id (lambda x x))
                (theorem id_computes
                  (forall value (is-value value)
                    (computes-to (id value) value))
                  (by
                    (intro value)
                    (eval)))
                ",
                &computations,
                &theorems,
                &symbols,
            ),
            Ok(ParsedModule {
                computations: vec![(
                    Name(1),
                    Computation::Lambda(Lambda {
                        parameter: Symbol(1),
                        body: Box::new(Computation::Var(Symbol(1))),
                    }),
                )],
                theorems: vec![ParsedTheorem {
                    name: Name(2),
                    prop: forall_where(
                        Symbol(2_000),
                        is_value(Computation::Var(Symbol(2_000))),
                        computes_to(
                            Computation::Apply {
                                function: Box::new(Computation::Ref(Name(1))),
                                argument: Box::new(Computation::Var(Symbol(2_000))),
                            },
                            Computation::Var(Symbol(2_000)),
                        ),
                    ),
                    proof: ProofScript::By(TacticScript {
                        tactics: vec![
                            TacticExpr::Intro(Symbol(2_000)),
                            TacticExpr::Eval { limit: 128 }
                        ],
                    }),
                    local_symbols: vec![LocalSymbol {
                        spelling: "value".to_owned(),
                        symbol: Symbol(2_000),
                    },],
                }],
            })
        );
    }

    #[test]
    fn parses_calc_tactic_scripts() {
        let computations = [NameBinding {
            spelling: "id",
            name: Name(1),
        }];
        let theorems = [NameBinding {
            spelling: "id_id_nil",
            name: Name(2),
        }];
        let symbols = [SymbolBinding {
            spelling: "x",
            symbol: Symbol(1),
        }];

        let module = parse_module(
            "
            (def id (lambda x x))
            (theorem id_id_nil
              (computes-to (id (id nil)) nil)
              (by
                (calc
                  (id (id nil))
                  (== (id nil) (by (eval)))
                  (== nil (by (eval))))))
            ",
            &computations,
            &theorems,
            &symbols,
        )
        .expect("calc tactic source should parse");

        let ProofScript::By(TacticScript { tactics }) = &module.theorems[0].proof else {
            panic!("expected a tactic proof script");
        };
        assert!(matches!(
            tactics.as_slice(),
            [TacticExpr::Calc { steps, .. }] if steps.len() == 2
        ));
    }

    #[test]
    fn parses_simp_tactic_scripts() {
        let theorems = [
            NameBinding {
                spelling: "nil_self",
                name: Name(1),
            },
            NameBinding {
                spelling: "nil_self_by_simp",
                name: Name(2),
            },
        ];

        let module = parse_module(
            "
            (theorem nil_self
              (computes-to nil nil)
              (by
                (eval)))
            (theorem nil_self_by_simp
              (computes-to nil nil)
              (by
                (simp only nil_self)))
            ",
            &[],
            &theorems,
            &[],
        )
        .expect("simp tactic source should parse");

        let ProofScript::By(TacticScript { tactics }) = &module.theorems[1].proof else {
            panic!("expected a tactic proof script");
        };
        assert!(matches!(
            tactics.as_slice(),
            [TacticExpr::Simp { rules }] if rules == &vec![ProofExpr::Known(Name(1))]
        ));
    }

    #[test]
    fn parses_simpa_tactic_scripts() {
        let theorems = [
            NameBinding {
                spelling: "nil_self",
                name: Name(1),
            },
            NameBinding {
                spelling: "nil_self_by_simpa",
                name: Name(2),
            },
        ];

        let module = parse_module(
            "
            (theorem nil_self
              (computes-to nil nil)
              (by
                (eval)))
            (theorem nil_self_by_simpa
              (computes-to nil nil)
              (by
                (simpa only nil_self using nil_self)))
            ",
            &[],
            &theorems,
            &[],
        )
        .expect("simpa tactic source should parse");

        let ProofScript::By(TacticScript { tactics }) = &module.theorems[1].proof else {
            panic!("expected a tactic proof script");
        };
        assert!(matches!(
            tactics.as_slice(),
            [TacticExpr::Simpa { rules, proof: Some(proof) }]
                if rules == &vec![ProofExpr::Known(Name(1))]
                    && **proof == ProofExpr::Known(Name(1))
        ));
    }

    #[test]
    fn parses_fold_tactic_scripts() {
        let computations = [NameBinding {
            spelling: "alias",
            name: Name(1),
        }];
        let theorems = [NameBinding {
            spelling: "fold_alias_nil",
            name: Name(2),
        }];

        let module = parse_module(
            "
            (def alias nil)
            (theorem fold_alias_nil
              (equal nil alias)
              (by
                (fold alias)
                (eval)))
            ",
            &computations,
            &theorems,
            &[],
        )
        .expect("fold tactic source should parse");

        let ProofScript::By(TacticScript { tactics }) = &module.theorems[0].proof else {
            panic!("expected a tactic proof script");
        };
        assert!(matches!(
            tactics.as_slice(),
            [
                TacticExpr::Fold {
                    definition: Name(1)
                },
                TacticExpr::Eval { limit: 128 }
            ]
        ));
    }

    #[test]
    fn parses_rewrite_tactic_scripts() {
        let computations = [NameBinding {
            spelling: "id",
            name: Name(1),
        }];
        let theorems = [NameBinding {
            spelling: "id_rewrite_nil",
            name: Name(2),
        }];
        let symbols = [SymbolBinding {
            spelling: "x",
            symbol: Symbol(1),
        }];

        let module = parse_module(
            "
            (def id (lambda x x))
            (theorem id_rewrite_nil
              (forall value (is-value value)
                (implies
                  (computes-to value nil)
                  (computes-to (id value) nil)))
              (by
                (intro value)
                (intro value_nil)
                (rewrite value_nil)
                (eval)))
            ",
            &computations,
            &theorems,
            &symbols,
        )
        .expect("rewrite tactic source should parse");

        let ProofScript::By(TacticScript { tactics }) = &module.theorems[0].proof else {
            panic!("expected a tactic proof script");
        };
        assert!(matches!(
            tactics.as_slice(),
            [
                TacticExpr::Intro(Symbol(2_000)),
                TacticExpr::Intro(Symbol(2_001)),
                TacticExpr::Rewrite { equality },
                TacticExpr::Eval { limit: 128 }
            ] if **equality == ProofExpr::Assume(Symbol(2_001))
        ));
    }

    #[test]
    fn parses_list_induction_tactic_scripts() {
        let theorems = [NameBinding {
            spelling: "list_identity",
            name: Name(1),
        }];

        let module = parse_module(
            "
            (theorem list_identity
              (forall list (is-list list)
                (computes-to list list))
              (by
                (list-induction list
                  (by
                    (eval))
                  head
                  tail
                  ih
                  (by
                    (eval)))))
            ",
            &[],
            &theorems,
            &[],
        )
        .expect("list-induction tactic source should parse");

        let ProofScript::By(TacticScript { tactics }) = &module.theorems[0].proof else {
            panic!("expected a tactic proof script");
        };
        assert!(matches!(
            tactics.as_slice(),
            [TacticExpr::ListInduction {
                variable: Symbol(2_000),
                head: Symbol(2_001),
                tail: Symbol(2_002),
                induction_hypothesis_assumption: Symbol(2_003),
                ..
            }]
        ));
    }

    #[test]
    fn parses_value_induction_tactic_scripts() {
        let theorems = [NameBinding {
            spelling: "value_identity",
            name: Name(1),
        }];

        let module = parse_module(
            "
            (theorem value_identity
              (forall value (is-value value)
                (computes-to value value))
              (by
                (value-induction value
                  value_is_symbol
                  (by
                    (eval))
                  value_is_lambda
                  (by
                    (eval))
                  (by
                    (eval))
                  head
                  tail
                  head_ih
                  tail_ih
                  (by
                    (eval)))))
            ",
            &[],
            &theorems,
            &[],
        )
        .expect("value-induction tactic source should parse");

        let ProofScript::By(TacticScript { tactics }) = &module.theorems[0].proof else {
            panic!("expected a tactic proof script");
        };
        assert!(matches!(
            tactics.as_slice(),
            [TacticExpr::ValueInduction {
                variable: Symbol(2_000),
                symbol_assumption: Symbol(2_001),
                lambda_assumption: Symbol(2_002),
                head: Symbol(2_003),
                tail: Symbol(2_004),
                head_induction_hypothesis_assumption: Symbol(2_005),
                tail_induction_hypothesis_assumption: Symbol(2_006),
                ..
            }]
        ));
    }

    #[test]
    fn parses_eliminator_tactic_scripts() {
        let theorems = [
            NameBinding {
                spelling: "list_exists",
                name: Name(1),
            },
            NameBinding {
                spelling: "value_self",
                name: Name(2),
            },
            NameBinding {
                spelling: "elim_example",
                name: Name(3),
            },
            NameBinding {
                spelling: "or_source",
                name: Name(4),
            },
            NameBinding {
                spelling: "or_example",
                name: Name(5),
            },
            NameBinding {
                spelling: "and_source",
                name: Name(6),
            },
            NameBinding {
                spelling: "cases_example",
                name: Name(7),
            },
            NameBinding {
                spelling: "specialize_example",
                name: Name(8),
            },
        ];

        let module = parse_module(
            "
            (theorem list_exists
              (exists result (is-list result)
                (computes-to nil result))
              (by
                (exists nil
                  (by
                    (eval)))))
            (theorem value_self
              (forall value (is-value value)
                (computes-to value value))
              (by
                (intro value)
                (eval)))
            (theorem elim_example
              (computes-to nil nil)
              (by
                (obtain witness witness_proof list_exists)
                (exact value_self nil)))
            (theorem or_source
              (or
                (computes-to nil nil)
                (computes-to diverge diverge))
              (by
                (left
                  (by
                    (eval)))))
            (theorem or_example
              (computes-to nil nil)
              (by
                (or-elim
                  or_source
                  left_case
                  (by
                    (eval))
                  right_case
                  (by
                    (eval)))))
            (theorem and_source
              (and
                (computes-to nil nil)
                (computes-to nil nil))
              (by
                (split
                  (by
                    (eval))
                  (by
                    (eval)))))
            (theorem cases_example
              (computes-to nil nil)
              (by
                (cases and_source left_case right_case)
                (exact left_case)))
            (theorem specialize_example
              (computes-to nil nil)
              (by
                (specialize nil_self value_self nil)
                (exact nil_self)))
            ",
            &[],
            &theorems,
            &[],
        )
        .expect("eliminator tactic source should parse");

        let ProofScript::By(TacticScript { tactics }) = &module.theorems[2].proof else {
            panic!("expected a tactic proof script");
        };
        assert!(matches!(
            tactics.as_slice(),
            [
                TacticExpr::Obtain {
                    existential,
                    witness: Symbol(2_002),
                    assumption: Symbol(2_003),
                    body: None,
                },
                TacticExpr::Exact(proof),
            ] if **existential == ProofExpr::Known(Name(1))
                && **proof == ProofExpr::Apply {
                    proof: Box::new(ProofExpr::Known(Name(2))),
                    arguments: vec![Computation::Nil],
                }
        ));

        let ProofScript::By(TacticScript { tactics }) = &module.theorems[4].proof else {
            panic!("expected a tactic proof script");
        };
        assert!(matches!(
            tactics.as_slice(),
            [TacticExpr::OrElim {
                disjunction,
                left_assumption: Symbol(2_004),
                right_assumption: Symbol(2_005),
                ..
            }] if **disjunction == ProofExpr::Known(Name(4))
        ));

        let ProofScript::By(TacticScript { tactics }) = &module.theorems[6].proof else {
            panic!("expected a tactic proof script");
        };
        assert!(matches!(
            tactics.as_slice(),
            [
                TacticExpr::Cases {
                    conjunction,
                    left_assumption: Symbol(2_006),
                    right_assumption: Symbol(2_007),
                    body: None,
                },
                TacticExpr::Exact(proof),
            ] if **conjunction == ProofExpr::Known(Name(6))
                && **proof == ProofExpr::Assume(Symbol(2_006))
        ));

        let ProofScript::By(TacticScript { tactics }) = &module.theorems[7].proof else {
            panic!("expected a tactic proof script");
        };
        assert!(matches!(
            tactics.as_slice(),
            [
                TacticExpr::Specialize {
                    assumption: Symbol(2_008),
                    proof,
                    arguments,
                    body: None,
                },
                TacticExpr::Exact(exact),
            ] if **proof == ProofExpr::Known(Name(2))
                && arguments.as_slice() == [Computation::Nil]
                && **exact == ProofExpr::Assume(Symbol(2_008))
        ));
    }

    #[test]
    fn parses_explicit_tactic_continuation_bodies() {
        let theorems = [
            NameBinding {
                spelling: "list_exists",
                name: Name(1),
            },
            NameBinding {
                spelling: "explicit_exists",
                name: Name(2),
            },
            NameBinding {
                spelling: "explicit_have",
                name: Name(3),
            },
            NameBinding {
                spelling: "explicit_specialize",
                name: Name(4),
            },
        ];

        let module = parse_module(
            "
            (theorem list_exists
              (exists result (is-list result)
                (computes-to nil result))
              (by
                (exists nil
                  (by
                    (eval)))))
            (theorem explicit_exists
              (computes-to nil nil)
              (by
                (obtain witness witness_proof list_exists
                  (by
                    (exact witness_proof)))))
            (theorem explicit_have
              (computes-to nil nil)
              (by
                (have nil_self
                  (computes-to nil nil)
                  (by
                    (eval))
                  (by
                    (exact nil_self)))))
            (theorem explicit_specialize
              (exists result (is-list result)
                (computes-to nil result))
              (by
                (specialize list_copy list_exists
                  (by
                    (exact list_copy)))))
            ",
            &[],
            &theorems,
            &[],
        )
        .expect("explicit tactic body source should parse");

        let ProofScript::By(TacticScript { tactics }) = &module.theorems[1].proof else {
            panic!("expected a tactic proof script");
        };
        let [
            TacticExpr::Obtain {
                assumption,
                body:
                    Some(TacticScript {
                        tactics: body_tactics,
                    }),
                ..
            },
        ] = tactics.as_slice()
        else {
            panic!("expected an obtain tactic with an explicit body");
        };
        let [TacticExpr::Exact(proof)] = body_tactics.as_slice() else {
            panic!("expected the obtain body to contain an exact tactic");
        };
        assert_eq!(**proof, ProofExpr::Assume(*assumption));

        let ProofScript::By(TacticScript { tactics }) = &module.theorems[2].proof else {
            panic!("expected a tactic proof script");
        };
        let [
            TacticExpr::Have {
                assumption,
                body:
                    Some(TacticScript {
                        tactics: body_tactics,
                    }),
                ..
            },
        ] = tactics.as_slice()
        else {
            panic!("expected a have tactic with an explicit body");
        };
        let [TacticExpr::Exact(proof)] = body_tactics.as_slice() else {
            panic!("expected the have body to contain an exact tactic");
        };
        assert_eq!(**proof, ProofExpr::Assume(*assumption));

        let ProofScript::By(TacticScript { tactics }) = &module.theorems[3].proof else {
            panic!("expected a tactic proof script");
        };
        let [
            TacticExpr::Specialize {
                assumption,
                body:
                    Some(TacticScript {
                        tactics: body_tactics,
                    }),
                ..
            },
        ] = tactics.as_slice()
        else {
            panic!("expected a specialize tactic with an explicit body");
        };
        let [TacticExpr::Exact(proof)] = body_tactics.as_slice() else {
            panic!("expected the specialize body to contain an exact tactic");
        };
        assert_eq!(**proof, ProofExpr::Assume(*assumption));
    }

    #[test]
    fn reports_likely_missing_close_paren_after_have() {
        let error = parse_module(
            "
            (theorem bad_have
              (computes-to nil nil)
              (by
                (have nil_self
                  (computes-to nil nil)
                  (by
                    (eval))
                  (exact nil_self))))
            ",
            &[],
            &[NameBinding {
                spelling: "bad_have",
                name: Name(1),
            }],
            &[],
        )
        .expect_err("extra non-body tactic inside have should not parse");

        assert_eq!(
            error.message(),
            "`have` got an extra argument that is not a `(by ...)` body; if this is the next tactic, close the `(have ...)` form before it"
        );
    }

    #[test]
    fn rejects_raw_eliminators_as_tactics() {
        for (source, theorem, tactic) in [
            (
                "
                (theorem bad_forall_elim
                  (computes-to nil nil)
                  (by
                    (forall-elim value_self nil)))
                ",
                "bad_forall_elim",
                "forall-elim",
            ),
            (
                "
                (theorem bad_exists_elim
                  (computes-to nil nil)
                  (by
                    (exists-elim list_exists witness witness_proof)))
                ",
                "bad_exists_elim",
                "exists-elim",
            ),
        ] {
            let error = parse_module(
                source,
                &[],
                &[NameBinding {
                    spelling: theorem,
                    name: Name(1),
                }],
                &[],
            )
            .expect_err("raw eliminator should not parse as a tactic");
            assert_eq!(error.message(), format!("unknown tactic `{tactic}`"));
        }
    }

    #[test]
    fn parses_have_and_proof_application_tactics() {
        let theorems = [
            NameBinding {
                spelling: "value_self",
                name: Name(1),
            },
            NameBinding {
                spelling: "have_example",
                name: Name(2),
            },
        ];

        let module = parse_module(
            "
            (theorem value_self
              (forall value (is-value value)
                (computes-to value value))
              (by
                (intro value)
                (eval)))
            (theorem have_example
              (computes-to nil nil)
              (by
                (have nil_self
                  (computes-to nil nil)
                  (by
                    (exact value_self nil)))
                (rewrite (value_self nil))
                (exact nil_self)))
            ",
            &[],
            &theorems,
            &[],
        )
        .expect("have and proof application tactics should parse");

        let ProofScript::By(TacticScript { tactics }) = &module.theorems[1].proof else {
            panic!("expected a tactic proof script");
        };
        assert!(matches!(
            tactics.as_slice(),
            [
                TacticExpr::Have {
                    assumption: Symbol(2_001),
                    proof: ProofScript::By(TacticScript { tactics: have_tactics }),
                    ..
                },
                TacticExpr::Rewrite { equality },
                TacticExpr::Exact(exact),
            ] if matches!(
                    have_tactics.as_slice(),
                    [TacticExpr::Exact(proof)]
                        if **proof == ProofExpr::Apply {
                            proof: Box::new(ProofExpr::Known(Name(1))),
                            arguments: vec![Computation::Nil],
                        }
                )
                && **equality == ProofExpr::Apply {
                    proof: Box::new(ProofExpr::Known(Name(1))),
                    arguments: vec![Computation::Nil],
                }
                && **exact == ProofExpr::Assume(Symbol(2_001))
        ));
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
                        proof: Box::new(ProofExpr::ImpliesIntro {
                            assumption: Symbol(2_000),
                            premise: is_list(Computation::Var(Symbol(2_000))),
                            proof: Box::new(ProofExpr::ExistsIntro {
                                variable: Symbol(2_001),
                                body: and(
                                    is_list(Computation::Var(Symbol(2_001))),
                                    computes_to(
                                        Computation::Apply {
                                            function: Box::new(Computation::Ref(Name(2))),
                                            argument: Box::new(Computation::Var(Symbol(2_000))),
                                        },
                                        Computation::Var(Symbol(2_001)),
                                    ),
                                ),
                                witness: Computation::Var(Symbol(2_000)),
                                proof: Box::new(ProofExpr::AndIntro(
                                    Box::new(ProofExpr::Primitive(is_list(Computation::Var(
                                        Symbol(2_000),
                                    )))),
                                    Box::new(ProofExpr::EvalTo {
                                        computation: Computation::Apply {
                                            function: Box::new(Computation::Ref(Name(2))),
                                            argument: Box::new(Computation::Var(Symbol(2_000))),
                                        },
                                        expected: Computation::Var(Symbol(2_000)),
                                        limit: 128,
                                    }),
                                )),
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
    fn parses_proof_helpers() {
        let module = parse_module(
            "
            (theorem pair_reflexive
              (exists x
                (and
                  (computes-to x x)
                  (computes-to x x)))
              (proof
                (exists-intro x
                  (and
                    (computes-to x x)
                    (computes-to x x))
                  nil
                  (and-intro
                    (eval-to nil nil)
                    (eval-to nil nil)))))
            ",
            &[],
            &[NameBinding {
                spelling: "pair_reflexive",
                name: Name(1),
            }],
            &[],
        )
        .expect("proof helper source should parse");

        let ProofScript::Proof(ProofExpr::ExistsIntro { variable, .. }) = &module.theorems[0].proof
        else {
            panic!("expected an exists-intro proof");
        };
        assert_eq!(*variable, Symbol(2_000));
    }

    #[test]
    fn computes_to_elaborates_to_equal() {
        let module = parse_module(
            "
            (theorem equal_statement
              (equal (head (cons nil nil)) nil)
              (proof
                (eval-to (head (cons nil nil)) nil)))
            (theorem computes_to_statement
              (computes-to (head (cons nil nil)) nil)
              (proof
                (eval-to (head (cons nil nil)) nil)))
            ",
            &[],
            &[
                NameBinding {
                    spelling: "equal_statement",
                    name: Name(1),
                },
                NameBinding {
                    spelling: "computes_to_statement",
                    name: Name(2),
                },
            ],
            &[],
        )
        .expect("equal and computes-to statements should parse");

        assert_eq!(module.theorems[0].prop, module.theorems[1].prop);
        assert_eq!(
            module.theorems[0].prop,
            equal(
                Computation::Head(Box::new(Computation::Cons {
                    head: Box::new(Computation::Nil),
                    tail: Box::new(Computation::Nil),
                })),
                Computation::Nil,
            )
        );
    }

    #[test]
    fn parses_bool_inversion_proof_helpers() {
        let module = parse_module(
            "
            (theorem bool_inversions
              (and
                (computes-to (quote :true) (quote :true))
                (and
                  (computes-to (quote :false) (quote :false))
                  (computes-to (quote unit) (quote unit))))
              (proof
                (and-intro
                  (if-true-condition
                    (eval-to
                      (if (quote :true) (quote :true) (quote :false))
                      (quote :true)))
                  (and-intro
                    (if-effect-then-condition-false
                      (eval-to
                        (if (quote :false) (error 0) (quote unit))
                        (quote unit)))
                    (if-effect-then-else
                      (eval-to
                        (if (quote :false) (error 0) (quote unit))
                        (quote unit)))))))

            (theorem symbol_eq_inversion
              (computes-to (quote unit) (quote unit))
              (proof
                (symbol-eq-true
                  (eval-to
                    (symbol-eq (quote unit) (quote unit))
                    (quote :true)))))

            (theorem condition_bool
              (is-bool (quote :true))
              (proof
                (if-value-condition-bool
                  (eval-to
                    (if (quote :true) nil nil)
                    nil))))

            (theorem distinct_outcomes
              (absurd)
              (proof
                (distinct-outcomes
                  (primitive
                    (equal (quote :true) (quote :false))))))

            (theorem absurd_elimination
              (is-value nil)
              (proof
                (absurd-elim
                  (distinct-outcomes
                    (primitive
                      (equal (quote :true) (quote :false))))
                  (is-value nil))))

            (theorem value_classification
              (is-list nil)
              (proof
                (value-non-symbol-non-lambda-is-list
                  (primitive (is-value nil))
                  (eval-to (is-symbol nil) (quote :false))
                  (eval-to (is-lambda nil) (quote :false)))))
            ",
            &[],
            &[
                NameBinding {
                    spelling: "bool_inversions",
                    name: Name(1),
                },
                NameBinding {
                    spelling: "symbol_eq_inversion",
                    name: Name(2),
                },
                NameBinding {
                    spelling: "condition_bool",
                    name: Name(3),
                },
                NameBinding {
                    spelling: "distinct_outcomes",
                    name: Name(4),
                },
                NameBinding {
                    spelling: "absurd_elimination",
                    name: Name(5),
                },
                NameBinding {
                    spelling: "value_classification",
                    name: Name(6),
                },
            ],
            &[
                SymbolBinding {
                    spelling: ":true",
                    symbol: TRUE_SYMBOL,
                },
                SymbolBinding {
                    spelling: ":false",
                    symbol: FALSE_SYMBOL,
                },
                SymbolBinding {
                    spelling: "unit",
                    symbol: Symbol(9),
                },
            ],
        )
        .expect("bool inversion proof helpers should parse");

        let ProofScript::Proof(ProofExpr::AndIntro(left, right)) = &module.theorems[0].proof else {
            panic!("expected an and-intro proof");
        };
        let ProofExpr::AndIntro(middle, right) = right.as_ref() else {
            panic!("expected nested and-intro proof");
        };
        assert!(matches!(left.as_ref(), ProofExpr::IfTrueCondition(_)));
        assert!(matches!(
            middle.as_ref(),
            ProofExpr::IfEffectThenConditionFalse(_)
        ));
        assert!(matches!(right.as_ref(), ProofExpr::IfEffectThenElse(_)));
        assert!(matches!(
            &module.theorems[1].proof,
            ProofScript::Proof(ProofExpr::SymbolEqTrue(_))
        ));
        assert!(matches!(
            &module.theorems[2].proof,
            ProofScript::Proof(ProofExpr::IfValueConditionBool(_))
        ));
        assert!(matches!(
            &module.theorems[3].proof,
            ProofScript::Proof(ProofExpr::DistinctOutcomes(_))
        ));
        assert!(matches!(
            &module.theorems[4].proof,
            ProofScript::Proof(ProofExpr::AbsurdElim { .. })
        ));
        assert!(matches!(
            &module.theorems[5].proof,
            ProofScript::Proof(ProofExpr::ValueNonSymbolNonLambdaIsList { .. })
        ));
    }

    #[test]
    fn rejects_legacy_sorted_quantifier_form() {
        let theorems = [NameBinding {
            spelling: "old_sort",
            name: Name(1),
        }];

        let error = parse_module(
            "
            (theorem old_sort
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
        .expect_err("legacy sorted quantifier form should not parse");

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
