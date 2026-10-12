//! The C++ standard-library model accessors a sidecar may apply, rewritten
//! to the field paths they name.

use super::*;

/// Rewrites each application of a bound C++ model accessor into its field
/// path: `std_span_data(s)` becomes `s._M_ptr` under libstdc++, and a
/// compound argument is parenthesized first. The rewritten access is then
/// parsed and checked like a written one, so an argument of another type is
/// refused where its field is resolved. An accessor is bound only when the
/// layouts hold a record with its path; otherwise its name is left as a call.
pub(super) fn rewrite_model_accessors(
    tokens: Vec<Token>,
    positions: Vec<SourcePosition>,
    layouts: &BTreeMap<String, syntax::C0StructLayout>,
) -> (Vec<Token>, Vec<SourcePosition>) {
    let accessors = crate::languages::cpp::standard_library::model_accessors(layouts);
    if accessors.is_empty() {
        return (tokens, positions);
    }
    let mut rewritten_tokens = Vec::with_capacity(tokens.len());
    let mut rewritten_positions = Vec::with_capacity(positions.len());
    let mut index = 0;
    while index < tokens.len() {
        let path = match &tokens[index] {
            Token::Ident(name) if tokens.get(index + 1) == Some(&Token::LParen) => {
                accessors.get(name.as_str()).copied()
            }
            _ => None,
        };
        let close = path.and_then(|_| {
            let mut depth = 0_usize;
            (index + 1..tokens.len()).find(|&candidate| {
                match tokens[candidate] {
                    Token::LParen => depth += 1,
                    Token::RParen => depth -= 1,
                    _ => {}
                }
                depth == 0
            })
        });
        let (Some(path), Some(close)) = (path, close) else {
            rewritten_tokens.push(tokens[index].clone());
            rewritten_positions.push(positions[index].clone());
            index += 1;
            continue;
        };
        let at = positions[index].clone();
        let argument = index + 2..close;
        if argument.len() == 1 && matches!(tokens[argument.start], Token::Ident(_)) {
            rewritten_tokens.push(tokens[argument.start].clone());
            rewritten_positions.push(positions[argument.start].clone());
        } else {
            rewritten_tokens.push(Token::LParen);
            rewritten_positions.push(at.clone());
            rewritten_tokens.extend(tokens[argument.clone()].iter().cloned());
            rewritten_positions.extend(positions[argument].iter().cloned());
            rewritten_tokens.push(Token::RParen);
            rewritten_positions.push(positions[close].clone());
        }
        for field in path {
            rewritten_tokens.push(Token::Dot);
            rewritten_positions.push(at.clone());
            rewritten_tokens.push(Token::Ident((*field).to_string()));
            rewritten_positions.push(at.clone());
        }
        index = close + 1;
    }
    (rewritten_tokens, rewritten_positions)
}
