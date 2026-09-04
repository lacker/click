use super::*;

pub(super) fn tokenize(source: &str) -> Result<(Vec<Token>, Vec<SourcePosition>), ClickError> {
    let chars: Vec<char> = source.chars().collect();
    let char_positions = crate::source::character_positions(source);
    let mut tokens = Vec::new();
    let mut positions = Vec::new();
    let mut index = 0;

    while let Some(ch) = chars.get(index).copied() {
        let position = char_positions[index];
        let tokens_before = tokens.len();
        match ch {
            ch if ch.is_whitespace() => {
                index += 1;
            }
            '{' => {
                tokens.push(Token::LBrace);
                index += 1;
            }
            '}' => {
                tokens.push(Token::RBrace);
                index += 1;
            }
            '(' => {
                tokens.push(Token::LParen);
                index += 1;
            }
            ')' => {
                tokens.push(Token::RParen);
                index += 1;
            }
            '[' => {
                tokens.push(Token::LBracket);
                index += 1;
            }
            ']' => {
                tokens.push(Token::RBracket);
                index += 1;
            }
            ':' => {
                tokens.push(Token::Colon);
                index += 1;
            }
            ',' => {
                tokens.push(Token::Comma);
                index += 1;
            }
            ';' => {
                tokens.push(Token::Semicolon);
                index += 1;
            }
            '.' => {
                if chars.get(index + 1) == Some(&'.') {
                    tokens.push(Token::DotDot);
                    index += 2;
                } else {
                    tokens.push(Token::Dot);
                    index += 1;
                }
            }
            '+' => {
                tokens.push(Token::Plus);
                index += 1;
            }
            '-' => {
                if chars.get(index + 1) == Some(&'>') {
                    tokens.push(Token::Arrow);
                    index += 2;
                } else {
                    tokens.push(Token::Minus);
                    index += 1;
                }
            }
            '*' => {
                tokens.push(Token::Star);
                index += 1;
            }
            '/' => {
                tokens.push(Token::Slash);
                index += 1;
            }
            '%' => {
                tokens.push(Token::Percent);
                index += 1;
            }
            '&' => {
                tokens.push(Token::Amp);
                index += 1;
            }
            '|' => {
                tokens.push(Token::Pipe);
                index += 1;
            }
            '^' => {
                tokens.push(Token::Caret);
                index += 1;
            }
            '~' => {
                tokens.push(Token::Tilde);
                index += 1;
            }
            '<' => {
                if chars.get(index + 1) == Some(&'<') {
                    tokens.push(Token::ShiftLeft);
                    index += 2;
                } else if chars.get(index + 1) == Some(&'=') {
                    tokens.push(Token::LessEqual);
                    index += 2;
                } else {
                    tokens.push(Token::LessThan);
                    index += 1;
                }
            }
            '>' => {
                if chars.get(index + 1) == Some(&'>') {
                    tokens.push(Token::ShiftRight);
                    index += 2;
                } else if chars.get(index + 1) == Some(&'=') {
                    tokens.push(Token::GreaterEqual);
                    index += 2;
                } else {
                    tokens.push(Token::GreaterThan);
                    index += 1;
                }
            }
            '!' => {
                if chars.get(index + 1) == Some(&'=') {
                    tokens.push(Token::BangEqual);
                    index += 2;
                } else {
                    return Err(ClickError::new(format!(
                        "{position}: expected `!=`, got `!`"
                    )));
                }
            }
            '=' => {
                if chars.get(index + 1) == Some(&'=') {
                    tokens.push(Token::EqualEqual);
                    index += 2;
                } else {
                    tokens.push(Token::Equal);
                    index += 1;
                }
            }
            '"' => {
                let (value, next_index) = tokenize_string(&chars, index)
                    .map_err(|error| ClickError::new(format!("{position}: {}", error.message())))?;
                tokens.push(Token::String(value));
                index = next_index;
            }
            '\'' => {
                let (value, next_index) = tokenize_char_literal(&chars, index)
                    .map_err(|error| ClickError::new(format!("{position}: {}", error.message())))?;
                tokens.push(Token::CharLiteral(value));
                index = next_index;
            }
            ch if ch.is_ascii_digit() => {
                let start = index;
                while chars.get(index).is_some_and(|next| next.is_ascii_digit()) {
                    index += 1;
                }
                let form: String = chars[start..index].iter().collect();
                let value = form.parse::<u64>().map_err(|_| {
                    ClickError::new(format!("{position}: number `{form}` does not fit in u64"))
                })?;
                if chars.get(index) == Some(&'u') && chars.get(index + 1) == Some(&'8') {
                    if chars
                        .get(index + 2)
                        .is_some_and(|next| is_ident_continue(*next))
                    {
                        return Err(ClickError::new(format!(
                            "{position}: invalid uint8 literal `{form}u8{}`",
                            chars[index + 2]
                        )));
                    }
                    let value = u8::try_from(value).map_err(|_| {
                        ClickError::new(format!(
                            "{position}: uint8 literal `{form}u8` is outside 0..255"
                        ))
                    })?;
                    tokens.push(Token::UInt8Number(value));
                    index += 2;
                } else if chars.get(index) == Some(&'u')
                    && chars.get(index + 1) == Some(&'3')
                    && chars.get(index + 2) == Some(&'2')
                {
                    if chars
                        .get(index + 3)
                        .is_some_and(|next| is_ident_continue(*next))
                    {
                        return Err(ClickError::new(format!(
                            "{position}: invalid uint32 literal `{form}u32{}`",
                            chars[index + 3]
                        )));
                    }
                    let value = u32::try_from(value).map_err(|_| {
                        ClickError::new(format!(
                            "{position}: uint32 literal `{form}u32` is outside 0..{}",
                            u32::MAX
                        ))
                    })?;
                    tokens.push(Token::UInt32Number(value));
                    index += 3;
                } else if chars.get(index) == Some(&'i')
                    && chars.get(index + 1) == Some(&'6')
                    && chars.get(index + 2) == Some(&'4')
                {
                    if chars
                        .get(index + 3)
                        .is_some_and(|next| is_ident_continue(*next))
                    {
                        return Err(ClickError::new(format!(
                            "{position}: invalid int64 literal `{form}i64{}`",
                            chars[index + 3]
                        )));
                    }
                    let value = i64::try_from(value).map_err(|_| {
                        ClickError::new(format!(
                            "{position}: int64 literal `{form}i64` is outside 0..{}",
                            i64::MAX
                        ))
                    })?;
                    tokens.push(Token::Int64Number(value));
                    index += 3;
                } else if chars.get(index) == Some(&'u')
                    && chars.get(index + 1) == Some(&'6')
                    && chars.get(index + 2) == Some(&'4')
                {
                    if chars
                        .get(index + 3)
                        .is_some_and(|next| is_ident_continue(*next))
                    {
                        return Err(ClickError::new(format!(
                            "{position}: invalid uint64 literal `{form}u64{}`",
                            chars[index + 3]
                        )));
                    }
                    tokens.push(Token::UInt64Number(value));
                    index += 3;
                } else {
                    if let Ok(value) = u32::try_from(value) {
                        tokens.push(Token::Number(value));
                    } else if let Ok(value) = i64::try_from(value) {
                        tokens.push(Token::Int64Number(value));
                    } else {
                        tokens.push(Token::UInt64Number(value));
                    }
                }
            }
            ch if is_ident_start(ch) => {
                let start = index;
                index += 1;
                while chars
                    .get(index)
                    .is_some_and(|next| is_ident_continue(*next))
                {
                    index += 1;
                }
                tokens.push(Token::Ident(chars[start..index].iter().collect()));
            }
            other => {
                return Err(ClickError::new(format!(
                    "{position}: unexpected character `{other}`"
                )));
            }
        }
        debug_assert!(tokens.len() <= tokens_before + 1);
        if tokens.len() > tokens_before {
            positions.push(position);
        }
    }

    Ok((tokens, positions))
}

fn tokenize_char_literal(chars: &[char], start: usize) -> Result<(u8, usize), ClickError> {
    let Some(first) = chars.get(start + 1).copied() else {
        return Err(ClickError::new("unterminated character literal"));
    };
    let (value, end) = if first == '\\' {
        let Some(escaped) = chars.get(start + 2).copied() else {
            return Err(ClickError::new("unterminated character literal"));
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
                return Err(ClickError::new(format!(
                    "unsupported character escape `\\{other}`"
                )));
            }
        };
        (value, start + 3)
    } else {
        if !first.is_ascii() {
            return Err(ClickError::new(
                "only ASCII character literals are supported",
            ));
        }
        (first as u8, start + 2)
    };

    if chars.get(end) != Some(&'\'') {
        return Err(ClickError::new(
            "character literals must contain exactly one byte",
        ));
    }

    Ok((value, end + 1))
}

fn tokenize_string(chars: &[char], start: usize) -> Result<(String, usize), ClickError> {
    let mut value = String::new();
    let mut index = start + 1;
    while let Some(ch) = chars.get(index).copied() {
        match ch {
            '"' => return Ok((value, index + 1)),
            '\\' => {
                let Some(escaped) = chars.get(index + 1).copied() else {
                    return Err(ClickError::new("unterminated string literal"));
                };
                match escaped {
                    '"' | '\\' => value.push(escaped),
                    'n' => value.push('\n'),
                    't' => value.push('\t'),
                    other => {
                        return Err(ClickError::new(format!(
                            "unsupported escape `\\{other}` in string literal"
                        )));
                    }
                }
                index += 2;
            }
            other => {
                value.push(other);
                index += 1;
            }
        }
    }

    Err(ClickError::new("unterminated string literal"))
}

fn is_ident_start(ch: char) -> bool {
    ch.is_ascii_alphabetic() || ch == '_'
}

fn is_ident_continue(ch: char) -> bool {
    ch.is_ascii_alphanumeric() || ch == '_'
}
