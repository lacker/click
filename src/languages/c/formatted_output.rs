//! `snprintf` calls whose format is a string literal (C11 7.21.6.1,
//! 7.21.6.5). The format fixes the call's arity and the meaning of each
//! argument, so each format is one fixed-arity function,
//! `__click_snprintf_<format bytes in hex>`, and its `extern` contract is
//! written here from the format's pieces. The contract states the output
//! with the decimal rendering functions of `library/format.click`, named by
//! their full `click::` paths so the text needs no import.

use std::fmt::Write as _;

/// The prefix of a formatted-output function's name.
pub(crate) const FORMATTED_OUTPUT_PREFIX: &str = "__click_snprintf_";

/// The widest field a conversion may request. It only keeps a field's
/// arithmetic small; the contract still bounds the whole output by `INT_MAX`.
const MAX_FIELD_WIDTH: u64 = 4096;

/// One piece of a format: the characters it writes, from the format itself
/// or from the argument it converts.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum FormatPiece {
    /// Ordinary characters, with `%%` read as `%`.
    Literal(Vec<u8>),
    /// `%u`, with an optional field width and `0` flag: an `unsigned int`'s
    /// decimal digits, padded on the left to `width` with `pad`.
    Unsigned { width: u64, pad: u8 },
    /// `%d` or `%i`: an `int`'s decimal digits, after a `-` when negative.
    Signed,
    /// `%s`: the characters of a C string, without its terminator.
    String,
}

/// The type of the argument a conversion consumes.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum FormatArgument {
    UnsignedInt,
    Int,
    String,
}

impl FormatPiece {
    pub(crate) fn argument(&self) -> Option<FormatArgument> {
        match self {
            Self::Literal(_) => None,
            Self::Unsigned { .. } => Some(FormatArgument::UnsignedInt),
            Self::Signed => Some(FormatArgument::Int),
            Self::String => Some(FormatArgument::String),
        }
    }
}

/// The pieces of `format`, the bytes of a format string literal without its
/// terminator, or why Click does not model it.
pub(crate) fn parse_format(format: &[u8]) -> Result<Vec<FormatPiece>, String> {
    let mut pieces = Vec::new();
    let mut literal = Vec::new();
    let mut index = 0;
    while index < format.len() {
        let byte = format[index];
        index += 1;
        if byte != b'%' {
            literal.push(byte);
            continue;
        }
        let start = index - 1;
        if format.get(index) == Some(&b'%') {
            index += 1;
            literal.push(b'%');
            continue;
        }
        let mut zero = false;
        while format.get(index) == Some(&b'0') {
            zero = true;
            index += 1;
        }
        let mut width = 0u64;
        while let Some(digit) = format.get(index).filter(|byte| byte.is_ascii_digit()) {
            width = width * 10 + u64::from(digit - b'0');
            if width > MAX_FIELD_WIDTH {
                return Err(format!(
                    "a field width above {MAX_FIELD_WIDTH} is not supported"
                ));
            }
            index += 1;
        }
        let spelling = |end: usize| String::from_utf8_lossy(&format[start..end]).into_owned();
        let Some(&conversion) = format.get(index) else {
            return Err(format!(
                "the format ends inside the conversion `{}`",
                spelling(index)
            ));
        };
        index += 1;
        let piece = match conversion {
            b'u' => FormatPiece::Unsigned {
                width,
                pad: if zero { b'0' } else { b' ' },
            },
            b'd' | b'i' if width == 0 && !zero => FormatPiece::Signed,
            b's' if width == 0 && !zero => FormatPiece::String,
            _ => {
                return Err(format!(
                    "the conversion `{}` is not supported; Click models `%u` with an optional `0` flag and width, `%d`, `%i`, `%s`, and `%%`",
                    spelling(index)
                ));
            }
        };
        if !literal.is_empty() {
            pieces.push(FormatPiece::Literal(std::mem::take(&mut literal)));
        }
        pieces.push(piece);
    }
    if !literal.is_empty() {
        pieces.push(FormatPiece::Literal(literal));
    }
    Ok(pieces)
}

/// The format of the formatted-output function `name`, when it is one.
pub(crate) fn function_format(name: &str) -> Option<Vec<u8>> {
    let hex = name.strip_prefix(FORMATTED_OUTPUT_PREFIX)?;
    (0..hex.len())
        .step_by(2)
        .map(|index| u8::from_str_radix(hex.get(index..index + 2)?, 16).ok())
        .collect()
}

/// The `extern` contract of `name` when it is a formatted-output function.
pub(crate) fn contract_for_function(name: &str) -> Option<String> {
    let pieces = parse_format(&function_format(name)?).ok()?;
    Some(contract_source(name, &pieces))
}

/// The C call a formatted-output function stands for, as a diagnostic
/// names it: `snprintf` with its format.
pub(crate) fn describe_function(name: &str) -> Option<String> {
    let format = function_format(name)?;
    Some(format!(
        "`snprintf` with format \"{}\"",
        String::from_utf8_lossy(&format).escape_default()
    ))
}

/// The formatted-output function for `format`.
pub(crate) fn function_name(format: &[u8]) -> String {
    let mut name = FORMATTED_OUTPUT_PREFIX.to_string();
    for byte in format {
        let _ = write!(name, "{byte:02x}");
    }
    name
}

/// The `extern` contract of the formatted-output function `name` for a
/// format with these pieces, as Click source.
///
/// `snprintf(buffer, size, format, ...)` writes the characters the format
/// produces, then a terminator, but no more than `size` characters: the
/// first `size - 1` characters and a terminator after them. Nothing is
/// written when `size` is zero, and the bytes after the terminator keep
/// their values. The result is the number of characters the format
/// produces, whether or not they fit (C11 7.21.6.5p2-3), and so is not
/// negative. Each character it writes, the terminator included, is stated
/// `defined`, so a caller may read a buffer `snprintf` filled though it never
/// wrote it itself. The contract requires that number and `size` to be at
/// most `INT_MAX`, where C and Linux would report an error; and it reads
/// each `%s` argument as a C string, so a null pointer, which Linux prints as
/// `(null)`, is refused.
pub(crate) fn contract_source(name: &str, pieces: &[FormatPiece]) -> String {
    let mut parameters = vec!["uint8 buffer[]".to_string(), "uint64 size".to_string()];
    let mut clauses = Vec::new();
    let mut lengths = Vec::new();
    let mut contents = Vec::new();
    let mut argument = 0usize;
    for piece in pieces {
        match piece {
            FormatPiece::Literal(bytes) => {
                lengths.push(format!("{}u64", bytes.len()));
                contents.push(Content::Bytes(bytes.clone()));
            }
            FormatPiece::Unsigned { width, pad } => {
                let value = format!("a{argument} as uint64");
                parameters.push(format!("uint32 a{argument}"));
                if *width == 0 {
                    lengths.push(format!("click::format::decimal_length({value})"));
                    contents.push(Content::Each(format!(
                        "click::format::decimal_digit({value}, k)"
                    )));
                } else {
                    lengths.push(format!("click::format::padded_length({value}, {width}u64)"));
                    contents.push(Content::Each(format!(
                        "click::format::padded_digit({value}, {width}u64, {pad}u8, k)"
                    )));
                }
                argument += 1;
            }
            FormatPiece::Signed => {
                parameters.push(format!("int32 a{argument}"));
                lengths.push(format!("click::format::signed_length(a{argument})"));
                contents.push(Content::Each(format!(
                    "click::format::signed_digit(a{argument}, k)"
                )));
                argument += 1;
            }
            FormatPiece::String => {
                parameters.push(format!("const uint8* a{argument}"));
                clauses.push(format!("    let n{argument}: uint64;"));
                clauses.push(format!(
                    "    views click::c::string::cstr_at(a{argument}, n{argument});"
                ));
                clauses.push(format!("    requires n{argument} <= 2147483647u64;"));
                lengths.push(format!("n{argument}"));
                contents.push(Content::Each(format!("a{argument}[k]")));
                argument += 1;
            }
        }
    }
    // Each length is at most `INT_MAX`, so their sum is exact in `uint64`.
    let total = if lengths.is_empty() {
        "0u64".to_string()
    } else {
        lengths.join(" + ")
    };
    clauses.push("    requires size <= 2147483647u64;".to_string());
    // The bound on the output's length is stated over the lengths the
    // arguments decide, with the literal pieces' fixed length moved to the
    // bound: one such length is then a comparison with no arithmetic, whose
    // `uint64` reading is the same whichever way the sidecar reads
    // arithmetic.
    let fixed = pieces
        .iter()
        .map(|piece| match piece {
            FormatPiece::Literal(bytes) => bytes.len() as u64,
            _ => 0,
        })
        .sum::<u64>();
    let decided = lengths
        .iter()
        .zip(pieces)
        .filter(|(_, piece)| !matches!(piece, FormatPiece::Literal(_)))
        .map(|(length, _)| length.clone())
        .collect::<Vec<_>>();
    clauses.push(match decided.as_slice() {
        [] => format!("    requires {total} <= 2147483647u64;"),
        [length] => format!(
            "    requires {length} <= {}u64;",
            2147483647u64.saturating_sub(fixed)
        ),
        lengths => format!(
            "    requires {} <= {};",
            lengths
                .iter()
                .map(|length| format!("to_integer({length})"))
                .collect::<Vec<_>>()
                .join(" + "),
            2147483647u64.saturating_sub(fixed)
        ),
    });
    clauses.push("    owns uninitialized(buffer[0..size]);".to_string());
    clauses.push(format!("    ensures result == ({total}) as int32;"));
    // The count is at most `INT_MAX` by the requirement above, so the
    // result is never negative; stating it spares each caller the cast.
    clauses.push("    ensures 0 <= result;".to_string());
    // The offset of the current piece, as a prefix of the index it adds to:
    // empty for the first piece.
    let mut offset = String::new();
    for (length, content) in lengths.iter().zip(&contents) {
        match content {
            Content::Bytes(bytes) => {
                for (position, byte) in bytes.iter().enumerate() {
                    clauses.push(format!(
                        "    ensures {offset}{position}u64 + 1u64 < size implies buffer[{offset}{position}u64] == {byte}u8;"
                    ));
                    clauses.push(format!(
                        "    ensures {offset}{position}u64 + 1u64 < size implies defined(buffer[{offset}{position}u64]);"
                    ));
                }
            }
            Content::Each(character) => {
                clauses.push(format!(
                    "    ensures forall (k: uint64) {{ k < {length} and {offset}k + 1u64 < size implies buffer[{offset}k] == {character} }};"
                ));
                clauses.push(format!(
                    "    ensures forall (k: uint64) {{ k < {length} and {offset}k + 1u64 < size implies defined(buffer[{offset}k]) }};"
                ));
            }
        }
        offset = format!("{offset}{length} + ");
    }
    // The terminator follows the output when it fits and ends the buffer
    // when it does not; a clipped output leaves no byte after it.
    clauses.push(format!(
        "    ensures {total} < size implies buffer[{total}] == 0u8;"
    ));
    clauses.push(format!(
        "    ensures {total} < size implies defined(buffer[{total}]);"
    ));
    // The same terminator read through the result, which is the count: a
    // caller states where its output ends with the value `snprintf` returned.
    clauses.push(
        "    ensures result as uint64 < size implies buffer[result as uint64] == 0u8;".to_string(),
    );
    clauses.push(format!(
        "    ensures size != 0u64 implies ({total} >= size implies buffer[size - 1u64] == 0u8);"
    ));
    clauses.push(
        "    ensures size != 0u64 implies (result as uint64 >= size implies buffer[size - 1u64] == 0u8);"
            .to_string(),
    );
    clauses.push(format!(
        "    ensures size != 0u64 implies ({total} >= size implies defined(buffer[size - 1u64]));"
    ));
    clauses.push(format!(
        "    ensures forall (k: uint64) {{ {total} < k and k < size implies buffer[k] == old(buffer[k]) }};"
    ));
    format!(
        "extern int32 {name}({}) {{\n{}\n}}\n",
        parameters.join(", "),
        clauses.join("\n")
    )
}

enum Content {
    Bytes(Vec<u8>),
    /// The character at position `k` of the piece.
    Each(String),
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_format_splits_into_literal_and_conversion_pieces() {
        assert_eq!(
            parse_format(b"%u%s.%03u%%").unwrap(),
            vec![
                FormatPiece::Unsigned {
                    width: 0,
                    pad: b' '
                },
                FormatPiece::String,
                FormatPiece::Literal(b".".to_vec()),
                FormatPiece::Unsigned {
                    width: 3,
                    pad: b'0'
                },
                FormatPiece::Literal(b"%".to_vec()),
            ]
        );
        assert_eq!(parse_format(b"").unwrap(), Vec::new());
        assert_eq!(parse_format(b"%i").unwrap(), vec![FormatPiece::Signed]);
    }

    #[test]
    fn unmodeled_conversions_are_refused_by_name() {
        for (format, conversion) in [
            ("%lu", "`%l`"),
            ("%5d", "`%5d`"),
            ("%-3u", "`%-`"),
            ("%.2s", "`%.`"),
            ("%x", "`%x`"),
            ("%", "`%`"),
        ] {
            let error = parse_format(format.as_bytes()).unwrap_err();
            assert!(error.contains(conversion), "{format}: {error}");
        }
    }

    #[test]
    fn a_contract_places_each_piece_after_the_ones_before_it() {
        let name = function_name(b"%u kB");
        let contract = contract_for_function(&name).unwrap();
        for clause in [
            "extern int32 __click_snprintf_2575206b42(uint8 buffer[], uint64 size, uint32 a0) {",
            "    requires size <= 2147483647u64;",
            "    requires click::format::decimal_length(a0 as uint64) <= 2147483644u64;",
            "    owns uninitialized(buffer[0..size]);",
            "    ensures result == (click::format::decimal_length(a0 as uint64) + 3u64) as int32;",
            "    ensures 0 <= result;",
            "    ensures result as uint64 < size implies buffer[result as uint64] == 0u8;",
            "    ensures forall (k: uint64) { k < click::format::decimal_length(a0 as uint64) and k + 1u64 < size implies buffer[k] == click::format::decimal_digit(a0 as uint64, k) };",
            "    ensures click::format::decimal_length(a0 as uint64) + 1u64 + 1u64 < size implies buffer[click::format::decimal_length(a0 as uint64) + 1u64] == 107u8;",
        ] {
            assert!(contract.contains(clause), "{clause}\n{contract}");
        }
        assert_eq!(contract_for_function("snprintf"), None);
    }

    #[test]
    fn a_format_names_its_function_by_its_bytes() {
        assert_eq!(function_name(b"%u"), "__click_snprintf_2575");
    }
}
