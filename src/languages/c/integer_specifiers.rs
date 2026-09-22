//! Shared normalization of contiguous standard C integer specifiers.

use super::syntax::C0Type;

pub(crate) fn parse<'a>(
    words: impl Iterator<Item = &'a str>,
) -> Result<Option<(C0Type, usize)>, &'static str> {
    let (mut chars, mut shorts, mut ints, mut longs, mut signs, mut unsigned) =
        (0, 0, 0, 0, 0, false);
    let mut count = 0;
    for word in words {
        match word {
            "char" => chars += 1,
            "short" => shorts += 1,
            "int" => ints += 1,
            "long" => longs += 1,
            "signed" | "unsigned" => {
                signs += 1;
                unsigned = word == "unsigned";
            }
            "double" if longs > 0 => {
                return Err(
                    "unsupported C type `long double`: extended-precision floating-point values are not modeled in C0",
                );
            }
            _ => break,
        }
        count += 1;
        // Reject immediately, bounding both lookahead and counters even on
        // malformed input. Typedef names and fixed-width aliases are not words
        // in this grammar and therefore cannot acquire extra specifiers.
        if chars > 1
            || shorts > 1
            || ints > 1
            || longs > 2
            || signs > 1
            || (chars > 0 && shorts + ints + longs > 0)
            || (shorts > 0 && longs > 0)
        {
            return Err("invalid combination of standard integer type specifiers");
        }
    }
    if count == 0 {
        return Ok(None);
    }
    let c_type = if chars > 0 {
        if unsigned {
            C0Type::UInt8
        } else if signs > 0 {
            C0Type::Int8
        } else {
            C0Type::Char
        }
    } else if shorts > 0 {
        if unsigned {
            C0Type::UInt16
        } else {
            C0Type::Int16
        }
    } else if longs > 0 {
        if unsigned {
            C0Type::UInt64
        } else {
            C0Type::Int64
        }
    } else if unsigned {
        C0Type::UInt32
    } else {
        C0Type::Int32
    };
    Ok(Some((c_type, count)))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn standard_integer_specifiers_accept_every_order() {
        fn permutations(words: &mut [&str], index: usize, expected: C0Type) {
            if index == words.len() {
                assert_eq!(
                    parse(words.iter().copied()),
                    Ok(Some((expected, words.len()))),
                    "{words:?}"
                );
                return;
            }
            for other in index..words.len() {
                words.swap(index, other);
                permutations(words, index + 1, expected);
                words.swap(index, other);
            }
        }
        for (spelling, expected) in [
            ("char", C0Type::Char),
            ("signed char", C0Type::Int8),
            ("unsigned char", C0Type::UInt8),
            ("short int", C0Type::Int16),
            ("signed short int", C0Type::Int16),
            ("unsigned short int", C0Type::UInt16),
            ("signed int", C0Type::Int32),
            ("unsigned int", C0Type::UInt32),
            ("long int", C0Type::Int64),
            ("signed long int", C0Type::Int64),
            ("unsigned long int", C0Type::UInt64),
            ("long long int", C0Type::Int64),
            ("signed long long int", C0Type::Int64),
            ("unsigned long long int", C0Type::UInt64),
        ] {
            permutations(
                &mut spelling.split_whitespace().collect::<Vec<_>>(),
                0,
                expected,
            );
        }
    }

    #[test]
    fn standard_integer_specifiers_reject_conflicts_and_duplicates() {
        for spelling in [
            "signed unsigned",
            "signed signed",
            "long long long",
            "char int",
            "char short",
            "long char",
            "short long",
            "int int",
            "short short",
            "char char",
            "unsigned unsigned",
        ] {
            assert!(parse(spelling.split_whitespace()).is_err(), "{spelling}");
        }
        assert_eq!(parse(["uint64", "int"].into_iter()), Ok(None));
        assert_eq!(
            parse(["long", "value"].into_iter()),
            Ok(Some((C0Type::Int64, 1)))
        );
    }
}
