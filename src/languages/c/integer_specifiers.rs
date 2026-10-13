//! Shared normalization of contiguous standard C integer specifiers.

use super::syntax::{C0Type, LongRank, PlainChar};

/// The refusal when plain `char` is spelled where no C target fixes its
/// signedness.
pub(crate) const PLAIN_CHAR_NEEDS_TARGET: &str = "plain `char` is signed or unsigned depending on the C target, and no C target is selected here; spell `signed char` or `unsigned char`, or verify against a C source so the sidecar's target applies";

/// Normalizes the specifier words starting a type. `plain_char` is the
/// signedness the C target gives plain `char`; `None` means no target is
/// selected, and spelling plain `char` is then refused.
pub(crate) fn parse<'a>(
    words: impl Iterator<Item = &'a str>,
    plain_char: Option<PlainChar>,
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
                    "unsupported C type `long double`: extended-precision floating-point values are not modeled by Click",
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
            C0Type::Char(plain_char.ok_or(PLAIN_CHAR_NEEDS_TARGET)?)
        }
    } else if shorts > 0 {
        if unsigned {
            C0Type::UInt16
        } else {
            C0Type::Int16
        }
    } else if longs > 0 {
        // `long` and `long long` share a representation but stay distinct.
        let rank = if longs == 2 {
            LongRank::LongLong
        } else {
            LongRank::Long
        };
        if unsigned {
            C0Type::UInt64(rank)
        } else {
            C0Type::Int64(rank)
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
                    parse(words.iter().copied(), Some(PlainChar::Unsigned)),
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
            ("char", C0Type::Char(PlainChar::Unsigned)),
            ("signed char", C0Type::Int8),
            ("unsigned char", C0Type::UInt8),
            ("short int", C0Type::Int16),
            ("signed short int", C0Type::Int16),
            ("unsigned short int", C0Type::UInt16),
            ("signed int", C0Type::Int32),
            ("unsigned int", C0Type::UInt32),
            ("long int", C0Type::Int64(LongRank::Long)),
            ("signed long int", C0Type::Int64(LongRank::Long)),
            ("unsigned long int", C0Type::UInt64(LongRank::Long)),
            ("long long int", C0Type::Int64(LongRank::LongLong)),
            ("signed long long int", C0Type::Int64(LongRank::LongLong)),
            ("unsigned long long int", C0Type::UInt64(LongRank::LongLong)),
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
            assert!(
                parse(spelling.split_whitespace(), Some(PlainChar::Unsigned)).is_err(),
                "{spelling}"
            );
        }
        assert_eq!(
            parse(["uint64", "int"].into_iter(), Some(PlainChar::Unsigned)),
            Ok(None)
        );
        assert_eq!(
            parse(["long", "value"].into_iter(), Some(PlainChar::Unsigned)),
            Ok(Some((C0Type::Int64(LongRank::Long), 1)))
        );
    }

    #[test]
    fn plain_char_takes_the_targets_signedness_and_stays_distinct() {
        for plain in [PlainChar::Unsigned, PlainChar::Signed] {
            assert_eq!(
                parse(["char"].into_iter(), Some(plain)),
                Ok(Some((C0Type::Char(plain), 1)))
            );
            assert_eq!(
                parse(["signed", "char"].into_iter(), Some(plain)),
                Ok(Some((C0Type::Int8, 2)))
            );
            assert_eq!(
                parse(["unsigned", "char"].into_iter(), Some(plain)),
                Ok(Some((C0Type::UInt8, 2)))
            );
        }
        assert_ne!(C0Type::Char(PlainChar::Signed), C0Type::Int8);
        assert_ne!(C0Type::Char(PlainChar::Unsigned), C0Type::UInt8);
        assert_eq!(
            parse(["char"].into_iter(), None),
            Err(PLAIN_CHAR_NEEDS_TARGET)
        );
        assert_eq!(
            parse(["signed", "char"].into_iter(), None),
            Ok(Some((C0Type::Int8, 2)))
        );
    }
}
