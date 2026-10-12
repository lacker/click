//! The names the Rust importer gives items, and their Rust spelling.
//!
//! The importer names an item at a path `quad::walk` by `__rust_q` and each
//! segment with its length, `__rust_q_I4_quad_I4_walk`, and an inherent
//! method by its module, then `_T` and its type's own name, then the method:
//! `__rust_q_I6_adler2_T29___rust_q_I6_adler2_I7_Adler32_I3_new`
//! ([`path_name`], [`inherent_method_name`]).
//! A sidecar writes the path, `adler2::Adler32::new`, and a diagnostic prints
//! it the same way. The encoding is self-delimiting, so decoding needs no
//! import.
//!
//! An operator-trait method is named by its type, the method, and the
//! trait's type argument (`rhs_name` in
//! `src/languages/rust/charon/assignment_operators.rs`):
//! `__rust_q_I6_adler2_I4_algo_I5_U32X4_mul_assign_u32`, and `Default` by its
//! type and `_default`. These print in Rust's qualified form,
//! `<adler2::algo::U32X4 as MulAssign<u32>>::mul_assign` and
//! `<adler2::Adler32 as Default>::default`. A name with any other suffix
//! keeps the importer's spelling.

use std::borrow::Cow;

const PREFIX: &str = "__rust_q";

/// Appends one path segment to an importer name: `_I`, its length, `_`, and
/// the segment.
pub(crate) fn push_path_segment(encoded: &mut String, segment: &str) {
    encoded.push_str(&format!("_I{}_{segment}", segment.len()));
}

/// Appends the type an inherent method's `impl` block names: `_T`, the
/// type's own importer name's length, `_`, and that name.
pub(crate) fn push_impl_type(encoded: &mut String, type_name: &str) {
    encoded.push_str(&format!("_T{}_{type_name}", type_name.len()));
}

/// The importer name of the item at a path, `quad::walk` or
/// `adler2::algo::U32X4`: the prefix and each segment
/// (`__rust_q_I4_quad_I4_walk`).
pub(crate) fn qualified_name<'s>(segments: impl IntoIterator<Item = &'s str>) -> String {
    let mut encoded = PREFIX.to_string();
    for segment in segments {
        push_path_segment(&mut encoded, segment);
    }
    encoded
}

/// The name a sidecar's path of segments denotes: a single segment is the
/// name itself, a longer path its [`qualified_name`].
pub(crate) fn path_name(segments: &[&str]) -> String {
    match segments {
        [name] => (*name).to_string(),
        _ => qualified_name(segments.iter().copied()),
    }
}

/// The name of an inherent method of the type named `impl_type`, whose
/// `impl` block is in the type's own module. A type named by a path has
/// the importer's qualified method name, its module, then the `impl` type,
/// then the method; any other is `Type_method`.
pub(crate) fn inherent_method_name(
    impl_module: Option<&str>,
    impl_type: &str,
    method: &str,
) -> String {
    // An item inside the method, `compute::LIMIT`, arrives with its path
    // segments already written after the method's own name
    // ([`method_path_name`]); the length the importer writes is the
    // method's alone.
    let (own, inside) = method.split_at(method.find("_I").unwrap_or(method.len()));
    match impl_module {
        Some(module) => {
            let mut encoded = module.to_string();
            push_impl_type(&mut encoded, impl_type);
            push_path_segment(&mut encoded, own);
            encoded.push_str(inside);
            encoded
        }
        None => format!("{impl_type}_{method}"),
    }
}

/// A method's name as written in an `impl` block, `compute` or
/// `compute::LIMIT`: the method's own name, then each further segment as
/// the importer writes a path segment.
pub(crate) fn method_path_name(path: &[&str]) -> String {
    let mut name = path[0].to_string();
    for segment in &path[1..] {
        push_path_segment(&mut name, segment);
    }
    name
}

/// The path `name` stands for, `quad::walk`, when it is a whole importer
/// name; `None` for any other name.
pub fn rust_display_name(name: &str) -> Option<String> {
    let (path, rest) = decode(name)?;
    if rest.is_empty() {
        return Some(path);
    }
    operator_method_display(&path, rest)
}

/// The operator-trait methods the importer names after their type, by method
/// name, with the trait each belongs to.
const OPERATOR_METHODS: [(&str, &str); 10] = [
    ("add_assign", "AddAssign"),
    ("sub_assign", "SubAssign"),
    ("mul_assign", "MulAssign"),
    ("div_assign", "DivAssign"),
    ("rem_assign", "RemAssign"),
    ("bitand_assign", "BitAndAssign"),
    ("bitor_assign", "BitOrAssign"),
    ("bitxor_assign", "BitXorAssign"),
    ("shl_assign", "ShlAssign"),
    ("shr_assign", "ShrAssign"),
];

/// The scalar types an operator trait's argument may name directly.
const SCALARS: [&str; 6] = ["i32", "u8", "u16", "u32", "usize", "bool"];

/// The qualified form of the method of type `type_path` whose importer name
/// continues with `suffix`: `_default`, or `_<method>_<argument>` for an
/// operator trait. `None` for any other suffix.
fn operator_method_display(type_path: &str, suffix: &str) -> Option<String> {
    let suffix = suffix.strip_prefix('_')?;
    if suffix == "default" {
        return Some(format!("<{type_path} as Default>::default"));
    }
    OPERATOR_METHODS.iter().find_map(|(method, trait_name)| {
        let argument = suffix.strip_prefix(method)?.strip_prefix('_')?;
        let argument = trait_argument_display(argument)?;
        Some(format!(
            "<{type_path} as {trait_name}<{argument}>>::{method}"
        ))
    })
}

/// The Rust spelling of an operator trait's type argument as the importer
/// encodes it: a scalar by name, a record by value as
/// `value_<length><name>`, and a reference as `ref_` or `ref_mut_` and what
/// it refers to.
fn trait_argument_display(argument: &str) -> Option<String> {
    if let Some(referent) = argument.strip_prefix("ref_mut_") {
        return Some(format!("&mut {}", type_display(referent)?));
    }
    if let Some(referent) = argument.strip_prefix("ref_") {
        return Some(format!("&{}", type_display(referent)?));
    }
    if let Some(value) = argument.strip_prefix("value_") {
        let digits = value.bytes().take_while(u8::is_ascii_digit).count();
        let length = value[..digits].parse::<usize>().ok()?;
        let name = value.get(digits..)?;
        return (name.len() == length).then(|| type_display(name)).flatten();
    }
    SCALARS.contains(&argument).then(|| argument.to_string())
}

/// A type name the importer wrote whole: a scalar, an importer path, or a
/// type at the crate root by its bare name.
fn type_display(name: &str) -> Option<String> {
    if SCALARS.contains(&name) {
        return Some(name.to_string());
    }
    match decode(name) {
        Some((path, "")) => Some(path),
        Some(_) => None,
        None => (!name.is_empty()
            && !name.starts_with(PREFIX)
            && name
                .bytes()
                .all(|byte| byte.is_ascii_alphanumeric() || byte == b'_'))
        .then(|| name.to_string()),
    }
}

/// Decodes the importer name at the start of `text`: its path and the text
/// after it.
fn decode(text: &str) -> Option<(String, &str)> {
    let mut rest = text.strip_prefix(PREFIX)?;
    let mut segments: Vec<String> = Vec::new();
    while let Some(tail) = rest.strip_prefix('_') {
        let (kind, tail) = match tail.as_bytes().first() {
            Some(b'I') => ('I', &tail[1..]),
            Some(b'T') => ('T', &tail[1..]),
            _ => break,
        };
        let digits = tail.bytes().take_while(u8::is_ascii_digit).count();
        if digits == 0 {
            break;
        }
        let Ok(length) = tail[..digits].parse::<usize>() else {
            break;
        };
        let Some(segment_start) = tail[digits..].strip_prefix('_') else {
            break;
        };
        let Some(segment) = segment_start.get(..length) else {
            break;
        };
        if kind == 'T' {
            // A type is named by its own path, which includes its module:
            // the method's module is not written again.
            let Some((type_path, "")) = decode(segment) else {
                // A type at the crate root is its bare name.
                segments.push(segment.to_string());
                rest = &segment_start[length..];
                continue;
            };
            segments = vec![type_path];
        } else {
            if !segment
                .bytes()
                .all(|byte| byte.is_ascii_alphanumeric() || byte == b'_')
            {
                break;
            }
            segments.push(segment.to_string());
        }
        rest = &segment_start[length..];
    }
    if segments.len() < 2 && !segments.iter().any(|segment| segment.contains("::")) {
        return None;
    }
    Some((segments.join("::"), rest))
}

/// `text` with every whole importer name it contains spelled as its path.
pub fn display_rust_names(text: &str) -> Cow<'_, str> {
    if !text.contains(PREFIX) {
        return Cow::Borrowed(text);
    }
    let mut output = String::with_capacity(text.len());
    let mut rest = text;
    while let Some(start) = rest.find(PREFIX) {
        let preceded_by_identifier = rest[..start]
            .bytes()
            .last()
            .is_some_and(|byte| byte.is_ascii_alphanumeric() || byte == b'_');
        output.push_str(&rest[..start]);
        let candidate = &rest[start..];
        let end = candidate
            .bytes()
            .position(|byte| !(byte.is_ascii_alphanumeric() || byte == b'_'))
            .unwrap_or(candidate.len());
        let identifier = &candidate[..end];
        match (!preceded_by_identifier)
            .then(|| rust_display_name(identifier))
            .flatten()
        {
            Some(path) => output.push_str(&path),
            None => output.push_str(identifier),
        }
        rest = &candidate[end..];
    }
    output.push_str(rest);
    Cow::Owned(output)
}

/// Whether the claim label `label` is the one `requested` names, as the
/// importer spells it or as its Rust path.
pub fn claim_label_matches(label: &str, requested: &str) -> bool {
    label == requested || (requested.contains("::") && display_rust_names(label) == requested)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn importer_names_read_as_their_paths() {
        assert_eq!(
            rust_display_name("__rust_q_I4_quad_I4_walk").as_deref(),
            Some("quad::walk")
        );
        assert_eq!(
            rust_display_name("__rust_q_I6_adler2_I4_algo_I5_U32X4").as_deref(),
            Some("adler2::algo::U32X4")
        );
        assert_eq!(
            rust_display_name("__rust_q_I6_adler2_T29___rust_q_I6_adler2_I7_Adler32_I3_new")
                .as_deref(),
            Some("adler2::Adler32::new")
        );
        assert_eq!(
            rust_display_name(
                "__rust_q_I6_adler2_I4_algo_T29___rust_q_I6_adler2_I7_Adler32_I7_compute_I3_MOD"
            )
            .as_deref(),
            Some("adler2::Adler32::compute::MOD")
        );
        // A suffix that is no operator method keeps the importer's spelling.
        assert_eq!(
            rust_display_name("__rust_q_I6_adler2_I4_algo_I5_U32X4_frobnicate_u32"),
            None
        );
        assert_eq!(
            rust_display_name("__rust_q_I6_adler2_I4_algo_I5_U32X4_mul_assign_f99"),
            None
        );
        assert_eq!(rust_display_name("walk"), None);
        assert_eq!(rust_display_name("__rust_q_I9_short"), None);
    }

    #[test]
    fn operator_methods_read_as_qualified_trait_methods() {
        let lanes = "__rust_q_I6_adler2_I4_algo_I5_U32X4";
        let cases = [
            (
                format!("{lanes}_mul_assign_u32"),
                "<adler2::algo::U32X4 as MulAssign<u32>>::mul_assign",
            ),
            (
                format!("{lanes}_add_assign_value_{}{lanes}", lanes.len()),
                "<adler2::algo::U32X4 as AddAssign<adler2::algo::U32X4>>::add_assign",
            ),
            (
                format!("{lanes}_add_assign_ref_{lanes}"),
                "<adler2::algo::U32X4 as AddAssign<&adler2::algo::U32X4>>::add_assign",
            ),
            (
                format!("{lanes}_rem_assign_ref_mut_{lanes}"),
                "<adler2::algo::U32X4 as RemAssign<&mut adler2::algo::U32X4>>::rem_assign",
            ),
            (
                format!("{lanes}_sub_assign_ref_u16"),
                "<adler2::algo::U32X4 as SubAssign<&u16>>::sub_assign",
            ),
            (
                format!("{lanes}_shl_assign_value_5Lanes"),
                "<adler2::algo::U32X4 as ShlAssign<Lanes>>::shl_assign",
            ),
            (
                "__rust_q_I6_adler2_I7_Adler32_default".to_string(),
                "<adler2::Adler32 as Default>::default",
            ),
        ];
        for (name, display) in cases {
            assert_eq!(rust_display_name(&name).as_deref(), Some(display), "{name}");
            let label = format!("{name}.contract");
            assert_eq!(display_rust_names(&label), format!("{display}.contract"));
            assert!(claim_label_matches(&label, &format!("{display}.contract")));
            assert!(claim_label_matches(&label, &label));
        }
        for (method, trait_name) in OPERATOR_METHODS {
            assert_eq!(
                rust_display_name(&format!("{lanes}_{method}_bool")),
                Some(format!(
                    "<adler2::algo::U32X4 as {trait_name}<bool>>::{method}"
                ))
            );
        }
        // A by-value record's length must cover its whole name.
        assert_eq!(
            rust_display_name(&format!("{lanes}_add_assign_value_4{lanes}")),
            None
        );
        assert_eq!(rust_display_name(&format!("{lanes}_default_u32")), None);
    }

    #[test]
    fn a_message_prints_paths_for_importer_names() {
        assert_eq!(
            display_rust_names(
                "`__rust_q_I4_quad_I4_walk.contract` path 0: x___rust_q_I4_quad_I4_walk stays"
            ),
            "`quad::walk.contract` path 0: x___rust_q_I4_quad_I4_walk stays"
        );
        assert!(matches!(
            display_rust_names("plain"),
            Cow::Borrowed("plain")
        ));
        assert!(claim_label_matches(
            "__rust_q_I4_quad_I4_walk.contract",
            "quad::walk.contract"
        ));
        assert!(claim_label_matches(
            "__rust_q_I4_quad_I4_walk.contract",
            "__rust_q_I4_quad_I4_walk.contract"
        ));
        assert!(!claim_label_matches(
            "__rust_q_I4_quad_I4_walk.contract",
            "quad::other.contract"
        ));
    }
}
