//! Tuples in Click's specification language (`design/tuples.md`).
//!
//! A tuple type `(A, B)` is a built-in datatype of one constructor whose
//! fields are its components, so a tuple is an ordinary algebraic value:
//! the kernel's constructor terms, constructor equality (congruence and
//! injectivity) and `match` elimination apply to it unchanged. The datatype
//! of arity `n` is named [`type_name`]`(n)`, which no Click declaration can
//! spell, and its one constructor has the same name. The Click library
//! carries the definitions of arities `0..=MAX_ARITY`.
//!
//! The value `(a, b)` is that constructor, `t.1` is the single-arm match
//! `match t { (_0, _1) => _1 }`, and `let (a, b) = t; body` is
//! `match t { (a, b) => body }`. A projection of a constructed tuple is the
//! known-constructor match, which lowering selects by construction.
//!
//! Printing spells the datatype `(A, B)`, the constructor `(a, b)`, a
//! single-arm match whose body is one of its bindings `t.i`, and any other
//! tuple match pattern `(a, b)`. Binding names are not part of a term's
//! identity, so each spelling lowers back to the term it was printed from.

use super::*;

/// The largest arity the library declares, as Rust implements its standard
/// traits on tuples of at most twelve components.
pub(crate) const MAX_ARITY: usize = 12;

const PREFIX: &str = "(tuple)";

/// The datatype, and constructor, name of the tuple type of `arity`
/// components.
pub(crate) fn type_name(arity: usize) -> String {
    format!("{PREFIX}{arity}")
}

/// The arity of tuple datatype `name`, when it is one.
pub(crate) fn arity(name: &str) -> Option<usize> {
    name.strip_prefix(PREFIX)?.parse().ok()
}

/// The binding a projection's match names its `index`th component with.
pub(crate) fn projection_binding(index: usize) -> String {
    format!("_{index}")
}

/// The method a written projection `t.index` is parsed as until the
/// receiver's type resolves it.
pub(crate) fn projection_method(index: u32) -> String {
    format!(".{index}")
}

/// The component a projection method names.
pub(crate) fn projection_method_index(method: &str) -> Option<usize> {
    method.strip_prefix('.')?.parse().ok()
}

/// The library's tuple datatypes, of every arity up to [`MAX_ARITY`].
pub(crate) fn definitions() -> Vec<AlgebraicTypeDefinition> {
    (0..=MAX_ARITY)
        .map(|arity| {
            let parameters = (0..arity)
                .map(|index| format!("T{index}"))
                .collect::<Vec<_>>();
            AlgebraicTypeDefinition {
                name: type_name(arity),
                type_parameters: parameters.clone(),
                variants: vec![AlgebraicVariantDefinition {
                    name: type_name(arity),
                    fields: parameters
                        .into_iter()
                        .map(AlgebraicFieldType::Parameter)
                        .collect(),
                }],
                primitive: false,
            }
        })
        .collect()
}

/// The type of a tuple whose components have types `components`.
pub(crate) fn click_type(components: Vec<ClickType>) -> ClickType {
    ClickType::Algebraic(AlgebraicTypeApplication {
        rigid: false,
        name: type_name(components.len()),
        arguments: components,
    })
}

/// The tuple value `(components...)`. Its type arguments are left for
/// constructor inference, as `List::Cons(x, xs)` leaves out `List`'s.
pub(crate) fn constructor(components: Vec<SyntaxTerm>) -> SyntaxTerm {
    let name = type_name(components.len());
    SyntaxTerm::AlgebraicConstructor {
        algebraic_type: AlgebraicTypeApplication::concrete(name.clone()),
        variant: name,
        arguments: components,
    }
}

/// The one arm of a match that binds a tuple's components to `bindings`.
pub(crate) fn arm(bindings: Vec<SurfaceBinder>, body: SyntaxTerm) -> AlgebraicMatchArm {
    let name = type_name(bindings.len());
    AlgebraicMatchArm {
        type_name: name.clone(),
        variant: name,
        bindings,
        body,
    }
}

/// `tuple.index` on a tuple of `arity` components: the match that binds its
/// components and yields the `index`th.
pub(crate) fn projection(tuple: SyntaxTerm, arity: usize, index: usize) -> SyntaxTerm {
    let bindings = (0..arity)
        .map(|component| SurfaceBinder::Written(projection_binding(component)))
        .collect::<Vec<_>>();
    let body = bindings[index].reference();
    SyntaxTerm::AlgebraicMatch {
        scrutinee: Box::new(tuple),
        arms: vec![arm(bindings, body)],
    }
}

/// The component a single-arm tuple match yields, when its body is one of
/// its own bindings: the match is `scrutinee.index`.
pub(crate) fn projected_index(arms: &[AlgebraicMatchArm]) -> Option<usize> {
    let [arm] = arms else {
        return None;
    };
    arity(&arm.type_name)?;
    // The last binding of a name is the one the body sees.
    if let Some(id) = arm.body.generated_binder() {
        return arm
            .bindings
            .iter()
            .rposition(|binding| *binding == SurfaceBinder::Generated(id));
    }
    let body = match &arm.body {
        SyntaxTerm::Binding(name) | SyntaxTerm::ProgramBinding(name) => name.as_str(),
        SyntaxTerm::ProgramExpression(ProgramExpression::Variable(
            crate::kernel::BindingName::Named(name),
        )) => name.as_str(),
        SyntaxTerm::AlgebraicVariable {
            name: SurfaceBinder::Written(name),
            ..
        } => name.as_str(),
        _ => return None,
    };
    arm.bindings
        .iter()
        .rposition(|binding| binding.written() == Some(body))
}

/// `(a, b)`, `(a,)` or `()` from the spelled components.
pub(crate) fn spell(components: &[String]) -> String {
    match components {
        [single] => format!("({single},)"),
        _ => format!("({})", components.join(", ")),
    }
}

/// The projection `tuple.index` from the spelled tuple. A tuple spelled
/// with a space outside every bracket (an operator, a `match`) or with a
/// prefix operator is parenthesized, as `(a + b).0` is in Rust.
pub(crate) fn spell_projection(tuple: &str, index: usize) -> String {
    let mut depth = 0usize;
    let mut compound = tuple.starts_with(['-', '!', '*', '&']);
    for ch in tuple.chars() {
        match ch {
            '(' | '[' | '{' => depth += 1,
            ')' | ']' | '}' => depth = depth.saturating_sub(1),
            ch if depth == 0 && ch.is_whitespace() => compound = true,
            _ => {}
        }
    }
    if compound {
        format!("({tuple}).{index}")
    } else {
        format!("{tuple}.{index}")
    }
}
