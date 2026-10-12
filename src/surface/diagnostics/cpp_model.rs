//! How diagnostics print the C++ standard-library model accessors a prepared
//! program's layouts support.

use super::*;

thread_local! {
    /// The C++ model accessors bound for the program being verified or
    /// expanded, each with its field path. Set for the lifetime of a prepared
    /// program's source context, so a printed accessor is one its parse binds.
    static MODEL_ACCESSORS: std::cell::RefCell<Vec<(&'static str, &'static [&'static str])>> =
        const { std::cell::RefCell::new(Vec::new()) };
}

/// Binds the model accessors a prepared program's layouts support for
/// printing, restoring the previous binding when dropped.
pub(in crate::surface) struct ModelAccessorScope {
    previous: Vec<(&'static str, &'static [&'static str])>,
}

impl ModelAccessorScope {
    pub(in crate::surface) fn enter(
        layouts: &BTreeMap<String, syntax::C0StructLayout>,
    ) -> Option<Self> {
        let accessors = crate::languages::cpp::standard_library::model_accessors(layouts);
        if accessors.is_empty() {
            return None;
        }
        let previous =
            MODEL_ACCESSORS.with(|bound| bound.replace(accessors.into_iter().collect::<Vec<_>>()));
        Some(Self { previous })
    }
}

impl Drop for ModelAccessorScope {
    fn drop(&mut self) {
        MODEL_ACCESSORS.with(|bound| *bound.borrow_mut() = std::mem::take(&mut self.previous));
    }
}

/// `std_span_size(span)` for the field chain `span._M_extent._M_extent_value`
/// when that chain is a bound accessor's path: a written proof names the
/// standard type's model, and the parse rewrites it back to the same path.
pub(super) fn describe_model_accessor(expression: &ContractExpression) -> Option<String> {
    MODEL_ACCESSORS.with(|bound| {
        let bound = bound.borrow();
        if bound.is_empty() {
            return None;
        }
        let mut path = Vec::new();
        let mut root = expression;
        while let ContractExpression::Field { base, field, .. } = root {
            path.push(field.as_str());
            root = base;
        }
        path.reverse();
        let (accessor, _) = bound
            .iter()
            .find(|(_, bound_path)| *bound_path == path.as_slice())?;
        // A reference parameter's carrier prints as `&span`; the accessor
        // takes the referent, as a written field access does.
        let root = describe_contract_expression(root);
        let root = object_at_address(&root).map_or(root.clone(), str::to_string);
        Some(format!("{accessor}({root})"))
    })
}
