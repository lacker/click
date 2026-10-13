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

/// Names a read address through a bound model accessor only when the
/// receiver's own layout identifies the exact scalar field at that address.
pub(super) fn describe_model_field_at(
    pointer: &Pointer,
    parameter_binding: ParameterBinding<'_>,
) -> Option<(String, CType)> {
    MODEL_ACCESSORS.with(|bound| {
        let bound = bound.borrow();
        if bound.is_empty() {
            return None;
        }
        for (parameter, argument) in parameter_binding
            .parameters
            .iter()
            .zip(parameter_binding.arguments)
        {
            let source = parameter
                .struct_name()
                .is_none()
                .then(|| {
                    crate::surface::proof_diagnostics::render::ambient_source_parameter(
                        parameter.name(),
                    )
                })
                .flatten();
            let parameter = source.as_ref().unwrap_or(parameter);
            if !parameter
                .struct_name()
                .is_some_and(|name| name.starts_with("span__"))
            {
                continue;
            }
            let CExpression::Value(CValue::Pointer(base)) = argument else {
                continue;
            };
            let Some(layout) = parameter
                .pointee_struct_layout()
                .or_else(|| parameter.struct_layout())
            else {
                continue;
            };
            let fields = layout.to_kernel_aggregate_layout();
            for (accessor, path) in bound.iter() {
                let field_path = path.join(".");
                let Some(field) = fields
                    .fields()
                    .iter()
                    .find(|field| field.name() == field_path)
                else {
                    continue;
                };
                let expected = base.pointer().offset_by_bytes(field.offset_bytes());
                if expected.block != pointer.block
                    || !crate::kernel::offsets_have_same_canonical_form(
                        &expected.offset,
                        &pointer.offset,
                    )
                {
                    continue;
                }
                let receiver = object_at_address(parameter.name()).unwrap_or(parameter.name());
                return Some((format!("{accessor}({receiver})"), field.c_type()));
            }
        }
        None
    })
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
