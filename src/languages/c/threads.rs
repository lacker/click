//! Recognition of the modeled user-space thread primitives.
//!
//! `pthread_create` and `pthread_join` are not ordinary external functions.
//! Under the `x86_64-linux-userspace` target their declarations come from
//! Click's modeled `<pthread.h>` projection, and a call to one means a checked
//! kernel transition selected by the declaration's identity. Nothing here
//! implements that transition; this module only decides which declarations
//! qualify and hands the kernel the exact declared interface.
//!
//! Recognition is by identity, so it has to be exact. A source that declares
//! its own `pthread_create` with a different shape is a different function
//! than the one the transition will be written against, and gets a diagnostic
//! naming the mismatch rather than silent ordinary treatment.

use std::collections::BTreeMap;
use std::sync::OnceLock;

use super::syntax::{self, C0FunctionHeader, C0FunctionPointerSignature, C0Parameter};
use super::target::CTarget;
use crate::kernel::ExternalCallSemantics;

/// The modeled thread primitives, in the order a diagnostic lists them.
pub(crate) const THREAD_PRIMITIVES: &[(&str, ExternalCallSemantics)] = &[
    ("pthread_create", ExternalCallSemantics::ThreadCreate),
    ("pthread_join", ExternalCallSemantics::ThreadJoin),
];

/// The kernel transition a declaration of `name` would stand for under
/// `target`, or `None` when the name is an ordinary function there. The
/// kernel target models no thread API at all, so nothing is recognized.
pub(crate) fn thread_primitive_semantics(
    target: CTarget,
    name: &str,
) -> Option<ExternalCallSemantics> {
    if target != CTarget::X86_64LinuxUserspace {
        return None;
    }
    THREAD_PRIMITIVES
        .iter()
        .find(|(primitive, _)| *primitive == name)
        .map(|(_, semantics)| *semantics)
}

/// Checks one source declaration of a recognized primitive against the
/// modeled header's, returning a sentence naming the first mismatch.
///
/// The modeled declarations are the specification the future transition is
/// written against, so this is the point where a same-named user declaration
/// is separated from the primitive rather than quietly standing in for it.
pub(crate) fn declaration_mismatch(name: &str, declared: &C0FunctionHeader) -> Option<String> {
    let modeled = modeled_declarations().get(name)?;
    if modeled.compatible_with(declared) {
        return None;
    }
    Some(format!(
        "C declaration of the thread primitive `{name}` does not match the modeled \
         `<pthread.h>` declaration: {}",
        first_difference(modeled, declared)
    ))
}

/// The exact declarations Click's modeled `<pthread.h>` projection provides,
/// parsed once from that header through the ordinary user-space include
/// model. Deriving them from the header rather than restating the shape here
/// keeps recognition and the projection from drifting apart.
fn modeled_declarations() -> &'static BTreeMap<String, C0FunctionHeader> {
    static MODELED: OnceLock<BTreeMap<String, C0FunctionHeader>> = OnceLock::new();
    MODELED.get_or_init(|| {
        let sources = BTreeMap::from([("__click_pthread_projection.c", "#include <pthread.h>\n")]);
        let expanded = super::source::expand_includes_for_target(
            "__click_pthread_projection.c",
            &sources,
            CTarget::X86_64LinuxUserspace,
        )
        .expect("the modeled pthread projection expands under the user-space target");
        let unit = syntax::parse_translation_unit_for_source(
            expanded.source(),
            "__click_pthread_projection.c",
            expanded.line_map(),
        )
        .expect("the modeled pthread projection parses");
        let declarations = unit.function_declarations;
        for (primitive, _) in THREAD_PRIMITIVES {
            assert!(
                declarations.contains_key(*primitive),
                "the modeled pthread projection must declare `{primitive}`"
            );
        }
        declarations
    })
}

fn first_difference(modeled: &C0FunctionHeader, declared: &C0FunctionHeader) -> String {
    if modeled.return_type() != declared.return_type()
        || modeled.return_pointee_is_constant() != declared.return_pointee_is_constant()
        || modeled.return_struct_name() != declared.return_struct_name()
        || modeled.return_pointer_struct_name() != declared.return_pointer_struct_name()
    {
        return format!(
            "the return type is `{}`, not `{}`",
            describe_return(declared),
            describe_return(modeled)
        );
    }
    if modeled.parameters().len() != declared.parameters().len() {
        return format!(
            "it takes {} parameters, not {}",
            declared.parameters().len(),
            modeled.parameters().len()
        );
    }
    for (index, (expected, actual)) in modeled
        .parameters()
        .iter()
        .zip(declared.parameters())
        .enumerate()
    {
        if !parameters_match(expected, actual) {
            return format!(
                "parameter {} is `{}`, not `{}`",
                index + 1,
                describe_parameter(actual),
                describe_parameter(expected)
            );
        }
    }
    // Every compared component matched, so the remaining difference is the
    // declaration's linkage: a `static` redeclaration is a different function.
    "it does not have the external linkage the primitive requires".to_string()
}

fn describe_return(header: &C0FunctionHeader) -> String {
    let base = match header
        .return_struct_name()
        .or(header.return_pointer_struct_name())
    {
        Some(name) => format!("struct {name}*"),
        None => format!("{:?}", header.return_type()),
    };
    if header.return_pointee_is_constant() {
        format!("const {base}")
    } else {
        base
    }
}

/// The parameter components `C0FunctionHeader::compatible_with` compares.
fn parameters_match(expected: &C0Parameter, actual: &C0Parameter) -> bool {
    expected.c_type() == actual.c_type()
        && expected.pointee_is_constant() == actual.pointee_is_constant()
        && expected.struct_name() == actual.struct_name()
        && expected.function_pointer_signature() == actual.function_pointer_signature()
        && expected.array_element_width() == actual.array_element_width()
}

fn describe_parameter(parameter: &C0Parameter) -> String {
    if let Some(signature) = parameter.function_pointer_signature() {
        return describe_callback(signature);
    }
    let base = match parameter.struct_name() {
        Some(name) => format!("struct {name}*"),
        None => format!("{:?}", parameter.c_type()),
    };
    if parameter.pointee_is_constant() {
        format!("const {base}")
    } else {
        base
    }
}

fn describe_callback(signature: &C0FunctionPointerSignature) -> String {
    let parameters = signature
        .parameters()
        .iter()
        .map(|parameter| match parameter.struct_name() {
            Some(name) => format!("struct {name}*"),
            None => format!("{:?}", parameter.c_type()),
        })
        .collect::<Vec<_>>()
        .join(", ");
    let return_type = match signature.return_struct_name() {
        Some(name) => format!("struct {name}*"),
        None => format!("{:?}", signature.return_type()),
    };
    format!("{return_type} (*)({parameters})")
}

/// The declared interface of a recognized primitive, ready for the kernel.
/// The declaration carries no contract: the semantics are the primitive's,
/// not a user's.
pub(crate) fn primitive_kernel_function(declared: &C0FunctionHeader) -> crate::kernel::CFunction {
    declared
        .to_declared_external_function()
        .to_kernel_function()
}
