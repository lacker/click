//! Native Rust ULLBC adapter for the supported subset. All bodies use the same CFG path.
//! Charon owns Rust normalization; Click owns execution and checked authority.
#[cfg(test)]
mod array_lengths_tests;
mod assignment_operators;
mod box_free;
mod box_place_drop;
mod chunks;
mod closures;
mod constants;
mod constructors;
mod core_methods;
mod enumerate;
mod option_take;
#[cfg(test)]
mod option_take_tests;
mod option_try;
#[cfg(test)]
mod option_try_tests;
mod panics;
mod protocol;
mod ranges;
mod referent_match;
mod result_try;
mod shared_arrays;
#[cfg(test)]
mod slice_into_iteration_tests;
mod split_slices;
#[cfg(test)]
mod split_slices_tests;
mod temporaries;
pub(super) use temporaries::{
    moved_drop_operands, scalar_expression_operands, tested_option_box_local,
};
mod traits;
mod user_iterators;
mod vec_methods;

use super::profile;
use super::schema::{
    self as out, Expression as E, MirCallee, MirLocalId, MirStatement as S, MirTerminator as T,
    Type,
};
use crate::languages::compiler_process::{CompilerLimits, run_compiler};
use charon_lib::ast::from_rustc::LangItem;
use charon_lib::ast::{AstVisitable, TyVisitable};
use charon_lib::{ast as a, ullbc_ast as u};
use std::collections::{BTreeMap, BTreeSet};
use std::path::Path;
use std::time::Duration;

#[derive(serde::Serialize, serde::Deserialize)]
#[serde(deny_unknown_fields)]
struct ExtractionArtifact {
    extractor_revision: String,
    compiler_commit: String,
    profile: String,
    flags: Vec<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    crate_config: Option<super::crate_inputs::CrateConfig>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    crate_profile: Option<String>,
    data: charon_lib::export::CrateData,
}

pub(super) fn extract_crate(
    runtime: &super::runtime::Runtime,
    source: &Path,
    root: &Path,
    crate_config: Option<&super::crate_inputs::CrateConfig>,
    sources: Option<&super::crate_inputs::SourceFiles>,
) -> Result<Vec<u8>, String> {
    let executable = &runtime.executable;
    let environment = &runtime.environment;
    let limits = CompilerLimits {
        timeout: Duration::from_secs(30),
        max_stdout_bytes: 64 << 10,
        max_stderr_bytes: 64 << 10,
    };
    runtime.check(root, limits)?;
    let temp = tempfile::tempdir().map_err(|e| e.to_string())?;
    // Compile a private immutable source copy, so even include_bytes! inputs cannot
    // change between dep-info, translation, and the final source recheck.
    let source_copy = temp.path().join("sources");
    let mut copied_source = None;
    if let Some(c) = crate_config {
        let files = sources.ok_or("missing crate source copy")?;
        for name in &c.files {
            let target = source_copy.join(name);
            std::fs::create_dir_all(target.parent().unwrap()).map_err(|e| e.to_string())?;
            std::fs::write(&target, files.get(name).ok_or("missing crate source file")?)
                .map_err(|e| e.to_string())?;
        }
        copied_source = Some(
            source_copy.join(
                source
                    .strip_prefix(root)
                    .map_err(|_| "crate root escapes inputs")?,
            ),
        );
    }
    let root = if crate_config.is_some() {
        source_copy.as_path()
    } else {
        root
    };
    let source = copied_source.as_deref().unwrap_or(source);
    let flags = crate_config.map_or_else(|| profile::get().flags.clone(), |c| c.flags());
    if let Some(c) = crate_config {
        let dep = temp.path().join("inputs.d");
        let mut rustc_args = vec![
            source.to_string_lossy().into_owned(),
            "--crate-type=lib".into(),
            format!("--crate-name={}", c.name),
            format!("--emit=dep-info={}", dep.display()),
        ];
        rustc_args.extend(flags.iter().cloned());
        runtime.run_rustc(&rustc_args, root, limits).map_err(|error| {
            format!("Rust crate input check failed; the compiler sees only configured files. Check `crate.files` for missing module/include inputs.\n{}", error.replace(&format!("{}/", root.display()), ""))
        })?;
        let observed =
            super::crate_inputs::dep_files(&std::fs::read(&dep).map_err(|e| e.to_string())?, root)?;
        super::crate_inputs::check_closure(&c.files, &observed)?;
    }
    // Historical metadata labels remain stable so naming cleanup does not
    // rewrite frozen artifacts. They are not the frontend's product identity.
    let artifact = temp.path().join("trial.ullbc");
    let mut args: Vec<String> = [
        "rustc",
        "--ullbc",
        "--mir",
        "optimized",
        "--precise-drops",
        "--reconstruct-fallible-operations",
        "--sysroot",
        "default",
        "--opaque",
        "core",
        "--opaque",
        "alloc",
        "--opaque",
        "std",
        "--error-on-warnings",
        "--dest-file",
    ]
    .into_iter()
    .map(str::to_string)
    .collect();
    args.push(artifact.to_string_lossy().into_owned());
    if let Some(c) = crate_config {
        for root in &c.roots {
            args.extend(["--start-from".into(), root.clone()]);
        }
    }
    args.extend(flags.iter().map(|flag| format!("--rustc-arg={flag}")));
    if let Some(sysroot) = &runtime.sysroot {
        args.push(format!("--rustc-arg=--sysroot={}", sysroot.display()));
    }
    args.extend([
        "--".into(),
        source.to_string_lossy().into_owned(),
        "--crate-name".into(),
        crate_config
            .map_or("click_charon_trial", |c| c.name.as_str())
            .into(),
        "--crate-type".into(),
        "lib".into(),
    ]);
    run_compiler(executable, &args, temp.path(), environment, limits)?;
    let metadata = std::fs::metadata(&artifact).map_err(|e| e.to_string())?;
    if !metadata.is_file() || metadata.len() > 4 << 20 {
        return Err("Rust frontend artifact exceeds its file bound".into());
    }
    let bytes = std::fs::read(artifact).map_err(|e| e.to_string())?;
    let mut data: charon_lib::export::CrateData =
        serde_json::from_slice(&bytes).map_err(|e| format!("Charon output: {e}"))?;
    // Temporary output paths are extraction metadata, not Rust semantics.
    // Keep artifacts reproducible, including configs that share one output.
    data.translated.options.dest_file = Some("trial.ullbc".into());
    if let Some(c) = crate_config {
        for file in &mut data.translated.files {
            if let a::FileName::Local(path) = &mut file.name {
                let absolute = if path.is_absolute() {
                    path.clone()
                } else {
                    temp.path().join(&*path)
                };
                let Ok(relative) = absolute.strip_prefix(root) else {
                    continue;
                };
                let relative = super::crate_inputs::resolve_parents(root, relative)?;
                let name = relative.to_str().ok_or("Charon source path is not UTF-8")?;
                if !c.files.iter().any(|f| f == name) {
                    return Err("Charon source is outside the compiler source closure".into());
                }
                *path = relative;
            }
        }
    }
    // Single-file imports also need portable metadata: rustc names this input
    // by its absolute checkout path. Only this crate's file is rewritten;
    // external library locations retain their compiler identity.
    if crate_config.is_none() {
        let name = source.file_name().ok_or("Rust source needs a filename")?;
        for file in &mut data.translated.files {
            if file.crate_name == data.translated.crate_name {
                file.name = a::FileName::Local(name.into());
            }
        }
    }
    serde_json::to_vec(&ExtractionArtifact {
        extractor_revision: profile::get().extractor_revision.clone(),
        compiler_commit: profile::get().compiler_commit.clone(),
        profile: profile::get().extraction.clone(),
        flags,
        crate_config: crate_config.cloned(),
        crate_profile: crate_config.map(|_| super::crate_inputs::PROFILE_ID.into()),
        data,
    })
    .map_err(|e| e.to_string())
}

fn unsupported(what: &str) -> String {
    format!("Rust frontend does not support {what}")
}
fn span(s: a::Span) -> out::Span {
    out::Span {
        line: s.data().beg.line as usize,
        column: s.data().beg.col as usize + 1,
    }
}
/// A macro's generated code can belong to a different file from its caller.
/// Keep the reported filename and line together, preferring either recorded
/// span in the enclosing item's file and otherwise the item's own location.
fn refusal_location(
    krate: &a::TranslatedCrate,
    source: &str,
    candidate: a::Span,
    enclosing: a::Span,
) -> String {
    let enclosing = enclosing.data();
    let selected = [Some(candidate.data()), candidate.generated_from_span()]
        .into_iter()
        .flatten()
        .find(|span| span.file_id == enclosing.file_id)
        .unwrap_or(enclosing);
    let filename = krate
        .files
        .get(selected.file_id)
        .and_then(|file| {
            if let a::FileName::Local(path) = &file.name {
                path.to_str()
            } else {
                None
            }
        })
        .unwrap_or(source);
    format!("{filename}:{}", selected.beg.line)
}
fn simple_name(n: &a::Name, krate: &str) -> Result<String, String> {
    match n.name.as_slice() {
        [a::PathElem::Ident(c, d), a::PathElem::Ident(name, nd)]
            if c == krate && d.is_zero() && nd.is_zero() =>
        {
            Ok(name.clone())
        }
        _ => Err(unsupported("nested or disambiguated source items")),
    }
}
// Length-prefixed, tagged components keep Rust paths injective in C identifiers.
fn qualified_record_name(name: &a::Name, krate: &str) -> Result<String, String> {
    let Some(a::PathElem::Ident(root, d)) = name.name.first() else {
        return Err(unsupported("qualified declaration root"));
    };
    if root != krate || !d.is_zero() {
        return Err(unsupported("qualified declaration crate identity"));
    }
    let mut segments = Vec::with_capacity(name.name.len());
    for part in &name.name {
        let a::PathElem::Ident(n, d) = part else {
            return Err(unsupported("record path component"));
        };
        if !d.is_zero() {
            return Err(unsupported("disambiguated source declaration"));
        }
        segments.push(n.as_str());
    }
    Ok(super::names::qualified_name(segments))
}
impl Adapter<'_> {
    /// A function declared in an `extern` block: its name, its scalar
    /// parameters by position, since Charon keeps no names for a foreign
    /// item, and no body. A sidecar's `extern fn` names the parameters.
    fn external_function(&self, name: &str, f: &a::FunDecl) -> Result<out::Function, String> {
        let scalar = |ty: &Type| ty.is_scalar();
        let return_type = self.ty(&f.signature.output)?;
        if !scalar(&return_type) && return_type != Type::Unit {
            return Err(unsupported(
                "extern function result other than a scalar or ()",
            ));
        }
        let parameters = f
            .signature
            .inputs
            .iter()
            .enumerate()
            .map(|(index, ty)| {
                let value_type = self.ty(ty)?;
                if !scalar(&value_type) {
                    return Err(unsupported("extern function parameter other than a scalar"));
                }
                Ok(out::Place {
                    name: MirLocalId::PositionalParameter { position: index },
                    value_type,
                    span: span(f.item_meta.span),
                })
            })
            .collect::<Result<_, String>>()?;
        Ok(out::Function {
            sites: Vec::new(),
            name: name.to_string(),
            return_type,
            parameters,
            body: vec![],
            mir: None,
            external: true,
            captures: 0,
            implements: None,
            instance_of: None,
            core_method: None,
            span: span(f.item_meta.span),
        })
    }

    /// The types a call gives its callee's abstract type parameters: each
    /// such parameter at the scalar type the call names, the others as the
    /// callee's bounds give them. `None` when the callee has none.
    fn call_instantiation(
        &self,
        callee_parameters: &[Option<Type>],
        pointer: &a::FnPtr,
    ) -> Result<Option<Vec<Option<Type>>>, String> {
        if !callee_parameters
            .iter()
            .any(|parameter| matches!(parameter, Some(Type::Parameter { .. })))
        {
            return Ok(None);
        }
        if pointer.generics.types.len() != callee_parameters.len() {
            return Err(unsupported("generic call of a different arity"));
        }
        callee_parameters
            .iter()
            .zip(pointer.generics.types.iter())
            .map(|(parameter, argument)| match parameter {
                Some(Type::Parameter { .. }) => match self.ty(argument)? {
                    // A call from generic code at its own type parameter,
                    // `read::<T>(cell)`, calls the instance at that abstract
                    // type.
                    scalar if scalar.is_scalar() => Ok(Some(scalar)),
                    parameter @ Type::Parameter { .. } => Ok(Some(parameter)),
                    record @ Type::Record { .. } => Ok(Some(record)),
                    _ => Err(unsupported(
                        "type parameter instantiated at a type other than a scalar",
                    )),
                },
                other => Ok(other.clone()),
            })
            .collect::<Result<Vec<_>, _>>()
            .map(Some)
    }

    /// A generic callee's parameter and result types with its type
    /// parameters at `types`.
    fn signature_types_at(
        &self,
        callee: &a::FunDecl,
        types: &[Option<Type>],
    ) -> Result<(Vec<Type>, Type), String> {
        let current =
            std::mem::replace(&mut *self.callable_parameters.borrow_mut(), types.to_vec());
        let result = callee
            .signature
            .inputs
            .iter()
            .map(|ty| self.ty(ty))
            .collect::<Result<Vec<_>, _>>()
            .and_then(|inputs| Ok((inputs, self.ty(&callee.signature.output)?)));
        *self.callable_parameters.borrow_mut() = current;
        result
    }

    /// The name of generic function `id`'s instance at `types`, recorded so
    /// the import declares it: a trait implementation's method is named for
    /// the instance of its trait, `<Echo as Keep<i32>>::keep`; another
    /// function, by its path then each type argument.
    fn generic_instance(
        &self,
        id: a::FunDeclId,
        callee: &a::FunDecl,
        types: &[Option<Type>],
    ) -> Result<String, String> {
        // The instance at the callee's own type parameters, a call from
        // generic code whose parameters share their names, is the generic
        // function itself.
        if callee.generics.types.len() == types.len()
            && callee
                .generics
                .types
                .iter()
                .zip(types)
                .all(|(parameter, ty)| match ty {
                    Some(Type::Parameter { name }) => *name == parameter.name,
                    _ => ty.is_none(),
                })
            && let Some(name) = self.functions.get(&id)
        {
            return Ok(name.clone());
        }
        let name = match &callee.src {
            a::FunSource::TraitImpl {
                trait_ref,
                impl_ref,
                item_id,
                ..
            } if self.interface_trait(trait_ref.id)? => {
                let imp = self
                    .krate
                    .trait_impls
                    .get(impl_ref.id)
                    .ok_or_else(|| unsupported("missing trait implementation"))?;
                let current =
                    std::mem::replace(&mut *self.callable_parameters.borrow_mut(), types.to_vec());
                let names = self.trait_impl_method_names(callee, imp, trait_ref.id, *item_id);
                *self.callable_parameters.borrow_mut() = current;
                names?.0
            }
            // A generic struct's method is named at the instance's `impl`
            // type, `<impl Cell<i32>>::get`.
            _ if callee.item_meta.name.name.iter().any(|part| {
                matches!(part, a::PathElem::Impl(a::ImplElem::Ty(binder)) if !binder.params.is_empty())
            }) =>
            {
                if !self.functions.contains_key(&id) {
                    return Err(self.unmodeled_call(callee));
                }
                self.qualified_function_name_at(&callee.item_meta.name, Some(types))?
            }
            _ => {
                let mut name = self
                    .functions
                    .get(&id)
                    .ok_or_else(|| self.unmodeled_call(callee))?
                    .clone();
                for ty in types.iter().flatten() {
                    if let Some(spelling) = record_argument_spelling(ty) {
                        super::names::push_type_argument(&mut name, &spelling);
                    }
                }
                name
            }
        };
        self.generic_instances
            .borrow_mut()
            .insert(name.clone(), (id, types.to_vec()));
        Ok(name)
    }

    /// The library's `Box` function `method`, `Box::new` or `Box::drop`, at
    /// the crate struct `record`: its instance `Box::new<R>`, declared so the
    /// import calls it under the library's contract.
    pub(super) fn box_library_function(&self, method: &str, record: &str) -> String {
        let function = super::standard_library::box_function(method, record);
        let boxed = Type::Box {
            pointee: Box::new(Type::Record {
                name: record.to_string(),
            }),
        };
        let (parameters, return_type) = if method == super::standard_library::BOX_NEW {
            (
                vec![(
                    "x",
                    Type::Record {
                        name: record.to_string(),
                    },
                )],
                boxed,
            )
        } else {
            (vec![("b", boxed)], Type::Unit)
        };
        self.core_methods
            .borrow_mut()
            .entry(function.clone())
            .or_insert_with(|| out::Function {
                sites: Vec::new(),
                name: function.clone(),
                return_type,
                parameters: parameters
                    .into_iter()
                    .map(|(name, value_type)| out::Place {
                        name: name.into(),
                        value_type,
                        span: out::Span { line: 0, column: 0 },
                    })
                    .collect(),
                body: vec![],
                mir: None,
                external: true,
                captures: 0,
                implements: None,
                instance_of: None,
                core_method: Some(method.to_string()),
                span: out::Span { line: 0, column: 0 },
            });
        function
    }

    fn qualified_function_name(&self, name: &a::Name) -> Result<String, String> {
        self.qualified_function_name_at(name, None)
    }

    /// The importer name of the function at `name`, with the `impl` type of
    /// a generic struct's method at `arguments`, `<impl Cell<i32>>::get`, or
    /// at its own parameters when there are none, `<impl Cell<T>>::get`.
    fn qualified_function_name_at(
        &self,
        name: &a::Name,
        arguments: Option<&[Option<Type>]>,
    ) -> Result<String, String> {
        let Some(a::PathElem::Ident(root, d)) = name.name.first() else {
            return Err(unsupported("qualified function root"));
        };
        if root != &self.krate.crate_name || !d.is_zero() {
            return Err(unsupported("qualified function crate identity"));
        }
        let mut encoded = super::names::qualified_name([]);
        for part in &name.name {
            match part {
                a::PathElem::Ident(n, d) if d.is_zero() => {
                    super::names::push_path_segment(&mut encoded, n)
                }
                a::PathElem::Impl(a::ImplElem::Ty(binder)) if binder.params.is_empty() => {
                    let id = self.record_id(&binder.skip_binder)?;
                    super::names::push_impl_type(&mut encoded, &self.records[&id]);
                }
                // A generic struct's own `impl<T> Cell<T>`: the type is the
                // instance at the block's parameters, or at `arguments`.
                a::PathElem::Impl(a::ImplElem::Ty(binder))
                    if binder.params.const_generics.is_empty()
                        && let a::TyKind::Adt(r) = binder.skip_binder.kind()
                        && let Some(base) = self.generic_records.get(&r.id) =>
                {
                    let mut record = base.clone();
                    for argument in r.generics.types.iter() {
                        let a::TyKind::TypeVar(a::DeBruijnVar::Bound(_, var)) = argument.kind()
                        else {
                            return Err(unsupported("generic struct `impl` at other types"));
                        };
                        let spelling = match arguments {
                            None => binder
                                .params
                                .types
                                .get(*var)
                                .map(|parameter| parameter.name.clone()),
                            Some(arguments) => arguments
                                .get(var.index())
                                .cloned()
                                .flatten()
                                .as_ref()
                                .and_then(record_argument_spelling),
                        }
                        .ok_or_else(|| unsupported("generic struct `impl` at other types"))?;
                        super::names::push_type_argument(&mut record, &spelling);
                    }
                    super::names::push_impl_type(&mut encoded, &record);
                }
                a::PathElem::Builtin(a::BuiltinPathElem::Closure, d) => {
                    super::names::push_path_segment(
                        &mut encoded,
                        &super::names::closure_segment(d.index() as u32),
                    )
                }
                _ => return Err(unsupported("qualified function path component")),
            }
        }
        Ok(encoded)
    }
}
fn local_impl_method_path(name: &a::Name, krate: &str, id: a::TraitImplId, method: &str) -> bool {
    let n = name.name.len();
    n >= 3
        && matches!(&name.name[0], a::PathElem::Ident(root, d) if root == krate && d.is_zero())
        && name.name[..n - 2]
            .iter()
            .all(|p| matches!(p, a::PathElem::Ident(_,d) if d.is_zero()))
        && matches!(&name.name[n-2], a::PathElem::Impl(a::ImplElem::Trait(found)) if *found == id)
        && matches!(&name.name[n-1], a::PathElem::Ident(found,d) if found == method && d.is_zero())
}

/// A variant of an enum as the adapter reads it. A field of a library
/// enum's parameter has no type of its own (`None`); the instance's argument
/// is its type.
struct EnumVariant {
    id: a::VariantId,
    name: String,
    discriminant: a::IntegerValue,
    fields: Vec<Option<a::Ty>>,
}

/// How a generic struct's instance name spells type argument `ty`: a type
/// parameter by its name, a scalar by its Rust name.
fn record_argument_spelling(ty: &Type) -> Option<String> {
    Some(match ty {
        Type::Parameter { name } => name.clone(),
        scalar if scalar.is_scalar() => scalar.scalar_name()?.into(),
        // A crate struct, by the importer's name for it.
        Type::Record { name } => name.clone(),
        _ => return None,
    })
}

/// The size and alignment of a generic struct field of type `ty`. Rust
/// fixes no layout for a generic struct, and no safe code reads one, so
/// Click lays each instance out itself: a scalar at its own size, and a value
/// of an abstract type parameter at a word.
fn model_field_size(ty: &Type) -> Option<u32> {
    Some(match ty {
        Type::Bool => 1,
        integer if integer.is_integer() => integer.integer_bits()? / 8,
        Type::Parameter { .. } | Type::Box { .. } | Type::OptionBox { .. } => 8,
        _ => return None,
    })
}

fn concrete_size(size: &a::Size) -> Result<u32, String> {
    let Some(expr) = &size.chosen else {
        return Err(unsupported("symbolic layout"));
    };
    let a::SizeExprKind::Constant(c) = expr.kind() else {
        return Err(unsupported("symbolic layout"));
    };
    let a::ConstantExprKind::Integer(a::IntegerValue::Unsigned(_, value)) = c.kind() else {
        return Err(unsupported("symbolic layout"));
    };
    u32::try_from(*value).map_err(|_| unsupported("large layout"))
}

fn byte_slice(ty: &a::Ty) -> bool {
    matches!(ty.kind(), a::TyKind::Slice(element, _) if matches!(element.kind(), a::TyKind::Scalar(a::ScalarTy::Integer(a::IntegerTy::Unsigned(a::UIntTy::U8)))))
}

struct Adapter<'a> {
    crate_mode: bool,
    krate: &'a a::TranslatedCrate,
    records: BTreeMap<a::TypeDeclId, String>,
    /// The crate's enums, by the name their `spec enum` takes.
    enums: BTreeMap<a::TypeDeclId, String>,
    functions: BTreeMap<a::FunDeclId, String>,
    destructors: BTreeMap<a::TypeDeclId, a::FunDeclId>,
    /// The compiler's drop glue of each crate struct holding a box, imported
    /// as a function whose sidecar contract is `impl Destruct`'s
    /// `drop_glue`.
    drop_glues: BTreeMap<a::TypeDeclId, a::FunDeclId>,
    /// Each closure's `ClosureAsFn` function, by the closure's name.
    closure_shims: BTreeMap<a::FunDeclId, String>,
    /// The `Fn::call` methods of closures, imported as the closures, with
    /// each closure's state type.
    closure_calls: BTreeMap<a::FunDeclId, a::TypeDeclId>,
    /// The names of the crate's own `Iterator::next` functions.
    user_iterator_nexts: BTreeSet<String>,
    /// The variables each closure captures, by its state type.
    closure_captures: BTreeMap<a::TypeDeclId, Vec<closures::Capture>>,
    /// The callable type of each type parameter of the function being
    /// adapted, `F: Fn(i32) -> i32`, by its index; `None` for one that is not.
    callable_parameters: std::cell::RefCell<Vec<Option<Type>>>,
    /// The crate trait method implementations, by the interface function
    /// each implements.
    trait_impl_methods: BTreeMap<a::FunDeclId, String>,
    /// Each crate struct a call passes as a crate trait's object, with the
    /// trait: the struct's pack and unpack functions are imported.
    object_coercions: std::cell::RefCell<BTreeSet<(String, a::TraitDeclId, String)>>,
    /// Each generic crate trait's instances an implementation or a call
    /// names, by importer name, with their type arguments after `Self`.
    trait_instances: std::cell::RefCell<BTreeMap<a::TraitDeclId, BTreeMap<String, Vec<a::Ty>>>>,
    /// Each instance of a generic function a call names, by its name: the
    /// generic function and the type each of its type parameters takes.
    generic_instances: std::cell::RefCell<BTreeMap<String, (a::FunDeclId, Vec<Option<Type>>)>>,
    /// Each crate trait instance's type arguments after `Self`, as they were
    /// when it was named.
    instance_types: std::cell::RefCell<BTreeMap<String, Vec<Type>>>,
    /// The crate's generic structs, `struct Cell<T>`, by their names.
    generic_records: BTreeMap<a::TypeDeclId, String>,
    /// Each instance of a generic struct a type names, `Cell<T>` or
    /// `Cell<i32>`, by its name: the struct and its type arguments.
    record_instances: std::cell::RefCell<BTreeMap<String, (a::TypeDeclId, Vec<Type>)>>,
    /// Each instance of a generic library enum the functions named, by the
    /// name of its type: `Option<u32>`, with the arguments it is at.
    enum_instances: std::cell::RefCell<BTreeMap<String, (String, Vec<Type>)>>,
    /// The external function of each Rust core method a call names, by its
    /// name: `u32::min`, declared once per method and type.
    core_methods: std::cell::RefCell<BTreeMap<String, out::Function>>,
}
impl Adapter<'_> {
    fn ty(&self, t: &a::Ty) -> Result<Type, String> {
        Ok(match t.kind() {
            a::TyKind::Scalar(a::ScalarTy::Bool) => Type::Bool,
            a::TyKind::Scalar(a::ScalarTy::Integer(a::IntegerTy::Signed(kind))) => match kind {
                a::IntTy::I8 => Type::I8,
                a::IntTy::I16 => Type::I16,
                a::IntTy::I32 => Type::I32,
                a::IntTy::I64 => Type::I64,
                a::IntTy::Isize => Type::Isize,
                _ => {
                    return Err(unsupported(&format!(
                        "integer width `{}`",
                        self.describe_type(t)
                    )));
                }
            },
            a::TyKind::Scalar(a::ScalarTy::Integer(a::IntegerTy::Unsigned(kind))) => match kind {
                a::UIntTy::U8 => Type::U8,
                a::UIntTy::U16 => Type::U16,
                a::UIntTy::U32 => Type::U32,
                a::UIntTy::U64 => Type::U64,
                a::UIntTy::Usize => Type::Usize,
                _ => {
                    return Err(unsupported(&format!(
                        "integer width `{}`",
                        self.describe_type(t)
                    )));
                }
            },
            a::TyKind::Ref(_, pointee, kind) if byte_slice(pointee) => Type::ByteSlice {
                mutable: *kind == a::RefKind::Mut,
            },
            a::TyKind::Ref(_, pointee, kind) if matches!(pointee.kind(), a::TyKind::Slice(..)) => {
                let a::TyKind::Slice(element, _) = pointee.kind() else {
                    unreachable!()
                };
                let element = self.ty(element)?;
                if !element.is_integer() {
                    return Err(unsupported("slice elements other than integers"));
                }
                Type::ScalarSlice {
                    element: Box::new(element),
                    mutable: *kind == a::RefKind::Mut,
                }
            }
            // An `F: Fn(A) -> R` parameter is a callable value, and so is a
            // shared reference to one, which a call through it borrows.
            a::TyKind::TypeVar(a::DeBruijnVar::Bound(depth, id)) if depth.index == 0 => self
                .callable_parameters
                .borrow()
                .get(id.index())
                .cloned()
                .flatten()
                .ok_or_else(|| unsupported("type parameter other than an Fn or a crate trait"))?,
            // A reference to a type parameter bound by a crate trait is a
            // reference to a value of unknown type.
            a::TyKind::Ref(_, pointee, kind)
                if matches!(pointee.kind(), a::TyKind::TypeVar(_))
                    && self.ty(pointee)? == Type::TraitObject =>
            {
                Type::Reference {
                    mutable: *kind == a::RefKind::Mut,
                    pointee: Box::new(Type::TraitObject),
                }
            }
            a::TyKind::Ref(_, pointee, a::RefKind::Shared)
                if matches!(pointee.kind(), a::TyKind::TypeVar(_)) =>
            {
                match self.ty(pointee)? {
                    // `&T` of an abstract type parameter, or of the scalar a
                    // generic callee's instance takes for it: a reference to
                    // one value.
                    value
                        if value.is_scalar()
                            || matches!(value, Type::Parameter { .. } | Type::Record { .. }) =>
                    {
                        Type::Reference {
                            mutable: false,
                            pointee: Box::new(value),
                        }
                    }
                    callable => callable,
                }
            }
            // So is a `&dyn Trait` of a crate trait.
            a::TyKind::Ref(_, pointee, kind)
                if matches!(pointee.kind(), a::TyKind::DynTrait(predicate)
                    if self.dyn_interface_trait(predicate)?.is_some()) =>
            {
                Type::Reference {
                    mutable: *kind == a::RefKind::Mut,
                    pointee: Box::new(Type::TraitObject),
                }
            }
            // A closure's state is the closure as a callable value.
            a::TyKind::Adt(r) if self.closure_state(r.id) => self.closure_state_type(r.id)?,
            // So is a function item's type, which an `impl Fn` argument has.
            a::TyKind::FnDef(binder) => self.function_item_type(&binder.skip_binder)?,
            // A `&dyn Fn(A) -> R` is a callable value, as a `fn` pointer is.
            a::TyKind::Ref(_, pointee, a::RefKind::Shared)
                if matches!(pointee.kind(), a::TyKind::DynTrait(_)) =>
            {
                let a::TyKind::DynTrait(predicate) = pointee.kind() else {
                    unreachable!()
                };
                let (parameters, result) = self.dyn_fn_signature(predicate)?;
                let scalar = |ty: &Type| ty.is_scalar();
                if !parameters.iter().all(scalar) || !(scalar(&result) || result == Type::Unit) {
                    return Err(unsupported("dyn Fn of non-scalar parameters or result"));
                }
                Type::FnPointer {
                    parameters,
                    result: Box::new(result),
                }
            }
            a::TyKind::Ref(_, pointee, kind) => Type::Reference {
                mutable: *kind == a::RefKind::Mut,
                pointee: Box::new(self.ty(pointee)?),
            },
            a::TyKind::Array(element, length, _) => Type::Array {
                element: Box::new(self.ty(element)?),
                length: length
                    .as_usize_literal()
                    .ok_or_else(|| unsupported("symbolic array length"))?
                    as u64,
            },
            a::TyKind::Adt(_) if self.enumerate_element(t).is_some() => Type::EnumerateIterator {
                element: Box::new(self.ty(self.enumerate_element(t).unwrap())?),
            },
            a::TyKind::Adt(_) if self.enumerate_option_element(t).is_some() => {
                Type::EnumerateOption {
                    element: Box::new(self.ty(self.enumerate_option_element(t).unwrap())?),
                }
            }
            a::TyKind::Adt(_) if self.shared_iterator_element(t, false).is_some() => {
                Type::SharedArrayIterator {
                    element: Box::new(self.ty(self.shared_iterator_element(t, false).unwrap())?),
                }
            }
            a::TyKind::Adt(_) if self.shared_option_element(t, false).is_some() => {
                Type::SharedArrayOption {
                    element: Box::new(self.ty(self.shared_option_element(t, false).unwrap())?),
                }
            }
            a::TyKind::Adt(_) if self.range_element(t, false).is_some() => Type::Range {
                element: Box::new(self.ty(self.range_element(t, false).unwrap())?),
                inclusive: self.inclusive_range(t),
            },
            a::TyKind::Adt(_) if self.chunk_type(t) => Type::ChunkIterator,
            a::TyKind::Adt(_) if self.chunk_option_type(t) => Type::ChunkOption,
            a::TyKind::Adt(r) if r.id == a::TypeDeclId::UNIT => Type::Unit,
            // A closure that captures nothing has no state to carry.
            a::TyKind::Adt(r) if self.empty_closure_state(r.id) => Type::Unit,
            a::TyKind::FnPtr(binder) => {
                let signature = &binder.skip_binder;
                if signature.is_unsafe || signature.abi != a::Abi::Rust || signature.is_variadic {
                    return Err(unsupported("unsafe or foreign function pointer"));
                }
                let scalar = |t: &Type| t.is_scalar();
                let parameters = signature
                    .inputs
                    .iter()
                    .map(|input| self.ty(input))
                    .collect::<Result<Vec<_>, _>>()?;
                let result = self.ty(&signature.output)?;
                if !parameters.iter().all(scalar) || !(scalar(&result) || result == Type::Unit) {
                    return Err(unsupported(
                        "function pointer of non-scalar parameters or result",
                    ));
                }
                Type::FnPointer {
                    parameters,
                    result: Box::new(result),
                }
            }
            // A `Box` of a crate struct is the address of its allocation, and
            // so is the `*const R` the compiler reads a box through.
            a::TyKind::Adt(r)
                if r.builtin == Some(a::BuiltinAdt::Box)
                    && let Some(pointee) = r.generics.types.first()
                    && self.boxable(pointee) =>
            {
                Type::Box {
                    pointee: Box::new(self.ty(pointee)?),
                }
            }
            // `Option<Box<R>>` is the box's address, or null for `None`.
            a::TyKind::Adt(_) if let Some(payload) = self.option_box_payload(t) => {
                let Type::Box { pointee } = self.ty(payload)? else {
                    unreachable!("an option's box payload is a box")
                };
                Type::OptionBox { pointee }
            }
            a::TyKind::RawPtr(pointee, _) if self.boxable(pointee) => Type::Box {
                pointee: Box::new(self.ty(pointee)?),
            },
            // An `Option<T>` of a scalar is the value of the library's
            // `spec enum Option<T>` at that scalar.
            a::TyKind::Adt(_) if let Some(payload) = self.option_payload(t) => {
                self.option_enum(self.ty(payload)?)?
            }
            // A `Result<T, E>` of scalars is the value of the library's
            // `spec enum Result<T, E>` at them.
            a::TyKind::Adt(_) if let Some((ok, err)) = self.result_payloads(t) => {
                self.result_enum(self.ty(ok)?, self.ty(err)?)?
            }
            // A `Vec<T>` of a scalar is the value of the library's primitive
            // type `Vec<T>` at that scalar.
            a::TyKind::Adt(_) if let Some(element) = self.vec_element(t) => {
                let element = self.ty(element)?;
                if !element.is_scalar() {
                    return Err(unsupported(&format!(
                        "type `{}`: a `Vec` holds integers or `bool` only",
                        self.describe_type(t)
                    )));
                }
                Type::Vec {
                    element: Box::new(element),
                }
            }
            // An instance of a generic struct is a record of its own, named
            // with its type arguments: `Cell<T>` in generic code, `Cell<i32>`
            // in a caller.
            a::TyKind::Adt(r)
                if r.generics.const_generics.is_empty()
                    && let Some(base) = self.generic_records.get(&r.id) =>
            {
                let id = r.id;
                let arguments = r
                    .generics
                    .types
                    .iter()
                    .map(|argument| self.ty(argument))
                    .collect::<Result<Vec<_>, _>>()?;
                let mut name = base.clone();
                for argument in &arguments {
                    super::names::push_type_argument(
                        &mut name,
                        &record_argument_spelling(argument).ok_or_else(|| {
                            unsupported(
                                "generic struct at a type other than a type parameter, \
                                 i32, u8, u16, u32, usize or bool",
                            )
                        })?,
                    );
                }
                self.record_instances
                    .borrow_mut()
                    .insert(name.clone(), (id, arguments));
                Type::Record { name }
            }
            a::TyKind::Adt(r) if self.enums.contains_key(&r.id) => Type::Enum {
                name: self.enums[&r.id].clone(),
            },
            a::TyKind::Adt(r)
                if r.generics.types.is_empty() && r.generics.const_generics.is_empty() =>
            {
                Type::Record {
                    name: self
                        .records
                        .get(&r.id)
                        .ok_or_else(|| unsupported("external aggregate"))?
                        .clone(),
                }
            }
            _ => {
                return Err(unsupported(&format!(
                    "type `{}` (raw pointers and general generics remain later work)",
                    self.describe_type(t)
                )));
            }
        })
    }
    /// The refusal of a call to `callee`, a function outside the crate the
    /// importer has no model of: `u32::min`, `core::panicking::panic`.
    fn unmodeled_call(&self, callee: &a::FunDecl) -> String {
        let path = callee
            .item_meta
            .name
            .name
            .iter()
            .map(|part| match part {
                a::PathElem::Ident(name, _) => name.clone(),
                a::PathElem::Impl(a::ImplElem::Ty(binder)) => {
                    self.describe_type(&binder.skip_binder)
                }
                // A trait method reads as its implementing type's.
                a::PathElem::Impl(a::ImplElem::Trait(id)) => self
                    .krate
                    .trait_impls
                    .get(*id)
                    .and_then(|imp| imp.impl_trait.generics.types.iter().next())
                    .map_or_else(|| "_".into(), |ty| self.describe_type(ty)),
                _ => "_".into(),
            })
            .collect::<Vec<_>>();
        // An inherent method reads as its type's: `u32::min`, not
        // `core::num::<impl u32>::min`.
        let start = callee
            .item_meta
            .name
            .name
            .iter()
            .rposition(|part| matches!(part, a::PathElem::Impl(_)))
            .unwrap_or(0);
        unsupported(&format!(
            "unmodeled external call to `{}`",
            path[start..].join("::")
        ))
    }
    /// `t` as Rust writes it, for a refusal: `RangeInclusive<u32>`,
    /// `(usize, &u8)`, `*const u8`.
    fn describe_type(&self, t: &a::Ty) -> String {
        let list = |types: &[a::Ty]| {
            types
                .iter()
                .map(|t| self.describe_type(t))
                .collect::<Vec<_>>()
                .join(", ")
        };
        match t.kind() {
            a::TyKind::Scalar(a::ScalarTy::Bool) => "bool".into(),
            a::TyKind::Scalar(a::ScalarTy::Integer(a::IntegerTy::Signed(kind))) => {
                format!("{kind:?}").to_lowercase()
            }
            a::TyKind::Scalar(a::ScalarTy::Integer(a::IntegerTy::Unsigned(kind))) => {
                format!("{kind:?}").to_lowercase()
            }
            a::TyKind::Ref(_, pointee, kind) => format!(
                "&{}{}",
                if *kind == a::RefKind::Mut { "mut " } else { "" },
                self.describe_type(pointee)
            ),
            a::TyKind::RawPtr(pointee, kind) => format!(
                "*{} {}",
                if *kind == a::RefKind::Mut {
                    "mut"
                } else {
                    "const"
                },
                self.describe_type(pointee)
            ),
            a::TyKind::Slice(element, _) => format!("[{}]", self.describe_type(element)),
            a::TyKind::Array(element, length, _) => match length.as_usize_literal() {
                Some(length) => format!("[{}; {length}]", self.describe_type(element)),
                None => format!("[{}; _]", self.describe_type(element)),
            },
            a::TyKind::Adt(r) if r.builtin == Some(a::BuiltinAdt::Tuple) => {
                format!("({})", list(r.generics.types.as_raw_slice()))
            }
            a::TyKind::Adt(r) => {
                let name = self
                    .krate
                    .type_decls
                    .get(r.id)
                    .and_then(|decl| match decl.item_meta.name.name.last() {
                        Some(a::PathElem::Ident(name, _)) => Some(name.clone()),
                        _ => None,
                    })
                    .unwrap_or_else(|| "an unnamed type".into());
                if r.generics.types.is_empty() {
                    name
                } else {
                    format!("{name}<{}>", list(r.generics.types.as_raw_slice()))
                }
            }
            a::TyKind::Scalar(a::ScalarTy::Char) => "char".into(),
            a::TyKind::Scalar(a::ScalarTy::Float(kind)) => format!("{kind:?}").to_lowercase(),
            a::TyKind::Never => "!".into(),
            a::TyKind::FnDef(_) => "of a function item".into(),
            a::TyKind::FnPtr(_) => "of a function pointer".into(),
            a::TyKind::DynTrait(_) => "of a `dyn` trait object".into(),
            a::TyKind::TypeVar(_) => "T".into(),
            _ => "of this kind".into(),
        }
    }
    fn resolve(&self, p: &a::FnPtr) -> Result<a::FunDeclId, String> {
        match p.kind.as_ref() {
            a::FnPtrKind::Fun(id) => Ok(*id),
            a::FnPtrKind::Trait(tr, method) => {
                let a::TraitRefKind::TraitImpl(r) = &tr.kind else {
                    return Err(unsupported("unresolved trait call"));
                };
                self.krate
                    .trait_impls
                    .get(r.id)
                    .and_then(|i| i.methods.get(*method))
                    .map(|m| m.skip_binder.id)
                    .ok_or_else(|| unsupported("missing trait method"))
            }
        }
    }
    /// The payload type of a `core::option::Option<T>` that is neither an
    /// option of a box nor one of the iterator protocols' options.
    fn option_payload<'t>(&self, ty: &'t a::Ty) -> Option<&'t a::Ty> {
        let a::TyKind::Adt(r) = ty.kind() else {
            return None;
        };
        let decl = self.krate.type_decls.get(r.id)?;
        let [payload] = r.generics.types.as_raw_slice() else {
            return None;
        };
        (!decl.item_meta.is_local
            && decl.item_meta.lang_item == Some(LangItem::Option)
            && self.option_box_payload(ty).is_none()
            && !self.protocol_option(ty))
        .then_some(payload)
    }
    /// The element type of an `alloc::vec::Vec<T, Global>`.
    fn vec_element<'t>(&self, ty: &'t a::Ty) -> Option<&'t a::Ty> {
        let a::TyKind::Adt(r) = ty.kind() else {
            return None;
        };
        let decl = self.krate.type_decls.get(r.id)?;
        let [element, _allocator] = r.generics.types.as_raw_slice() else {
            return None;
        };
        (!decl.item_meta.is_local && protocol::path(&decl.item_meta.name, &["alloc", "vec", "Vec"]))
            .then_some(element)
    }
    /// The `Ok` and `Err` payload types of a `core::result::Result<T, E>`.
    fn result_payloads<'t>(&self, ty: &'t a::Ty) -> Option<(&'t a::Ty, &'t a::Ty)> {
        let a::TyKind::Adt(r) = ty.kind() else {
            return None;
        };
        let decl = self.krate.type_decls.get(r.id)?;
        let [ok, err] = r.generics.types.as_raw_slice() else {
            return None;
        };
        (!decl.item_meta.is_local
            && protocol::path(&decl.item_meta.name, &["core", "result", "Result"]))
        .then_some((ok, err))
    }
    /// Whether `ty` is an instance of a library enum: an `Option` or a
    /// `Result` the importer reads as the library's `spec enum`.
    fn library_enum(&self, ty: &a::Ty) -> bool {
        self.option_payload(ty).is_some() || self.result_payloads(ty).is_some()
    }
    /// The locals of `body` that hold a crate enum's discriminant, with the
    /// enum each reads.
    fn enum_discriminants(&self, body: &u::ExprBody) -> BTreeMap<a::LocalId, a::Place> {
        let mut discriminants = BTreeMap::new();
        for block in &body.body {
            for statement in &block.statements {
                if let u::StatementKind::Assign(target, a::Rvalue::Discriminant(place)) =
                    &statement.kind
                    && let a::PlaceKind::Local(local) = target.kind
                    && (matches!(place.ty.kind(), a::TyKind::Adt(r) if self.enums.contains_key(&r.id))
                        || self.library_enum(&place.ty))
                {
                    discriminants.insert(local, place.clone());
                }
            }
        }
        discriminants
    }
    /// The name of enum `ty`'s type, a crate enum or an `Option` or `Result`
    /// instance, and its variants. The compiler leaves the library enums'
    /// declarations opaque; `Option`'s variants are `None` and `Some(T)`,
    /// tagged 0 and 1, and `Result`'s `Ok(T)` and `Err(E)`, tagged 0 and 1.
    fn enum_variants(&self, ty: &a::Ty) -> Result<(String, Vec<EnumVariant>), String> {
        let a::TyKind::Adt(r) = ty.kind() else {
            return Err(unsupported("enum type"));
        };
        if self.option_payload(ty).is_some() {
            let Type::Enum { name } = self.ty(ty)? else {
                unreachable!("an option of a scalar is an enum")
            };
            let variant = |index: usize, name: &str, fields| EnumVariant {
                id: a::VariantId::from_usize(index),
                name: name.into(),
                discriminant: a::IntegerValue::Signed(a::IntTy::Isize, index as i128),
                fields,
            };
            return Ok((
                name,
                vec![variant(0, "None", vec![]), variant(1, "Some", vec![None])],
            ));
        }
        if self.result_payloads(ty).is_some() {
            let Type::Enum { name } = self.ty(ty)? else {
                unreachable!("a result of scalars is an enum")
            };
            let variant = |index: usize, name: &str| EnumVariant {
                id: a::VariantId::from_usize(index),
                name: name.into(),
                discriminant: a::IntegerValue::Signed(a::IntTy::Isize, index as i128),
                fields: vec![None],
            };
            return Ok((name, vec![variant(0, "Ok"), variant(1, "Err")]));
        }
        let name = self
            .enums
            .get(&r.id)
            .ok_or_else(|| unsupported("nonlocal enum"))?;
        let a::TypeDeclKind::Enum(variants) = &self.krate.type_decls[r.id].kind else {
            return Err(unsupported("enum declaration"));
        };
        Ok((
            name.clone(),
            variants
                .iter()
                .map(|variant| EnumVariant {
                    id: variant.id,
                    name: variant.name.clone(),
                    discriminant: variant.discriminant,
                    fields: variant
                        .fields
                        .iter()
                        .map(|field| Some(field.ty.clone()))
                        .collect(),
                })
                .collect(),
        ))
    }
    /// The `Box<R>` an `Option<Box<R>>` of a crate struct `R` holds.
    fn option_box_payload<'t>(&self, ty: &'t a::Ty) -> Option<&'t a::Ty> {
        let a::TyKind::Adt(r) = ty.kind() else {
            return None;
        };
        let decl = self.krate.type_decls.get(r.id)?;
        let [payload] = r.generics.types.as_raw_slice() else {
            return None;
        };
        (!decl.item_meta.is_local
            && decl.item_meta.lang_item == Some(LangItem::Option)
            && matches!(payload.kind(), a::TyKind::Adt(b)
                if b.builtin == Some(a::BuiltinAdt::Box)
                    && b.generics.types.first().is_some_and(|p| self.boxable(p))))
        .then_some(payload)
    }
    /// How a library enum instance's name spells payload `ty`: as a generic
    /// struct's argument is, or a crate enum by its name, so
    /// `Result<u32, ParseError>` holds a crate error enum.
    fn library_argument_spelling(&self, ty: &Type) -> Option<String> {
        record_argument_spelling(ty).or_else(|| match ty {
            Type::Enum { name } if self.enums.values().any(|declared| declared == name) => {
                Some(name.clone())
            }
            _ => None,
        })
    }
    /// The library's `spec enum Option<T>` at `payload`, recorded so the
    /// import declares the instance.
    fn option_enum(&self, payload: Type) -> Result<Type, String> {
        let name = super::names::option_type_name(
            &self.library_argument_spelling(&payload).ok_or_else(|| {
                unsupported(
                    "Option of a type other than a type parameter, a crate enum, \
                     i32, u8, u16, u32, usize or bool",
                )
            })?,
        );
        self.enum_instances
            .borrow_mut()
            .insert(name.clone(), ("Option".into(), vec![payload]));
        Ok(Type::Enum { name })
    }
    /// The library's `spec enum Result<T, E>` at `ok` and `err`, recorded so
    /// the import declares the instance.
    fn result_enum(&self, ok: Type, err: Type) -> Result<Type, String> {
        let spell = |payload: &Type| {
            self.library_argument_spelling(payload).ok_or_else(|| {
                unsupported(
                    "Result of a type other than a type parameter, a crate enum, \
                     i32, u8, u16, u32, usize or bool",
                )
            })
        };
        let name = super::names::result_type_name(&spell(&ok)?, &spell(&err)?);
        self.enum_instances
            .borrow_mut()
            .insert(name.clone(), ("Result".into(), vec![ok, err]));
        Ok(Type::Enum { name })
    }
    /// Whether a box may hold `ty`: a crate struct, or an instance of a
    /// generic one.
    fn boxable(&self, ty: &a::Ty) -> bool {
        matches!(ty.kind(), a::TyKind::Adt(p)
            if self.records.contains_key(&p.id) || self.generic_records.contains_key(&p.id))
    }
    /// The crate struct a `Box<R>` or an `Option<Box<R>>` holds.
    fn boxed_record<'t>(&self, ty: &'t a::Ty) -> Option<&'t a::Ty> {
        let a::TyKind::Adt(boxed) = self.option_box_payload(ty).unwrap_or(ty).kind() else {
            return None;
        };
        (boxed.builtin == Some(a::BuiltinAdt::Box))
            .then(|| boxed.generics.types.first())
            .flatten()
    }
    /// Whether crate struct `id`, generic or not, holds a box or an option
    /// of one.
    fn record_holds_box(&self, id: a::TypeDeclId) -> Result<bool, String> {
        Ok(self.fields(id)?.iter().any(|field| {
            self.option_box_payload(&field.ty).is_some()
                || matches!(field.ty.kind(), a::TyKind::Adt(b)
                    if b.builtin == Some(a::BuiltinAdt::Box)
                        && b.generics.types.first().is_some_and(|p| self.boxable(p)))
        }))
    }
    /// The drop glue of the struct `ty`, a crate struct holding a box or an
    /// instance of a generic one, if it has one: its name, `R_drop_glue` at
    /// the struct's own name. An instance of a generic struct's glue at other
    /// types than its own parameters is recorded so the import declares it,
    /// with the generic glue's contract at those types.
    fn drop_glue_of(&self, ty: &a::Ty) -> Result<Option<String>, String> {
        let a::TyKind::Adt(r) = ty.kind() else {
            return Ok(None);
        };
        let Some(&glue) = self.drop_glues.get(&r.id) else {
            return Ok(None);
        };
        let Type::Record { name } = self.ty(ty)? else {
            return Err(unsupported("drop glue of a non-record"));
        };
        let name = format!("{name}_drop_glue");
        if self.functions.get(&glue) != Some(&name) {
            let types = r
                .generics
                .types
                .iter()
                .map(|argument| self.ty(argument).map(Some))
                .collect::<Result<Vec<_>, _>>()?;
            self.generic_instances
                .borrow_mut()
                .insert(name.clone(), (glue, types));
        }
        Ok(Some(name))
    }
    /// Whether dropping a value of the crate struct `ty` runs code: its own
    /// `Drop`, or a field's drop, a box's or a struct's that runs code.
    fn record_has_drop_glue(&self, ty: &a::Ty) -> Result<bool, String> {
        let id = self.struct_id(ty)?;
        if self.destructors.contains_key(&id) || self.drop_glues.contains_key(&id) {
            return Ok(true);
        }
        for field in self.fields(id)? {
            if matches!(
                self.ty(&field.ty)?,
                Type::Box { .. } | Type::OptionBox { .. }
            ) || (matches!(self.ty(&field.ty)?, Type::Record { .. })
                && self.record_has_drop_glue(&field.ty)?)
            {
                return Ok(true);
            }
        }
        Ok(false)
    }
    fn record_id(&self, ty: &a::Ty) -> Result<a::TypeDeclId, String> {
        match ty.kind() {
            a::TyKind::Adt(r) if self.records.contains_key(&r.id) => Ok(r.id),
            _ => Err(unsupported("nonlocal record")),
        }
    }
    /// The importer name of the crate struct `ty` is, `Wrap<u32>` for an
    /// instance of a generic struct, when it is one.
    fn object_record(&self, ty: &a::Ty) -> Option<String> {
        self.struct_id(ty).ok()?;
        match self.ty(ty) {
            Ok(Type::Record { name }) => Some(name),
            _ => None,
        }
    }
    /// The struct of `ty`, an instance of a generic struct included.
    fn struct_id(&self, ty: &a::Ty) -> Result<a::TypeDeclId, String> {
        match ty.kind() {
            a::TyKind::Adt(r)
                if self.records.contains_key(&r.id) || self.generic_records.contains_key(&r.id) =>
            {
                Ok(r.id)
            }
            _ => Err(unsupported("nonlocal record")),
        }
    }
    fn fields(
        &self,
        id: a::TypeDeclId,
    ) -> Result<&charon_lib::ids::IndexVec<a::FieldId, a::Field>, String> {
        match &self
            .krate
            .type_decls
            .get(id)
            .ok_or_else(|| unsupported("missing record"))?
            .kind
        {
            a::TypeDeclKind::Struct(fields) => Ok(fields),
            _ => Err(unsupported("non-struct aggregate")),
        }
    }
}

struct BodyAdapter<'a, 'b> {
    adapter: &'a Adapter<'b>,
    body: &'a u::ExprBody,
    plumbing: closures::ClosurePlumbing,
    names: BTreeMap<a::LocalId, MirLocalId>,
    /// The locals whose source name is bound more than once: each one's
    /// storage starts where rustc's does, so its declaration does too.
    spelled: BTreeSet<a::LocalId>,
    slice_pairs: BTreeMap<a::LocalId, [MirLocalId; 2]>,
    iterator_refs: BTreeMap<a::LocalId, a::LocalId>,
    iterator_discriminants: BTreeMap<a::LocalId, a::LocalId>,
    /// The locals that hold a crate enum's discriminant, `_2 = @discriminant(s)`,
    /// with the enum they read: a `match` switches on the enum itself.
    enum_discriminants: BTreeMap<a::LocalId, a::Place>,
    /// The locals a crate struct reference is unsized into a `&dyn` crate
    /// trait for.
    unsized_objects: BTreeMap<a::LocalId, (String, (a::TraitDeclId, String), bool)>,
    /// The pack, unpack, and argument of each object the block's call makes
    /// from a crate struct reference.
    coercions: std::cell::RefCell<Vec<(String, String, E)>>,
}
impl BodyAdapter<'_, '_> {
    /// Named interpretations for compiler-resolved slice length and unsigned From.
    fn modeled_call(&self, t: &u::Terminator) -> Result<Option<S>, String> {
        // A call through a `&dyn Fn` is no modeled library call.
        if let u::TerminatorKind::Call { call, .. } = &t.kind
            && let a::FnOperand::Regular(pointer) = &call.func
            && self.adapter.is_dyn_fn_call(pointer)
        {
            return Ok(None);
        }
        // Nor is a call through a crate trait.
        if let u::TerminatorKind::Call { call, .. } = &t.kind {
            match &call.func {
                a::FnOperand::Regular(pointer)
                    if self.adapter.interface_call(pointer)?.is_some() =>
                {
                    return Ok(None);
                }
                a::FnOperand::Dynamic(pointer) if self.adapter.vtable_call(pointer)?.is_some() => {
                    return Ok(None);
                }
                _ => {}
            }
        }
        if let Some(protocol::BorrowedProtocolCall::Next {
            source,
            option,
            shared,
        }) = self.adapter.borrowed_protocol_call(t)?
        {
            let source = self.body.locals.locals[source].index;
            let root = self.iterator_refs.get(&source).copied().unwrap_or(source);
            let iterator = self.local(root)?;
            let option = self.local(option)?;
            return Ok(Some(if shared {
                S::SharedArrayNext {
                    iterator,
                    option: Some(option),
                    payload: None,
                    taken: None,
                }
            } else {
                S::ChunkNext {
                    iterator,
                    option: Some(option),
                    payload: None,
                    taken: None,
                }
            }));
        }
        if let Some(statement) = self.split_slice_call(t)? {
            return Ok(Some(statement));
        }
        if let Some(statement) = self.enumerate_call(t)? {
            return Ok(Some(statement));
        }
        if let Some(statement) = self.range_call(t)? {
            return Ok(Some(statement));
        }
        if let Some(statement) = self.shared_array_call(t)? {
            return Ok(Some(statement));
        }
        if let Some(statement) = self.chunk_call(t)? {
            return Ok(Some(statement));
        }
        if let Some(statement) = self.user_iterator_into_iter(t)? {
            return Ok(Some(statement));
        }
        let u::TerminatorKind::Call { call, .. } = &t.kind else {
            return Ok(None);
        };
        let a::FnOperand::Regular(ptr) = &call.func else {
            return Ok(None);
        };
        let id = self.adapter.resolve(ptr)?;
        let callee = self
            .adapter
            .krate
            .fun_decls
            .get(id)
            .ok_or_else(|| unsupported("missing call definition"))?;
        if callee.item_meta.lang_item == Some(LangItem::SliceLen) {
            let [argument] = call.args.as_slice() else {
                return Err(unsupported("slice len arity"));
            };
            let signature = matches!(callee.signature.inputs.as_slice(), [input]
                if matches!(input.kind(), a::TyKind::Ref(_, pointee, a::RefKind::Shared)
                    if matches!(pointee.kind(), a::TyKind::Slice(element, _)
                        if matches!(element.kind(), a::TyKind::TypeVar(a::DeBruijnVar::Bound(depth, id)) if depth.index == 0 && id.index() == 0))));
            if callee.item_meta.is_local
                || !matches!(callee.src, a::FunSource::Normal)
                || callee.signature.is_unsafe
                || callee.signature.is_variadic
                || callee.signature.abi != a::Abi::Rust
                || call.safety == a::CallSafety::Unsafe
                || callee.generics.types.len() != 1
                || !callee.generics.const_generics.is_empty()
                || !signature
                || self.adapter.ty(&callee.signature.output)? != Type::Usize
                || ptr.generics.types.len() != 1
                || !ptr.generics.const_generics.is_empty()
                || !match (
                    self.adapter.ty(&ptr.generics.types[0])?,
                    self.adapter.ty(argument.ty())?,
                ) {
                    (Type::U8, Type::ByteSlice { mutable: false }) => true,
                    (
                        element,
                        Type::ScalarSlice {
                            element: actual, ..
                        },
                    ) => element == *actual,
                    _ => false,
                }
                || self.adapter.ty(&call.dest.ty)? != Type::Usize
            {
                return Err(unsupported("slice len declaration/type mismatch"));
            }
            return Ok(Some(S::Assign {
                target: self.place(&call.dest)?,
                value: E::SliceLength {
                    slice: Box::new(self.operand(argument)?),
                },
            }));
        }
        let a::FunSource::TraitImpl {
            trait_ref,
            impl_ref,
            item_id,
            ..
        } = &callee.src
        else {
            return Ok(None);
        };
        let tr = self
            .adapter
            .krate
            .trait_decls
            .get(trait_ref.id)
            .ok_or_else(|| unsupported("missing conversion trait"))?;
        if tr.item_meta.diagnostic_item.as_deref() != Some("From") {
            return Ok(None);
        }
        let imp = self
            .adapter
            .krate
            .trait_impls
            .get(impl_ref.id)
            .ok_or_else(|| unsupported("missing conversion implementation"))?;
        let [argument] = call.args.as_slice() else {
            return Err(unsupported("integer From arity"));
        };
        let source = self.adapter.ty(argument.ty())?;
        let destination = self.adapter.ty(&call.dest.ty)?;
        let generic_identity = source == destination
            && callee.generics.types.len() == 1
            && imp.generics.types.len() == 1
            && ptr.generics.types.len() == 1
            && ptr.generics.types.iter().next() == Some(&call.dest.ty)
            && imp.impl_trait.generics.types.len() == 2
            && imp.impl_trait.generics.types.iter().all(|ty| {
                matches!(ty.kind(), a::TyKind::TypeVar(a::DeBruijnVar::Bound(depth, id))
                    if depth.index == 0 && id.index() == 0)
            })
            && callee.signature.inputs.len() == 1
            && callee.signature.inputs[0] == callee.signature.output
            && matches!(callee.signature.output.kind(),
                a::TyKind::TypeVar(a::DeBruijnVar::Bound(depth, id))
                    if depth.index == 0 && id.index() == 0);
        let concrete_conversion = callee.generics.types.is_empty()
            && imp.generics.types.is_empty()
            && ptr.generics.types.is_empty()
            && imp.impl_trait.generics.types.len() == 2
            && imp
                .impl_trait
                .generics
                .types
                .iter()
                .eq([&call.dest.ty, argument.ty()])
            && callee.signature.inputs.as_slice() == [argument.ty().clone()]
            && callee.signature.output == call.dest.ty;
        if callee.item_meta.is_local
            || imp.item_meta.is_local
            || tr.item_meta.is_local
            || call.safety == a::CallSafety::Unsafe
            || callee.signature.is_unsafe
            || callee.signature.is_variadic
            || callee.signature.abi != a::Abi::Rust
            || !callee.generics.const_generics.is_empty()
            || !imp.generics.const_generics.is_empty()
            || !ptr.generics.const_generics.is_empty()
            || tr
                .methods
                .get(*item_id)
                .is_none_or(|method| method.skip_binder.name.0.as_str() != "from")
            || imp.impl_trait.id != trait_ref.id
            || imp
                .methods
                .get(*item_id)
                .is_none_or(|method| method.skip_binder.id != id)
            || !(concrete_conversion || generic_identity)
            || !source.converts_losslessly_to(&destination)
        {
            return Err(unsupported("integer From implementation/type mismatch"));
        }
        Ok(Some(S::Assign {
            target: self.place(&call.dest)?,
            value: E::IntegerFrom {
                value: Box::new(self.operand(argument)?),
                source_type: source,
                value_type: destination,
            },
        }))
    }
    fn local(&self, id: a::LocalId) -> Result<MirLocalId, String> {
        self.names
            .get(&id)
            .cloned()
            .ok_or_else(|| unsupported("unknown local identity"))
    }
    fn place(&self, p: &a::Place) -> Result<E, String> {
        if let Some(value) = self.slice_pair_projection(p)? {
            return Ok(value);
        }
        // `(o as Some).0` of an `Option<Box<R>>` is the box's address.
        if let a::PlaceKind::Projection(base, a::ProjectionElem::Field(Some(variant), field)) =
            &p.kind
            && let Type::OptionBox { .. } = self.adapter.ty(&base.ty)?
        {
            if variant.index() != 1 || field.index() != 0 {
                return Err(unsupported("Option projection"));
            }
            return self.place(base);
        }
        if let Some(value) = self.enumerate_projection(p)? {
            return Ok(value);
        }
        if let Some(value) = self.iterator_projection(p)? {
            return Ok(value);
        }
        Ok(match &p.kind {
            a::PlaceKind::Local(id) if self.slice_pairs.contains_key(id) => {
                return Err(unsupported(
                    "shared slice pair outside component projection/copy",
                ));
            }
            a::PlaceKind::Local(id) => E::Local {
                name: self.local(*id)?,
            },
            a::PlaceKind::Projection(base, a::ProjectionElem::PtrMetadata)
                if matches!(
                    self.adapter.ty(&base.ty)?,
                    Type::ByteSlice { .. } | Type::ScalarSlice { .. }
                ) && self.adapter.ty(&p.ty)? == Type::Usize =>
            {
                E::SliceLength {
                    slice: Box::new(self.place(base)?),
                }
            }
            a::PlaceKind::Projection(base, a::ProjectionElem::Deref)
                if matches!(
                    self.adapter.ty(&base.ty)?,
                    Type::ByteSlice { .. } | Type::ScalarSlice { .. }
                ) =>
            {
                self.place(base)?
            }
            a::PlaceKind::Projection(base, a::ProjectionElem::Deref)
                if matches!(base.ty.kind(), a::TyKind::Ref(..))
                    || matches!(self.adapter.ty(&base.ty)?, Type::Box { .. }) =>
            {
                E::Deref {
                    reference: Box::new(self.place(base)?),
                    value_type: self.adapter.ty(&p.ty)?,
                }
            }
            a::PlaceKind::Projection(base, a::ProjectionElem::Field(Some(variant), field))
                if matches!(self.adapter.ty(&base.ty)?, Type::Enum { .. }) =>
            {
                let (name, variants) = self.adapter.enum_variants(&base.ty)?;
                let declared = variants
                    .get(variant.index())
                    .ok_or_else(|| unsupported("invalid enum variant"))?;
                let field_type = declared
                    .fields
                    .get(field.index())
                    .ok_or_else(|| unsupported("invalid enum field"))?;
                // A library enum's field is of its parameter, which the
                // projected place's own type instantiates.
                if let Some(field_type) = field_type
                    && self.adapter.ty(&p.ty)? != self.adapter.ty(field_type)?
                {
                    return Err(unsupported("enum field projection type mismatch"));
                }
                E::EnumField {
                    base: Box::new(self.place(base)?),
                    name,
                    variant: declared.name.clone(),
                    index: field.index(),
                }
            }
            a::PlaceKind::Projection(base, a::ProjectionElem::Field(None, field)) => {
                let id = self.adapter.struct_id(&base.ty)?;
                let declaration = self
                    .adapter
                    .fields(id)?
                    .get(*field)
                    .ok_or_else(|| unsupported("invalid field"))?;
                // A generic struct's field type names the struct's own
                // parameters; the instance's arguments replace them.
                let a::TyKind::Adt(instance) = base.ty.kind() else {
                    return Err(unsupported("nonlocal record"));
                };
                let declared = declaration.ty.clone().substitute(&instance.generics);
                if self.adapter.ty(&p.ty)? != self.adapter.ty(&declared)? {
                    return Err(unsupported("field projection type mismatch"));
                }
                let Type::Record { name: record } = self.adapter.ty(&base.ty)? else {
                    return Err(unsupported("nonlocal record"));
                };
                E::Field {
                    base: Box::new(self.place(base)?),
                    record,
                    field: declaration.name.clone(),
                }
            }
            a::PlaceKind::Projection(
                base,
                a::ProjectionElem::Index {
                    offset,
                    from_end: false,
                },
            ) if matches!(base.ty.kind(), a::TyKind::Array(..) | a::TyKind::Slice(..)) => {
                E::Index {
                    slice: Box::new(self.place(base)?),
                    index: Box::new(self.operand(offset)?),
                }
            }
            _ => return Err(unsupported("place projection")),
        })
    }
    fn constant(&self, c: &a::ConstantExpr) -> Result<E, String> {
        Ok(match c.kind() {
            a::ConstantExprKind::Global(reference) => {
                return self.adapter.constant_read(reference, c.ty());
            }
            a::ConstantExprKind::Bool(value) => E::Boolean { value: *value },
            a::ConstantExprKind::Integer(a::IntegerValue::Signed(a::IntTy::I32, value)) => {
                E::Integer {
                    value: i32::try_from(*value)
                        .map_err(|_| unsupported("invalid i32 constant"))?,
                }
            }
            a::ConstantExprKind::Integer(a::IntegerValue::Unsigned(a::UIntTy::Usize, value)) => {
                E::UsizeInteger {
                    value: u64::try_from(*value)
                        .map_err(|_| unsupported("invalid usize constant"))?,
                }
            }
            a::ConstantExprKind::Integer(a::IntegerValue::Unsigned(_, value)) => {
                E::UnsignedInteger {
                    value: u64::try_from(*value)
                        .map_err(|_| unsupported("large unsigned constant"))?,
                    value_type: self.adapter.ty(c.ty())?,
                }
            }
            a::ConstantExprKind::Integer(a::IntegerValue::Signed(_, value)) => E::SignedInteger {
                value: i64::try_from(*value).map_err(|_| unsupported("large signed constant"))?,
                value_type: self.adapter.ty(c.ty())?,
            },
            _ => return Err(unsupported("constant")),
        })
    }
    /// A call through a function-pointer local, `f(x)`: scalar arguments,
    /// the pointer's own parameter types, and a local destination.
    fn pointer_call(
        &self,
        pointer: &a::Operand,
        call: &a::Call,
        target: u::BlockId,
    ) -> Result<T, String> {
        self.pointer_call_with(pointer, &call.args, call, target)
    }
    fn pointer_call_with(
        &self,
        pointer: &a::Operand,
        args: &[a::Operand],
        call: &a::Call,
        target: u::BlockId,
    ) -> Result<T, String> {
        let (a::Operand::Move(place) | a::Operand::Copy(place)) = pointer else {
            return Err(unsupported("call through a constant function pointer"));
        };
        let a::PlaceKind::Local(local) = place.kind else {
            return Err(unsupported("call through a projected function pointer"));
        };
        let Type::FnPointer { parameters, result } = self.adapter.ty(&place.ty)? else {
            return Err(unsupported("indirect call through a non-function-pointer"));
        };
        let a::PlaceKind::Local(dest) = call.dest.kind else {
            return Err(unsupported("projected call destination"));
        };
        if call.safety == a::CallSafety::Unsafe
            || args.len() != parameters.len()
            || self.adapter.ty(&call.dest.ty)? != *result
        {
            return Err(unsupported(
                "function pointer call signature/destination type",
            ));
        }
        let arguments = args
            .iter()
            .zip(&parameters)
            .map(|(argument, parameter)| {
                if self.adapter.ty(argument.ty())? != *parameter {
                    return Err(unsupported("function pointer call operand type"));
                }
                self.operand(argument)
            })
            .collect::<Result<_, String>>()?;
        Ok(T::Call {
            function: MirCallee::Pointer {
                local: self.local(local)?,
            },
            arguments,
            owned_arguments: Vec::new(),
            destination: Some(self.local(dest)?),
            target: target.index(),
            result: None,
        })
    }
    fn operand(&self, op: &a::Operand) -> Result<E, String> {
        match op {
            a::Operand::Copy(p) | a::Operand::Move(p) => {
                if let a::PlaceKind::Global(reference) = &p.kind {
                    return self.adapter.constant_read(reference, &p.ty);
                }
                if matches!(self.adapter.ty(&p.ty)?, Type::Record { .. }) {
                    return Err(unsupported("aggregate operand without a move event"));
                }
                self.place(p)
            }
            // A function item passed for an `impl Fn` parameter is its
            // address, as a closure that captures nothing is.
            a::Operand::Const(c) if matches!(c.kind(), a::ConstantExprKind::FnDef(_)) => {
                let a::ConstantExprKind::FnDef(pointer) = c.kind() else {
                    unreachable!()
                };
                self.function_item_address(pointer, c.ty())
            }
            a::Operand::Const(c) => self.constant(c),
        }
    }
    /// The address of the crate function item `pointer` names, as a value of
    /// type `ty`.
    fn function_item_address(&self, pointer: &a::FnPtr, ty: &a::Ty) -> Result<E, String> {
        if !pointer.generics.types.is_empty() {
            return Err(unsupported("function pointer to a generic function"));
        }
        let id = self.adapter.resolve(pointer)?;
        Ok(E::FunctionAddress {
            function: self
                .adapter
                .functions
                .get(&id)
                .or_else(|| self.adapter.closure_shims.get(&id))
                .ok_or_else(|| unsupported("function pointer to an unmodeled function"))?
                .clone(),
            value_type: self.adapter.ty(ty)?,
        })
    }
    fn rvalue(&self, v: &a::Rvalue, ty: &a::Ty) -> Result<E, String> {
        Ok(match v {
            // `transmute::<Unique<R>, *const R>(b.0)`: the compiler reads a
            // box through its own pointer, which is the box's address.
            a::Rvalue::UnaryOp(
                a::UnOp::Cast(a::CastKind::Transmute(..)),
                a::Operand::Copy(place) | a::Operand::Move(place),
            ) if let a::PlaceKind::Projection(boxed, a::ProjectionElem::Field(None, field)) =
                &place.kind
                && field.index() == 0
                && let Ok(Type::Box { pointee }) = self.adapter.ty(&boxed.ty)
                && self.adapter.ty(ty)? == (Type::Box { pointee }) =>
            {
                self.place(boxed)?
            }
            // `transmute::<NonNull<R>, *const R>(b.0.0)`, the pointer inside
            // a box's `Unique`, is the box's address too.
            a::Rvalue::UnaryOp(
                a::UnOp::Cast(a::CastKind::Transmute(..)),
                a::Operand::Copy(place) | a::Operand::Move(place),
            ) if let a::PlaceKind::Projection(unique, a::ProjectionElem::Field(None, inner)) =
                &place.kind
                && inner.index() == 0
                && let a::PlaceKind::Projection(boxed, a::ProjectionElem::Field(None, field)) =
                    &unique.kind
                && field.index() == 0
                && let Type::Box { pointee } = self.adapter.ty(&boxed.ty)?
                && self.adapter.ty(ty)? == (Type::Box { pointee }) =>
            {
                self.place(boxed)?
            }
            // `None` is the null address and `Some(b)` the box's address.
            a::Rvalue::Aggregate(a::AggregateKind::Adt(_, Some(variant), None), fields)
                if matches!(self.adapter.ty(ty)?, Type::OptionBox { .. }) =>
            {
                match (variant.index(), fields.as_slice()) {
                    (0, []) => E::NoneBox,
                    (1, [box_value]) => self.operand(box_value)?,
                    _ => return Err(unsupported("Option constructor")),
                }
            }
            a::Rvalue::Use(op, _) => self.operand(op)?,
            a::Rvalue::Len(place, _, _)
                if matches!(place.ty.kind(), a::TyKind::Slice(..))
                    && self.adapter.ty(ty)? == Type::Usize =>
            {
                E::SliceLength {
                    slice: Box::new(self.place(place)?),
                }
            }
            a::Rvalue::Repeat(value, _, length, _) => E::Repeat {
                value: Box::new(self.operand(value)?),
                length: length
                    .as_usize_literal()
                    .ok_or_else(|| unsupported("symbolic array repeat"))?
                    as u64,
            },
            a::Rvalue::Aggregate(a::AggregateKind::Adt(r, Some(variant), None), fields)
                if self.adapter.enums.contains_key(&r.id) || self.adapter.library_enum(ty) =>
            {
                let (name, variants) = self.adapter.enum_variants(ty)?;
                let declared = variants
                    .get(variant.index())
                    .ok_or_else(|| unsupported("invalid enum variant"))?;
                if declared.fields.len() != fields.len() {
                    return Err(unsupported("enum constructor arity"));
                }
                E::EnumConstruct {
                    name,
                    variant: declared.name.clone(),
                    fields: fields
                        .iter()
                        .map(|field| self.operand(field))
                        .collect::<Result<_, _>>()?,
                }
            }
            a::Rvalue::Aggregate(a::AggregateKind::Array(..), elements) => E::Array {
                elements: elements
                    .iter()
                    .map(|value| self.operand(value))
                    .collect::<Result<_, _>>()?,
            },
            a::Rvalue::Ref { place, .. } if self.trait_object_reborrow(place)?.is_some() => {
                self.trait_object_reborrow(place)?.expect("checked")
            }
            // A reference to a crate struct unsized to a `&dyn` crate trait
            // is the same reference.
            a::Rvalue::UnaryOp(
                a::UnOp::Cast(a::CastKind::Unsize(source, _, a::UnsizingMetadata::VTable(..))),
                op,
            ) if matches!(self.adapter.ty(ty)?, Type::Reference { pointee, .. } if *pointee == Type::TraitObject) =>
            {
                let (
                    Type::Reference { mutable, pointee },
                    Type::Reference {
                        mutable: unsized_mutable,
                        ..
                    },
                ) = (self.adapter.ty(source)?, self.adapter.ty(ty)?)
                else {
                    return Err(unsupported("dyn unsize source"));
                };
                if !matches!(*pointee, Type::Record { .. })
                    || mutable != unsized_mutable
                    || self.adapter.ty(op.ty())? != self.adapter.ty(source)?
                {
                    return Err(unsupported(
                        "dyn unsize of a value other than a crate struct reference",
                    ));
                }
                self.operand(op)?
            }
            a::Rvalue::Ref {
                place,
                kind,
                ptr_metadata,
            } if matches!(place.ty.kind(), a::TyKind::Slice(..)) => {
                let a::PlaceKind::Projection(base, a::ProjectionElem::Deref) = &place.kind else {
                    return Err(unsupported("slice reborrow place"));
                };
                let source = self.adapter.ty(&base.ty)?;
                let destination = self.adapter.ty(ty)?;
                let mutable = matches!(kind, a::BorrowKind::Mut | a::BorrowKind::TwoPhaseMut);
                let compatible = match (&source, &destination) {
                    (
                        Type::ByteSlice { mutable: source },
                        Type::ByteSlice {
                            mutable: destination,
                        },
                    ) => *destination == mutable && (!mutable || *source),
                    (
                        Type::ScalarSlice {
                            element: source,
                            mutable: source_mutable,
                        },
                        Type::ScalarSlice {
                            element: destination,
                            mutable: destination_mutable,
                        },
                    ) => {
                        *destination_mutable == mutable
                            && (!mutable || *source_mutable)
                            && source == destination
                    }
                    _ => false,
                };
                if !matches!(
                    kind,
                    a::BorrowKind::Shared | a::BorrowKind::Mut | a::BorrowKind::TwoPhaseMut
                ) || !compatible
                    || !matches!(base.ty.kind(), a::TyKind::Ref(_, pointee, _) if pointee == &place.ty)
                    || !matches!(ptr_metadata, a::Operand::Copy(p) | a::Operand::Move(p)
                        if matches!(&p.kind, a::PlaceKind::Projection(metadata_base, a::ProjectionElem::PtrMetadata) if metadata_base == base)
                            && self.adapter.ty(&p.ty)? == Type::Usize)
                {
                    return Err(unsupported("slice reborrow pointer/metadata/type mismatch"));
                }
                E::Borrow {
                    place: Box::new(self.place(base)?),
                    value_type: destination,
                }
            }
            a::Rvalue::Ref {
                place,
                kind:
                    kind @ (a::BorrowKind::Shared | a::BorrowKind::Mut | a::BorrowKind::TwoPhaseMut),
                ptr_metadata,
            } if ptr_metadata.ty().is_unit() => {
                let destination = self.adapter.ty(ty)?;
                let source = self.adapter.ty(&place.ty)?;
                let mutable = matches!(kind, a::BorrowKind::Mut | a::BorrowKind::TwoPhaseMut);
                if !matches!(&destination, Type::Reference { mutable: m, pointee } if *m == mutable && **pointee == source)
                {
                    return Err(unsupported("borrow kind/pointee/type mismatch"));
                }
                E::Borrow {
                    place: Box::new(self.place(place)?),
                    value_type: destination,
                }
            }
            a::Rvalue::UnaryOp(a::UnOp::Not, op) if self.adapter.ty(op.ty())? == Type::Bool => {
                E::Not {
                    value: Box::new(self.operand(op)?),
                }
            }
            // `-x` is `0 - x`, whose panic check is the subtraction's.
            a::Rvalue::UnaryOp(a::UnOp::Neg(a::OverflowMode::Panic), op)
                if self.adapter.ty(op.ty())?.is_signed_integer() =>
            {
                let value_type = self.adapter.ty(op.ty())?;
                let zero = match value_type {
                    Type::I32 => E::Integer { value: 0 },
                    _ => E::SignedInteger {
                        value: 0,
                        value_type: value_type.clone(),
                    },
                };
                E::Binary {
                    operator: "sub".into(),
                    left_type: value_type.clone(),
                    right_type: value_type,
                    left: Box::new(zero),
                    right: Box::new(self.operand(op)?),
                }
            }
            a::Rvalue::UnaryOp(a::UnOp::Not, op)
                if self.adapter.ty(op.ty())?.is_integer()
                    && !matches!(self.adapter.ty(op.ty())?, Type::I8 | Type::I16) =>
            {
                E::BitwiseNot {
                    value: Box::new(self.operand(op)?),
                    value_type: self.adapter.ty(op.ty())?,
                }
            }
            a::Rvalue::UnaryOp(
                a::UnOp::Cast(a::CastKind::Unsize(
                    source,
                    destination,
                    a::UnsizingMetadata::Length(length),
                )),
                op,
            ) => {
                let a::TyKind::Ref(_, array, source_kind) = source.kind() else {
                    return Err(unsupported("array unsize source"));
                };
                let a::TyKind::Array(element, array_length, _) = array.kind() else {
                    return Err(unsupported("array unsize source"));
                };
                let Some(array_length) = array_length.as_usize_literal() else {
                    return Err(unsupported("symbolic array unsize"));
                };
                let mutable = matches!(destination.kind(), a::TyKind::Ref(_, _, a::RefKind::Mut));
                if self.adapter.ty(source)? != self.adapter.ty(op.ty())?
                    || self.adapter.ty(destination)? != self.adapter.ty(ty)?
                    || !matches!(self.adapter.ty(element)?, Type::I32 | Type::U8 | Type::U32)
                    || !(self.adapter.ty(destination)? == (Type::ByteSlice { mutable })
                        || (!mutable
                            && self.adapter.ty(destination)?
                                == (Type::ScalarSlice {
                                    element: Box::new(self.adapter.ty(element)?),
                                    mutable: false,
                                })))
                    || (mutable && *source_kind != a::RefKind::Mut)
                    || length.as_usize_literal() != Some(array_length)
                    || array_length
                        > i32::MAX as u128
                            / match self.adapter.ty(element)? {
                                Type::U8 => 1,
                                _ => 4,
                            }
                {
                    return Err(unsupported("array unsize pointer/length/type mismatch"));
                }
                E::ArrayToSlice {
                    array: Box::new(self.operand(op)?),
                    mutable,
                }
            }
            // `twice as fn(i32) -> i32`: a crate function item reified as a
            // function pointer.
            a::Rvalue::UnaryOp(a::UnOp::Cast(a::CastKind::FnPtr(..)), a::Operand::Const(c)) => {
                let a::ConstantExprKind::FnDef(pointer) = c.kind() else {
                    return Err(unsupported("function pointer from a non-item"));
                };
                self.function_item_address(pointer, ty)?
            }
            a::Rvalue::UnaryOp(a::UnOp::Cast(a::CastKind::Scalar(..)), op) => E::Cast {
                value: Box::new(self.operand(op)?),
                value_type: self.adapter.ty(ty)?,
            },
            a::Rvalue::BinaryOp(op, l, r) => {
                let left_type = self.adapter.ty(l.ty())?;
                let right_type = self.adapter.ty(r.ty())?;
                // Division, remainder and bitwise operations take two
                // integers of one type, signed or unsigned; Rust panics on a
                // zero divisor and on `MIN / -1`. Narrow signed bitwise
                // results are refused: no proof can yet relate their
                // sign-extended `int` result to the narrow value.
                let same_integer = left_type.is_integer() && left_type == right_type;
                let bitwise = same_integer && !matches!(left_type, Type::I8 | Type::I16);
                let operator = match op {
                    a::BinOp::Add(a::OverflowMode::Panic) => "add",
                    a::BinOp::Sub(a::OverflowMode::Panic) => "sub",
                    a::BinOp::Mul(a::OverflowMode::Panic) => "mul",
                    a::BinOp::Div(a::OverflowMode::Panic) if same_integer => "div",
                    a::BinOp::Rem(a::OverflowMode::Panic) if same_integer => "rem",
                    a::BinOp::Shl(a::OverflowMode::Panic) if left_type.is_integer() => "shl",
                    a::BinOp::Shr(a::OverflowMode::Panic) if left_type.is_integer() => "shr",
                    a::BinOp::BitAnd if bitwise => "bit_and",
                    a::BinOp::BitOr if bitwise => "bit_or",
                    a::BinOp::BitXor if bitwise => "bit_xor",
                    a::BinOp::Eq => "eq",
                    a::BinOp::Ne => "ne",
                    a::BinOp::Lt => "lt",
                    a::BinOp::Le => "le",
                    a::BinOp::Gt => "gt",
                    a::BinOp::Ge => "ge",
                    _ => return Err(unsupported("binary operation or overflow mode")),
                };
                E::Binary {
                    operator: operator.into(),
                    left_type,
                    right_type,
                    left: Box::new(self.operand(l)?),
                    right: Box::new(self.operand(r)?),
                }
            }
            _ => return Err(unsupported("rvalue")),
        })
    }
    fn statement(&self, s: &u::Statement) -> Result<Option<S>, String> {
        if let Some(statement) = self.closure_statement(s)? {
            return Ok(statement);
        }
        if let Some(statement) = self.range_statement(s)? {
            return Ok(Some(statement));
        }
        if let Some(statement) = self.iterator_statement(s)? {
            return Ok(statement);
        }
        match &s.kind {
            // A `match` reads the enum itself; its discriminant local is gone.
            u::StatementKind::Assign(
                a::Place {
                    kind: a::PlaceKind::Local(local),
                    ..
                },
                a::Rvalue::Discriminant(_),
            )
            | u::StatementKind::StorageLive(local)
            | u::StatementKind::StorageDead(local)
                if self.enum_discriminants.contains_key(local) =>
            {
                return Ok(None);
            }
            // `match *r` mentions the referent; a reference's referent is
            // always a valid place, so the mention has no effect.
            u::StatementKind::PlaceMention(a::Place {
                kind: a::PlaceKind::Projection(base, a::ProjectionElem::Deref),
                ..
            }) if base.as_local().is_some() && matches!(base.ty.kind(), a::TyKind::Ref(..)) => {
                return Ok(None);
            }
            _ => {}
        }
        Ok(match &s.kind {
            u::StatementKind::Assign(p, v) => {
                if self.adapter.ty(&p.ty)? == Type::Unit {
                    // Only the literal unit value can disappear; never discard a call/read.
                    if !matches!(v, a::Rvalue::Aggregate(a::AggregateKind::Adt(r, None, None), fields)
                        if (r.id == a::TypeDeclId::UNIT || self.adapter.empty_closure_state(r.id))
                            && fields.is_empty())
                    {
                        return Err(unsupported("nonliteral unit assignment"));
                    }
                    return Ok(None);
                }
                if let Type::Record { name } = self.adapter.ty(&p.ty)? {
                    let a::PlaceKind::Local(target) = p.kind else {
                        return Err(unsupported("partial record assignment"));
                    };
                    match v {
                        a::Rvalue::Aggregate(a::AggregateKind::Adt(r, None, None), fields)
                            if r.id == self.adapter.struct_id(&p.ty)? =>
                        {
                            Some(S::Initialize {
                                target: self.local(target)?,
                                record: name,
                                fields: fields
                                    .iter()
                                    .map(|op| self.operand(op))
                                    .collect::<Result<_, _>>()?,
                            })
                        }
                        a::Rvalue::Use(
                            op @ (a::Operand::Move(source) | a::Operand::Copy(source)),
                            _,
                        ) if self.adapter.ty(&source.ty)? == self.adapter.ty(&p.ty)? => {
                            let a::PlaceKind::Local(source) = source.kind else {
                                return Err(unsupported("partial move"));
                            };
                            if matches!(op, a::Operand::Copy(_)) {
                                if !self.adapter.crate_mode {
                                    return Err(unsupported("record copy outside crate imports"));
                                }
                                Some(S::Copy {
                                    target: self.local(target)?,
                                    source: self.local(source)?,
                                    record: name,
                                })
                            } else {
                                Some(S::Move {
                                    target: self.local(target)?,
                                    source: self.local(source)?,
                                    record: name,
                                })
                            }
                        }
                        _ => return Err(unsupported("record constructor or move")),
                    }
                } else {
                    Some(S::Assign {
                        target: self.place(p)?,
                        value: self.rvalue(v, &p.ty)?,
                    })
                }
            }
            u::StatementKind::StorageDead(id) => Some(S::EndStorage {
                local: self.local(*id)?,
            }),
            u::StatementKind::StorageLive(id)
                if (matches!(self.body.locals.locals[*id].ty.kind(), a::TyKind::Adt(r) if self.adapter.records.contains_key(&r.id) || self.adapter.generic_records.contains_key(&r.id))
                    || matches!(self.body.locals.locals[*id].ty.kind(), a::TyKind::Array(..))
                    || self.spelled.contains(id)) =>
            {
                Some(S::BeginStorage {
                    local: self.local(*id)?,
                })
            }
            u::StatementKind::StorageLive(_)
            | u::StatementKind::Nop
            | u::StatementKind::Borrowck(_) => None,
            _ => return Err(unsupported("statement")),
        })
    }
    /// Whether `block` is the compiler's unreachable fallback of a `match`
    /// that names every variant.
    fn unreachable_block(&self, block: u::BlockId) -> bool {
        self.body.body.get(block).is_some_and(|block| {
            block.statements.iter().all(|statement| {
                matches!(
                    statement.kind,
                    u::StatementKind::StorageLive(_)
                        | u::StatementKind::StorageDead(_)
                        | u::StatementKind::Nop
                )
            }) && matches!(block.terminator.kind, u::TerminatorKind::UndefinedBehavior)
        })
    }
    /// A `match` of crate enum `matched`: one case for each variant a branch
    /// names by its discriminant. The compiler's unreachable fallback of a
    /// `match` that names every variant is dropped; any other fallback is
    /// the case of the variants no branch names.
    fn enum_switch(
        &self,
        matched: &a::Place,
        data: &a::SwitchData,
        branches: &charon_lib::ids::IndexVec<a::BranchId, u::BlockId>,
    ) -> Result<T, String> {
        let (_, variants) = self.adapter.enum_variants(&matched.ty)?;
        let mut cases = Vec::new();
        let mut named = BTreeSet::new();
        for (constant, branch) in &data.branches {
            let variant = match constant.kind() {
                a::ConstantExprKind::Integer(value) => variants
                    .iter()
                    .find(|variant| variant.discriminant == *value),
                a::ConstantExprKind::Discriminant(_, variant) => variants.get(variant.index()),
                _ => None,
            }
            .ok_or_else(|| unsupported("enum switch constant"))?;
            if !named.insert(variant.id) {
                return Err(unsupported("repeated enum switch variant"));
            }
            cases.push(out::SwitchCase {
                label: out::SwitchLabel::Variant {
                    name: variant.name.clone(),
                },
                target: branches[*branch].index(),
            });
        }
        let otherwise = match data.fallback {
            Some(fallback)
                if named.len() == variants.len() && self.unreachable_block(branches[fallback]) =>
            {
                None
            }
            Some(fallback) if named.len() < variants.len() => Some(branches[fallback].index()),
            Some(_) => return Err(unsupported("reachable fallback of an exhaustive match")),
            None if named.len() == variants.len() => None,
            None => return Err(unsupported("enum switch without every variant")),
        };
        Ok(T::Switch {
            scrutinee: self.place(matched)?,
            cases,
            otherwise,
        })
    }
    /// A `match` of an integer with several values: a case for each.
    fn integer_switch(
        &self,
        value: &a::Operand,
        data: &a::SwitchData,
        branches: &charon_lib::ids::IndexVec<a::BranchId, u::BlockId>,
    ) -> Result<T, String> {
        if !self.adapter.ty(value.ty())?.is_integer() {
            return Err(unsupported("multiway switch on a non-integer"));
        }
        let cases = data
            .branches
            .iter()
            .map(|(constant, branch)| {
                Ok(out::SwitchCase {
                    label: out::SwitchLabel::Value {
                        value: self.constant(constant)?,
                    },
                    target: branches[*branch].index(),
                })
            })
            .collect::<Result<_, String>>()?;
        Ok(T::Switch {
            scrutinee: self.operand(value)?,
            cases,
            otherwise: Some(
                branches[data
                    .fallback
                    .ok_or_else(|| unsupported("integer switch without a fallback"))?]
                .index(),
            ),
        })
    }
    fn terminator(&self, t: &u::Terminator) -> Result<T, String> {
        if let Some(terminator) = self.iterator_switch(t)? {
            return Ok(terminator);
        }
        Ok(match &t.kind {
            u::TerminatorKind::Goto { target } => T::Goto {
                target: target.index(),
            },
            u::TerminatorKind::Return => T::Return,
            // Code compiled with `-Cpanic=abort` never unwinds, but the
            // compiler's drop glue keeps its cleanup blocks.
            u::TerminatorKind::UndefinedBehavior
            | u::TerminatorKind::UnwindTerminate
            | u::TerminatorKind::UnwindResume => T::Unreachable,
            u::TerminatorKind::Switch { data, branches } => {
                let a::SwitchScrutinee::Value(value) = &data.scrutinee else {
                    return Err(unsupported("enum switch"));
                };
                if let a::Operand::Move(place) | a::Operand::Copy(place) = value
                    && let a::PlaceKind::Local(local) = place.kind
                    && let Some(matched) = self.enum_discriminants.get(&local)
                {
                    return self.enum_switch(matched, data, branches);
                }
                let [(constant, yes)] = data.branches.as_slice() else {
                    return self.integer_switch(value, data, branches);
                };
                let no = data
                    .fallback
                    .ok_or_else(|| unsupported("exhaustive switch"))?;
                let condition = if let a::ConstantExprKind::Bool(expected) = constant.kind() {
                    if self.adapter.ty(value.ty())? != Type::Bool {
                        return Err(unsupported("boolean switch type mismatch"));
                    }
                    let operand = self.operand(value)?;
                    if *expected {
                        operand
                    } else {
                        E::Not {
                            value: Box::new(operand),
                        }
                    }
                } else {
                    E::Binary {
                        operator: "eq".into(),
                        left_type: self.adapter.ty(value.ty())?,
                        right_type: self.adapter.ty(constant.ty())?,
                        left: Box::new(self.operand(value)?),
                        right: Box::new(self.constant(constant)?),
                    }
                };
                T::If {
                    condition,
                    then_target: branches[*yes].index(),
                    else_target: branches[no].index(),
                }
            }
            // A callable value owns no resource: an `impl Fn` argument is a
            // closure whose captures are scalars.
            u::TerminatorKind::Drop {
                kind: a::DropKind::Precise,
                place,
                target,
                ..
            } if matches!(self.adapter.ty(&place.ty), Ok(Type::FnPointer { .. })) => T::Goto {
                target: target.index(),
            },
            // A value of an abstract type parameter: generic code is
            // instantiated only at the scalar types, whose values have no
            // drop, so dropping one does nothing at every instance.
            u::TerminatorKind::Drop {
                kind: a::DropKind::Precise,
                place,
                target,
                ..
            } if matches!(self.adapter.ty(&place.ty), Ok(Type::Parameter { .. })) => T::Goto {
                target: target.index(),
            },
            // A `Vec` of scalars: its elements have no drop, and the heap
            // buffer it frees is outside the model, so dropping one has no
            // effect a proof reads.
            u::TerminatorKind::Drop {
                kind: a::DropKind::Precise,
                place,
                target,
                ..
            } if matches!(self.adapter.ty(&place.ty), Ok(Type::Vec { .. })) => T::Goto {
                target: target.index(),
            },
            // A box of a record, or an option of one: its drop runs the
            // record's glue on a `Some` box and frees the allocation, and
            // freeing `None`'s null is no effect.
            u::TerminatorKind::Drop {
                kind: a::DropKind::Precise,
                place,
                target,
                ..
            } if matches!(
                self.adapter.ty(&place.ty),
                Ok(Type::Box { .. } | Type::OptionBox { .. })
            ) =>
            {
                let place_type = self.adapter.ty(&place.ty)?;
                let optional = matches!(place_type, Type::OptionBox { .. });
                let (Type::Box { pointee } | Type::OptionBox { pointee }) = place_type else {
                    unreachable!()
                };
                let Type::Record { name } = *pointee else {
                    return Err(unsupported("box of a non-record"));
                };
                let record = self
                    .adapter
                    .boxed_record(&place.ty)
                    .ok_or_else(|| unsupported("box of a non-record"))?;
                let glue = match self.adapter.drop_glue_of(record)? {
                    Some(glue) => Some(glue),
                    None if self.adapter.record_has_drop_glue(record)? => {
                        return Err(unsupported("box of a record with a destructor"));
                    }
                    None => None,
                };
                let a::PlaceKind::Local(local) = place.kind else {
                    return Err(unsupported("partial box drop"));
                };
                self.adapter
                    .box_library_function(super::standard_library::BOX_DROP, &name);
                T::BoxFree {
                    local: self.local(local)?,
                    record: name,
                    glue,
                    optional,
                    target: target.index(),
                }
            }
            u::TerminatorKind::Drop {
                kind: a::DropKind::Precise,
                place,
                fn_ptr,
                target,
                ..
            } => {
                let id = self.adapter.struct_id(&place.ty)?;
                let glue = self
                    .adapter
                    .krate
                    .fun_decls
                    .get(self.adapter.resolve(fn_ptr)?)
                    .ok_or_else(|| unsupported("missing drop glue"))?;
                // Named flat-record drop interpretation: scalar/reference fields need no
                // field cleanup; rustc-generated Destruct glue calls the imported Drop method.
                let a::FunSource::TraitImpl {
                    trait_ref,
                    impl_ref,
                    ..
                } = &glue.src
                else {
                    return Err(unsupported("non-generated drop glue"));
                };
                let tr = self
                    .adapter
                    .krate
                    .trait_decls
                    .get(trait_ref.id)
                    .ok_or_else(|| unsupported("missing Destruct trait"))?;
                let imp = self
                    .adapter
                    .krate
                    .trait_impls
                    .get(impl_ref.id)
                    .ok_or_else(|| unsupported("missing Destruct impl"))?;
                if tr.item_meta.lang_item != Some(LangItem::Destruct)
                    || !matches!(imp.src, a::TraitImplSource::Destruct)
                    || imp
                        .impl_trait
                        .generics
                        .types
                        .first()
                        .and_then(|t| self.adapter.struct_id(t).ok())
                        != Some(id)
                {
                    return Err(unsupported("drop glue/type mismatch"));
                }
                let a::PlaceKind::Local(local) = place.kind else {
                    return Err(unsupported("partial drop"));
                };
                // An instance of a generic struct's glue is declared where a
                // drop names it.
                self.adapter.drop_glue_of(&place.ty)?;
                let Type::Record { name: record } = self.adapter.ty(&place.ty)? else {
                    return Err(unsupported("drop of a non-record"));
                };
                T::Drop {
                    local: self.local(local)?,
                    record,
                    target: target.index(),
                }
            }
            u::TerminatorKind::Call { call, target, .. } => {
                let ptr = match &call.func {
                    a::FnOperand::Regular(ptr) if self.adapter.is_dyn_fn_call(ptr) => {
                        return self.dyn_fn_call(call, *target);
                    }
                    a::FnOperand::Regular(ptr) => {
                        if let Some(interface) = self.adapter.interface_call(ptr)? {
                            return self.interface_method_call(interface, call, *target);
                        }
                        ptr
                    }
                    a::FnOperand::Dynamic(pointer) => {
                        if let Some(interface) = self.adapter.vtable_call(pointer)? {
                            return self.interface_method_call(interface, call, *target);
                        }
                        return self.pointer_call(pointer, call, *target);
                    }
                };
                // `<Box as Drop>::drop(b)` of a box whose contents were moved
                // out frees the allocation alone.
                if self.adapter.box_drop_call(call)? {
                    let [a::Operand::Move(boxed)] = call.args.as_slice() else {
                        return Err(unsupported("`Box` drop operand"));
                    };
                    let (a::PlaceKind::Local(local), Type::Box { pointee }) =
                        (&boxed.kind, self.adapter.ty(&boxed.ty)?)
                    else {
                        return Err(unsupported("`Box` drop operand"));
                    };
                    let Type::Record { name } = *pointee else {
                        return Err(unsupported("box of a non-record"));
                    };
                    self.adapter
                        .box_library_function(super::standard_library::BOX_DROP, &name);
                    return Ok(T::BoxFree {
                        local: self.local(*local)?,
                        record: name,
                        glue: None,
                        optional: false,
                        target: target.index(),
                    });
                }
                let id = self.adapter.resolve(ptr)?;
                let callee = self
                    .adapter
                    .krate
                    .fun_decls
                    .get(id)
                    .ok_or_else(|| unsupported("missing call definition"))?;
                // `Box::new(value)` of a record moves it into a new allocation.
                if callee.item_meta.diagnostic_item.as_deref() == Some("box_new") {
                    let [a::Operand::Move(source)] = call.args.as_slice() else {
                        return Err(unsupported("Box::new operand"));
                    };
                    let (a::PlaceKind::Local(source_local), a::PlaceKind::Local(destination)) =
                        (&source.kind, &call.dest.kind)
                    else {
                        return Err(unsupported("projected Box::new operand or destination"));
                    };
                    let Type::Record { name } = self.adapter.ty(&source.ty)? else {
                        return Err(unsupported("Box::new of a non-record"));
                    };
                    if self.adapter.ty(&call.dest.ty)?
                        != (Type::Box {
                            pointee: Box::new(Type::Record { name: name.clone() }),
                        })
                    {
                        return Err(unsupported("Box::new destination type"));
                    }
                    // The library's `Box::new<R>`, whose contract is the box.
                    let function = self
                        .adapter
                        .box_library_function(super::standard_library::BOX_NEW, &name);
                    let source_local = self.local(*source_local)?;
                    return Ok(T::Call {
                        function: function.into(),
                        arguments: vec![E::Local {
                            name: source_local.clone(),
                        }],
                        owned_arguments: vec![out::OwnedArgument {
                            index: 0,
                            local: Some(source_local),
                            record: name,
                            moved: true,
                        }],
                        destination: Some(self.local(*destination)?),
                        target: target.index(),
                        result: None,
                    });
                }
                // A Rust core method the library specifies calls its
                // external function, whose contract is the library's.
                let core_method = match self.adapter.core_method_call(callee, ptr, call)? {
                    Some(function) => Some(function),
                    None => match self.adapter.option_method_call(callee, ptr, call)? {
                        Some(function) => Some(function),
                        None => match self.adapter.result_method_call(callee, ptr, call)? {
                            Some(function) => Some(function),
                            None => match self.adapter.slice_method_call(callee, ptr, call)? {
                                Some(function) => Some(function),
                                None => {
                                    match self.adapter.option_take_method_call(callee, ptr, call)? {
                                        Some(function) => Some(function),
                                        None => self.adapter.vec_method_call(callee, ptr, call)?,
                                    }
                                }
                            },
                        },
                    },
                };
                if let Some(function) = core_method {
                    let a::PlaceKind::Local(destination) = call.dest.kind else {
                        return Err(unsupported("projected call destination"));
                    };
                    // `expect`'s message is not passed on.
                    let passed = self.adapter.core_methods.borrow()[&function]
                        .parameters
                        .len();
                    return Ok(T::Call {
                        function: function.into(),
                        arguments: call
                            .args
                            .iter()
                            .take(passed)
                            .map(|argument| self.operand(argument))
                            .collect::<Result<_, _>>()?,
                        owned_arguments: Vec::new(),
                        destination: Some(self.local(destination)?),
                        target: target.index(),
                        result: None,
                    });
                }
                self.adapter.assignment_operator_call(callee, ptr, call)?;
                self.adapter.default_constructor_call(callee, ptr, call)?;
                if callee.item_meta.diagnostic_item.as_deref() == Some("mem_drop") {
                    let [a::Operand::Move(p)] = call.args.as_slice() else {
                        return Err(unsupported("mem::drop operand"));
                    };
                    let a::PlaceKind::Local(local) = p.kind else {
                        return Err(unsupported("partial explicit drop"));
                    };
                    let record = self.adapter.record_id(&p.ty)?;
                    T::Drop {
                        local: self.local(local)?,
                        record: self.adapter.records[&record].clone(),
                        target: target.index(),
                    }
                } else {
                    // The callee's `impl Fn` parameters take their callable
                    // types from its own bounds; a closure argument's type is
                    // compared with them.
                    let callee_parameters =
                        self.adapter.callable_type_parameters(&callee.generics)?;
                    // A call of a generic function at scalar types calls its
                    // instance there, whose types are the call's.
                    let instantiation = self.adapter.call_instantiation(&callee_parameters, ptr)?;
                    let callee_inputs = match &instantiation {
                        Some(types) => self.adapter.signature_types_at(callee, types)?.0,
                        None => self.adapter.callee_signature_types(callee)?,
                    };
                    let callee_output = match &instantiation {
                        Some(types) => self.adapter.signature_types_at(callee, types)?.1,
                        None if self.adapter.crate_mode => {
                            self.adapter.ty(&callee.signature.output)?
                        }
                        None => Type::Unit,
                    };
                    if self.adapter.crate_mode
                        && (call.args.len() != callee_inputs.len()
                            || self.adapter.ty(&call.dest.ty)? != callee_output)
                    {
                        return Err(unsupported("source call signature/destination type"));
                    }
                    if self.adapter.crate_mode {
                        for (arg, ty) in call.args.iter().zip(&callee_inputs) {
                            let argument = self.adapter.ty(arg.ty())?;
                            // A reference to a crate struct is passed for a
                            // reference to a crate trait's type parameter.
                            let trait_object = matches!(
                                (ty, &argument),
                                (
                                    Type::Reference { mutable, pointee },
                                    Type::Reference { mutable: passed, pointee: value },
                                ) if **pointee == Type::TraitObject
                                    && mutable == passed
                                    && matches!(**value, Type::Record { .. } | Type::TraitObject)
                            );
                            if argument != *ty && !trait_object {
                                return Err(unsupported("source call operand type"));
                            }
                        }
                    }
                    if call.safety == a::CallSafety::Unsafe
                        || callee.signature.is_unsafe
                        || ptr.generics.types.len() != callee_parameters.len()
                        || !ptr.generics.types.iter().zip(&callee_parameters).all(
                            |(ty, parameter)| match ty.kind() {
                                a::TyKind::Adt(r) if self.adapter.closure_state(r.id) => true,
                                a::TyKind::FnDef(_) => true,
                                // A crate trait's type parameter is reached
                                // only through the trait.
                                _ if *parameter == Some(Type::TraitObject) => true,
                                // An abstract type parameter is instantiated.
                                _ => {
                                    matches!(parameter, Some(Type::Parameter { .. }))
                                        && instantiation.is_some()
                                }
                            },
                        )
                    {
                        return Err(unsupported("unsafe or generic call"));
                    }
                    let a::PlaceKind::Local(dest) = call.dest.kind else {
                        return Err(unsupported("projected call destination"));
                    };
                    let mut owned_arguments = Vec::new();
                    let arguments: Vec<E> = call
                        .args
                        .iter()
                        .enumerate()
                        .map(|(index, op)| {
                            if let Type::Record { name } = self.adapter.ty(op.ty())? {
                                if !self.adapter.crate_mode {
                                    return Err(unsupported(
                                        "owned call operand outside crate imports",
                                    ));
                                }
                                let (a::Operand::Move(place) | a::Operand::Copy(place)) = op else {
                                    return Err(unsupported("owned constant call operand"));
                                };
                                let a::PlaceKind::Local(local) = place.kind else {
                                    return Err(unsupported("projected owned call operand"));
                                };
                                let local = self.local(local)?;
                                owned_arguments.push(out::OwnedArgument {
                                    index,
                                    local: Some(local.clone()),
                                    record: name,
                                    moved: matches!(op, a::Operand::Move(_)),
                                });
                                Ok(E::Local { name: local })
                            } else {
                                self.operand(op)
                            }
                        })
                        .collect::<Result<_, String>>()?;
                    // A crate struct reference passed as a crate trait's
                    // object becomes the object for the call.
                    for (index, operand) in call.args.iter().enumerate() {
                        let generic = callee
                            .signature
                            .inputs
                            .get(index)
                            .and_then(|ty| self.adapter.object_parameter_trait(callee, ty))
                            .and_then(|trait_id| match operand.ty().kind() {
                                a::TyKind::Ref(_, pointee, kind) => {
                                    self.adapter.object_record(pointee).map(|record| {
                                        (record, trait_id, matches!(kind, a::RefKind::Shared))
                                    })
                                }
                                _ => None,
                            });
                        let unsized_object = match operand {
                            a::Operand::Move(place) | a::Operand::Copy(place) => match place.kind {
                                a::PlaceKind::Local(local) => {
                                    self.unsized_objects.get(&local).cloned()
                                }
                                _ => None,
                            },
                            _ => None,
                        };
                        if let Some((record, (trait_id, instance), shared)) =
                            generic.or(unsized_object)
                        {
                            let (pack, unpack) = self
                                .adapter
                                .object_coercion_names(&record, &instance, shared)?;
                            self.adapter
                                .object_coercions
                                .borrow_mut()
                                .insert((record, trait_id, instance));
                            self.coercions.borrow_mut().push((
                                pack,
                                unpack,
                                arguments[index].clone(),
                            ));
                        }
                    }
                    let function = match &instantiation {
                        Some(types) => self.adapter.generic_instance(id, callee, types)?,
                        None => self
                            .adapter
                            .functions
                            .get(&id)
                            .ok_or_else(|| self.adapter.unmodeled_call(callee))?
                            .clone(),
                    };
                    T::Call {
                        function: function.into(),
                        arguments,
                        owned_arguments,
                        destination: Some(self.local(dest)?),
                        target: target.index(),
                        result: None,
                    }
                }
            }
            _ => return Err(unsupported("terminator (including unreconstructed checks)")),
        })
    }
}

pub(super) fn decode(
    bytes: &[u8],
    source: &str,
    source_bytes: &[u8],
) -> Result<out::RustExport, String> {
    decode_crate(bytes, source, source_bytes, None, None)
}

pub(super) fn decode_crate(
    bytes: &[u8],
    source: &str,
    source_bytes: &[u8],
    crate_config: Option<&super::crate_inputs::CrateConfig>,
    sources: Option<&super::crate_inputs::SourceFiles>,
) -> Result<out::RustExport, String> {
    let artifact: ExtractionArtifact =
        serde_json::from_slice(bytes).map_err(|e| format!("Charon artifact: {e}"))?;
    if artifact.extractor_revision != profile::get().extractor_revision
        || artifact.compiler_commit != profile::get().compiler_commit
        || artifact.profile != profile::get().extraction
        || artifact.flags
            != crate_config.map_or_else(|| profile::get().flags.clone(), |c| c.flags())
        || artifact.crate_config.as_ref() != crate_config
        || artifact.crate_profile.as_deref()
            != crate_config.map(|_| super::crate_inputs::PROFILE_ID)
    {
        return Err("Charon artifact differs from the locked compiler profile".into());
    }
    let data = artifact.data;
    if data.has_errors {
        return Err("Charon partial artifact rejected".into());
    }
    let krate = data.translated;
    let opts = &krate.options;
    let expected = charon_lib::options::CliOpts {
        ullbc: true,
        mir: Some(charon_lib::options::MirLevel::Optimized),
        precise_drops: true,
        reconstruct_fallible_operations: true,
        sysroot: Some("default".into()),
        opaque: vec!["core".into(), "alloc".into(), "std".into()],
        error_on_warnings: true,
        dest_file: opts.dest_file.clone(),
        start_from: crate_config.map_or_else(Vec::new, |c| c.roots.clone()),
        ..Default::default()
    };
    // The driver clears rustc_args after consuming them; the refresh-owned
    // envelope records those flags along with the checked compiler identity.
    if opts != &expected {
        return Err("Rust artifact differs from the pinned extraction profile".into());
    }
    if let Some(c) = crate_config {
        if krate.crate_name != c.name {
            return Err("Charon crate identity differs from configuration".into());
        }
        let sources = sources.ok_or("missing locked crate sources")?;
        let mut seen = BTreeSet::new();
        for file in &krate.files {
            if let a::FileName::Local(path) = &file.name {
                if path.is_absolute() {
                    continue;
                }
                let name = path.to_str().ok_or("Charon source path is not UTF-8")?;
                if !seen.insert(name)
                    || sources.get(name).map(Vec::as_slice)
                        != file.contents.as_deref().map(str::as_bytes)
                {
                    return Err(format!(
                        "Charon file `{}` differs from locked crate source closure",
                        name.chars().take(120).collect::<String>()
                    ));
                }
            }
        }
        // External source locations may also be Local (e.g. /rustc/library).
        // Ownership comes from declarations, never the crate-name spelling.
        let metadata = krate
            .type_decls
            .iter()
            .map(|d| &d.item_meta)
            .chain(krate.fun_decls.iter().map(|d| &d.item_meta))
            .chain(krate.global_decls.iter().map(|d| &d.item_meta))
            .chain(krate.trait_decls.iter().map(|d| &d.item_meta))
            .chain(krate.trait_impls.iter().map(|d| &d.item_meta));
        for meta in metadata.filter(|m| m.is_local) {
            let file = krate
                .files
                .get(meta.span.data().file_id)
                .ok_or("missing local declaration source")?;
            let a::FileName::Local(path) = &file.name else {
                return Err("local declaration is outside locked crate sources".into());
            };
            if !path.to_str().is_some_and(|name| seen.contains(name)) {
                return Err("local declaration is outside locked crate sources".into());
            }
        }
        if !seen.contains(source) {
            return Err("Charon artifact is missing the crate root".into());
        }
    } else {
        let files: Vec<_> = krate
            .files
            .iter()
            .filter(|f| f.crate_name == krate.crate_name)
            .collect();
        if files.len() != 1 || files[0].contents.as_deref().map(str::as_bytes) != Some(source_bytes)
        {
            return Err("Rust single-file import requires exactly one locked source file".into());
        }
    }
    let mut adapter = Adapter {
        crate_mode: crate_config.is_some(),
        krate: &krate,
        records: BTreeMap::new(),
        enums: BTreeMap::new(),
        functions: BTreeMap::new(),
        destructors: BTreeMap::new(),
        drop_glues: BTreeMap::new(),
        closure_shims: BTreeMap::new(),
        closure_calls: BTreeMap::new(),
        user_iterator_nexts: BTreeSet::new(),
        closure_captures: BTreeMap::new(),
        callable_parameters: std::cell::RefCell::new(Vec::new()),
        trait_impl_methods: BTreeMap::new(),
        object_coercions: std::cell::RefCell::new(BTreeSet::new()),
        trait_instances: std::cell::RefCell::default(),
        generic_instances: std::cell::RefCell::default(),
        instance_types: std::cell::RefCell::default(),
        generic_records: BTreeMap::new(),
        record_instances: std::cell::RefCell::default(),
        enum_instances: std::cell::RefCell::default(),
        core_methods: std::cell::RefCell::default(),
    };
    if crate_config.is_some() {
        adapter.record_closure_captures()?;
    }
    for (id, record) in krate.type_decls.iter_indexed() {
        if record.item_meta.is_local {
            // A closure's state is not a record: its captures become the
            // closure's leading parameters.
            if let a::TypeSource::Closure { .. } = &record.src {
                if !record.generics.types.is_empty() {
                    return Err(unsupported("generic closure"));
                }
                continue;
            }
            // A crate trait's vtable is not a record either: a call through
            // it is a call of the trait's interface function.
            if let a::TypeSource::VTable { .. } = &record.src {
                continue;
            }
            // An enum is a value the sidecar names as a `spec enum`.
            if let a::TypeDeclKind::Enum(_) = &record.kind {
                if !record.generics.types.is_empty()
                    || !record.generics.const_generics.is_empty()
                    || !matches!(record.src, a::TypeSource::Normal)
                {
                    return Err(unsupported("generic enum"));
                }
                if crate_config.is_some() {
                    return Err(unsupported("enum in a crate unit"));
                }
                adapter
                    .enums
                    .insert(id, simple_name(&record.item_meta.name, &krate.crate_name)?);
                continue;
            }
            if !record.generics.types.is_empty()
                && record.generics.const_generics.is_empty()
                && record.generics.trait_clauses.iter().all(|clause| {
                    krate
                        .trait_decls
                        .get(clause.trait_.skip_binder.id)
                        .and_then(|decl| decl.item_meta.lang_item.clone())
                        .is_some_and(|item| {
                            matches!(
                                item,
                                LangItem::Sized
                                    | LangItem::MetaSized
                                    | LangItem::Destruct
                                    | LangItem::Copy
                                    | LangItem::Clone
                            )
                        })
                })
                && matches!(record.src, a::TypeSource::Normal)
                && crate_config.is_some()
            {
                adapter.generic_records.insert(
                    id,
                    qualified_record_name(&record.item_meta.name, &krate.crate_name)?,
                );
                continue;
            }
            if !record.generics.types.is_empty()
                || !record.generics.const_generics.is_empty()
                || !matches!(record.src, a::TypeSource::Normal)
            {
                return Err(unsupported("generic or generated source record"));
            }
            adapter.records.insert(
                id,
                if crate_config.is_some() {
                    qualified_record_name(&record.item_meta.name, &krate.crate_name)?
                } else {
                    simple_name(&record.item_meta.name, &krate.crate_name)?
                },
            );
        }
    }
    // A refusal while naming or checking an item names where it is.
    let mut item_location = format!("{source}:1");
    let mut constant_initializers = BTreeSet::new();
    (|| -> Result<(), String> {
        for (id, f) in krate.fun_decls.iter_indexed() {
            if !f.item_meta.is_local {
                continue;
            }
            item_location = refusal_location(&krate, source, f.item_meta.span, f.item_meta.span);
            let name = match &f.src {
                a::FunSource::Normal
                    if crate_config.is_some() && adapter.closure_as_fn_name(f)?.is_some() =>
                {
                    let closure = adapter.closure_as_fn_name(f)?.unwrap();
                    adapter.closure_shims.insert(id, closure);
                    continue;
                }
                a::FunSource::Normal => {
                    if crate_config.is_some() {
                        adapter.qualified_function_name(&f.item_meta.name)?
                    } else {
                        simple_name(&f.item_meta.name, &krate.crate_name)?
                    }
                }
                // A crate trait method's implementation, which a call through
                // the trait reaches by the trait's interface function.
                a::FunSource::TraitImpl {
                    trait_ref,
                    impl_ref,
                    item_id,
                    ..
                } if adapter.interface_trait(trait_ref.id)? => {
                    let (name, interface) =
                        adapter.trait_impl_method(f, impl_ref.id, trait_ref.id, *item_id)?;
                    adapter.trait_impl_methods.insert(id, interface);
                    name
                }
                // A crate trait's default method: its body is the trait's
                // interface function for that method, generic over the
                // implementing type, verified once against the interface.
                a::FunSource::TraitDefault {
                    trait_ref, item_id, ..
                } if adapter.interface_trait(trait_ref.id)? => {
                    adapter.interface_name(trait_ref.id, *item_id, &trait_ref.generics)?
                }
                a::FunSource::TraitImpl {
                    trait_ref,
                    impl_ref,
                    ..
                } => {
                    let tr = krate
                        .trait_decls
                        .get(trait_ref.id)
                        .ok_or_else(|| unsupported("missing trait"))?;
                    if tr.item_meta.lang_item == Some(LangItem::Destruct) {
                        // A struct holding a box drops it in its glue, which frees
                        // the box's contents through their own glue: a recursive
                        // function, checked against its sidecar contract.
                        let imp = krate
                            .trait_impls
                            .get(impl_ref.id)
                            .ok_or_else(|| unsupported("missing Destruct impl"))?;
                        let Some((rec, record)) = imp
                            .impl_trait
                            .generics
                            .types
                            .first()
                            .and_then(|ty| adapter.struct_id(ty).ok().map(|rec| (rec, ty)))
                        else {
                            continue;
                        };
                        if !adapter.record_holds_box(rec)? {
                            continue;
                        }
                        // A generic struct's glue is generic over its parameters,
                        // named at the struct's instance at them.
                        let parameters = std::mem::replace(
                            &mut *adapter.callable_parameters.borrow_mut(),
                            adapter.callable_type_parameters(&f.generics)?,
                        );
                        let record = adapter.ty(record);
                        *adapter.callable_parameters.borrow_mut() = parameters;
                        let Type::Record { name } = record? else {
                            return Err(unsupported("drop glue of a non-record"));
                        };
                        adapter.drop_glues.insert(rec, id);
                        adapter.functions.insert(id, format!("{name}_drop_glue"));
                        continue;
                    }
                    // A closure's `Fn::call` is the closure; its `FnMut` and
                    // `FnOnce` methods only forward to it.
                    if matches!(
                        tr.item_meta.lang_item,
                        Some(LangItem::Fn | LangItem::FnMut | LangItem::FnOnce)
                    ) {
                        let imp = krate
                            .trait_impls
                            .get(impl_ref.id)
                            .ok_or_else(|| unsupported("missing Fn impl"))?;
                        // A function item's `Fn` methods forward to the item,
                        // which an `impl Fn` argument names directly.
                        if matches!(
                            imp.impl_trait.generics.types.first().map(|ty| ty.kind()),
                            Some(a::TyKind::FnDef(_))
                        ) {
                            continue;
                        }
                        let (closure, state) = adapter.closure_impl_path(imp).ok_or_else(|| {
                            unsupported("Fn trait implementation outside a closure")
                        })?;
                        if crate_config.is_none() {
                            return Err(unsupported("closure outside crate imports"));
                        }
                        if tr.item_meta.lang_item != Some(LangItem::Fn) {
                            continue;
                        }
                        adapter.closure_calls.insert(id, state);
                        let name = adapter.closure_name(closure)?;
                        adapter.functions.insert(id, name);
                        continue;
                    }
                    // A derived `clone` of a `Copy` type is the bitwise copy
                    // Click makes of every `Copy` value; a `Copy` bound
                    // reaches it as the supertrait's method, never a call.
                    if tr.item_meta.lang_item == Some(LangItem::Clone)
                        && krate.trait_impls.get(impl_ref.id).is_some_and(|imp| {
                            imp.item_meta.attr_info.attributes.iter().any(|attribute| {
                                matches!(
                                    attribute,
                                    a::Attribute::Builtin(
                                        charon_lib::ast::from_rustc::AttributeKind::AutomaticallyDerived
                                    )
                                )
                            })
                        })
                    {
                        continue;
                    }
                    if tr.item_meta.lang_item != Some(LangItem::Drop) {
                        let name = if adapter.is_default_method(f) {
                            adapter.default_constructor_name(f)?
                        } else if Adapter::is_core_iterator(tr) {
                            let name = adapter.user_iterator_next_name(f)?;
                            adapter.user_iterator_nexts.insert(name.clone());
                            name
                        } else {
                            adapter.assignment_operator_name(f)?
                        };
                        adapter.functions.insert(id, name);
                        continue;
                    }
                    let imp = krate
                        .trait_impls
                        .get(impl_ref.id)
                        .ok_or_else(|| unsupported("missing Drop impl"))?;
                    let rec = adapter.record_id(
                        imp.impl_trait
                            .generics
                            .types
                            .first()
                            .ok_or_else(|| unsupported("missing Drop receiver"))?,
                    )?;
                    if adapter.destructors.insert(rec, id).is_some() {
                        return Err(unsupported("duplicate destructor"));
                    }
                    format!("{}_drop", adapter.records[&rec])
                }
                // A `dyn Fn` value's vtable and its shims carry no behavior the
                // importer reads: a call through the value is checked against a
                // contract of the value, not the vtable's entries.
                a::FunSource::GlobalInitializer(reference)
                    if krate.global_decls.get(reference.id).is_some_and(|global| {
                        matches!(global.src, a::GlobalSource::VTableInstance { .. })
                    }) =>
                {
                    continue;
                }
                a::FunSource::VTableShim => continue,
                a::FunSource::GlobalInitializer(reference) => {
                    let name = adapter.constant_initializer_name(id, f, reference)?;
                    constant_initializers.insert(name.clone());
                    name
                }
                _ => return Err(unsupported("function source")),
            };
            let located = |error: String| {
                format!(
                    "{} in {name}: {error}",
                    refusal_location(&krate, source, f.item_meta.span, f.item_meta.span)
                )
            };
            if !adapter.crate_mode
                && matches!(adapter.ty(&f.signature.output)?, Type::Record { .. })
            {
                return Err(located(
                    "Rust reference/aggregate returns are not supported".into(),
                ));
            }
            // A box moves into a function and out of one by value; a reference
            // to a box is not supported.
            let boxed = |ty: &a::Ty| -> Result<bool, String> {
                Ok(match adapter.ty(ty) {
                    Ok(Type::Reference { pointee, .. }) => {
                        matches!(*pointee, Type::Box { .. } | Type::OptionBox { .. })
                    }
                    _ => false,
                })
            };
            if boxed(&f.signature.output)?
                || f.signature.inputs.iter().map(boxed).any(|b| b == Ok(true))
            {
                return Err(located(unsupported(
                    "reference to a box parameter or result",
                )));
            }
            // A `safe fn` in an `unsafe extern "C"` block is a declaration
            // without a body, whose calls a sidecar `extern fn` contract states.
            let abi = if matches!(f.body, a::Body::Extern(_)) {
                a::Abi::C
            } else {
                a::Abi::Rust
            };
            if f.signature.is_unsafe
                || f.signature.abi != abi
                || f.signature.is_variadic
                || (!f.generics.types.is_empty()
                    && (crate_config.is_none()
                        || adapter
                            .callable_type_parameters(&f.generics)?
                            .iter()
                            .any(Option::is_none)))
                || !f.generics.const_generics.is_empty()
            {
                return Err(unsupported("unsafe, foreign, or generic function"));
            }
            adapter.functions.insert(id, name);
        }
        Ok(())
    })()
    .map_err(|error| {
        if error.starts_with(&format!("{item_location}:"))
            || error.starts_with(&format!("{item_location} in "))
        {
            error
        } else {
            format!("{item_location}: {error}")
        }
    })?;
    // A `Drop` implementation runs before the glue drops the fields; a
    // struct with both is later work.
    if adapter
        .drop_glues
        .keys()
        .any(|id| adapter.destructors.contains_key(id))
    {
        return Err(unsupported("destructor of a struct holding a box"));
    }
    let mut records = Vec::new();
    for (id, name) in &adapter.records {
        let decl = &krate.type_decls[*id];
        let layout = decl
            .layout
            .get(out::TARGET)
            .ok_or_else(|| unsupported("missing target layout"))?;
        let variant = layout
            .variant_layouts
            .first()
            .and_then(Option::as_ref)
            .ok_or_else(|| unsupported("missing struct field layout"))?;
        let mut fields = Vec::new();
        for (field_id, field) in adapter.fields(*id)?.iter_enumerated() {
            let located = |error: String| {
                format!(
                    "{} in struct `{name}`, field `{}`: {error}",
                    refusal_location(&krate, source, field.span, decl.item_meta.span),
                    field.name,
                )
            };
            let ty = adapter.ty(&field.ty).map_err(located)?;
            if matches!(ty, Type::Record { .. } | Type::Unit) {
                return Err(located(unsupported("nested owned field")));
            }
            fields.push(out::Field {
                name: field.name.clone(),
                value_type: ty,
                offset: variant.field_offsets[field_id]
                    .chosen
                    .and_then(|v| u32::try_from(v).ok())
                    .ok_or_else(|| unsupported("missing field offset"))?,
            });
        }
        records.push(out::Record {
            name: name.clone(),
            size: concrete_size(&layout.size)?,
            alignment: concrete_size(&layout.align)?,
            fields,
            destructor: adapter
                .destructors
                .get(id)
                .or(adapter.drop_glues.get(id))
                .map(|f| adapter.functions[f].clone()),
            symbolic: false,
        });
    }
    let mut enums = Vec::new();
    for (id, name) in &adapter.enums {
        let a::TypeDeclKind::Enum(variants) = &krate.type_decls[*id].kind else {
            return Err(unsupported("enum declaration"));
        };
        let mut exported = Vec::new();
        for variant in variants.iter() {
            let mut fields = Vec::new();
            for field in variant.fields.iter() {
                let ty = adapter.ty(&field.ty)?;
                if !ty.is_scalar() {
                    return Err(unsupported("enum field other than an integer or bool"));
                }
                fields.push(ty);
            }
            exported.push(out::Variant {
                name: variant.name.clone(),
                field_names: if variant.fields.iter().any(|field| !field.is_positional) {
                    variant
                        .fields
                        .iter()
                        .map(|field| field.name.clone())
                        .collect()
                } else {
                    Vec::new()
                },
                fields,
            });
        }
        if exported.is_empty() {
            return Err(unsupported("enum without variants"));
        }
        enums.push(out::Enum {
            name: name.clone(),
            generic: None,
            arguments: Vec::new(),
            variants: exported,
        });
    }
    let mut functions = Vec::new();
    let mut used_names = BTreeSet::new();
    // Each source file parsed once, for its functions' statements as written.
    let mut parsed_files = BTreeMap::<usize, Option<syn::File>>::new();
    for (id, name) in &adapter.functions {
        if !used_names.insert(name) {
            return Err(unsupported("colliding proof function names"));
        }
        let f = &krate.fun_decls[*id];
        // An `impl Fn` parameter's type is the callable its bound names.
        *adapter.callable_parameters.borrow_mut() =
            adapter.callable_type_parameters(&f.generics)?;
        if let a::Body::Extern(_) = &f.body {
            functions.push(adapter.external_function(name, f)?);
            continue;
        }
        let a::Body::Unstructured(body) = &f.body else {
            return Err(unsupported("missing or non-CFG source body"));
        };
        // A closure's parameters are its captures, then the fields of its
        // argument tuple.
        let captures = adapter.closure_calls.get(id).map(|state| {
            adapter
                .closure_captures
                .get(state)
                .cloned()
                .unwrap_or_default()
        });
        let closure_body;
        let body = if let Some(captures) = &captures {
            closure_body = closures::closure_call_body(body, captures)?;
            &closure_body
        } else {
            body
        };
        // Drop glue's parameter is unnamed; its sidecar contract, as a
        // `Drop` method's, names it `self`.
        let glue_body;
        let body = if adapter.drop_glues.values().any(|glue| glue == id) {
            glue_body = {
                let mut body = body.clone();
                if let Some(receiver) = body.locals.locals.get_mut(1) {
                    receiver.name.get_or_insert_with(|| "self".into());
                }
                body
            };
            &glue_body
        } else {
            body
        };
        // A block that can only reach a panic is one obligation.
        let panic_body;
        let (body, panic_messages, panic_pruned) = if let Some(rewritten) = adapter.panic_body(body)
        {
            panic_body = rewritten.body;
            (&panic_body, rewritten.messages, rewritten.pruned)
        } else {
            (body, BTreeMap::new(), BTreeSet::new())
        };
        let try_body;
        let body = if let Some(rewritten) = adapter.option_try_body(body).map_err(|e| {
            format!(
                "{} in {name}: {e}",
                refusal_location(&krate, source, body.span, f.item_meta.span)
            )
        })? {
            try_body = rewritten;
            &try_body
        } else {
            body
        };
        let result_try_body;
        let body = if let Some(rewritten) = adapter.result_try_body(body).map_err(|e| {
            format!(
                "{} in {name}: {e}",
                refusal_location(&krate, source, body.span, f.item_meta.span)
            )
        })? {
            result_try_body = rewritten;
            &result_try_body
        } else {
            body
        };
        let take_body;
        let body = if let Some(rewritten) = adapter.option_take_body(body).map_err(|e| {
            format!(
                "{} in {name}: {e}",
                refusal_location(&krate, source, body.span, f.item_meta.span)
            )
        })? {
            take_body = rewritten;
            &take_body
        } else {
            body
        };
        let box_free_body;
        let body = if let Some(rewritten) = adapter.box_free_body(body).map_err(|e| {
            format!(
                "{} in {name}: {e}",
                refusal_location(&krate, source, body.span, f.item_meta.span)
            )
        })? {
            box_free_body = rewritten;
            &box_free_body
        } else {
            body
        };
        let box_drop_body;
        let body = if let Some(rewritten) = adapter.box_place_drop_body(body) {
            box_drop_body = rewritten;
            &box_drop_body
        } else {
            body
        };
        let referent_body;
        let body = if let Some(rewritten) = adapter.referent_match_body(body) {
            referent_body = rewritten;
            &referent_body
        } else {
            body
        };
        let vec_index_body;
        let body = if let Some(rewritten) = adapter.vec_index_body(body).map_err(|e| {
            format!(
                "{} in {name}: {e}",
                refusal_location(&krate, source, body.span, f.item_meta.span)
            )
        })? {
            vec_index_body = rewritten;
            &vec_index_body
        } else {
            body
        };
        let inputs = if let Some(captures) = &captures {
            closures::closure_parameter_types(&f.signature, captures)?
        } else {
            f.signature.inputs.clone()
        };
        if adapter.crate_mode {
            let return_local = body
                .locals
                .locals
                .first()
                .ok_or_else(|| unsupported("missing function return local"))?;
            if body.locals.arg_count != inputs.len()
                || adapter.ty(&return_local.ty)? != adapter.ty(&f.signature.output)?
            {
                return Err(unsupported("function body return/argument signature"));
            }
            for (local, ty) in body
                .locals
                .locals
                .iter()
                .skip(1)
                .take(body.locals.arg_count)
                .zip(&inputs)
            {
                if adapter.ty(&local.ty)? != adapter.ty(ty)? {
                    return Err(unsupported("function parameter local type"));
                }
            }
        }
        let (iterator_refs, iterator_discriminants) = protocol::bindings(&adapter, body)?;
        let enum_discriminants = adapter.enum_discriminants(body);
        let plumbing = adapter.closure_plumbing(body)?;
        let mut names = BTreeMap::new();
        let mut slice_pairs = BTreeMap::new();
        let mut anonymous_slice_components = BTreeSet::new();
        let mut parameters = Vec::new();
        let mut locals = Vec::new();
        let mut local_names = BTreeSet::new();
        let mut occurrences = BTreeMap::<&str, usize>::new();
        let return_place = out::return_place_id();
        // The locals the source does not name, apart from the return slot.
        let mut temporaries = BTreeSet::new();
        let mut spellings = BTreeMap::new();
        let mut spelled = BTreeSet::new();
        for local in &body.locals.locals {
            if let Some(name) = &local.name {
                *occurrences.entry(name).or_default() += 1;
            }
        }
        for local in &body.locals.locals {
            if plumbing.elided.contains(&local.index)
                || enum_discriminants.contains_key(&local.index)
                || panic_pruned.contains(&local.index)
            {
                continue;
            }
            let param = local.index.index() > 0 && local.index.index() <= body.locals.arg_count;
            let n = if param {
                local
                    .name
                    .clone()
                    .ok_or_else(|| unsupported("unnamed parameter"))?
                    .into()
            } else if let Some(name) = &local.name
                && occurrences[name.as_str()] == 1
                && local.index.index() != 0
            {
                name.clone().into()
            } else if local.index.index() == 0 {
                return_place.clone()
            } else {
                // A source name bound more than once, as `word` in two
                // `Some(word)` arms or `iter` in nested `for` loops, is one
                // declaration per binding, each spelled as the source spells
                // it (`spellings`), as C's are. Unnamed locals use their
                // compiler IDs in a namespace disjoint from source names.
                let generated = MirLocalId::Compiler(
                    u32::try_from(local.index.index())
                        .map_err(|_| unsupported("local index exceeds u32"))?,
                );
                match &local.name {
                    Some(name) => {
                        spellings.insert(generated.clone(), name.clone());
                        spelled.insert(local.index);
                    }
                    None => {
                        temporaries.insert(generated.clone());
                    }
                }
                generated
            };
            if !local_names.insert(n.clone()) {
                return Err(unsupported("local identity collision"));
            }
            names.insert(local.index, n.clone());
            if adapter.shared_slice_pair(&local.ty, false) {
                if param || local.index.index() == 0 {
                    return Err(unsupported("shared slice pair function boundary"));
                }
                let mut components = Vec::new();
                for component in 0..2 {
                    let component = MirLocalId::SliceComponent {
                        slot: u32::try_from(local.index.index())
                            .map_err(|_| unsupported("local index exceeds u32"))?,
                        component,
                    };
                    if local.name.is_none() {
                        anonymous_slice_components.insert(component.clone());
                    }
                    locals.push(out::Place {
                        name: component.clone(),
                        value_type: Type::ByteSlice { mutable: false },
                        span: span(local.span),
                    });
                    components.push(component);
                }
                slice_pairs.insert(local.index, components.try_into().unwrap());
                continue;
            }
            let place = out::Place {
                name: n,
                value_type: if iterator_discriminants.contains_key(&local.index) {
                    Type::Bool
                } else {
                    adapter.ty(&local.ty).map_err(|error| {
                        format!(
                            "{} in {name}: {error}",
                            refusal_location(&krate, source, local.span, f.item_meta.span)
                        )
                    })?
                },
                span: span(local.span),
            };
            if param {
                if !adapter.crate_mode && matches!(place.value_type, Type::Record { .. }) {
                    // Preserve the schema-3 value boundary and its existing diagnostic.
                    return Err("Rust value type outside direct scalar/reference lowering".into());
                }
                parameters.push(place);
            } else {
                locals.push(place);
            }
        }
        let b = BodyAdapter {
            adapter: &adapter,
            body,
            plumbing,
            names,
            spelled,
            slice_pairs,
            iterator_refs,
            iterator_discriminants,
            enum_discriminants,
            unsized_objects: traits::unsized_objects(&adapter, body),
            coercions: std::cell::RefCell::new(Vec::new()),
        };
        // The function's statements as written, and the one each MIR
        // statement and terminator comes from: the innermost whose source
        // holds where it starts, in the function's own file (a macro's code
        // is where the macro is called).
        let item_span = f.item_meta.span.data();
        let parsed = parsed_files
            .entry(item_span.file_id.index())
            .or_insert_with(|| {
                krate
                    .files
                    .get(item_span.file_id)
                    .and_then(|file| file.contents.as_deref())
                    .and_then(super::source_statements::parse)
            });
        let written = parsed
            .as_ref()
            .and_then(|file| {
                super::source_statements::function_source(
                    file,
                    (item_span.beg.line as usize, item_span.beg.col as usize),
                )
            })
            .unwrap_or_default();
        let site_of = |span: a::Span| -> Option<u32> {
            let at = [Some(span.data()), span.generated_from_span()]
                .into_iter()
                .flatten()
                .find(|data| data.file_id == item_span.file_id)?;
            super::source_statements::innermost(
                &written.statements,
                (at.beg.line as usize, at.beg.col as usize),
            )
            .map(|index| index as u32)
        };
        let mut blocks = Vec::new();
        let mut coercions = Vec::new();
        let mut literal_initializers = BTreeMap::new();
        let mut ambiguous_literals = BTreeSet::new();
        let written_range = |span: a::Span| {
            let at = span.data();
            if at.file_id != item_span.file_id || span.generated_from_span().is_some() {
                return None;
            }
            Some((
                (at.beg.line as usize, at.beg.col as usize),
                (at.end.line as usize, at.end.col as usize),
            ))
        };
        let literal_at = |span| {
            written
                .compound_literals
                .get(&written_range(span)?)
                .copied()
        };
        // Find the scalar backing objects before converting storage markers.
        let mut borrowed_occurrences = BTreeMap::<_, Option<a::LocalId>>::new();
        if !written.borrows.is_empty() {
            for statement in b.body.body.iter().flat_map(|block| &block.statements) {
                if let u::StatementKind::Assign(_, a::Rvalue::Ref { place, .. }) = &statement.kind
                    && let Some(local) = place.as_local()
                    && b.names
                        .get(&local)
                        .is_some_and(|name| temporaries.contains(name))
                    && let Some(&ordinal) =
                        written_range(statement.span).and_then(|range| written.borrows.get(&range))
                    && b.adapter.ty(&place.ty).is_ok_and(|ty| ty.is_scalar())
                {
                    // A span shared by two different objects cannot identify either.
                    borrowed_occurrences
                        .entry(ordinal)
                        .and_modify(|object| {
                            if *object != Some(local) {
                                *object = None;
                            }
                        })
                        .or_insert(Some(local));
                }
            }
        }
        let borrowed_scalars: BTreeMap<_, _> = borrowed_occurrences
            .into_iter()
            .filter_map(|(ordinal, local)| Some((local?, ordinal)))
            .collect();
        for (id, block) in b.body.body.iter_enumerated() {
            if let Some(message) = panic_messages.get(&id) {
                coercions.push((blocks.len(), Vec::new()));
                blocks.push(out::MirBlock {
                    terminator_site: None,
                    statements: Vec::new(),
                    terminator: T::Panic {
                        message: message.clone(),
                    },
                });
                continue;
            }
            let mut statements: Vec<S> = Vec::new();
            let mut current_site = None;
            for s in &block.statements {
                let converted = if let u::StatementKind::StorageLive(local) = &s.kind
                    && borrowed_scalars.contains_key(local)
                {
                    vec![S::BeginStorage {
                        local: b.local(*local)?,
                    }]
                } else {
                    match b.slice_pair_statement(s)? {
                        Some(statements) => statements,
                        None => b
                            .statement(s)
                            .map(|s| s.into_iter().collect::<Vec<_>>())
                            .map_err(|e| {
                                format!(
                                    "{} in {name}: {e}",
                                    refusal_location(&krate, source, s.span, f.item_meta.span)
                                )
                            })?,
                    }
                };
                if converted.is_empty() {
                    continue;
                }
                let site = site_of(s.span);
                if site != current_site
                    && let Some(site) = site
                {
                    statements.push(S::Site { site });
                }
                current_site = site;
                let literal_local = match converted.as_slice() {
                    [
                        S::Assign {
                            target: E::Local { name },
                            value: E::Array { .. } | E::Repeat { .. },
                        },
                    ] => Some(name),
                    [S::Initialize { target, .. }] => Some(target),
                    _ => None,
                };
                if let Some(name) = literal_local
                    && temporaries.contains(name)
                    && let u::StatementKind::Assign(place, _) = &s.kind
                    && let Some(local) = place.as_local()
                    && let Some(ordinal) = literal_at(s.span)
                    && literal_at(b.body.locals.locals[local].span) == Some(ordinal)
                    && literal_initializers.insert(ordinal, name.clone()).is_some()
                {
                    ambiguous_literals.insert(ordinal);
                }
                statements.extend(converted);
            }
            let terminator_site = site_of(block.terminator.span);
            let conversion = if matches!(
                b.adapter.borrowed_protocol_call(&block.terminator)?,
                Some(protocol::BorrowedProtocolCall::Into { .. })
            ) {
                None
            } else {
                b.modeled_call(&block.terminator)?
            };
            let forwarding = matches!(
                b.adapter.borrowed_protocol_call(&block.terminator)?,
                Some(protocol::BorrowedProtocolCall::Into { .. })
            );
            let terminator = if forwarding {
                let u::TerminatorKind::Call { target, .. } = &block.terminator.kind else {
                    unreachable!()
                };
                Ok(T::Goto {
                    target: target.index(),
                })
            } else if let Some(conversion) = conversion {
                if terminator_site != current_site
                    && let Some(site) = terminator_site
                {
                    statements.push(S::Site { site });
                }
                statements.push(conversion);
                let u::TerminatorKind::Call { target, .. } = &block.terminator.kind else {
                    unreachable!();
                };
                Ok(T::Goto {
                    target: target.index(),
                })
            } else {
                b.terminator(&block.terminator)
            }
            .map_err(|e| {
                format!(
                    "{} in {name}: {e}",
                    refusal_location(&krate, source, block.terminator.span, f.item_meta.span)
                )
            })?;
            coercions.push((blocks.len(), b.coercions.take()));
            blocks.push(out::MirBlock {
                terminator_site,
                statements,
                terminator,
            });
        }
        traits::wrap_object_coercions(&mut blocks, coercions)?;
        protocol::split_next_branches(&mut blocks)?;
        user_iterators::test_user_next_results(&mut blocks, &adapter.user_iterator_nexts);
        panics::assert_branches(&mut blocks);
        let parameter_types = parameters
            .iter()
            .map(|parameter| (parameter.name.clone(), parameter.value_type.clone()))
            .collect();
        temporaries::substitute_literals(&mut locals, &mut blocks, &temporaries, &parameter_types);
        temporaries::substitute_pure_values(
            &mut locals,
            &mut blocks,
            &temporaries,
            &constant_initializers,
        );
        temporaries::fold_callback_copies(&mut locals, &mut blocks, &temporaries, &parameter_types);
        temporaries::call_steps(&mut locals, &mut blocks, &temporaries);
        temporaries::collapse_iterator_moves(&mut locals, &mut blocks, &temporaries);
        temporaries::bind_range_payloads(&mut locals, &mut blocks, &temporaries);
        temporaries::bind_slice_payloads(&mut locals, &mut blocks, &temporaries);
        temporaries::bind_copied_slice_elements(&mut locals, &mut blocks, &temporaries);
        temporaries::bind_split_slice_results(
            &mut locals,
            &mut blocks,
            &anonymous_slice_components,
        );
        temporaries::bind_copied_call_arguments(&mut locals, &mut blocks, &temporaries);
        temporaries::return_values(&mut locals, &mut blocks, &return_place);
        temporaries::remove_unused(&mut locals, &mut blocks, &temporaries);
        temporaries::fold_try_result_aliases(&mut locals, &mut blocks, &temporaries);
        temporaries::fold_constructor_reborrows(&mut locals, &mut blocks, &temporaries);
        temporaries::fold_returned_slice_lengths(&mut locals, &mut blocks, &temporaries);
        temporaries::bind_copied_enum_scrutinees(
            &mut locals,
            &mut blocks,
            &temporaries,
            &parameter_types,
        );
        let kept: BTreeSet<_> = locals.iter().map(|local| &local.name).collect();
        spellings.retain(|key, _| kept.contains(key));
        temporaries.retain(|key| kept.contains(key));
        let compound_literals = literal_initializers
            .into_iter()
            .filter(|(ordinal, local)| {
                kept.contains(&local) && !ambiguous_literals.contains(ordinal)
            })
            .map(|(ordinal, local)| (local, ordinal))
            .collect();
        let borrowed_scalars = borrowed_scalars
            .into_iter()
            .filter_map(|(local, ordinal)| {
                let name = b.names.get(&local)?;
                kept.contains(name).then(|| (name.clone(), ordinal))
            })
            .collect();
        functions.push(out::Function {
            sites: written
                .statements
                .iter()
                .map(|statement| statement.path.clone())
                .collect(),
            name: name.clone(),
            return_type: adapter.ty(&f.signature.output).map_err(|error| {
                format!(
                    "{} in {name}: {error}",
                    refusal_location(&krate, source, f.item_meta.span, f.item_meta.span)
                )
            })?,
            parameters,
            body: vec![],
            mir: Some(out::MirBody {
                spellings,
                unnamed_locals: temporaries,
                compound_literals,
                borrowed_scalars,
                locals,
                blocks,
                return_place,
            }),
            external: false,
            captures: captures.as_ref().map_or(0, Vec::len),
            implements: adapter.trait_impl_methods.get(id).cloned(),
            instance_of: None,
            core_method: None,
            span: span(f.item_meta.span),
        });
    }
    // Each crate trait's methods are external functions, whose contracts are
    // the interfaces. A call through the trait reaches whichever
    // implementation the value has, so every one must be imported, to be
    // checked against them.
    for id in krate.trait_decls.iter_indexed().map(|(id, _)| id) {
        if !adapter.interface_trait(id)? {
            continue;
        }
        for function in adapter.interface_functions(id)? {
            if used_names.contains(&function.name) {
                return Err(unsupported("colliding proof function names"));
            }
            functions.push(function);
        }
    }
    for (record, trait_id, instance) in adapter.object_coercions.borrow().iter() {
        functions.extend(adapter.object_coercion_functions(record, *trait_id, instance)?);
    }
    // Each instance of a generic function a call names is declared at its
    // types, with the generic function's parameter names; its contract is
    // the generic function's, which is verified once for every type.
    for (name, (id, types)) in adapter.generic_instances.borrow().iter() {
        if used_names.contains(name) {
            return Err(unsupported("colliding proof function names"));
        }
        let generic_name = adapter
            .functions
            .get(id)
            .ok_or_else(|| unsupported("unmodeled generic function"))?;
        let generic = functions
            .iter()
            .find(|function| &function.name == generic_name)
            .ok_or_else(|| unsupported("generic function not imported"))?;
        let callee = &krate.fun_decls[*id];
        let (inputs, output) = adapter.signature_types_at(callee, types)?;
        let parameters = generic
            .parameters
            .iter()
            .zip(inputs)
            .map(|(parameter, value_type)| out::Place {
                name: parameter.name.clone(),
                value_type,
                span: parameter.span.clone(),
            })
            .collect();
        let instance = out::Function {
            sites: Vec::new(),
            name: name.clone(),
            return_type: output,
            parameters,
            body: vec![],
            mir: None,
            external: true,
            captures: 0,
            implements: None,
            instance_of: Some(generic_name.clone()),
            core_method: None,
            span: generic.span.clone(),
        };
        functions.push(instance);
    }
    for (name, function) in adapter.core_methods.borrow().iter() {
        if used_names.contains(name) {
            return Err(unsupported("colliding proof function names"));
        }
        functions.push(function.clone());
    }
    for imp in krate.trait_impls.iter() {
        let id = imp.impl_trait.id;
        if krate.trait_decls.get(id).is_none() || !adapter.interface_trait(id)? {
            continue;
        }
        if imp.methods.iter().count() != krate.trait_decls[id].methods.iter().count()
            || imp.methods.iter().any(|method| {
                let function = method.skip_binder.id;
                // A method the implementation does not write is the
                // trait's default, imported as the interface function.
                let default = krate.fun_decls.get(function).is_some_and(|f| {
                    matches!(&f.src, a::FunSource::TraitDefault { trait_ref, .. } if trait_ref.id == id)
                });
                !default && !adapter.trait_impl_methods.contains_key(&function)
            })
        {
            return Err(unsupported(
                "crate trait implementation method not imported",
            ));
        }
    }
    // Each instance of a generic struct the functions named, laid out in
    // declaration order. A field's type at the instance's arguments may name
    // further instances, `Option<Box<Node<T>>>`'s `Node<u32>`, which are laid
    // out in turn.
    let mut laid_out = BTreeSet::new();
    loop {
        let pending = adapter
            .record_instances
            .borrow()
            .iter()
            .filter(|(name, _)| !laid_out.contains(*name))
            .map(|(name, instance)| (name.clone(), instance.clone()))
            .collect::<Vec<_>>();
        if pending.is_empty() {
            break;
        }
        for (name, (id, arguments)) in pending {
            laid_out.insert(name.clone());
            let instance = arguments.iter().cloned().map(Some).collect::<Vec<_>>();
            let parameters = std::mem::replace(
                &mut *adapter.callable_parameters.borrow_mut(),
                instance.clone(),
            );
            let field_types = adapter
                .fields(id)?
                .iter()
                .map(|field| adapter.ty(&field.ty))
                .collect::<Result<Vec<_>, _>>();
            *adapter.callable_parameters.borrow_mut() = parameters;
            let field_types = field_types?;
            // A field of an abstract type takes `sizeof(T)` bytes, so the
            // instance's size and offsets are terms: it is laid out
            // symbolically, and the importer states no numbers for it.
            let symbolic = field_types
                .iter()
                .any(|ty| matches!(ty, out::Type::Parameter { .. }));
            let mut fields = Vec::new();
            let (mut size, mut alignment) = (0u32, 1u32);
            for (field, ty) in adapter.fields(id)?.iter().zip(field_types) {
                // A field is of one of the struct's parameters, at the
                // instance's argument, of a scalar type, or a box of a struct.
                let field_size = model_field_size(&ty).ok_or_else(|| {
                    unsupported("generic struct field other than a parameter, scalar or box")
                })?;
                let offset = size.next_multiple_of(field_size);
                size = offset + field_size;
                alignment = alignment.max(field_size);
                fields.push(out::Field {
                    name: field.name.clone(),
                    value_type: ty,
                    offset: if symbolic { 0 } else { offset },
                });
            }
            // The instance's drop glue, when the struct holds a box.
            let destructor = match adapter.drop_glues.get(&id) {
                Some(&glue) => {
                    let glue_name = format!("{name}_drop_glue");
                    if adapter.functions.get(&glue) != Some(&glue_name) {
                        adapter
                            .generic_instances
                            .borrow_mut()
                            .insert(glue_name.clone(), (glue, instance));
                    }
                    Some(glue_name)
                }
                None => None,
            };
            records.push(out::Record {
                name,
                size: if symbolic {
                    0
                } else {
                    size.next_multiple_of(alignment)
                },
                alignment,
                fields,
                destructor,
                symbolic,
            });
        }
    }
    // Each instance of a library enum, with its variants' fields at the
    // instance's arguments.
    for (name, (generic, arguments)) in adapter.enum_instances.borrow().iter() {
        let variant = |name: &str, fields: Vec<Type>| out::Variant {
            name: name.into(),
            field_names: Vec::new(),
            fields,
        };
        let exported = match (generic.as_str(), arguments.as_slice()) {
            ("Option", [payload]) => vec![
                variant("None", vec![]),
                variant("Some", vec![payload.clone()]),
            ],
            ("Result", [ok, err]) => vec![
                variant("Ok", vec![ok.clone()]),
                variant("Err", vec![err.clone()]),
            ],
            _ => return Err(unsupported("library enum instance")),
        };
        enums.push(out::Enum {
            name: name.clone(),
            generic: Some(generic.clone()),
            arguments: arguments.clone(),
            variants: exported,
        });
    }
    Ok(out::RustExport {
        schema: out::SCHEMA,
        compiler_commit: profile::get().compiler_commit.clone(),
        target: out::TARGET.into(),
        edition: "2024".into(),
        overflow_checks: true,
        panic: "abort".into(),
        mir_opt_level: 0,
        logical_source: source.into(),
        records,
        enums,
        functions,
    })
}

#[cfg(test)]
mod tests {
    #[test]
    fn charon_refusal_locations_keep_file_and_line_together() {
        let artifact: ExtractionArtifact = serde_json::from_slice(NESTED_ARTIFACT).unwrap();
        let krate = &artifact.data.translated;
        let owner = krate
            .fun_decls
            .iter()
            .find(|f| f.item_meta.is_local)
            .unwrap()
            .item_meta
            .span;
        let mut local = owner.data();
        local.beg.line = 2;
        local.end = local.beg;
        let mut foreign = local;
        foreign.file_id = a::FileId::from_usize(99_999);
        foreign.beg.line = 45;
        foreign.end = foreign.beg;
        let local_location = refusal_location(krate, "nested.rs", a::Span::new(local, None), owner);
        assert_eq!(local_location, "nested.rs:2");
        // A crate's entry file need not be the enclosing function's file.
        assert_eq!(
            refusal_location(krate, "root.rs", a::Span::new(local, None), owner),
            local_location
        );
        // Prefer the direct caller location when the generated code is foreign.
        assert_eq!(
            refusal_location(
                krate,
                "nested.rs",
                a::Span::new(local, Some(foreign)),
                owner
            ),
            local_location
        );
        // Also accept a caller location recorded in generated_from_span.
        assert_eq!(
            refusal_location(
                krate,
                "nested.rs",
                a::Span::new(foreign, Some(local)),
                owner
            ),
            local_location
        );
        // Never attach a foreign line to the caller's filename.
        assert_eq!(
            refusal_location(krate, "nested.rs", a::Span::new(foreign, None), owner),
            format!("nested.rs:{}", owner.data().beg.line)
        );
    }

    #[test]
    fn charon_plain_record_loop_starts_each_pass_with_fresh_storage() {
        let artifact = include_bytes!(
            "../../../design/charon-trial/plain-record-loop/.click/captures/loop/loop.rs.ullbc"
        );
        let source = include_bytes!("../../../design/charon-trial/plain-record-loop/loop.rs");
        let claim = include_str!("../../../design/charon-trial/plain-record-loop/loop.click");
        let export = decode(artifact, "loop.rs", source).unwrap();
        let prepared = super::super::import::prepared_for_test(export).unwrap();
        ProgramVerificationSession::new_program_prepared(claim, &prepared).unwrap();
    }

    fn loop_array_copy_export() -> out::RustExport {
        let source = include_bytes!("../../../design/charon-trial/loop-array-copy/quad.rs");
        let config: serde_json::Value = serde_json::from_slice(include_bytes!(
            "../../../design/charon-trial/loop-array-copy/click.project.json"
        ))
        .unwrap();
        let config = serde_json::from_value(config["units"]["quad"]["crate"].clone()).unwrap();
        let sources = BTreeMap::from([("quad.rs".into(), source.to_vec())]);
        decode_crate(
            include_bytes!(
                "../../../design/charon-trial/loop-array-copy/.click/captures/quad/quad.rs.ullbc"
            ),
            "quad.rs",
            source,
            Some(&config),
            Some(&sources),
        )
        .unwrap()
    }

    #[test]
    #[cfg(not(feature = "fast-gate"))]
    #[ignore = "nightly: 2s in the parallel gate"]
    fn charon_loop_array_copy_requires_fresh_initialized_storage() {
        let export = loop_array_copy_export();
        let claim = include_str!("../../../design/charon-trial/loop-array-copy/quad.click");
        for mutation in 0..4 {
            let mut altered = export.clone();
            let walk = altered
                .functions
                .iter_mut()
                .find(|f| f.name.ends_with("I4_walk"))
                .unwrap();
            let mir = walk.mir.as_mut().unwrap();
            let mut changed = false;
            match mutation {
                0 => {
                    for block in &mut mir.blocks {
                        block.statements.retain(|s| {
                            if matches!(s, S::BeginStorage { local } if local == "array") {
                                changed = true;
                                false
                            } else {
                                true
                            }
                        });
                    }
                }
                1 | 2 => {
                    for block in &mut mir.blocks {
                        if let Some(index) = block.statements.iter().position(|s|
                            matches!(s, S::Assign { target: E::Local { name }, .. } if name == "array")) {
                            if mutation == 1 {
                                block.statements.remove(index);
                            } else {
                                // A second lifetime cannot retain initialized bytes
                                // or readable states from its predecessor.
                                block.statements.insert(index + 1, S::BeginStorage { local: "array".into() });
                            }
                            changed = true;
                            break;
                        }
                    }
                }
                3 => {
                    let array = mir.locals.iter_mut().find(|p| p.name == "array").unwrap();
                    let Type::Array { length, .. } = &mut array.value_type else {
                        unreachable!()
                    };
                    *length = 3;
                    changed = true;
                }
                _ => unreachable!(),
            }
            assert!(changed);
            let rejected = match super::super::import::prepared_for_test(altered) {
                Err(_) => true,
                Ok(prepared) => {
                    ProgramVerificationSession::new_program_prepared(claim, &prepared).is_err()
                }
            };
            assert!(rejected, "accepted array storage mutation {mutation}");
        }
    }

    #[test]
    fn charon_array_storage_starts_keep_layout_and_lowering_compact() {
        let original = loop_array_copy_export();
        fn shape(s: &crate::kernel::ProgramStatement) -> (usize, usize) {
            use crate::kernel::ProgramStatement;
            match s {
                ProgramStatement::Seq(statements) => {
                    let mut total = (statements.len() - 1, 0);
                    for statement in statements.iter() {
                        let part = shape(statement);
                        total = (total.0 + part.0, total.1 + part.1);
                    }
                    total
                }
                ProgramStatement::DeclareAggregate { layout, .. } => (1, layout.fields().len()),
                ProgramStatement::If {
                    then_branch,
                    else_branch,
                    ..
                } => {
                    let a = shape(then_branch);
                    let b = shape(else_branch);
                    (1 + a.0 + b.0, a.1 + b.1)
                }
                ProgramStatement::Loop { body, .. } => {
                    let a = shape(body);
                    (1 + a.0, a.1)
                }
                _ => (1, 0),
            }
        }
        let mut samples = Vec::new();
        for length in [4, 1024, 1_000_000] {
            let mut export = original.clone();
            let mir = export
                .functions
                .iter_mut()
                .find(|f| f.name.ends_with("I4_walk"))
                .unwrap()
                .mir
                .as_mut()
                .unwrap();
            let local = mir.locals.iter_mut().find(|p| p.name == "array").unwrap();
            let Type::Array { length: count, .. } = &mut local.value_type else {
                unreachable!()
            };
            *count = length;
            // Only examine storage lowering: remove the four-element copy,
            // whose type deliberately does not change with the test length.
            for block in &mut mir.blocks {
                block.statements.retain(|s| !matches!(s, S::Assign { target: E::Local { name }, .. } if name == "array"));
            }
            let (functions, _) = super::super::lowering::lower(&export).unwrap();
            let walk = functions
                .iter()
                .find(|f| f.name().ends_with("I4_walk"))
                .unwrap()
                .to_kernel_function();
            samples.push(shape(walk.body()));
        }
        assert!(
            samples.iter().all(|sample| *sample == samples[0]),
            "{samples:?}"
        );
    }

    #[test]
    fn charon_storage_restart_cannot_erase_a_drop_record() {
        let mut export = decode(
            include_bytes!(
                "../../../design/charon-trial/borrowed-loop/.click/captures/loop/loop.rs.ullbc"
            ),
            "loop.rs",
            include_bytes!("../../../design/charon-trial/borrowed-loop/loop.rs"),
        )
        .unwrap();
        let function = export
            .functions
            .iter_mut()
            .find(|f| f.name == "guarded_walk")
            .unwrap();
        let block = function
            .mir
            .as_mut()
            .unwrap()
            .blocks
            .iter_mut()
            .find(|b| {
                b.statements
                    .iter()
                    .any(|s| matches!(s, S::Initialize { .. }))
            })
            .unwrap();
        let index = block
            .statements
            .iter()
            .position(|s| matches!(s, S::Initialize { .. }))
            .unwrap();
        let constructor = block.statements[index].clone();
        let S::Initialize { target, .. } = &constructor else {
            unreachable!()
        };
        block.statements.insert(
            index + 1,
            S::BeginStorage {
                local: target.clone(),
            },
        );
        block.statements.insert(index + 2, constructor);
        let prepared = super::super::import::prepared_for_test(export).unwrap();
        assert!(
            ProgramVerificationSession::new_program_prepared(
                include_str!("../../../design/charon-trial/borrowed-loop/loop.click"),
                &prepared,
            )
            .is_err()
        );
    }
    use super::*;
    use crate::surface::ProgramVerificationSession;
    const ARTIFACT: &[u8] =
        include_bytes!("../../../design/charon-trial/.click/captures/trial/trial.rs.ullbc");
    const SOURCE: &[u8] = include_bytes!("../../../design/charon-trial/trial.rs");

    const ARRAY_ARTIFACT: &[u8] = include_bytes!(
        "../../../design/charon-trial/conversions-arrays/.click/captures/arrays/arrays.rs.ullbc"
    );
    const ARRAY_SOURCE: &[u8] =
        include_bytes!("../../../design/charon-trial/conversions-arrays/arrays.rs");

    #[test]
    fn charon_chunks_keep_state_and_owned_moves() {
        let export = decode(
            include_bytes!(
                "../../../design/charon-trial/chunks/.click/captures/chunks/chunks.rs.ullbc"
            ),
            "chunks.rs",
            include_bytes!("../../../design/charon-trial/chunks/chunks.rs"),
        )
        .unwrap();
        let walk = export
            .functions
            .iter()
            .find(|f| f.name == "walk")
            .unwrap()
            .mir
            .as_ref()
            .unwrap();
        assert!(
            walk.blocks
                .iter()
                .flat_map(|b| &b.statements)
                .any(|s| matches!(s, S::ChunkMove { .. }))
        );
        assert_eq!(
            walk.blocks
                .iter()
                .filter(|b| matches!(
                    b.terminator,
                    T::If {
                        condition: E::ChunkHasNext { .. },
                        ..
                    }
                ))
                .count(),
            1
        );
        assert_eq!(
            walk.blocks
                .iter()
                .flat_map(|b| &b.statements)
                .filter(|s| matches!(s, S::ChunkNext { .. }))
                .count(),
            2
        );
    }

    #[test]
    #[cfg(not(feature = "fast-gate"))]
    #[ignore = "nightly: original chunk-iterator whole-sidecar proof measured at 16.9 s"]
    fn charon_chunks_original_sidecar_verifies() {
        let export = decode(
            include_bytes!(
                "../../../design/charon-trial/chunks/.click/captures/chunks/chunks.rs.ullbc"
            ),
            "chunks.rs",
            include_bytes!("../../../design/charon-trial/chunks/chunks.rs"),
        )
        .unwrap();
        let prepared = super::super::import::prepared_for_test(export).unwrap();
        ProgramVerificationSession::new_program_prepared(
            include_str!("../../../design/charon-trial/chunks/chunks.click"),
            &prepared,
        )
        .unwrap();
    }

    const OPERATOR_ARTIFACT: &[u8] = include_bytes!(
        "../../../design/charon-trial/assignment-operators/.click/captures/operators/operators.rs.ullbc"
    );
    const OPERATOR_SOURCE: &[u8] =
        include_bytes!("../../../design/charon-trial/assignment-operators/operators.rs");

    #[test]
    fn charon_assignment_operators_import_source_bodies_and_ordinary_calls() {
        let export = decode(OPERATOR_ARTIFACT, "operators.rs", OPERATOR_SOURCE).unwrap();
        for (caller, method) in [
            ("scaled", "U32X4_mul_assign_u32"),
            ("reduced", "U32X4_rem_assign_u32"),
            ("added", "U32X4_add_assign_ref_U32X4"),
        ] {
            let body = export.functions.iter().find(|f| f.name == method).unwrap();
            assert!(body.mir.is_some() && body.body.is_empty());
            let caller = export.functions.iter().find(|f| f.name == caller).unwrap();
            assert!(
                caller.mir.as_ref().unwrap().blocks.iter().any(
                    |b| matches!(&b.terminator, T::Call { function, .. } if function.source_name() == Some(method))
                )
            );
        }
    }

    #[test]
    #[cfg(not(feature = "fast-gate"))]
    #[ignore = "nightly: assignment-operator whole-sidecar proof measured at 13 s"]
    fn charon_assignment_operator_source_bodies_verify() {
        let export = decode(OPERATOR_ARTIFACT, "operators.rs", OPERATOR_SOURCE).unwrap();
        let prepared = super::super::import::prepared_for_test(export).unwrap();
        ProgramVerificationSession::new_program_prepared(
            include_str!("../../../design/charon-trial/assignment-operators/operators.click"),
            &prepared,
        )
        .unwrap();
    }

    #[test]
    fn charon_assignment_operators_reject_forged_identity_signatures_and_calls() {
        for mutation in 0..15 {
            let mut artifact: ExtractionArtifact =
                serde_json::from_slice(OPERATOR_ARTIFACT).unwrap();
            let krate = &mut artifact.data.translated;
            if mutation < 12 {
                let f = krate.fun_decls.iter_mut().find(|f| matches!(f.item_meta.name.name.last(), Some(a::PathElem::Ident(n, _)) if n == "mul_assign")).unwrap();
                let a::FunSource::TraitImpl {
                    trait_ref,
                    impl_ref,
                    ..
                } = &f.src
                else {
                    panic!()
                };
                match mutation {
                    0 => krate.trait_decls[trait_ref.id].item_meta.is_local = true,
                    1 => krate.trait_decls[trait_ref.id].is_unsafe = true,
                    2 => {
                        krate.trait_decls[trait_ref.id].item_meta.name.name[0] =
                            a::PathElem::Ident("impostor".into(), a::Disambiguator::ZERO)
                    }
                    3 => {
                        krate.trait_decls[trait_ref.id].item_meta.lang_item =
                            Some(LangItem::AddAssign)
                    }
                    4 => krate.trait_impls[impl_ref.id].is_negative = true,
                    5 => krate.trait_impls[impl_ref.id].is_unsafe = true,
                    6 => krate.trait_impls[impl_ref.id].item_meta.is_local = false,
                    7 => f.signature.is_unsafe = true,
                    8 => f.signature.output = f.signature.inputs[1].clone(),
                    9 => f.signature.inputs[0] = f.signature.inputs[1].clone(),
                    10 => f.signature.inputs[1] = f.signature.inputs[0].clone(),
                    11 => {
                        f.item_meta.name.name[2] =
                            a::PathElem::Ident("add_assign".into(), a::Disambiguator::ZERO)
                    }
                    _ => unreachable!(),
                }
            } else {
                let f = krate.fun_decls.iter_mut().find(|f| matches!(f.item_meta.name.name.last(), Some(a::PathElem::Ident(n, _)) if n == "scaled")).unwrap();
                let a::Body::Unstructured(body) = &mut f.body else {
                    panic!()
                };
                let call = body
                    .body
                    .iter_mut()
                    .find_map(|b| match &mut b.terminator.kind {
                        u::TerminatorKind::Call { call, .. } => Some(call),
                        _ => None,
                    })
                    .unwrap();
                match mutation {
                    12 => call.args[0] = call.args[1].clone(),
                    13 => call.args.clear(),
                    14 => {
                        let a::FnOperand::Regular(ptr) = &mut call.func else {
                            panic!()
                        };
                        ptr.generics.regions.clear();
                    }
                    _ => unreachable!(),
                }
            }
            assert!(
                decode(
                    &serde_json::to_vec(&artifact).unwrap(),
                    "operators.rs",
                    OPERATOR_SOURCE
                )
                .is_err(),
                "mutation {mutation}"
            );
        }
    }

    const ITERATION_ARTIFACT: &[u8] = include_bytes!(
        "../../../design/charon-trial/array-iteration/.click/captures/iteration/iteration.rs.ullbc"
    );
    const ITERATION_SOURCE: &[u8] =
        include_bytes!("../../../design/charon-trial/array-iteration/iteration.rs");
    const ITERATION_CLAIM: &str =
        include_str!("../../../design/charon-trial/array-iteration/iteration.click");

    #[test]
    #[cfg(not(feature = "fast-gate"))]
    #[ignore = "nightly: 1.7s in the parallel gate"]
    fn charon_shared_array_iteration_keeps_typed_state_and_both_next_edges() {
        let export = decode(ITERATION_ARTIFACT, "iteration.rs", ITERATION_SOURCE).unwrap();
        let mir = export
            .functions
            .iter()
            .find(|f| f.name == "borrowed")
            .unwrap()
            .mir
            .as_ref()
            .unwrap();
        assert!(mir.locals.iter().any(|l| matches!(&l.value_type, Type::SharedArrayIterator { element } if **element == Type::U32)));
        assert_eq!(
            mir.blocks
                .iter()
                .filter(|b| matches!(
                    b.terminator,
                    T::If {
                        condition: E::SharedArrayHasNext { .. },
                        ..
                    }
                ))
                .count(),
            1
        );
        assert_eq!(
            mir.blocks
                .iter()
                .flat_map(|b| &b.statements)
                .filter(|s| matches!(s, S::SharedArrayNext { .. }))
                .count(),
            2
        );
        // MIR builds the iterator in a temporary and moves it into the
        // loop's; the move collapses, so the loop's local is built directly.
        let statements = || mir.blocks.iter().flat_map(|b| &b.statements);
        assert_eq!(
            statements()
                .filter(|s| matches!(s, S::SharedArrayInitialize { .. }))
                .count(),
            1
        );
        assert!(!statements().any(|s| matches!(s, S::SharedArrayMove { .. })));
        let prepared = super::super::import::prepared_for_test(export).unwrap();
        ProgramVerificationSession::new_program_prepared(ITERATION_CLAIM, &prepared).unwrap();
    }

    #[test]
    #[cfg(not(feature = "fast-gate"))]
    #[ignore = "nightly: 0.7s in the parallel gate"]
    fn charon_shared_iteration_rejects_forged_declarations_signatures_and_paths() {
        for mutation in 0..8 {
            let mut artifact: ExtractionArtifact =
                serde_json::from_slice(ITERATION_ARTIFACT).unwrap();
            let callee =
                artifact
                    .data
                    .translated
                    .fun_decls
                    .iter_mut()
                    .find(|f| {
                        f.item_meta.name.name.last().is_some_and(
                            |p| matches!(p, a::PathElem::Ident(name, _) if name == "next"),
                        )
                    })
                    .unwrap();
            match mutation {
                0 => callee.item_meta.is_local = true,
                1 => callee.signature.is_unsafe = true,
                2 => callee.signature.output = callee.signature.inputs[0].clone(),
                3..=5 => {
                    let a::FunSource::TraitImpl {
                        trait_ref,
                        impl_ref,
                        ..
                    } = &callee.src
                    else {
                        panic!()
                    };
                    match mutation {
                        3 => {
                            artifact.data.translated.trait_decls[trait_ref.id]
                                .item_meta
                                .diagnostic_item = Some("Lookalike".into())
                        }
                        4 => artifact.data.translated.trait_impls[impl_ref.id].is_negative = true,
                        5 => {
                            artifact.data.translated.trait_impls[impl_ref.id]
                                .item_meta
                                .name
                                .name[0] =
                                a::PathElem::Ident("impostor".into(), a::Disambiguator::ZERO);
                            callee.item_meta.name.name[0] =
                                a::PathElem::Ident("impostor".into(), a::Disambiguator::ZERO);
                        }
                        _ => unreachable!(),
                    }
                }
                6 => {
                    artifact
                        .data
                        .translated
                        .type_decls
                        .iter_mut()
                        .find(|t| t.item_meta.lang_item == Some(LangItem::Option))
                        .unwrap()
                        .item_meta
                        .is_local = true
                }
                7 => callee.signature.inputs.clear(),
                _ => unreachable!(),
            }
            assert!(
                decode(
                    &serde_json::to_vec(&artifact).unwrap(),
                    "iteration.rs",
                    ITERATION_SOURCE
                )
                .is_err(),
                "mutation {mutation}"
            );
        }
    }

    #[test]
    fn charon_shared_iteration_rejects_uninitialized_state() {
        // An iterator moves as a plain value, its fields; a move from a
        // consumed iterator is the compiler's to reject, as it is for a
        // range or a chunk iterator. One never built has no state to read.
        let mut export = decode(ITERATION_ARTIFACT, "iteration.rs", ITERATION_SOURCE).unwrap();
        export.functions.retain(|f| f.name == "signed");
        let mir = export.functions[0].mir.as_mut().unwrap();
        for block in &mut mir.blocks {
            block
                .statements
                .retain(|s| !matches!(s, S::SharedArrayInitialize { .. }));
        }
        let prepared = super::super::import::prepared_for_test(export).unwrap();
        let claim = "verifying \"iteration.rs\"; fn signed(words: &[i32; 4]) -> i32 { views words[0..4]; ensures result == old(words[0]); }";
        assert!(ProgramVerificationSession::new_program_prepared(claim, &prepared).is_err());
    }

    const OWNED_ARRAY_ARTIFACT: &[u8] = include_bytes!(
        "../../../design/charon-trial/owned-array-fields/.click/captures/owned/owned.rs.ullbc"
    );
    const OWNED_ARRAY_SOURCE: &[u8] =
        include_bytes!("../../../design/charon-trial/owned-array-fields/owned.rs");
    const FIELDS_ARTIFACT: &[u8] = include_bytes!(
        "../../../design/charon-trial/array-fields/.click/captures/fields/fields.rs.ullbc"
    );
    const FIELDS_SOURCE: &[u8] =
        include_bytes!("../../../design/charon-trial/array-fields/fields.rs");
    #[test]
    fn charon_array_fields_reject_overlapping_layouts_and_forged_mutability() {
        let mut export = decode(FIELDS_ARTIFACT, "fields.rs", FIELDS_SOURCE).unwrap();
        let original = export.clone();
        let record = export
            .records
            .iter_mut()
            .find(|r| r.name == "Lanes")
            .unwrap();
        record
            .fields
            .iter_mut()
            .find(|f| f.name == "marker")
            .unwrap()
            .offset = 0;
        assert!(
            super::super::lowering::lower(&export)
                .unwrap_err()
                .contains("invalid layout")
        );
        export = original;
        let function = export
            .functions
            .iter_mut()
            .find(|f| f.name == "borrowed_first")
            .unwrap();
        // The field borrow is a statement's value or, passed to a call, the
        // call's argument.
        let mut changed = false;
        for block in &mut function.mir.as_mut().unwrap().blocks {
            let arguments = match &mut block.terminator {
                T::Call { arguments, .. } => arguments.iter_mut().collect::<Vec<_>>(),
                _ => Vec::new(),
            };
            let values = block
                .statements
                .iter_mut()
                .filter_map(|statement| match statement {
                    S::Assign { value, .. } => Some(value),
                    _ => None,
                })
                .chain(arguments);
            for value in values {
                if let E::Borrow {
                    value_type: Type::Reference { mutable, .. },
                    place,
                } = value
                    && matches!(place.as_ref(), E::Field { .. })
                {
                    *mutable = true;
                    changed = true;
                }
            }
        }
        assert!(changed);
        let Err(error) = super::super::lowering::lower(&export) else {
            panic!("forged mutable array borrow must be rejected");
        };
        assert!(error.contains("mutable array field borrow"));
    }

    const ARITHMETIC_ARTIFACT: &[u8] = include_bytes!(
        "../../../design/charon-trial/arithmetic/.click/captures/arithmetic/arithmetic.rs.ullbc"
    );
    const ARITHMETIC_SOURCE: &[u8] =
        include_bytes!("../../../design/charon-trial/arithmetic/arithmetic.rs");

    #[test]
    fn charon_checksum_operators_reject_wrapping_and_unchecked_modes() {
        for name in ["quotient", "reduce", "wide_left", "wide_right"] {
            for mode in [a::OverflowMode::Wrap, a::OverflowMode::UB] {
                let mut artifact: ExtractionArtifact =
                    serde_json::from_slice(ARITHMETIC_ARTIFACT).unwrap();
                let function = artifact.data.translated.fun_decls.iter_mut().find(|f| matches!(f.item_meta.name.name.last(), Some(a::PathElem::Ident(n, _)) if n == name)).unwrap();
                let a::Body::Unstructured(body) = &mut function.body else {
                    panic!()
                };
                let mut changed = false;
                for statement in body.body.iter_mut().flat_map(|block| &mut block.statements) {
                    let u::StatementKind::Assign(_, a::Rvalue::BinaryOp(operator, _, _)) =
                        &mut statement.kind
                    else {
                        continue;
                    };
                    match operator {
                        a::BinOp::Div(m)
                        | a::BinOp::Rem(m)
                        | a::BinOp::Shl(m)
                        | a::BinOp::Shr(m) => {
                            *m = mode;
                            changed = true;
                        }
                        _ => (),
                    }
                }
                assert!(changed);
                let error = decode(
                    &serde_json::to_vec(&artifact).unwrap(),
                    "arithmetic.rs",
                    ARITHMETIC_SOURCE,
                )
                .unwrap_err();
                assert!(
                    error.contains("binary operation or overflow mode"),
                    "{error}"
                );
            }
        }
    }

    #[test]
    fn charon_checksum_unsigned_operator_types_must_match() {
        let mut artifact: ExtractionArtifact = serde_json::from_slice(ARITHMETIC_ARTIFACT).unwrap();
        let function = artifact.data.translated.fun_decls.iter_mut().find(|f| matches!(f.item_meta.name.name.last(), Some(a::PathElem::Ident(n, _)) if n == "quotient")).unwrap();
        let a::Body::Unstructured(body) = &mut function.body else {
            panic!()
        };
        let mut changed = false;
        for statement in body.body.iter_mut().flat_map(|block| &mut block.statements) {
            let u::StatementKind::Assign(_, a::Rvalue::BinaryOp(a::BinOp::Div(_), _, operand)) =
                &mut statement.kind
            else {
                continue;
            };
            let (a::Operand::Copy(right) | a::Operand::Move(right)) = operand else {
                continue;
            };
            right.ty =
                a::TyKind::Scalar(a::ScalarTy::Integer(a::IntegerTy::Unsigned(a::UIntTy::U16)))
                    .into_ty();
            changed = true;
        }
        assert!(changed);
        assert!(
            decode(
                &serde_json::to_vec(&artifact).unwrap(),
                "arithmetic.rs",
                ARITHMETIC_SOURCE
            )
            .is_err()
        );
    }

    const NESTED_ARTIFACT: &[u8] = include_bytes!(
        "../../../design/charon-trial/nested/.click/captures/nested/nested.rs.ullbc"
    );
    const NESTED_SOURCE: &[u8] = include_bytes!("../../../design/charon-trial/nested/nested.rs");

    #[test]
    fn charon_nested_loops_keep_distinct_iterator_identities() {
        let export = decode(NESTED_ARTIFACT, "nested.rs", NESTED_SOURCE).unwrap();
        let mir = export
            .functions
            .iter()
            .find(|f| f.name == "nested")
            .unwrap()
            .mir
            .as_ref()
            .unwrap();
        assert_eq!(
            mir.locals
                .iter()
                .map(|p| &p.name)
                .collect::<BTreeSet<_>>()
                .len(),
            mir.locals.len()
        );
        assert_eq!(
            mir.blocks
                .iter()
                .filter(|b| matches!(
                    b.terminator,
                    T::If {
                        condition: E::ChunkHasNext { .. },
                        ..
                    }
                ))
                .count(),
            2
        );
        let (functions, _) = super::super::lowering::lower(&export).unwrap();
        let kernel = functions
            .iter()
            .find(|f| f.name() == "nested")
            .unwrap()
            .to_kernel_function();
        fn visit(s: &crate::kernel::ProgramStatement, depth: usize, loops: &mut Vec<usize>) {
            use crate::kernel::ProgramStatement as C;
            match s {
                C::Seq(statements) => {
                    for statement in statements.iter() {
                        visit(statement, depth, loops);
                    }
                }
                C::Loop { body, .. } => {
                    loops.push(depth);
                    visit(body, depth + 1, loops);
                }
                C::If {
                    then_branch,
                    else_branch,
                    ..
                } => {
                    visit(then_branch, depth, loops);
                    visit(else_branch, depth, loops);
                }
                _ => (),
            }
        }
        let mut loops = Vec::new();
        visit(kernel.body(), 0, &mut loops);
        assert_eq!(loops, [0, 1]);
    }

    #[test]
    fn charon_compiler_locals_have_typed_identities_disjoint_from_source_names() {
        let mut artifact: ExtractionArtifact = serde_json::from_slice(NESTED_ARTIFACT).unwrap();
        let body = artifact.data.translated.fun_decls.iter_mut().find_map(|function| {
            if !matches!(function.item_meta.name.name.last(), Some(a::PathElem::Ident(name, _)) if name == "nested") { return None; }
            let a::Body::Unstructured(body) = &mut function.body else { return None; };
            Some(body)
        }).unwrap();
        // A source local named `result` is independent of the return ID.
        body.locals.locals[a::LocalId::from_usize(1)].name = Some("result".into());
        body.locals.locals[a::LocalId::from_usize(7)].name = Some("__rust_mir_8".into());
        let export = decode(
            &serde_json::to_vec(&artifact).unwrap(),
            "nested.rs",
            NESTED_SOURCE,
        )
        .unwrap();
        let function = export
            .functions
            .iter()
            .find(|f| f.name == "nested")
            .unwrap();
        let names = function
            .parameters
            .iter()
            .chain(&function.mir.as_ref().unwrap().locals)
            .map(|p| &p.name)
            .collect::<Vec<_>>();
        assert_eq!(
            names.iter().copied().collect::<BTreeSet<_>>().len(),
            names.len()
        );
        assert!(names.iter().any(|n| n.source_name() == Some("result")));
        assert_eq!(
            function.mir.as_ref().unwrap().return_place,
            out::return_place_id()
        );
        assert!(names.iter().any(|n| **n == MirLocalId::Compiler(8)));
    }

    #[test]
    fn charon_array_unsize_rejects_mismatched_metadata_and_reference_types() {
        for mutation in 0..4 {
            let mut artifact: ExtractionArtifact = serde_json::from_slice(NESTED_ARTIFACT).unwrap();
            let mut changed = false;
            'functions: for function in artifact.data.translated.fun_decls.iter_mut() {
                let a::Body::Unstructured(body) = &mut function.body else {
                    continue;
                };
                for statement in body.body.iter_mut().flat_map(|block| &mut block.statements) {
                    let u::StatementKind::Assign(
                        _,
                        a::Rvalue::UnaryOp(
                            a::UnOp::Cast(a::CastKind::Unsize(
                                source,
                                destination,
                                a::UnsizingMetadata::Length(length),
                            )),
                            _,
                        ),
                    ) = &mut statement.kind
                    else {
                        continue;
                    };
                    match mutation {
                        0 => *length = a::ConstantExpr::mk_usize(9),
                        1 => std::mem::swap(source, destination),
                        2 => source.with_kind_mut(|kind| {
                            let a::TyKind::Ref(_, _, ref_kind) = kind else {
                                panic!()
                            };
                            *ref_kind = a::RefKind::Mut;
                        }),
                        3 => destination.with_kind_mut(|kind| {
                            let a::TyKind::Ref(_, _, ref_kind) = kind else {
                                panic!()
                            };
                            *ref_kind = a::RefKind::Mut;
                        }),
                        _ => unreachable!(),
                    }
                    changed = true;
                    break 'functions;
                }
            }
            assert!(changed);
            assert!(
                decode(
                    &serde_json::to_vec(&artifact).unwrap(),
                    "nested.rs",
                    NESTED_SOURCE
                )
                .is_err(),
                "mutation {mutation}"
            );
        }
    }

    #[test]
    fn charon_array_unsize_metadata_has_bounded_work_across_lengths() {
        let export = decode(NESTED_ARTIFACT, "nested.rs", NESTED_SOURCE).unwrap();
        let prepared = super::super::import::prepared_for_test(export).unwrap();
        // Standard-library initialization is fixed work, independent of the
        // array length. Warm it outside the metadata scaling measurement.
        {
            let _session = crate::kernel::VerificationSession::enter();
            crate::surface::verify_c_sources(
                "theorem warm_array_metadata_library() { ensures 0 == 0 by close(); }",
                &[],
            )
            .unwrap();
        }
        let mut samples = Vec::new();
        for (name, length) in [
            ("empty_array_len", 0),
            ("array_len", 8),
            ("medium_array_len", 1024),
            ("large_array_len", 1_000_000),
        ] {
            let _session = crate::kernel::VerificationSession::enter();
            let claim = format!(
                "verifying \"nested.rs\"; fn {name}() -> usize {{ ensures result == {length}u64; }}"
            );
            let (verified, work) = crate::instrumentation::measure_deterministic_work(|| {
                ProgramVerificationSession::new_program_prepared(&claim, &prepared)
            });
            verified.unwrap();
            samples.push(work);
        }
        assert!(
            samples.iter().all(|work| *work <= 40_000)
                && samples[1..]
                    .iter()
                    .all(|work| work.abs_diff(samples[1]) <= 128),
            "{samples:?}"
        );
    }

    const CHUNK_ARTIFACT: &[u8] = include_bytes!(
        "../../../design/charon-trial/chunks/.click/captures/chunks/chunks.rs.ullbc"
    );
    const CHUNK_SOURCE: &[u8] = include_bytes!("../../../design/charon-trial/chunks/chunks.rs");

    #[test]
    #[cfg(not(feature = "fast-gate"))]
    #[ignore = "nightly: 0.5s in the parallel gate"]
    fn charon_chunk_models_check_resolved_identity_and_signature() {
        for mutation in 0..7 {
            let mut artifact: ExtractionArtifact = serde_json::from_slice(CHUNK_ARTIFACT).unwrap();
            let callee =
                artifact
                    .data
                    .translated
                    .fun_decls
                    .iter_mut()
                    .find(|f| {
                        f.item_meta.name.name.last().is_some_and(
                            |p| matches!(p, a::PathElem::Ident(name, _) if name == "next"),
                        )
                    })
                    .unwrap();
            match mutation {
                0 => callee.item_meta.is_local = true,
                1 => callee.signature.is_unsafe = true,
                2 => callee.signature.output = callee.signature.inputs[0].clone(),
                3..=5 => {
                    let a::FunSource::TraitImpl {
                        trait_ref,
                        impl_ref,
                        ..
                    } = &callee.src
                    else {
                        panic!()
                    };
                    if mutation == 3 {
                        artifact.data.translated.trait_decls[trait_ref.id]
                            .item_meta
                            .diagnostic_item = Some("Lookalike".into());
                    }
                    if mutation == 4 {
                        artifact.data.translated.trait_impls[impl_ref.id].is_negative = true;
                    }
                    if mutation == 5 {
                        artifact.data.translated.trait_impls[impl_ref.id]
                            .impl_trait
                            .generics
                            .types
                            .clear();
                    }
                }
                6 => {
                    let option = artifact
                        .data
                        .translated
                        .type_decls
                        .iter_mut()
                        .find(|t| t.item_meta.lang_item == Some(LangItem::Option))
                        .unwrap();
                    option.item_meta.is_local = true;
                }
                _ => unreachable!(),
            }
            assert!(
                decode(
                    &serde_json::to_vec(&artifact).unwrap(),
                    "chunks.rs",
                    CHUNK_SOURCE
                )
                .is_err(),
                "mutation {mutation}"
            );
        }
    }

    #[test]
    #[cfg(not(feature = "fast-gate"))]
    #[ignore = "nightly: 5 s, it verifies the whole sidecar (2026-11-11)"]
    fn charon_chunk_missing_initialization_fails_and_a_duplicate_move_copies_a_value() {
        // Under the library model an iterator is a value. One never
        // initialized is refused where it is read. A repeated move, which
        // the compiler never emits, copies the same value and is accepted:
        // the hidden-state model's liveness flag refused it, and that flag
        // went with the hidden state (`design/rust-iterators.md`).
        for duplicate in [false, true] {
            let mut export = decode(CHUNK_ARTIFACT, "chunks.rs", CHUNK_SOURCE).unwrap();
            let name = if duplicate { "walk" } else { "tail" };
            let mir = export
                .functions
                .iter_mut()
                .find(|f| f.name == name)
                .unwrap()
                .mir
                .as_mut()
                .unwrap();
            if duplicate {
                let block = mir
                    .blocks
                    .iter_mut()
                    .find(|b| {
                        b.statements
                            .iter()
                            .any(|s| matches!(s, S::ChunkMove { .. }))
                    })
                    .unwrap();
                let index = block
                    .statements
                    .iter()
                    .position(|s| matches!(s, S::ChunkMove { .. }))
                    .unwrap();
                block
                    .statements
                    .insert(index + 1, block.statements[index].clone());
            } else {
                for block in &mut mir.blocks {
                    block
                        .statements
                        .retain(|s| !matches!(s, S::ChunkInitialize { .. }));
                }
            }
            // The fixture's unit imports its iterators as library values.
            let prepared = super::super::import::prepared_for_test(export).unwrap();
            // The repeated move reads the iterator once more, so the loop
            // body's first byte read is one read later.
            let sidecar = include_str!("../../../design/charon-trial/chunks/chunks.click");
            let sidecar = if duplicate {
                sidecar.replace("step_until(read(1).entry)", "step_until(read(2).entry)")
            } else {
                sidecar.to_string()
            };
            assert_eq!(
                ProgramVerificationSession::new_program_prepared(&sidecar, &prepared).is_err(),
                !duplicate,
                "duplicate={duplicate}"
            );
        }
    }

    #[test]
    fn charon_chunk_option_projection_checks_variant_and_field() {
        let mut artifact: ExtractionArtifact = serde_json::from_slice(CHUNK_ARTIFACT).unwrap();
        let mut changed = false;
        for function in artifact.data.translated.fun_decls.iter_mut() {
            let a::Body::Unstructured(body) = &mut function.body else {
                continue;
            };
            for statement in body.body.iter_mut().flat_map(|block| &mut block.statements) {
                let u::StatementKind::Assign(_, a::Rvalue::Use(a::Operand::Copy(place), _)) =
                    &mut statement.kind
                else {
                    continue;
                };
                let a::PlaceKind::Projection(_, a::ProjectionElem::Field(Some(variant), field)) =
                    &mut place.kind
                else {
                    continue;
                };
                if variant.index() == 1 && field.index() == 0 {
                    *field = a::FieldId::from_usize(1);
                    changed = true;
                }
            }
        }
        assert!(changed);
        let error = decode(
            &serde_json::to_vec(&artifact).unwrap(),
            "chunks.rs",
            CHUNK_SOURCE,
        )
        .unwrap_err();
        assert!(error.contains("iterator Option projection"), "{error}");
    }

    const SLICE_ARTIFACT: &[u8] = include_bytes!(
        "../../../design/charon-trial/slices/.click/captures/slices/slices.rs.ullbc"
    );
    const SLICE_SOURCE: &[u8] = include_bytes!("../../../design/charon-trial/slices/slices.rs");

    #[test]
    fn charon_slice_length_checks_declaration_identity_and_types() {
        for mutation in 0..4 {
            let mut artifact: ExtractionArtifact = serde_json::from_slice(SLICE_ARTIFACT).unwrap();
            let callee = artifact
                .data
                .translated
                .fun_decls
                .iter_mut()
                .find(|f| f.item_meta.lang_item == Some(LangItem::SliceLen))
                .unwrap();
            match mutation {
                0 => callee.item_meta.lang_item = None,
                1 => callee.item_meta.is_local = true,
                2 => callee.signature.is_unsafe = true,
                3 => callee.signature.inputs.clear(),
                _ => unreachable!(),
            }
            assert!(
                decode(
                    &serde_json::to_vec(&artifact).unwrap(),
                    "slices.rs",
                    SLICE_SOURCE
                )
                .is_err()
            );
        }
    }

    #[test]
    fn charon_slice_reborrow_rejects_unrelated_metadata() {
        let mut artifact: ExtractionArtifact = serde_json::from_slice(SLICE_ARTIFACT).unwrap();
        let mut changed = false;
        for function in artifact.data.translated.fun_decls.iter_mut() {
            let a::Body::Unstructured(body) = &mut function.body else {
                continue;
            };
            for statement in body.body.iter_mut().flat_map(|block| &mut block.statements) {
                let u::StatementKind::Assign(
                    _,
                    a::Rvalue::Ref {
                        place,
                        ptr_metadata,
                        ..
                    },
                ) = &mut statement.kind
                else {
                    continue;
                };
                if !byte_slice(&place.ty) {
                    continue;
                }
                let (a::Operand::Copy(metadata) | a::Operand::Move(metadata)) = ptr_metadata else {
                    panic!("expected slice metadata projection")
                };
                let a::PlaceKind::Projection(base, a::ProjectionElem::PtrMetadata) =
                    &mut metadata.kind
                else {
                    panic!("expected slice metadata projection")
                };
                base.kind = a::PlaceKind::Local(a::LocalId::from_usize(0));
                changed = true;
            }
        }
        assert!(changed);
        let error = decode(
            &serde_json::to_vec(&artifact).unwrap(),
            "slices.rs",
            SLICE_SOURCE,
        )
        .unwrap_err();
        assert!(error.contains("pointer/metadata/type mismatch"), "{error}");
    }

    #[test]
    fn charon_unsigned_from_checks_resolved_identity_and_signature() {
        for mutation in 0..4 {
            let mut artifact: ExtractionArtifact = serde_json::from_slice(ARRAY_ARTIFACT).unwrap();
            let tr = artifact
                .data
                .translated
                .trait_decls
                .iter_mut()
                .find(|tr| tr.item_meta.diagnostic_item.as_deref() == Some("From"))
                .unwrap();
            let trait_id = tr.def_id;
            if mutation == 0 {
                tr.item_meta.diagnostic_item = Some("Lookalike".into());
            }
            if mutation == 1 {
                tr.item_meta.is_local = true;
            }
            let callee = artifact.data.translated.fun_decls.iter_mut().find(|f| matches!(&f.src, a::FunSource::TraitImpl { trait_ref, .. } if trait_ref.id == trait_id)).unwrap();
            if mutation == 2 {
                callee.signature.output = callee.signature.inputs[0].clone();
            }
            if mutation == 3 {
                callee.signature.is_unsafe = true;
            }
            assert!(
                decode(
                    &serde_json::to_vec(&artifact).unwrap(),
                    "arrays.rs",
                    ARRAY_SOURCE
                )
                .is_err()
            );
        }
    }

    #[test]
    fn charon_identity_from_requires_the_resolved_generic_signature() {
        const ARTIFACT: &[u8] = include_bytes!(
            "../../../design/charon-trial/identity-from/.click/captures/identity/identity.rs.ullbc"
        );
        const SOURCE: &[u8] =
            include_bytes!("../../../design/charon-trial/identity-from/identity.rs");
        let export = decode(ARTIFACT, "identity.rs", SOURCE).unwrap();
        let prepared = super::super::import::prepared_for_test(export).unwrap();
        ProgramVerificationSession::new_program_prepared(
            include_str!("../../../design/charon-trial/identity-from/identity.click"),
            &prepared,
        )
        .unwrap();
        for mutation in 0..6 {
            let mut artifact: ExtractionArtifact = serde_json::from_slice(ARTIFACT).unwrap();
            let trait_id = artifact
                .data
                .translated
                .trait_decls
                .iter()
                .find(|tr| tr.item_meta.diagnostic_item.as_deref() == Some("From"))
                .unwrap()
                .def_id;
            let concrete = artifact
                .data
                .translated
                .fun_decls
                .iter()
                .find(|f| f.item_meta.is_local)
                .unwrap()
                .signature
                .inputs[0]
                .clone();
            let callee = artifact.data.translated.fun_decls.iter_mut()
                .find(|f| matches!(&f.src, a::FunSource::TraitImpl {trait_ref, ..} if trait_ref.id == trait_id)).unwrap();
            match mutation {
                0 => callee.signature.output = concrete,
                1 => callee.signature.inputs[0] = concrete,
                2 => callee.signature.is_unsafe = true,
                3 => callee.item_meta.is_local = true,
                4 => callee.generics.types.clear(),
                5 => callee.signature.is_variadic = true,
                _ => unreachable!(),
            }
            assert!(
                decode(
                    &serde_json::to_vec(&artifact).unwrap(),
                    "identity.rs",
                    SOURCE
                )
                .is_err(),
                "mutation {mutation}"
            );
        }
    }

    #[test]
    fn charon_borrowed_iterator_forwarding_keeps_one_state_and_checks_declarations() {
        const ARTIFACT: &[u8] = include_bytes!(
            "../../../design/charon-trial/borrowed-chunks/.click/captures/chunks/chunks.rs.ullbc"
        );
        const SOURCE: &[u8] =
            include_bytes!("../../../design/charon-trial/borrowed-chunks/chunks.rs");
        let export = decode(ARTIFACT, "chunks.rs", SOURCE).unwrap();
        let mir = export
            .functions
            .iter()
            .find(|f| f.name == "cover")
            .unwrap()
            .mir
            .as_ref()
            .unwrap();
        assert_eq!(
            mir.blocks
                .iter()
                .flat_map(|b| &b.statements)
                .filter(|s| matches!(s, S::ChunkInitialize { .. }))
                .count(),
            1
        );
        assert!(
            !mir.blocks
                .iter()
                .flat_map(|b| &b.statements)
                .any(|s| matches!(s, S::ChunkMove { .. }))
        );
        let next_states: Vec<_> = mir
            .blocks
            .iter()
            .flat_map(|b| &b.statements)
            .filter_map(|s| match s {
                S::ChunkNext { iterator, .. } => Some(iterator),
                _ => None,
            })
            .collect();
        assert_eq!(next_states.len(), 2);
        assert!(next_states.iter().all(|name| *name == "chunks"));
        for mutation in 0..6 {
            let mut artifact: ExtractionArtifact = serde_json::from_slice(ARTIFACT).unwrap();
            let wrapper = artifact.data.translated.fun_decls.iter_mut().find(|f| {
                f.item_meta.name.name.last().is_some_and(|p| matches!(p, a::PathElem::Ident(name, _) if name == "next"))
                    && matches!(f.signature.inputs.as_slice(), [input] if matches!(input.kind(), a::TyKind::Ref(_, p, _) if matches!(p.kind(), a::TyKind::Ref(..))))
            }).unwrap();
            let a::FunSource::TraitImpl {
                trait_ref,
                impl_ref,
                ..
            } = &wrapper.src
            else {
                unreachable!()
            };
            let trait_id = trait_ref.id;
            let impl_id = impl_ref.id;
            match mutation {
                0 => wrapper.signature.is_unsafe = true,
                1 => wrapper.signature.is_variadic = true,
                2 => wrapper.signature.output = wrapper.signature.inputs[0].clone(),
                3 => {
                    artifact.data.translated.trait_decls[trait_id]
                        .item_meta
                        .diagnostic_item = Some("Lookalike".into())
                }
                4 => artifact.data.translated.trait_impls[impl_id].is_negative = true,
                5 => wrapper.item_meta.is_local = true,
                _ => unreachable!(),
            }
            assert!(
                decode(&serde_json::to_vec(&artifact).unwrap(), "chunks.rs", SOURCE).is_err(),
                "mutation {mutation}"
            );
        }
        let mut artifact: ExtractionArtifact = serde_json::from_slice(ARTIFACT).unwrap();
        let function = artifact
            .data
            .translated
            .fun_decls
            .iter_mut()
            .find(|f| f.item_meta.is_local)
            .unwrap();
        let a::Body::Unstructured(body) = &mut function.body else {
            unreachable!()
        };
        let mut changed = false;
        for statement in body.body.iter_mut().flat_map(|b| &mut b.statements) {
            if let u::StatementKind::Assign(target, a::Rvalue::Use(operand, _)) =
                &mut statement.kind
                && matches!(target.ty.kind(), a::TyKind::Ref(_, _, a::RefKind::Mut))
                && let a::Operand::Move(place) = operand
            {
                *operand = a::Operand::Copy(place.clone());
                changed = true;
                break;
            }
        }
        assert!(changed, "fixture must exercise a mutable-reference move");
        let error =
            decode(&serde_json::to_vec(&artifact).unwrap(), "chunks.rs", SOURCE).unwrap_err();
        assert!(error.contains("iterator reference assignment"), "{error}");
    }

    #[test]
    #[cfg(not(feature = "fast-gate"))]
    #[ignore = "nightly: 0.6s in the parallel gate"]
    fn charon_array_index_bounds_remain_checked_after_normalization() {
        const CLAIM: &str =
            "verifying \"arrays.rs\"; fn large_array() -> u8 { ensures result == 7; }";
        let mut export = decode(ARRAY_ARTIFACT, "arrays.rs", ARRAY_SOURCE).unwrap();
        {
            let prepared = super::super::import::prepared_for_test(export.clone()).unwrap();
            ProgramVerificationSession::new_program_prepared(CLAIM, &prepared)
                .expect("the original in-bounds array access should verify");
        }
        let mir = export
            .functions
            .iter_mut()
            .find(|f| f.name == "large_array")
            .unwrap()
            .mir
            .as_mut()
            .unwrap();
        // Normalization substitutes the temporary into the array read, which
        // the returned value now reads directly. Mutate that index, rather
        // than looking for its removed assignment.
        fn last_index(blocks: &mut [crate::languages::rust::schema::MirBlock]) -> Option<&mut u64> {
            for block in blocks {
                let assigned = block.statements.iter_mut().filter_map(|s| match s {
                    S::Assign { value, .. } => Some(value),
                    _ => None,
                });
                let returned = match &mut block.terminator {
                    crate::languages::rust::schema::MirTerminator::ReturnValue { value } => {
                        Some(value)
                    }
                    _ => None,
                };
                for value in assigned.chain(returned) {
                    if let E::Index { index, .. } = value
                        && let E::UsizeInteger { value } = index.as_mut()
                        && *value == 999_999
                    {
                        return Some(value);
                    }
                }
            }
            None
        }
        let index = last_index(&mut mir.blocks)
            .expect("the normalized read should retain the last in-bounds index");
        *index = 1_000_000;
        let prepared = super::super::import::prepared_for_test(export).unwrap();
        let error = ProgramVerificationSession::new_program_prepared(CLAIM, &prepared)
            .err()
            .expect("the out-of-bounds array access must fail");
        assert_eq!(error.kind(), crate::surface::ClickErrorKind::Proof);
        assert!(
            error.message().contains("Rust array index panic check"),
            "{}",
            error.message()
        );
    }

    #[test]
    fn charon_borrowed_loop_keeps_a_real_while_guard() {
        let export = decode(
            include_bytes!(
                "../../../design/charon-trial/borrowed-loop/.click/captures/loop/loop.rs.ullbc"
            ),
            "loop.rs",
            include_bytes!("../../../design/charon-trial/borrowed-loop/loop.rs"),
        )
        .unwrap();
        let (functions, _) = super::super::lowering::lower(&export).unwrap();
        let function = functions
            .iter()
            .find(|f| f.name() == "guarded_walk")
            .unwrap()
            .to_kernel_function();
        fn visit(statement: &crate::kernel::ProgramStatement, guards: &mut Vec<String>) {
            use crate::kernel::ProgramStatement as C;
            match statement {
                C::Seq(statements) => {
                    for statement in statements.iter() {
                        visit(statement, guards);
                    }
                }
                C::Loop { test, body, .. } => {
                    let condition = test
                        .source_condition()
                        .expect("reconstructed while has one decision");
                    guards.push(format!("{condition:?}"));
                    visit(body, guards);
                }
                C::If {
                    then_branch,
                    else_branch,
                    ..
                } => {
                    visit(then_branch, guards);
                    visit(else_branch, guards);
                }
                C::Break => panic!("a reconstructed while must not add an artificial break"),
                _ => {}
            }
        }
        let mut guards = Vec::new();
        visit(function.body(), &mut guards);
        assert_eq!(
            guards,
            ["LessThan(Variable(Named(\"i\")), Variable(Named(\"n\")))"]
        );
    }

    #[test]
    #[cfg(not(feature = "fast-gate"))]
    #[ignore = "nightly: 0.7s in the parallel gate"]
    fn charon_borrowed_loop_rejects_missing_guard_cleanup() {
        let mut export = decode(
            include_bytes!(
                "../../../design/charon-trial/borrowed-loop/.click/captures/loop/loop.rs.ullbc"
            ),
            "loop.rs",
            include_bytes!("../../../design/charon-trial/borrowed-loop/loop.rs"),
        )
        .unwrap();
        let mir = export
            .functions
            .iter_mut()
            .find(|f| f.name == "guarded_walk")
            .unwrap()
            .mir
            .as_mut()
            .unwrap();
        let drop = mir
            .blocks
            .iter_mut()
            .find(|b| matches!(b.terminator, T::Drop { .. }))
            .unwrap();
        let T::Drop { target, .. } = drop.terminator else {
            unreachable!()
        };
        drop.terminator = T::Goto { target };
        let prepared = super::super::import::prepared_for_test(export).unwrap();
        assert!(
            ProgramVerificationSession::new_program_prepared(
                include_str!("../../../design/charon-trial/borrowed-loop/loop.click"),
                &prepared
            )
            .is_err()
        );
    }

    #[test]
    fn charon_trial_rejects_partial_or_incompatible_extraction() {
        let mutations: [fn(&mut ExtractionArtifact); 5] = [
            |a| a.data.has_errors = true,
            |a| a.compiler_commit = "untrusted-compiler".into(),
            |a| a.flags[3] = "-Coverflow-checks=off".into(),
            |a| a.data.translated.options.skip_borrowck = true,
            |a| a.data.translated.options.mir = Some(charon_lib::options::MirLevel::Elaborated),
        ];
        for mutation in mutations {
            let mut artifact: ExtractionArtifact = serde_json::from_slice(ARTIFACT).unwrap();
            mutation(&mut artifact);
            assert!(decode(&serde_json::to_vec(&artifact).unwrap(), "trial.rs", SOURCE).is_err());
        }
    }

    #[cfg(test)]
    mod scaling_tests {
        include!("../../scaling_tests/languages/rust/charon/tests.rs");
    }
}
