//! Rust core methods, `a.min(b)`, `o.unwrap_or(d)` or `xs.swap(i, j)`: each
//! call is a call of an external function the importer declares once per
//! method and type, whose contract is the library's. The callee is checked
//! by identity, an inherent method of `core::num`, `Option` or `[T]`, or
//! `<T as Ord>::{min, max}`, with the signature the method has.
use super::*;

/// What a core method returns: its type, an `Option` of it, or the
/// unsigned type of its width.
#[derive(Clone, Copy, PartialEq)]
enum Returns {
    Same,
    Option,
    Unsigned,
}

/// The unsigned integer type of `ty`'s width.
fn unsigned_of(ty: &Type) -> Type {
    match ty {
        Type::I8 => Type::U8,
        Type::I16 => Type::U16,
        Type::I32 => Type::U32,
        Type::I64 => Type::U64,
        Type::Isize => Type::Usize,
        other => other.clone(),
    }
}

/// The parameter count and result of `method` of integer type `ty`, when it
/// is one the library specifies.
fn specified(method: &str, ty: &Type) -> Option<(usize, Returns)> {
    let signed = ty.is_signed_integer();
    Some(match method {
        "min" | "max" | "wrapping_add" | "wrapping_sub" | "wrapping_mul" | "saturating_add"
        | "saturating_sub" => (2, Returns::Same),
        "checked_add" | "checked_sub" => (2, Returns::Option),
        "abs_diff" if signed => (2, Returns::Unsigned),
        "abs_diff" => (2, Returns::Same),
        "unsigned_abs" if signed => (1, Returns::Unsigned),
        _ => return None,
    })
}

impl Adapter<'_> {
    /// The integer type and method a call of `callee` is, when it is a core
    /// method the library specifies.
    fn core_method_identity(&self, callee: &a::FunDecl) -> Result<Option<(Type, String)>, String> {
        if callee.item_meta.is_local {
            return Ok(None);
        }
        let name = &callee.item_meta.name.name;
        let Some(a::PathElem::Ident(method, d)) = name.last() else {
            return Ok(None);
        };
        if *d != a::Disambiguator::ZERO {
            return Ok(None);
        }
        let receiver = match (&callee.src, name.as_slice()) {
            // An inherent method, `core::num::<impl u32>::checked_add`.
            (
                a::FunSource::Normal,
                [
                    a::PathElem::Ident(core, _),
                    a::PathElem::Ident(num, _),
                    a::PathElem::Impl(a::ImplElem::Ty(receiver)),
                    _,
                ],
            ) if core == "core" && num == "num" => receiver.skip_binder.clone(),
            // `<u32 as Ord>::min`, the trait's own method at the type.
            (
                a::FunSource::TraitImpl {
                    trait_ref,
                    impl_ref,
                    ..
                },
                _,
            ) if matches!(method.as_str(), "min" | "max") => {
                let tr = &self.krate.trait_decls[trait_ref.id];
                let imp = &self.krate.trait_impls[impl_ref.id];
                if tr.item_meta.is_local
                    || tr.item_meta.diagnostic_item.as_deref() != Some("Ord")
                    || imp.item_meta.is_local
                {
                    return Ok(None);
                }
                let Some(receiver) = imp.impl_trait.generics.types.iter().next() else {
                    return Ok(None);
                };
                receiver.clone()
            }
            _ => return Ok(None),
        };
        let Ok(receiver) = self.ty(&receiver) else {
            return Ok(None);
        };
        Ok(receiver
            .is_integer()
            .then(|| (receiver, method.clone()))
            .filter(|(receiver, method)| specified(method, receiver).is_some()))
    }

    /// The external function a call of `callee` calls when it is a core
    /// method the library specifies, declared once per method and type.
    pub(super) fn core_method_call(
        &self,
        callee: &a::FunDecl,
        pointer: &a::FnPtr,
        call: &a::Call,
    ) -> Result<Option<String>, String> {
        let Some((receiver, method)) = self.core_method_identity(callee)? else {
            return Ok(None);
        };
        let (arity, returns) = specified(&method, &receiver).expect("checked by the identity");
        let result = match returns {
            Returns::Same => receiver.clone(),
            Returns::Option => self.option_enum(receiver.clone())?,
            Returns::Unsigned => unsigned_of(&receiver),
        };
        if callee.signature.is_unsafe
            || callee.signature.is_variadic
            || callee.signature.abi != a::Abi::Rust
            || call.safety == a::CallSafety::Unsafe
            || !pointer.generics.const_generics.is_empty()
            || call.args.len() != arity
            || callee.signature.inputs.len() != arity
            || call
                .args
                .iter()
                .map(|argument| self.ty(argument.ty()))
                .collect::<Result<Vec<_>, _>>()?
                .iter()
                .any(|argument| *argument != receiver)
            || self.ty(&call.dest.ty)? != result
        {
            return Err(unsupported(&format!(
                "core method `{}::{method}` signature",
                receiver.scalar_name().unwrap_or("_")
            )));
        }
        let type_name = receiver.scalar_name().expect("an integer");
        let name = super::super::names::qualified_name([type_name, method.as_str()]);
        self.core_methods.borrow_mut().insert(
            name.clone(),
            out::Function {
                sites: Vec::new(),
                name: name.clone(),
                return_type: result,
                parameters: ["a", "b"][..arity]
                    .iter()
                    .map(|parameter| out::Place {
                        name: (*parameter).into(),
                        value_type: receiver.clone(),
                        span: span(callee.item_meta.span),
                    })
                    .collect(),
                body: vec![],
                mir: None,
                external: true,
                captures: 0,
                implements: None,
                instance_of: None,
                core_method: Some(format!("click::rust::{type_name}::{method}")),
                span: span(callee.item_meta.span),
            },
        );
        Ok(Some(name))
    }

    /// The external function a call of `Option::<T>::unwrap_or`, `unwrap`
    /// or `expect` calls, declared once per method and payload type:
    /// A call of `Result::unwrap_or`, `Result::unwrap` or `Result::expect`
    /// on a `Result` of scalars, as [`Self::option_method_call`] reads
    /// `Option`'s: `unwrap_or`'s contract is the library's
    /// `result::unwrap_or`, and `unwrap`'s and `expect`'s require `Ok` and
    /// return its payload. Their `E: Debug` bound and the formatted panic
    /// are not imported: the panic is an obligation.
    pub(super) fn result_method_call(
        &self,
        callee: &a::FunDecl,
        pointer: &a::FnPtr,
        call: &a::Call,
    ) -> Result<Option<String>, String> {
        let name = &callee.item_meta.name.name;
        let method = match name.as_slice() {
            [
                a::PathElem::Ident(core, _),
                a::PathElem::Ident(result, _),
                a::PathElem::Impl(a::ImplElem::Ty(_)),
                a::PathElem::Ident(method, d),
            ] if !callee.item_meta.is_local
                && matches!(callee.src, a::FunSource::Normal)
                && core == "core"
                && result == "result"
                && *d == a::Disambiguator::ZERO
                && matches!(method.as_str(), "unwrap_or" | "unwrap" | "expect") =>
            {
                method.as_str()
            }
            _ => return Ok(None),
        };
        let refused = || unsupported(&format!("core method `Result::{method}` signature"));
        let [ok, err] = pointer.generics.types.as_raw_slice() else {
            return Err(refused());
        };
        let (ok, err) = (self.ty(ok)?, self.ty(err)?);
        let Some(argument) = call.args.first() else {
            return Err(refused());
        };
        let result = self.ty(argument.ty())?;
        let second = match (method, call.args.as_slice()) {
            ("unwrap", [_]) => None,
            ("unwrap_or", [_, default]) => Some(self.ty(default.ty())? == ok),
            ("expect", [_, message]) => Some(matches!(message.ty().kind(),
                a::TyKind::Ref(_, text, a::RefKind::Shared) if matches!(text.kind(), a::TyKind::Adt(r) if r.builtin == Some(a::BuiltinAdt::Str)))),
            _ => Some(false),
        };
        if !ok.is_scalar()
            || !err.is_scalar()
            || callee.signature.is_unsafe
            || call.safety == a::CallSafety::Unsafe
            || !pointer.generics.const_generics.is_empty()
            || result != self.result_enum(ok.clone(), err.clone())?
            || second == Some(false)
            || self.ty(&call.dest.ty)? != ok
        {
            return Err(refused());
        }
        let mut function = super::super::names::qualified_name(["Result", method]);
        for argument in [&ok, &err] {
            super::super::names::push_type_argument(
                &mut function,
                argument.scalar_name().expect("a scalar"),
            );
        }
        let parameter = |name: &str, value_type: Type| out::Place {
            name: name.into(),
            value_type,
            span: span(callee.item_meta.span),
        };
        let (parameters, specification) = if method == "unwrap_or" {
            (
                vec![parameter("r", result), parameter("d", ok.clone())],
                super::super::standard_library::RESULT_UNWRAP_OR,
            )
        } else {
            (
                vec![parameter("r", result)],
                super::super::standard_library::RESULT_UNWRAP,
            )
        };
        self.core_methods.borrow_mut().insert(
            function.clone(),
            out::Function {
                sites: Vec::new(),
                name: function.clone(),
                return_type: ok,
                parameters,
                body: vec![],
                mir: None,
                external: true,
                captures: 0,
                implements: None,
                instance_of: None,
                core_method: Some(specification.into()),
                span: span(callee.item_meta.span),
            },
        );
        Ok(Some(function))
    }
    /// `unwrap_or`'s contract is the library's `option::unwrap_or`, and
    /// `unwrap`'s and `expect`'s require `Some` and return its payload.
    /// `expect`'s message is not passed: it serves the panic alone.
    pub(super) fn option_method_call(
        &self,
        callee: &a::FunDecl,
        pointer: &a::FnPtr,
        call: &a::Call,
    ) -> Result<Option<String>, String> {
        let name = &callee.item_meta.name.name;
        let method = match name.as_slice() {
            [
                a::PathElem::Ident(core, _),
                a::PathElem::Ident(option, _),
                a::PathElem::Impl(a::ImplElem::Ty(_)),
                a::PathElem::Ident(method, d),
            ] if !callee.item_meta.is_local
                && matches!(callee.src, a::FunSource::Normal)
                && core == "core"
                && option == "option"
                && *d == a::Disambiguator::ZERO
                && matches!(method.as_str(), "unwrap_or" | "unwrap" | "expect") =>
            {
                method.as_str()
            }
            _ => return Ok(None),
        };
        let refused = || unsupported(&format!("core method `Option::{method}` signature"));
        let [payload] = pointer.generics.types.as_raw_slice() else {
            return Err(refused());
        };
        let payload = self.ty(payload)?;
        let Some(option) = call.args.first() else {
            return Err(refused());
        };
        let option = self.ty(option.ty())?;
        let second = match (method, call.args.as_slice()) {
            ("unwrap", [_]) => None,
            ("unwrap_or", [_, default]) => Some(self.ty(default.ty())? == payload),
            ("expect", [_, message]) => Some(matches!(message.ty().kind(),
                a::TyKind::Ref(_, text, a::RefKind::Shared) if matches!(text.kind(), a::TyKind::Adt(r) if r.builtin == Some(a::BuiltinAdt::Str)))),
            _ => Some(false),
        };
        if !payload.is_scalar()
            || callee.signature.is_unsafe
            || call.safety == a::CallSafety::Unsafe
            || !pointer.generics.const_generics.is_empty()
            || option != self.option_enum(payload.clone())?
            || second == Some(false)
            || self.ty(&call.dest.ty)? != payload
        {
            return Err(refused());
        }
        let type_name = payload.scalar_name().expect("a scalar");
        let mut function = super::super::names::qualified_name(["Option", method]);
        super::super::names::push_type_argument(&mut function, type_name);
        let parameter = |name: &str, value_type: Type| out::Place {
            name: name.into(),
            value_type,
            span: span(callee.item_meta.span),
        };
        let (parameters, specification) = if method == "unwrap_or" {
            (
                vec![parameter("o", option), parameter("d", payload.clone())],
                "click::rust::option::unwrap_or",
            )
        } else {
            (
                vec![parameter("o", option)],
                super::super::standard_library::OPTION_UNWRAP,
            )
        };
        self.core_methods.borrow_mut().insert(
            function.clone(),
            out::Function {
                sites: Vec::new(),
                name: function.clone(),
                return_type: payload,
                parameters,
                body: vec![],
                mir: None,
                external: true,
                captures: 0,
                implements: None,
                instance_of: None,
                core_method: Some(specification.into()),
                span: span(callee.item_meta.span),
            },
        );
        Ok(Some(function))
    }

    /// The external function a call of `<[T]>::swap` calls, declared once
    /// per element type: its contract, which the library supplies, owns the
    /// slice and exchanges two of its elements.
    pub(super) fn slice_method_call(
        &self,
        callee: &a::FunDecl,
        pointer: &a::FnPtr,
        call: &a::Call,
    ) -> Result<Option<String>, String> {
        let name = &callee.item_meta.name.name;
        let identity = !callee.item_meta.is_local
            && matches!(callee.src, a::FunSource::Normal)
            && matches!(name.as_slice(), [
                a::PathElem::Ident(core, _),
                a::PathElem::Ident(slice, _),
                a::PathElem::Impl(a::ImplElem::Ty(_)),
                a::PathElem::Ident(method, d),
            ] if core == "core" && slice == "slice" && method == "swap" && *d == a::Disambiguator::ZERO);
        if !identity {
            return Ok(None);
        }
        let [element] = pointer.generics.types.as_raw_slice() else {
            return Err(unsupported("core method `<[T]>::swap` instance"));
        };
        let element = self.ty(element)?;
        let [slice, a, b] = call.args.as_slice() else {
            return Err(unsupported("core method `<[T]>::swap` arity"));
        };
        let slice = self.ty(slice.ty())?;
        let mutable_slice = match &slice {
            Type::ScalarSlice {
                element: e,
                mutable: true,
            } => **e == element,
            Type::ByteSlice { mutable: true } => element == Type::U8,
            _ => false,
        };
        if !element.is_integer()
            || !mutable_slice
            || callee.signature.is_unsafe
            || call.safety == a::CallSafety::Unsafe
            || !pointer.generics.const_generics.is_empty()
            || self.ty(a.ty())? != Type::Usize
            || self.ty(b.ty())? != Type::Usize
            || self.ty(&call.dest.ty)? != Type::Unit
        {
            return Err(unsupported("core method `<[T]>::swap` signature"));
        }
        let type_name = element.scalar_name().expect("an integer");
        let mut function = super::super::names::qualified_name(["slice", "swap"]);
        super::super::names::push_type_argument(&mut function, type_name);
        let parameter = |name: &str, value_type: Type| out::Place {
            name: name.into(),
            value_type,
            span: span(callee.item_meta.span),
        };
        self.core_methods.borrow_mut().insert(
            function.clone(),
            out::Function {
                sites: Vec::new(),
                name: function.clone(),
                return_type: Type::Unit,
                parameters: vec![
                    parameter("s", slice),
                    parameter("a", Type::Usize),
                    parameter("b", Type::Usize),
                ],
                body: vec![],
                mir: None,
                external: true,
                captures: 0,
                implements: None,
                instance_of: None,
                core_method: Some(super::super::standard_library::SLICE_SWAP.into()),
                span: span(callee.item_meta.span),
            },
        );
        Ok(Some(function))
    }
}
