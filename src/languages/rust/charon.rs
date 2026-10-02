//! Opt-in, deliberately narrow ULLBC adapter. All bodies use the same CFG path.
//! Charon owns Rust normalization; Click owns execution and checked authority.
mod chunks;

use super::schema::{self as out, Expression as E, MirStatement as S, MirTerminator as T, Type};
use crate::languages::compiler_process::{CompilerLimits, run_compiler};
use charon_lib::ast::from_rustc::LangItem;
use charon_lib::{ast as a, ullbc_ast as u};
use std::collections::{BTreeMap, BTreeSet};
use std::path::Path;
use std::time::Duration;

pub(super) const COMMIT: &str = "5d6b812e5f77dbf3d7f66c21b9b57091f0e084cb";
pub(super) const COMPILER: &str = "923c95cdf5ba65cea505aa2ea829f578e1506ed8";
pub(super) const TOOLCHAIN: &str = "nightly-2026-09-17";
const FLAGS: &[&str] = &[
    "--edition=2024",
    "--target=x86_64-unknown-linux-gnu",
    "-Cpanic=abort",
    "-Coverflow-checks=on",
    "-Zmir-opt-level=0",
];
const PROFILE: &str = "click-charon-optimized-abort-checked-v1";

#[derive(serde::Serialize, serde::Deserialize)]
#[serde(deny_unknown_fields)]
struct TrialArtifact {
    extractor_revision: String,
    compiler_commit: String,
    profile: String,
    flags: Vec<String>,
    data: charon_lib::export::CrateData,
}

pub(super) fn extract(executable: &Path, source: &Path, root: &Path) -> Result<Vec<u8>, String> {
    // The wrapper selects its compiled-in rustup toolchain. Keep only runtime
    // selectors; no ambient rustc flags or Charon configuration can enter.
    let environment: BTreeMap<_, _> = [
        "PATH",
        "HOME",
        "RUSTUP_HOME",
        "CARGO_HOME",
        "RUST_MIN_STACK",
    ]
    .into_iter()
    .filter_map(|key| {
        std::env::var(key)
            .ok()
            .map(|value| (key.to_string(), value))
    })
    .collect();
    let limits = CompilerLimits {
        timeout: Duration::from_secs(30),
        max_stdout_bytes: 64 << 10,
        max_stderr_bytes: 64 << 10,
    };
    let version = run_compiler(executable, &["version".into()], root, &environment, limits)?;
    if String::from_utf8_lossy(&version.stdout).trim() != format!("0.1.279 ({COMMIT})") {
        return Err("Charon trial requires its pinned extractor revision".into());
    }
    let rustup = std::env::split_paths(environment.get("PATH").ok_or("Charon runtime needs PATH")?)
        .map(|p| p.join("rustup"))
        .find(|p| p.is_file())
        .ok_or("Charon runtime needs rustup")?;
    let compiler = run_compiler(
        &rustup,
        &["run".into(), TOOLCHAIN.into(), "rustc".into(), "-vV".into()],
        root,
        &environment,
        limits,
    )?;
    if !String::from_utf8_lossy(&compiler.stdout)
        .lines()
        .any(|line| line == format!("commit-hash: {COMPILER}"))
    {
        return Err("Charon trial requires its pinned compiler commit".into());
    }
    let temp = tempfile::tempdir().map_err(|e| e.to_string())?;
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
    args.extend(FLAGS.iter().map(|flag| format!("--rustc-arg={flag}")));
    args.extend([
        "--".into(),
        source.to_string_lossy().into_owned(),
        "--crate-name".into(),
        "click_charon_trial".into(),
        "--crate-type".into(),
        "lib".into(),
    ]);
    run_compiler(executable, &args, temp.path(), &environment, limits)?;
    let metadata = std::fs::metadata(&artifact).map_err(|e| e.to_string())?;
    if !metadata.is_file() || metadata.len() > 4 << 20 {
        return Err("Charon trial artifact exceeds its file bound".into());
    }
    let bytes = std::fs::read(artifact).map_err(|e| e.to_string())?;
    let data = serde_json::from_slice(&bytes).map_err(|e| format!("Charon output: {e}"))?;
    serde_json::to_vec(&TrialArtifact {
        extractor_revision: COMMIT.into(),
        compiler_commit: COMPILER.into(),
        profile: PROFILE.into(),
        flags: FLAGS.iter().map(|s| (*s).into()).collect(),
        data,
    })
    .map_err(|e| e.to_string())
}

fn unsupported(what: &str) -> String {
    format!("Charon trial does not support {what}")
}
fn span(s: a::Span) -> out::Span {
    out::Span {
        line: s.data().beg.line as usize,
        column: s.data().beg.col as usize + 1,
    }
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
    krate: &'a a::TranslatedCrate,
    records: BTreeMap<a::TypeDeclId, String>,
    functions: BTreeMap<a::FunDeclId, String>,
    destructors: BTreeMap<a::TypeDeclId, a::FunDeclId>,
}
impl Adapter<'_> {
    fn ty(&self, t: &a::Ty) -> Result<Type, String> {
        Ok(match t.kind() {
            a::TyKind::Scalar(a::ScalarTy::Bool) => Type::Bool,
            a::TyKind::Scalar(a::ScalarTy::Integer(a::IntegerTy::Signed(a::IntTy::I32))) => {
                Type::I32
            }
            a::TyKind::Scalar(a::ScalarTy::Integer(a::IntegerTy::Unsigned(kind))) => match kind {
                a::UIntTy::U8 => Type::U8,
                a::UIntTy::U16 => Type::U16,
                a::UIntTy::U32 => Type::U32,
                a::UIntTy::Usize => Type::Usize,
                _ => return Err(unsupported("integer width")),
            },
            a::TyKind::Ref(_, pointee, kind) if byte_slice(pointee) => Type::ByteSlice {
                mutable: *kind == a::RefKind::Mut,
            },
            a::TyKind::Ref(_, pointee, _) if matches!(pointee.kind(), a::TyKind::Slice(..)) => {
                return Err(unsupported("slice elements other than u8"));
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
            a::TyKind::Adt(_) if self.chunk_type(t) => Type::ChunkIterator,
            a::TyKind::Adt(_) if self.chunk_option_type(t) => Type::ChunkOption,
            a::TyKind::Adt(r) if r.id == a::TypeDeclId::UNIT => Type::Unit,
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
                return Err(unsupported(
                    "type (raw pointers and general generics remain later work)",
                ));
            }
        })
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
    fn record_id(&self, ty: &a::Ty) -> Result<a::TypeDeclId, String> {
        match ty.kind() {
            a::TyKind::Adt(r) if self.records.contains_key(&r.id) => Ok(r.id),
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
    names: BTreeMap<a::LocalId, String>,
    chunk_refs: BTreeMap<a::LocalId, a::LocalId>,
    chunk_discriminants: BTreeMap<a::LocalId, a::LocalId>,
}
impl BodyAdapter<'_, '_> {
    /// Named interpretations for compiler-resolved slice length and unsigned From.
    fn modeled_call(&self, t: &u::Terminator) -> Result<Option<S>, String> {
        if let Some(statement) = self.chunk_call(t)? {
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
                || self.adapter.ty(&ptr.generics.types[0])? != Type::U8
                || !ptr.generics.const_generics.is_empty()
                || self.adapter.ty(argument.ty())? != (Type::ByteSlice { mutable: false })
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
        let width = |ty: &Type| match ty {
            Type::U8 => Some(8),
            Type::U16 => Some(16),
            Type::U32 => Some(32),
            Type::Usize => Some(64),
            _ => None,
        };
        let source = self.adapter.ty(argument.ty())?;
        let destination = self.adapter.ty(&call.dest.ty)?;
        if callee.item_meta.is_local
            || imp.item_meta.is_local
            || tr.item_meta.is_local
            || call.safety == a::CallSafety::Unsafe
            || callee.signature.is_unsafe
            || !ptr.generics.types.is_empty()
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
            || imp.impl_trait.generics.types.len() != 2
            || imp
                .impl_trait
                .generics
                .types
                .iter()
                .ne([&call.dest.ty, argument.ty()])
            || callee.signature.inputs.as_slice() != [argument.ty().clone()]
            || callee.signature.output != call.dest.ty
            || !matches!((width(&source), width(&destination)), (Some(a), Some(b)) if a <= b)
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
    fn local(&self, id: a::LocalId) -> Result<String, String> {
        self.names
            .get(&id)
            .cloned()
            .ok_or_else(|| unsupported("unknown local identity"))
    }
    fn place(&self, p: &a::Place) -> Result<E, String> {
        if let Some(value) = self.chunk_projection(p)? {
            return Ok(value);
        }
        Ok(match &p.kind {
            a::PlaceKind::Local(id) => E::Local {
                name: self.local(*id)?,
            },
            a::PlaceKind::Projection(base, a::ProjectionElem::PtrMetadata)
                if matches!(self.adapter.ty(&base.ty)?, Type::ByteSlice { .. })
                    && self.adapter.ty(&p.ty)? == Type::Usize =>
            {
                E::SliceLength {
                    slice: Box::new(self.place(base)?),
                }
            }
            a::PlaceKind::Projection(base, a::ProjectionElem::Deref)
                if matches!(self.adapter.ty(&base.ty)?, Type::ByteSlice { .. }) =>
            {
                self.place(base)?
            }
            a::PlaceKind::Projection(base, a::ProjectionElem::Deref)
                if matches!(base.ty.kind(), a::TyKind::Ref(..)) =>
            {
                E::Deref {
                    reference: Box::new(self.place(base)?),
                    value_type: self.adapter.ty(&p.ty)?,
                }
            }
            a::PlaceKind::Projection(base, a::ProjectionElem::Field(None, field)) => {
                let id = self.adapter.record_id(&base.ty)?;
                E::Field {
                    base: Box::new(self.place(base)?),
                    record: self.adapter.records[&id].clone(),
                    field: self
                        .adapter
                        .fields(id)?
                        .get(*field)
                        .ok_or_else(|| unsupported("invalid field"))?
                        .name
                        .clone(),
                }
            }
            a::PlaceKind::Projection(
                base,
                a::ProjectionElem::Index {
                    offset,
                    from_end: false,
                },
            ) if matches!(base.ty.kind(), a::TyKind::Array(..)) || byte_slice(&base.ty) => {
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
                    value: u32::try_from(*value)
                        .map_err(|_| unsupported("large unsigned constant"))?,
                    value_type: self.adapter.ty(c.ty())?,
                }
            }
            _ => return Err(unsupported("constant")),
        })
    }
    fn operand(&self, op: &a::Operand) -> Result<E, String> {
        match op {
            a::Operand::Copy(p) | a::Operand::Move(p) => {
                if matches!(self.adapter.ty(&p.ty)?, Type::Record { .. }) {
                    return Err(unsupported("aggregate operand without a move event"));
                }
                self.place(p)
            }
            a::Operand::Const(c) => self.constant(c),
        }
    }
    fn rvalue(&self, v: &a::Rvalue, ty: &a::Ty) -> Result<E, String> {
        Ok(match v {
            a::Rvalue::Use(op, _) => self.operand(op)?,
            a::Rvalue::Len(place, _, _) if byte_slice(&place.ty) => E::SliceLength {
                slice: Box::new(self.place(place)?),
            },
            a::Rvalue::Repeat(value, _, length, _) => E::Repeat {
                value: Box::new(self.operand(value)?),
                length: length
                    .as_usize_literal()
                    .ok_or_else(|| unsupported("symbolic array repeat"))?
                    as u64,
            },
            a::Rvalue::Aggregate(a::AggregateKind::Array(..), elements) => E::Array {
                elements: elements
                    .iter()
                    .map(|value| self.operand(value))
                    .collect::<Result<_, _>>()?,
            },
            a::Rvalue::Ref {
                place,
                kind,
                ptr_metadata,
            } if byte_slice(&place.ty) => {
                let a::PlaceKind::Projection(base, a::ProjectionElem::Deref) = &place.kind else {
                    return Err(unsupported("slice reborrow place"));
                };
                let source = self.adapter.ty(&base.ty)?;
                let destination = self.adapter.ty(ty)?;
                let mutable = matches!(kind, a::BorrowKind::Mut | a::BorrowKind::TwoPhaseMut);
                if !matches!(
                    kind,
                    a::BorrowKind::Shared | a::BorrowKind::Mut | a::BorrowKind::TwoPhaseMut
                ) || destination != (Type::ByteSlice { mutable })
                    || !matches!(source, Type::ByteSlice { mutable: source } if !mutable || source)
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
                kind: a::BorrowKind::Shared | a::BorrowKind::Mut | a::BorrowKind::TwoPhaseMut,
                ptr_metadata,
            } if ptr_metadata.ty().is_unit() => E::Borrow {
                place: Box::new(self.place(place)?),
                value_type: self.adapter.ty(ty)?,
            },
            a::Rvalue::UnaryOp(a::UnOp::Not, op) if self.adapter.ty(op.ty())? == Type::Bool => {
                E::Not {
                    value: Box::new(self.operand(op)?),
                }
            }
            a::Rvalue::UnaryOp(a::UnOp::Not, op)
                if matches!(
                    self.adapter.ty(op.ty())?,
                    Type::U8 | Type::U16 | Type::U32 | Type::Usize
                ) =>
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
                let a::TyKind::Array(element, extent, _) = array.kind() else {
                    return Err(unsupported("array unsize source"));
                };
                let Some(extent) = extent.as_usize_literal() else {
                    return Err(unsupported("symbolic array unsize"));
                };
                let mutable = matches!(destination.kind(), a::TyKind::Ref(_, _, a::RefKind::Mut));
                if self.adapter.ty(source)? != self.adapter.ty(op.ty())?
                    || self.adapter.ty(destination)? != self.adapter.ty(ty)?
                    || self.adapter.ty(element)? != Type::U8
                    || self.adapter.ty(destination)? != (Type::ByteSlice { mutable })
                    || (mutable && *source_kind != a::RefKind::Mut)
                    || length.as_usize_literal() != Some(extent)
                    || extent > i32::MAX as u128
                {
                    return Err(unsupported("array unsize pointer/length/type mismatch"));
                }
                E::ArrayToSlice {
                    array: Box::new(self.operand(op)?),
                    mutable,
                }
            }
            a::Rvalue::UnaryOp(a::UnOp::Cast(a::CastKind::Scalar(..)), op) => E::Cast {
                value: Box::new(self.operand(op)?),
                value_type: self.adapter.ty(ty)?,
            },
            a::Rvalue::BinaryOp(op, l, r) => {
                let left_type = self.adapter.ty(l.ty())?;
                let right_type = self.adapter.ty(r.ty())?;
                let unsigned = matches!(left_type, Type::U8 | Type::U16 | Type::U32 | Type::Usize);
                let same_unsigned = unsigned && left_type == right_type;
                let operator = match op {
                    a::BinOp::Add(a::OverflowMode::Panic) => "add",
                    a::BinOp::Sub(a::OverflowMode::Panic) => "sub",
                    a::BinOp::Mul(a::OverflowMode::Panic) => "mul",
                    a::BinOp::Div(a::OverflowMode::Panic) if same_unsigned => "div",
                    a::BinOp::Rem(a::OverflowMode::Panic) if same_unsigned => "rem",
                    a::BinOp::Shl(a::OverflowMode::Panic) if unsigned => "shl",
                    a::BinOp::Shr(a::OverflowMode::Panic) if unsigned => "shr",
                    a::BinOp::BitAnd if same_unsigned => "bit_and",
                    a::BinOp::BitOr if same_unsigned => "bit_or",
                    a::BinOp::BitXor if same_unsigned => "bit_xor",
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
        if let Some(statement) = self.chunk_statement(s)? {
            return Ok(statement);
        }
        Ok(match &s.kind {
            u::StatementKind::Assign(p, v) => {
                if self.adapter.ty(&p.ty)? == Type::Unit {
                    // Only the literal unit value can disappear; never discard a call/read.
                    if !matches!(v, a::Rvalue::Aggregate(a::AggregateKind::Adt(r, None, None), fields) if r.id == a::TypeDeclId::UNIT && fields.is_empty())
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
                            if r.id == self.adapter.record_id(&p.ty)? =>
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
                        a::Rvalue::Use(a::Operand::Move(source), _)
                            if self.adapter.ty(&source.ty)? == self.adapter.ty(&p.ty)? =>
                        {
                            let a::PlaceKind::Local(source) = source.kind else {
                                return Err(unsupported("partial move"));
                            };
                            Some(S::Move {
                                target: self.local(target)?,
                                source: self.local(source)?,
                                record: name,
                            })
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
            u::StatementKind::StorageLive(_)
            | u::StatementKind::Nop
            | u::StatementKind::Borrowck(_) => None,
            _ => return Err(unsupported("statement")),
        })
    }
    fn terminator(&self, t: &u::Terminator) -> Result<T, String> {
        if let Some(terminator) = self.chunk_switch(t)? {
            return Ok(terminator);
        }
        Ok(match &t.kind {
            u::TerminatorKind::Goto { target } => T::Goto {
                target: target.index(),
            },
            u::TerminatorKind::Return => T::Return,
            u::TerminatorKind::UndefinedBehavior | u::TerminatorKind::UnwindTerminate => {
                T::Unreachable
            }
            u::TerminatorKind::Switch { data, branches } => {
                let a::SwitchScrutinee::Value(value) = &data.scrutinee else {
                    return Err(unsupported("enum switch"));
                };
                let [(constant, yes)] = data.branches.as_slice() else {
                    return Err(unsupported("multiway switch"));
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
            u::TerminatorKind::Drop {
                kind: a::DropKind::Precise,
                place,
                fn_ptr,
                target,
                ..
            } => {
                let id = self.adapter.record_id(&place.ty)?;
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
                        .and_then(|t| self.adapter.record_id(t).ok())
                        != Some(id)
                {
                    return Err(unsupported("drop glue/type mismatch"));
                }
                let a::PlaceKind::Local(local) = place.kind else {
                    return Err(unsupported("partial drop"));
                };
                T::Drop {
                    local: self.local(local)?,
                    record: self.adapter.records[&id].clone(),
                    target: target.index(),
                }
            }
            u::TerminatorKind::Call { call, target, .. } => {
                let a::FnOperand::Regular(ptr) = &call.func else {
                    return Err(unsupported("indirect call"));
                };
                let id = self.adapter.resolve(ptr)?;
                let callee = self
                    .adapter
                    .krate
                    .fun_decls
                    .get(id)
                    .ok_or_else(|| unsupported("missing call definition"))?;
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
                    if call.safety == a::CallSafety::Unsafe
                        || callee.signature.is_unsafe
                        || !ptr.generics.types.is_empty()
                    {
                        return Err(unsupported("unsafe or generic call"));
                    }
                    let a::PlaceKind::Local(dest) = call.dest.kind else {
                        return Err(unsupported("projected call destination"));
                    };
                    T::Call {
                        function: self
                            .adapter
                            .functions
                            .get(&id)
                            .ok_or_else(|| unsupported("unmodeled external call"))?
                            .clone(),
                        arguments: call
                            .args
                            .iter()
                            .map(|op| self.operand(op))
                            .collect::<Result<_, _>>()?,
                        destination: self.local(dest)?,
                        target: target.index(),
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
    let artifact: TrialArtifact =
        serde_json::from_slice(bytes).map_err(|e| format!("Charon artifact: {e}"))?;
    if artifact.extractor_revision != COMMIT
        || artifact.compiler_commit != COMPILER
        || artifact.profile != PROFILE
        || artifact.flags != FLAGS
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
        ..Default::default()
    };
    // The driver clears rustc_args after consuming them; the refresh-owned
    // envelope records those flags along with the checked compiler identity.
    if opts != &expected {
        return Err("Charon artifact differs from the trial extraction profile".into());
    }
    let files: Vec<_> = krate
        .files
        .iter()
        .filter(|f| f.crate_name == krate.crate_name)
        .collect();
    if files.len() != 1 || files[0].contents.as_deref().map(str::as_bytes) != Some(source_bytes) {
        return Err("Charon trial requires exactly one locked source file".into());
    }
    let mut adapter = Adapter {
        krate: &krate,
        records: BTreeMap::new(),
        functions: BTreeMap::new(),
        destructors: BTreeMap::new(),
    };
    for (id, record) in krate.type_decls.iter_indexed() {
        if record.item_meta.is_local {
            if !record.generics.types.is_empty()
                || !record.generics.const_generics.is_empty()
                || !matches!(record.src, a::TypeSource::Normal)
            {
                return Err(unsupported("generic or generated source record"));
            }
            adapter
                .records
                .insert(id, simple_name(&record.item_meta.name, &krate.crate_name)?);
        }
    }
    for (id, f) in krate.fun_decls.iter_indexed() {
        if !f.item_meta.is_local {
            continue;
        }
        let name = match &f.src {
            a::FunSource::Normal => simple_name(&f.item_meta.name, &krate.crate_name)?,
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
                    continue;
                }
                if tr.item_meta.lang_item != Some(LangItem::Drop) {
                    return Err(unsupported("source trait method other than Drop"));
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
            _ => return Err(unsupported("function source")),
        };
        if f.signature.is_unsafe
            || f.signature.abi != a::Abi::Rust
            || f.signature.is_variadic
            || !f.generics.types.is_empty()
            || !f.generics.const_generics.is_empty()
        {
            return Err(unsupported("unsafe, foreign, or generic function"));
        }
        adapter.functions.insert(id, name);
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
            let ty = adapter.ty(&field.ty)?;
            if matches!(ty, Type::Record { .. } | Type::Unit) {
                return Err(unsupported("nested owned field"));
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
                .map(|f| adapter.functions[f].clone()),
        });
    }
    let mut functions = Vec::new();
    let mut used_names = BTreeSet::new();
    for (id, name) in &adapter.functions {
        if !used_names.insert(name) {
            return Err(unsupported("colliding proof function names"));
        }
        let f = &krate.fun_decls[*id];
        let a::Body::Unstructured(body) = &f.body else {
            return Err(unsupported("missing or non-CFG source body"));
        };
        let (chunk_refs, chunk_discriminants) = chunks::bindings(&adapter, body)?;
        let mut names = BTreeMap::new();
        let mut parameters = Vec::new();
        let mut locals = Vec::new();
        let mut local_names = BTreeSet::new();
        let mut occurrences = BTreeMap::<&str, usize>::new();
        let mut reserved = BTreeSet::new();
        for local in &body.locals.locals {
            if let Some(name) = &local.name {
                *occurrences.entry(name).or_default() += 1;
                reserved.insert(name.clone());
            }
        }
        for local in &body.locals.locals {
            let param = local.index.index() > 0 && local.index.index() <= body.locals.arg_count;
            let n = if param {
                local
                    .name
                    .clone()
                    .ok_or_else(|| unsupported("unnamed parameter"))?
            } else if let Some(name) = &local.name
                && occurrences[name.as_str()] == 1
                && local.index.index() != 0
            {
                name.clone()
            } else {
                // rustc gives every nested `for` temporary the name `iter`.
                // Preserve unique source names; ambiguous/unnamed locals use
                // their compiler IDs in a namespace disjoint from source names.
                let mut generated = format!("__rust_mir_{}", local.index.index());
                while !reserved.insert(generated.clone()) {
                    generated.push('_');
                }
                generated
            };
            if !local_names.insert(n.clone()) {
                return Err(unsupported("local identity collision"));
            }
            names.insert(local.index, n.clone());
            let place = out::Place {
                name: n,
                value_type: if chunk_discriminants.contains_key(&local.index) {
                    Type::Bool
                } else {
                    adapter.ty(&local.ty)?
                },
                span: span(local.span),
            };
            if param {
                parameters.push(place);
            } else {
                locals.push(place);
            }
        }
        let b = BodyAdapter {
            adapter: &adapter,
            body,
            names,
            chunk_refs,
            chunk_discriminants,
        };
        let mut blocks = Vec::new();
        for block in &b.body.body {
            let mut statements: Vec<S> = block
                .statements
                .iter()
                .map(|s| {
                    b.statement(s)
                        .map_err(|e| format!("{source}:{} in {name}: {e}", s.span.data().beg.line))
                })
                .collect::<Result<Vec<_>, _>>()?
                .into_iter()
                .flatten()
                .collect();
            let conversion = b.modeled_call(&block.terminator)?;
            let terminator = if let Some(conversion) = conversion {
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
                    "{source}:{} in {name}: {e}",
                    block.terminator.span.data().beg.line
                )
            })?;
            blocks.push(out::MirBlock {
                statements,
                terminator,
            });
        }
        chunks::split_next_branches(&mut blocks)?;
        functions.push(out::Function {
            name: name.clone(),
            return_type: adapter.ty(&f.signature.output)?,
            parameters,
            body: vec![],
            mir: Some(out::MirBody { locals, blocks }),
            span: span(f.item_meta.span),
        });
    }
    Ok(out::RustExport {
        schema: out::SCHEMA,
        compiler_commit: COMPILER.into(),
        target: out::TARGET.into(),
        edition: "2024".into(),
        overflow_checks: true,
        panic: "abort".into(),
        mir_opt_level: 0,
        logical_source: source.into(),
        records,
        functions,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::surface::C0VerificationSession;
    const ARTIFACT: &[u8] = include_bytes!("../../../design/charon-trial/trial.ullbc");
    const SOURCE: &[u8] = include_bytes!("../../../design/charon-trial/trial.rs");
    const CLAIM: &str = include_str!("../../../design/charon-trial/trial.click");

    const ARRAY_ARTIFACT: &[u8] =
        include_bytes!("../../../design/charon-trial/conversions-arrays/arrays.ullbc");
    const ARRAY_SOURCE: &[u8] =
        include_bytes!("../../../design/charon-trial/conversions-arrays/arrays.rs");
    const ARRAY_CLAIM: &str =
        include_str!("../../../design/charon-trial/conversions-arrays/arrays.click");

    #[test]
    fn charon_chunks_keep_state_and_owned_moves() {
        let export = decode(
            include_bytes!("../../../design/charon-trial/chunks/chunks.ullbc"),
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
        let prepared = super::super::import::prepared_for_test(export).unwrap();
        C0VerificationSession::new_program_prepared(
            include_str!("../../../design/charon-trial/chunks/chunks.click"),
            &prepared,
        )
        .unwrap();
    }

    const ARITHMETIC_ARTIFACT: &[u8] =
        include_bytes!("../../../design/charon-trial/arithmetic/arithmetic.ullbc");
    const ARITHMETIC_SOURCE: &[u8] =
        include_bytes!("../../../design/charon-trial/arithmetic/arithmetic.rs");

    #[test]
    fn charon_checksum_operators_reject_wrapping_and_unchecked_modes() {
        for name in ["quotient", "reduce", "wide_left", "wide_right"] {
            for mode in [a::OverflowMode::Wrap, a::OverflowMode::UB] {
                let mut artifact: TrialArtifact =
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
        let mut artifact: TrialArtifact = serde_json::from_slice(ARITHMETIC_ARTIFACT).unwrap();
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

    const NESTED_ARTIFACT: &[u8] =
        include_bytes!("../../../design/charon-trial/nested/nested.ullbc");
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
        fn visit(s: &crate::kernel::CStatement, depth: usize, loops: &mut Vec<usize>) {
            use crate::kernel::CStatement as C;
            match s {
                C::Seq(a, b) => {
                    visit(a, depth, loops);
                    visit(b, depth, loops);
                }
                C::While { body, .. } => {
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
    fn charon_generated_local_names_do_not_collide_with_source_names() {
        let mut artifact: TrialArtifact = serde_json::from_slice(NESTED_ARTIFACT).unwrap();
        let body = artifact.data.translated.fun_decls.iter_mut().find_map(|function| {
            if !matches!(function.item_meta.name.name.last(), Some(a::PathElem::Ident(name, _)) if name == "nested") { return None; }
            let a::Body::Unstructured(body) = &mut function.body else { return None; };
            Some(body)
        }).unwrap();
        body.locals.locals[a::LocalId::from_usize(1)].name = Some("__rust_mir_0".into());
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
        assert!(names.iter().any(|n| n.as_str() == "__rust_mir_0_"));
        assert!(names.iter().any(|n| n.as_str() == "__rust_mir_8_"));
    }

    #[test]
    fn charon_array_unsize_rejects_mismatched_metadata_and_reference_types() {
        for mutation in 0..4 {
            let mut artifact: TrialArtifact = serde_json::from_slice(NESTED_ARTIFACT).unwrap();
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
        let mut samples = Vec::new();
        for (name, length) in [
            ("empty_array_len", 0),
            ("array_len", 8),
            ("medium_array_len", 1024),
            ("large_array_len", 1_000_000),
        ] {
            let _session = crate::kernel::VerificationSession::enter();
            let claim = format!(
                "verifying \"nested.rs\"; uint64 {name}() {{ ensures result == {length}u64; }} by {{ execute(); simp(); }}"
            );
            let (verified, work) = crate::instrumentation::measure_deterministic_work(|| {
                C0VerificationSession::new_program_prepared(&claim, &prepared)
            });
            verified.unwrap();
            samples.push(work);
        }
        assert!(
            samples[0] <= 40_000 && samples[1..].iter().all(|work| *work <= samples[1] + 128),
            "{samples:?}"
        );
    }

    const CHUNK_ARTIFACT: &[u8] =
        include_bytes!("../../../design/charon-trial/chunks/chunks.ullbc");
    const CHUNK_SOURCE: &[u8] = include_bytes!("../../../design/charon-trial/chunks/chunks.rs");

    #[test]
    fn charon_chunk_models_check_resolved_identity_and_signature() {
        for mutation in 0..7 {
            let mut artifact: TrialArtifact = serde_json::from_slice(CHUNK_ARTIFACT).unwrap();
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
    fn charon_chunk_missing_initialization_and_duplicate_moves_fail() {
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
            let prepared = super::super::import::prepared_for_test(export).unwrap();
            assert!(
                C0VerificationSession::new_program_prepared(
                    include_str!("../../../design/charon-trial/chunks/chunks.click"),
                    &prepared
                )
                .is_err()
            );
        }
    }

    #[test]
    fn charon_chunk_option_projection_checks_variant_and_field() {
        let mut artifact: TrialArtifact = serde_json::from_slice(CHUNK_ARTIFACT).unwrap();
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
        assert!(error.contains("chunk Option projection"), "{error}");
    }

    #[test]
    fn charon_chunk_none_cannot_supply_a_slice_payload() {
        let mut export = decode(CHUNK_ARTIFACT, "chunks.rs", CHUNK_SOURCE).unwrap();
        let mir = export
            .functions
            .iter_mut()
            .find(|f| f.name == "next_len")
            .unwrap()
            .mir
            .as_mut()
            .unwrap();
        let payload = mir
            .blocks
            .iter()
            .flat_map(|b| &b.statements)
            .find(|s| {
                matches!(
                    s,
                    S::Assign {
                        value: E::ChunkOptionSlice { .. },
                        ..
                    }
                )
            })
            .unwrap()
            .clone();
        let none_edge = mir
            .blocks
            .iter()
            .find_map(|b| match b.terminator {
                T::If {
                    condition: E::ChunkHasNext { .. },
                    else_target,
                    ..
                } => Some(else_target),
                _ => None,
            })
            .unwrap();
        let T::Goto { target: none } = mir.blocks[none_edge].terminator else {
            panic!()
        };
        mir.blocks[none].statements.insert(0, payload);
        let prepared = super::super::import::prepared_for_test(export).unwrap();
        let claim = "verifying \"chunks.rs\"; uint64 next_len(const uint8* bytes, uint64 bytes_len) { requires bytes_len == 0u64; ensures result == 0u64; } by { execute(); simp(); }";
        assert!(C0VerificationSession::new_program_prepared(claim, &prepared).is_err());
    }

    #[test]
    fn charon_chunk_metadata_work_is_independent_of_input_length() {
        let export = decode(CHUNK_ARTIFACT, "chunks.rs", CHUNK_SOURCE).unwrap();
        let prepared = super::super::import::prepared_for_test(export).unwrap();
        let mut samples = Vec::new();
        for length in [0u64, 8, 1024, 1_000_000] {
            let _session = crate::kernel::VerificationSession::enter();
            let claim = format!(
                "verifying \"chunks.rs\"; uint64 tail(const uint8* bytes, uint64 bytes_len, uint64 size) {{ requires bytes_len == {length}u64; requires size == 4u64; ensures result == {}u64; }} by {{ execute(); simp(); }}",
                length % 4
            );
            let (verified, work) = crate::instrumentation::measure_deterministic_work(|| {
                C0VerificationSession::new_program_prepared(&claim, &prepared)
            });
            verified.unwrap();
            samples.push(work);
        }
        assert!(
            samples.iter().all(|work| *work <= samples[0] + 64),
            "{samples:?}"
        );
    }

    const SLICE_ARTIFACT: &[u8] =
        include_bytes!("../../../design/charon-trial/slices/slices.ullbc");
    const SLICE_SOURCE: &[u8] = include_bytes!("../../../design/charon-trial/slices/slices.rs");

    #[test]
    fn charon_slice_length_checks_declaration_identity_and_types() {
        for mutation in 0..4 {
            let mut artifact: TrialArtifact = serde_json::from_slice(SLICE_ARTIFACT).unwrap();
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
        let mut artifact: TrialArtifact = serde_json::from_slice(SLICE_ARTIFACT).unwrap();
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
    fn charon_slice_metadata_verification_work_is_independent_of_length() {
        let export = decode(SLICE_ARTIFACT, "slices.rs", SLICE_SOURCE).unwrap();
        let prepared = super::super::import::prepared_for_test(export).unwrap();
        let mut samples = Vec::new();
        for length in [0u64, 8, 1024, 1_000_000, u64::MAX] {
            let _session = crate::kernel::VerificationSession::enter();
            let claim = format!(
                "verifying \"slices.rs\"; uint64 length(const uint8* bytes, uint64 bytes_len) {{ requires bytes_len == {length}u64; ensures result == {length}u64; }} by {{ execute(); simp(); }}"
            );
            let (verified, work) = crate::instrumentation::measure_deterministic_work(|| {
                C0VerificationSession::new_program_prepared(&claim, &prepared)
            });
            verified.unwrap();
            samples.push(work);
        }
        assert!(
            samples.iter().all(|work| *work <= samples[0] + 64),
            "{samples:?}"
        );
    }

    #[test]
    fn charon_unsigned_from_checks_resolved_identity_and_signature() {
        for mutation in 0..4 {
            let mut artifact: TrialArtifact = serde_json::from_slice(ARRAY_ARTIFACT).unwrap();
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
    fn charon_array_index_bounds_remain_checked_after_normalization() {
        let mut export = decode(ARRAY_ARTIFACT, "arrays.rs", ARRAY_SOURCE).unwrap();
        let mir = export
            .functions
            .iter_mut()
            .find(|f| f.name == "large_array")
            .unwrap()
            .mir
            .as_mut()
            .unwrap();
        let index = mir
            .blocks
            .iter_mut()
            .flat_map(|b| &mut b.statements)
            .find_map(|s| match s {
                S::Assign {
                    value: E::UsizeInteger { value, .. },
                    ..
                } if *value == 999_999 => Some(value),
                _ => None,
            })
            .unwrap();
        *index = 1_000_000;
        let prepared = super::super::import::prepared_for_test(export).unwrap();
        assert!(C0VerificationSession::new_program_prepared(ARRAY_CLAIM, &prepared).is_err());
    }

    #[test]
    fn charon_array_lowering_and_verification_work_do_not_expand_with_length() {
        use crate::kernel::CStatement as C;
        fn shape(s: &C) -> (usize, usize) {
            match s {
                C::Seq(a, b) => {
                    let a = shape(a);
                    let b = shape(b);
                    (1 + a.0 + b.0, a.1 + b.1)
                }
                C::DeclareAggregate { layout, .. } => (1, layout.fields().len()),
                _ => (1, 0),
            }
        }
        let mut samples = Vec::new();
        for length in [8, 1024, 1_000_000] {
            let _session = crate::kernel::VerificationSession::enter();
            let mut export = decode(ARRAY_ARTIFACT, "arrays.rs", ARRAY_SOURCE).unwrap();
            let mir = export
                .functions
                .iter_mut()
                .find(|f| f.name == "large_array")
                .unwrap()
                .mir
                .as_mut()
                .unwrap();
            for local in &mut mir.locals {
                if let Type::Array { length: n, .. } = &mut local.value_type {
                    *n = length;
                }
            }
            for statement in mir.blocks.iter_mut().flat_map(|b| &mut b.statements) {
                match statement {
                    S::Assign {
                        value: E::Repeat { length: n, .. },
                        ..
                    } => *n = length,
                    S::Assign {
                        value: E::UsizeInteger { value, .. },
                        ..
                    } if *value == 999_999 => *value = length - 1,
                    _ => {}
                }
            }
            let (functions, _) = super::super::lowering::lower(&export).unwrap();
            let function = functions
                .iter()
                .find(|f| f.name() == "large_array")
                .unwrap()
                .to_kernel_function();
            let shape = shape(function.body());
            assert_eq!(shape.1, 0);
            let prepared = super::super::import::prepared_for_test(export).unwrap();
            let (verified, work) = crate::instrumentation::measure_deterministic_work(|| {
                C0VerificationSession::new_program_prepared(
                    "verifying \"arrays.rs\"; uint8 large_array() { ensures result == 7; } by { execute(); simp(); }",
                    &prepared,
                )
            });
            verified.unwrap();
            samples.push((length, shape, work));
        }
        eprintln!("array proof (length, nodes/fields, work): {samples:?}");
        assert!(
            samples
                .iter()
                .all(|(_, shape, work)| *shape == samples[0].1 && *work <= samples[0].2 + 64),
            "{samples:?}"
        );
    }

    #[test]
    fn charon_borrowed_loop_keeps_a_real_while_guard() {
        let export = decode(
            include_bytes!("../../../design/charon-trial/borrowed-loop/loop.ullbc"),
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
        fn visit(statement: &crate::kernel::CStatement, guards: &mut Vec<String>) {
            use crate::kernel::CStatement as C;
            match statement {
                C::Seq(a, b) => {
                    visit(a, guards);
                    visit(b, guards);
                }
                C::While {
                    condition, body, ..
                } => {
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
        assert_eq!(guards, ["LessThan(Variable(\"i\"), Variable(\"n\"))"]);
    }

    #[test]
    fn charon_borrowed_loop_rejects_missing_guard_cleanup() {
        let mut export = decode(
            include_bytes!("../../../design/charon-trial/borrowed-loop/loop.ullbc"),
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
            C0VerificationSession::new_program_prepared(
                include_str!("../../../design/charon-trial/borrowed-loop/loop.click"),
                &prepared
            )
            .is_err()
        );
    }

    #[test]
    fn charon_trial_rejects_partial_or_incompatible_extraction() {
        let mutations: [fn(&mut TrialArtifact); 5] = [
            |a| a.data.has_errors = true,
            |a| a.compiler_commit = out::COMPILER_COMMIT.into(),
            |a| a.flags[3] = "-Coverflow-checks=off".into(),
            |a| a.data.translated.options.skip_borrowck = true,
            |a| a.data.translated.options.mir = Some(charon_lib::options::MirLevel::Elaborated),
        ];
        for mutation in mutations {
            let mut artifact: TrialArtifact = serde_json::from_slice(ARTIFACT).unwrap();
            mutation(&mut artifact);
            assert!(decode(&serde_json::to_vec(&artifact).unwrap(), "trial.rs", SOURCE).is_err());
        }
    }

    #[test]
    fn charon_trial_checked_authority_rejects_duplicate_move_drop_and_missing_cleanup() {
        let original = decode(ARTIFACT, "trial.rs", SOURCE).unwrap();
        for corruption in 0..4 {
            let mut export = original.clone();
            let mir = export
                .functions
                .iter_mut()
                .find(|f| f.name == "guarded_increment")
                .unwrap()
                .mir
                .as_mut()
                .unwrap();
            if corruption == 0 || corruption == 3 {
                let block = mir
                    .blocks
                    .iter_mut()
                    .find(|b| b.statements.iter().any(|s| matches!(s, S::Move { .. })))
                    .unwrap();
                let index = block
                    .statements
                    .iter()
                    .position(|s| matches!(s, S::Move { .. }))
                    .unwrap();
                let extra = if corruption == 0 {
                    block.statements[index].clone()
                } else {
                    let S::Move { source, record, .. } = &block.statements[index] else {
                        unreachable!()
                    };
                    S::Assign {
                        target: E::Local {
                            name: "__rust_mir_0".into(),
                        },
                        value: E::Cast {
                            value: Box::new(E::Field {
                                base: Box::new(E::Local {
                                    name: source.clone(),
                                }),
                                record: record.clone(),
                                field: "saved".into(),
                            }),
                            value_type: Type::U16,
                        },
                    }
                };
                block.statements.insert(index + 1, extra);
            } else {
                let index = mir
                    .blocks
                    .iter()
                    .position(|b| matches!(b.terminator, T::Drop { .. }))
                    .unwrap();
                let T::Drop {
                    local,
                    record,
                    target,
                } = mir.blocks[index].terminator.clone()
                else {
                    unreachable!()
                };
                if corruption == 1 {
                    let duplicate = mir.blocks.len();
                    mir.blocks.push(out::MirBlock {
                        statements: vec![],
                        terminator: T::Drop {
                            local: local.clone(),
                            record: record.clone(),
                            target,
                        },
                    });
                    mir.blocks[index].terminator = T::Drop {
                        local,
                        record,
                        target: duplicate,
                    };
                } else {
                    mir.blocks[index].terminator = T::Goto { target };
                }
            }
            // Corrupt the compiler correspondence deliberately, then test the actual
            // shared checker rather than rustc's rejection of invalid safe source.
            let prepared = super::super::import::prepared_for_test(export).unwrap();
            assert!(
                C0VerificationSession::new_program_prepared(CLAIM, &prepared).is_err(),
                "corruption {corruption}"
            );
        }
    }
}
