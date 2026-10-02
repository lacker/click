//! `shared-byte-chunks-exact-v1`: resolved standard protocol and typed Option
//! dispatch. State moves and next effects are retained; no iteration counter.
use super::*;

fn path(name: &a::Name, expected: &[&str]) -> bool {
    name.name.len() == expected.len()
        && name.name.iter().zip(expected).all(|(part, expected)| matches!(part, a::PathElem::Ident(actual, d) if actual == expected && *d == a::Disambiguator::ZERO))
}
fn variable(ty: &a::Ty) -> bool {
    matches!(ty.kind(), a::TyKind::TypeVar(a::DeBruijnVar::Bound(depth, id)) if depth.index == 0 && id.index() == 0)
}
fn shared_slice(ty: &a::Ty, template: bool) -> bool {
    matches!(ty.kind(), a::TyKind::Ref(_, pointee, a::RefKind::Shared)
        if matches!(pointee.kind(), a::TyKind::Slice(element, _) if if template { variable(element) } else { byte_slice(pointee) }))
}
impl Adapter<'_> {
    fn chunk_adt(&self, ty: &a::Ty, template: bool) -> bool {
        let a::TyKind::Adt(r) = ty.kind() else {
            return false;
        };
        let Some(decl) = self.krate.type_decls.get(r.id) else {
            return false;
        };
        !decl.item_meta.is_local
            && path(
                &decl.item_meta.name,
                &["core", "slice", "iter", "ChunksExact"],
            )
            && matches!(decl.src, a::TypeSource::Normal)
            && matches!(decl.kind, a::TypeDeclKind::Opaque)
            && decl.generics.regions.len() == 1
            && r.generics.regions.len() == 1
            && decl.generics.types.len() == 1
            && decl.generics.const_generics.is_empty()
            && r.generics.types.len() == 1
            && r.generics.const_generics.is_empty()
            && if template {
                variable(&r.generics.types[0])
            } else {
                matches!(self.ty(&r.generics.types[0]), Ok(Type::U8))
            }
    }
    pub(super) fn chunk_type(&self, ty: &a::Ty) -> bool {
        self.chunk_adt(ty, false)
    }
    fn option_adt(&self, ty: &a::Ty, template: bool) -> bool {
        let a::TyKind::Adt(r) = ty.kind() else {
            return false;
        };
        let Some(decl) = self.krate.type_decls.get(r.id) else {
            return false;
        };
        !decl.item_meta.is_local
            && decl.item_meta.lang_item == Some(LangItem::Option)
            && path(&decl.item_meta.name, &["core", "option", "Option"])
            && matches!(decl.src, a::TypeSource::Normal)
            && matches!(decl.kind, a::TypeDeclKind::Opaque)
            && decl.generics.regions.is_empty()
            && decl.generics.types.len() == 1
            && decl.generics.const_generics.is_empty()
            && r.generics.regions.is_empty()
            && r.generics.types.len() == 1
            && r.generics.const_generics.is_empty()
            && shared_slice(&r.generics.types[0], template)
    }
    pub(super) fn chunk_option_type(&self, ty: &a::Ty) -> bool {
        self.option_adt(ty, false)
    }
    fn chunk_reference(&self, ty: &a::Ty) -> Option<bool> {
        match ty.kind() {
            a::TyKind::Ref(_, p, kind) if self.chunk_type(p) => Some(*kind == a::RefKind::Mut),
            _ => None,
        }
    }
}

pub(super) fn bindings(
    adapter: &Adapter<'_>,
    body: &u::ExprBody,
) -> Result<
    (
        BTreeMap<a::LocalId, a::LocalId>,
        BTreeMap<a::LocalId, a::LocalId>,
    ),
    String,
> {
    let mut references = BTreeMap::new();
    let mut discriminants = BTreeMap::new();
    for statement in body.body.iter().flat_map(|block| &block.statements) {
        let u::StatementKind::Assign(target, value) = &statement.kind else {
            continue;
        };
        if let Some(mutable) = adapter.chunk_reference(&target.ty) {
            let a::PlaceKind::Local(target) = target.kind else {
                return Err(unsupported("partial chunk reference"));
            };
            let a::Rvalue::Ref {
                place,
                kind,
                ptr_metadata,
            } = value
            else {
                return Err(unsupported("chunk reference assignment"));
            };
            if !ptr_metadata.ty().is_unit()
                || !matches!(
                    kind,
                    a::BorrowKind::Shared | a::BorrowKind::Mut | a::BorrowKind::TwoPhaseMut
                )
                || mutable != matches!(kind, a::BorrowKind::Mut | a::BorrowKind::TwoPhaseMut)
            {
                return Err(unsupported("chunk reference mutability/metadata"));
            }
            let source = match &place.kind {
                a::PlaceKind::Local(id) if adapter.chunk_type(&place.ty) => *id,
                a::PlaceKind::Projection(base, a::ProjectionElem::Deref)
                    if adapter.chunk_type(&place.ty)
                        && adapter
                            .chunk_reference(&base.ty)
                            .is_some_and(|source| !mutable || source) =>
                {
                    local(base)?
                }
                _ => return Err(unsupported("chunk reference origin")),
            };
            if references.insert(target, source).is_some() {
                return Err(unsupported("reassigned chunk reference"));
            }
        }
        if let a::Rvalue::Discriminant(option) = value
            && adapter.chunk_option_type(&option.ty)
        {
            if !matches!(
                target.ty.kind(),
                a::TyKind::Scalar(a::ScalarTy::Integer(a::IntegerTy::Signed(a::IntTy::Isize)))
            ) {
                return Err(unsupported("chunk option discriminant type"));
            }
            if discriminants
                .insert(local(target)?, local(option)?)
                .is_some()
            {
                return Err(unsupported("reassigned chunk discriminant"));
            }
        }
    }
    // Resolve each alias path once. Subsequent method calls use its root
    // directly, including long source reborrow chains.
    let mut roots = BTreeMap::new();
    for &start in references.keys() {
        let mut current = start;
        let mut pending = Vec::new();
        let mut seen = BTreeSet::new();
        while let Some(&next) = references.get(&current) {
            if let Some(&root) = roots.get(&current) {
                current = root;
                break;
            }
            if !seen.insert(current) {
                return Err(unsupported("cyclic chunk reference"));
            }
            pending.push(current);
            current = next;
        }
        for reference in pending {
            roots.insert(reference, current);
        }
    }
    Ok((roots, discriminants))
}
fn local(place: &a::Place) -> Result<a::LocalId, String> {
    match place.kind {
        a::PlaceKind::Local(id) => Ok(id),
        _ => Err(unsupported("chunk protocol requires complete locals")),
    }
}
fn operand_place(op: &a::Operand) -> Result<&a::Place, String> {
    match op {
        a::Operand::Copy(p) | a::Operand::Move(p) => Ok(p),
        _ => Err(unsupported("chunk protocol operand")),
    }
}
impl BodyAdapter<'_, '_> {
    fn chunk_root(&self, place: &a::Place) -> Result<String, String> {
        let mut id = local(place)?;
        let mut seen = BTreeSet::new();
        while let Some(source) = self.chunk_refs.get(&id) {
            if !seen.insert(id) {
                return Err(unsupported("cyclic chunk reference"));
            }
            id = *source;
        }
        let entry = self
            .body
            .locals
            .locals
            .get(id)
            .ok_or_else(|| unsupported("chunk reference root"))?;
        if !self.adapter.chunk_type(&entry.ty) {
            return Err(unsupported("chunk reference root type"));
        }
        self.local(id)
    }
    pub(super) fn chunk_statement(
        &self,
        statement: &u::Statement,
    ) -> Result<Option<Option<S>>, String> {
        match &statement.kind {
            u::StatementKind::Assign(target, _)
                if self.adapter.chunk_reference(&target.ty).is_some() =>
            {
                Ok(Some(None))
            }
            u::StatementKind::Assign(target, a::Rvalue::Discriminant(option))
                if self.adapter.chunk_option_type(&option.ty) =>
            {
                Ok(Some(Some(S::Assign {
                    target: self.place(target)?,
                    value: E::ChunkOptionTag {
                        option: self.local(local(option)?)?,
                    },
                })))
            }
            u::StatementKind::Assign(target, value) if self.adapter.chunk_type(&target.ty) => {
                let a::Rvalue::Use(a::Operand::Move(source), _) = value else {
                    return Err(unsupported("chunk iterator requires a complete move"));
                };
                if !self.adapter.chunk_type(&source.ty) {
                    return Err(unsupported("chunk move type"));
                }
                Ok(Some(Some(S::ChunkMove {
                    target: self.local(local(target)?)?,
                    source: self.local(local(source)?)?,
                })))
            }
            u::StatementKind::StorageDead(id) if self.chunk_refs.contains_key(id) => Ok(Some(None)),
            _ => Ok(None),
        }
    }
    pub(super) fn chunk_projection(&self, place: &a::Place) -> Result<Option<E>, String> {
        if let a::PlaceKind::Projection(base, a::ProjectionElem::Field(Some(variant), field)) =
            &place.kind
            && self.adapter.chunk_option_type(&base.ty)
        {
            if variant.index() != 1 || field.index() != 0 || !shared_slice(&place.ty, false) {
                return Err(unsupported("chunk Option projection"));
            }
            return Ok(Some(E::ChunkOptionSlice {
                option: self.local(local(base)?)?,
            }));
        }
        Ok(None)
    }
    pub(super) fn chunk_switch(&self, t: &u::Terminator) -> Result<Option<T>, String> {
        let u::TerminatorKind::Switch { data, branches } = &t.kind else {
            return Ok(None);
        };
        let a::SwitchScrutinee::Value(value) = &data.scrutinee else {
            return Ok(None);
        };
        let place = operand_place(value)?;
        let a::PlaceKind::Local(id) = place.kind else {
            return Ok(None);
        };
        let Some(option) = self.chunk_discriminants.get(&id) else {
            return Ok(None);
        };
        let mut targets = [None, None];
        for (constant, branch) in &data.branches {
            let a::ConstantExprKind::Integer(a::IntegerValue::Signed(a::IntTy::Isize, tag)) =
                constant.kind()
            else {
                return Err(unsupported("chunk discriminant branch type"));
            };
            let tag =
                usize::try_from(*tag).map_err(|_| unsupported("chunk discriminant branch"))?;
            if tag > 1
                || targets[tag]
                    .replace(
                        branches
                            .get(*branch)
                            .ok_or_else(|| unsupported("chunk Option branch target"))?
                            .index(),
                    )
                    .is_some()
            {
                return Err(unsupported("chunk discriminant branch"));
            }
        }
        if data.branches.len() != 2
            || !data
                .fallback
                .and_then(|fallback| branches.get(fallback))
                .and_then(|target| self.body.body.get(*target))
                .is_some_and(|block| {
                    matches!(block.terminator.kind, u::TerminatorKind::UndefinedBehavior)
                })
        {
            return Err(unsupported("chunk Option dispatch"));
        }
        Ok(Some(T::If {
            condition: E::ChunkOptionTag {
                option: self.local(*option)?,
            },
            then_target: targets[1].ok_or_else(|| unsupported("missing Some branch"))?,
            else_target: targets[0].ok_or_else(|| unsupported("missing None branch"))?,
        }))
    }
    pub(super) fn chunk_call(&self, terminator: &u::Terminator) -> Result<Option<S>, String> {
        let u::TerminatorKind::Call { call, .. } = &terminator.kind else {
            return Ok(None);
        };
        let a::FnOperand::Regular(ptr) = &call.func else {
            return Ok(None);
        };
        let callee = &self.adapter.krate.fun_decls[self.adapter.resolve(ptr)?];
        let relevant = self.adapter.chunk_type(&call.dest.ty)
            || self.adapter.chunk_option_type(&call.dest.ty)
            || call
                .args
                .iter()
                .any(|op| self.adapter.chunk_reference(op.ty()).is_some());
        if !relevant {
            return Ok(None);
        }
        if callee.item_meta.is_local
            || callee.signature.is_unsafe
            || callee.signature.is_variadic
            || callee.signature.abi != a::Abi::Rust
            || call.safety == a::CallSafety::Unsafe
            || callee.generics.types.len() != 1
            || !callee.generics.const_generics.is_empty()
            || ptr.generics.types.len() != 1
            || !ptr.generics.const_generics.is_empty()
        {
            return Err(unsupported("chunk model declaration/type mismatch"));
        }
        let elements = &callee.item_meta.name.name;
        let method = match elements.last() {
            Some(a::PathElem::Ident(name, d)) if *d == a::Disambiguator::ZERO => name.as_str(),
            _ => return Err(unsupported("chunk model method identity")),
        };
        let destination = self.local(local(&call.dest)?)?;
        match (&callee.src, method) {
            (a::FunSource::Normal, "chunks_exact" | "remainder") => {
                let prefix: &[&str] = if method == "chunks_exact" {
                    &["core", "slice"]
                } else {
                    &["core", "slice", "iter"]
                };
                if elements.len() != prefix.len() + 2 || !elements[..prefix.len()].iter().zip(prefix).all(|(part, expected)| matches!(part, a::PathElem::Ident(actual, d) if actual == expected && *d == a::Disambiguator::ZERO)) { return Err(unsupported("chunk inherent method identity")) }
                let a::PathElem::Impl(a::ImplElem::Ty(receiver)) = &elements[prefix.len()] else {
                    return Err(unsupported("chunk inherent receiver"));
                };
                if self.adapter.ty(&ptr.generics.types[0])? != Type::U8 {
                    return Err(unsupported("chunk element instantiation"));
                }
                if method == "chunks_exact" {
                    if !matches!(receiver.skip_binder.kind(), a::TyKind::Slice(element, _) if variable(element))
                        || !matches!(callee.signature.inputs.as_slice(), [slice, size] if shared_slice(slice, true) && self.adapter.ty(size).ok() == Some(Type::Usize))
                        || !self.adapter.chunk_adt(&callee.signature.output, true)
                        || !self.adapter.chunk_type(&call.dest.ty)
                    {
                        return Err(unsupported("chunks_exact signature"));
                    }
                    let [slice, size] = call.args.as_slice() else {
                        return Err(unsupported("chunks_exact arity"));
                    };
                    if !shared_slice(slice.ty(), false)
                        || self.adapter.ty(size.ty())? != Type::Usize
                    {
                        return Err(unsupported("chunks_exact argument types"));
                    }
                    Ok(Some(S::ChunkInitialize {
                        target: destination,
                        slice: self.operand(slice)?,
                        size: self.operand(size)?,
                    }))
                } else {
                    if !self.adapter.chunk_adt(&receiver.skip_binder, true)
                        || !matches!(callee.signature.inputs.as_slice(), [reference] if matches!(reference.kind(), a::TyKind::Ref(_, p, a::RefKind::Shared) if self.adapter.chunk_adt(p, true)))
                        || !shared_slice(&callee.signature.output, true)
                        || !shared_slice(&call.dest.ty, false)
                    {
                        return Err(unsupported("chunk remainder signature"));
                    }
                    let [argument] = call.args.as_slice() else {
                        return Err(unsupported("chunk remainder arity"));
                    };
                    if self.adapter.chunk_reference(argument.ty()) != Some(false) {
                        return Err(unsupported("chunk remainder receiver type"));
                    }
                    Ok(Some(S::Assign {
                        target: E::Local { name: destination },
                        value: E::ChunkRemainder {
                            iterator: self.chunk_root(operand_place(argument)?)?,
                        },
                    }))
                }
            }
            (
                a::FunSource::TraitImpl {
                    trait_ref,
                    impl_ref,
                    item_id,
                    ..
                },
                "next" | "into_iter",
            ) => {
                let tr = &self.adapter.krate.trait_decls[trait_ref.id];
                let imp = &self.adapter.krate.trait_impls[impl_ref.id];
                if tr.item_meta.is_local
                    || imp.item_meta.is_local
                    || elements[..elements.len() - 1] != imp.item_meta.name.name
                    || imp.is_unsafe
                    || imp.is_negative
                    || !matches!(imp.src, a::TraitImplSource::Normal)
                    || imp.impl_trait.id != trait_ref.id
                    || imp.impl_trait.generics.types.len() != 1
                    || !imp.impl_trait.generics.const_generics.is_empty()
                    || tr
                        .methods
                        .get(*item_id)
                        .is_none_or(|declaration| declaration.skip_binder.name.0 != method)
                    || item_id.index() != 0
                    || tr.item_meta.diagnostic_item.as_deref()
                        != Some(if method == "next" {
                            "Iterator"
                        } else {
                            "IntoIterator"
                        })
                    || imp
                        .methods
                        .get(*item_id)
                        .is_none_or(|definition| definition.skip_binder.id != callee.def_id)
                {
                    return Err(unsupported("chunk trait/implementation identity"));
                }
                let [argument] = call.args.as_slice() else {
                    return Err(unsupported("chunk protocol arity"));
                };
                if method == "into_iter" {
                    if !path(
                        &tr.item_meta.name,
                        &["core", "iter", "traits", "collect", "IntoIterator"],
                    ) || !variable(&imp.impl_trait.generics.types[0])
                        || !variable(&callee.signature.output)
                        || !matches!(callee.signature.inputs.as_slice(), [input] if variable(input))
                        || !self.adapter.chunk_type(&ptr.generics.types[0])
                        || !self.adapter.chunk_type(argument.ty())
                        || !self.adapter.chunk_type(&call.dest.ty)
                        || !matches!(argument, a::Operand::Move(_))
                    {
                        return Err(unsupported("chunk into_iter signature/type"));
                    }
                    Ok(Some(S::ChunkMove {
                        target: destination,
                        source: self.local(local(operand_place(argument)?)?)?,
                    }))
                } else {
                    if !path(
                        &tr.item_meta.name,
                        &["core", "iter", "traits", "iterator", "Iterator"],
                    ) || !self
                        .adapter
                        .chunk_adt(&imp.impl_trait.generics.types[0], true)
                        || tr.item_meta.lang_item != Some(LangItem::Iterator)
                        || !matches!(callee.signature.inputs.as_slice(), [input] if matches!(input.kind(), a::TyKind::Ref(_, p, a::RefKind::Mut) if self.adapter.chunk_adt(p, true)))
                        || !self.adapter.option_adt(&callee.signature.output, true)
                        || self.adapter.ty(&ptr.generics.types[0])? != Type::U8
                        || self.adapter.chunk_reference(argument.ty()) != Some(true)
                        || !self.adapter.chunk_option_type(&call.dest.ty)
                    {
                        return Err(unsupported("chunk next signature/type"));
                    }
                    Ok(Some(S::ChunkNext {
                        iterator: self.chunk_root(operand_place(argument)?)?,
                        option: destination,
                    }))
                }
            }
            _ => Err(unsupported("unmodeled chunk iterator method")),
        }
    }
}

/// Split the assessed next+Option dispatch into a pure state guard and two
/// edge-local transitions. Both taken and final false calls still execute
/// `next` exactly once. This exposes the natural loop to the shared CFG pass.
pub(super) fn split_next_branches(blocks: &mut Vec<out::MirBlock>) -> Result<(), String> {
    let original_len = blocks.len();
    let mut predecessors = vec![Vec::new(); original_len];
    for (index, block) in blocks.iter().enumerate() {
        crate::instrumentation::record_deterministic_work(1);
        let targets = match block.terminator {
            T::Goto { target } | T::Call { target, .. } | T::Drop { target, .. } => vec![target],
            T::If {
                then_target,
                else_target,
                ..
            } => vec![then_target, else_target],
            _ => Vec::new(),
        };
        for target in targets {
            crate::instrumentation::record_deterministic_work(1);
            predecessors
                .get_mut(target)
                .ok_or_else(|| unsupported("chunk CFG successor"))?
                .push(index);
        }
    }
    for header in 0..original_len {
        crate::instrumentation::record_deterministic_work(1);
        let Some(S::ChunkNext { iterator, option }) = blocks[header].statements.last().cloned()
        else {
            continue;
        };
        let T::Goto { target: dispatch } = blocks[header].terminator else {
            return Err(unsupported("chunk next continuation"));
        };
        let T::If {
            condition: E::ChunkOptionTag { option: dispatched },
            then_target,
            else_target,
        } = &blocks[dispatch].terminator
        else {
            return Err(unsupported("chunk next requires typed Option dispatch"));
        };
        if dispatched != &option || !blocks[dispatch].statements.iter().all(|s| matches!(s, S::Assign { target: E::Local { .. }, value: E::ChunkOptionTag { option: value } } if value == &option)) { return Err(unsupported("chunk next dispatch effects")) }
        // Reject external entry into the dispatch; it must denote this call.
        if predecessors[dispatch].as_slice() != [header] {
            return Err(unsupported("shared chunk next dispatch"));
        }
        let targets = [*then_target, *else_target];
        let first = blocks.len();
        for target in targets {
            blocks.push(out::MirBlock {
                statements: vec![S::ChunkNext {
                    iterator: iterator.clone(),
                    option: option.clone(),
                }],
                terminator: T::Goto { target },
            });
        }
        blocks[header].statements.pop();
        blocks[header].terminator = T::If {
            condition: E::ChunkHasNext { iterator },
            then_target: first,
            else_target: first + 1,
        };
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    fn protocol() -> Vec<out::MirBlock> {
        vec![
            out::MirBlock {
                statements: vec![S::ChunkNext {
                    iterator: "iter".into(),
                    option: "option".into(),
                }],
                terminator: T::Goto { target: 1 },
            },
            out::MirBlock {
                statements: vec![],
                terminator: T::If {
                    condition: E::ChunkOptionTag {
                        option: "option".into(),
                    },
                    then_target: 2,
                    else_target: 3,
                },
            },
            out::MirBlock {
                statements: vec![],
                terminator: T::Goto { target: 0 },
            },
            out::MirBlock {
                statements: vec![],
                terminator: T::Return,
            },
        ]
    }
    #[test]
    fn next_dispatch_retains_both_transitions_and_rejects_extra_effects_or_entries() {
        let mut blocks = protocol();
        split_next_branches(&mut blocks).unwrap();
        assert_eq!(blocks.len(), 6);
        assert!(blocks[0].statements.is_empty());
        for index in [4, 5] {
            assert!(matches!(
                blocks[index].statements.as_slice(),
                [S::ChunkNext { .. }]
            ));
        }
        for shared in [false, true] {
            let mut blocks = protocol();
            if shared {
                blocks[2].terminator = T::Goto { target: 1 };
            } else {
                blocks[1].statements.push(S::ChunkMove {
                    source: "iter".into(),
                    target: "other".into(),
                });
            }
            assert!(split_next_branches(&mut blocks).is_err());
        }
    }
    #[test]
    fn next_dispatch_output_scales_with_protocol_count() {
        for count in [8, 128, 1024] {
            let mut blocks = Vec::new();
            for index in 0..count {
                let offset = index * 4;
                let mut added = protocol();
                for block in &mut added {
                    match &mut block.terminator {
                        T::Goto { target } => *target += offset,
                        T::If {
                            then_target,
                            else_target,
                            ..
                        } => {
                            *then_target += offset;
                            *else_target += offset;
                        }
                        _ => (),
                    }
                }
                blocks.extend(added);
            }
            let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
                split_next_branches(&mut blocks)
            });
            result.unwrap();
            assert_eq!(work, count * 12);
            assert_eq!(blocks.len(), count * 6);
            assert_eq!(blocks.iter().flat_map(|b| &b.statements).count(), count * 2);
        }
    }
}
