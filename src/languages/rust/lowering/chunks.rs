//! A `ChunksExact<'_, u8>` is held as its own fields, as `core` declares
//! them: `v`, the chunks still to come, `rem`, the elements they leave over,
//! and `chunk_size`. Each slice holds a pointer and a length. A proof reads
//! these fields as `iter.v`, `iter.v.len()`, `iter.rem`, `iter.rem.len()`
//! and `iter.chunk_size`.
use super::*;
use crate::kernel::program_expression::variable;
use crate::languages::interface::ChunkIteratorFields;

impl ChunkIteratorFields {
    fn advance(&self) -> ProgramStatement {
        use crate::kernel::program_expression::{add, subtract};
        program_seq(
            program_assign(
                self.remaining.clone(),
                add(variable(&self.remaining), variable(&self.size)),
            ),
            program_assign(
                self.remaining_length.clone(),
                subtract(variable(&self.remaining_length), variable(&self.size)),
            ),
        )
    }

    fn has_next(&self) -> ProgramExpression {
        crate::kernel::program_expression::less_equal(
            variable(&self.size),
            variable(&self.remaining_length),
        )
    }
}

/// The tag and payload storage of `Option<&[u8]>` returned by `next`.
pub(super) struct ChunkOptionFields {
    pub(super) tag: BindingName,
    pub(super) pointer: BindingName,
    pub(super) length: BindingName,
}

impl Context<'_> {
    pub(super) fn chunk_iterator(&self, name: &MirLocalId) -> Result<&ChunkIteratorFields, String> {
        self.mir_chunk_iterators
            .get(name)
            .ok_or_else(|| "unknown Rust chunk iterator".into())
    }

    pub(super) fn chunk_option(&self, name: &MirLocalId) -> Result<&ChunkOptionFields, String> {
        self.chunk_options
            .get(name)
            .ok_or_else(|| "unknown chunk Option".into())
    }

    pub(super) fn chunk_storage(
        &mut self,
        name: &MirLocalId,
        option: bool,
        owner: &LocalFunctionId,
        ordinal: u32,
    ) -> Result<ProgramStatement, String> {
        if !self.locals.insert(name.clone()) {
            return Err("chunk state identity collision".into());
        }
        if !option {
            let [
                remaining,
                remaining_length,
                remainder,
                remainder_length,
                size,
            ] = LocalBindingId::chunk_iterator_fields(owner.clone(), ordinal)
                .map(BindingName::from);
            let fields = ChunkIteratorFields {
                remaining,
                remaining_length,
                remainder,
                remainder_length,
                size,
            };
            let mut result = program_skip();
            for binding in fields.bindings() {
                let ty = binding.program_type().expect("chunk field type");
                result = program_seq(
                    result,
                    program_declare_with_all_qualifiers(
                        binding.clone(),
                        ty,
                        false,
                        false,
                        false,
                        ty.is_pointer(),
                    ),
                );
            }
            self.mir_chunk_iterators.insert(name.clone(), fields);
            return Ok(result);
        }

        let [tag, pointer] =
            LocalBindingId::iterator_option_fields(owner, ordinal, ProgramType::UInt8Pointer)
                .map(BindingName::from);
        let length = LocalBindingId::iterator_option_length(owner, ordinal).into();
        let mut result = program_skip();
        for binding in [&tag, &pointer, &length] {
            let ty = binding.program_type().expect("chunk Option field type");
            result = program_seq(
                result,
                program_declare_with_all_qualifiers(
                    binding.clone(),
                    ty,
                    false,
                    false,
                    false,
                    ty.is_pointer(),
                ),
            );
        }
        result = program_seq(
            result,
            program_assign(
                tag.clone(),
                crate::kernel::program_expression::int32_literal(0),
            ),
        );
        self.chunk_options.insert(
            name.clone(),
            ChunkOptionFields {
                tag,
                pointer,
                length,
            },
        );
        Ok(result)
    }

    /// `slice.chunks_exact(size)`, as `core` builds it: it panics on a zero
    /// size, then `v` is the first `len - len % size` elements and `rem` the
    /// rest.
    pub(super) fn chunk_initialize_mir(
        &mut self,
        iterator: &MirLocalId,
        slice: &E,
        size: &E,
    ) -> Result<ProgramStatement, String> {
        if !self.shared_byte_slice(slice) {
            return Err("chunks_exact requires a shared byte-slice local".into());
        }
        let fields = self.chunk_iterator(iterator)?.clone();
        // The slice is a local, so its parts are its own locals, read
        // before anything here writes.
        let (pointer, length) = self.slice_parts(slice)?;
        let (size_prefix, size) = self.prepared_expr(size)?;
        use crate::kernel::program_expression::{
            add, not_equal, remainder, subtract, uint64_literal,
        };
        let mut result = size_prefix;
        for statement in [
            program_assign(fields.size.clone(), size),
            program_labeled_assert(
                not_equal(variable(&fields.size), uint64_literal(0)),
                "Rust chunks_exact panic check",
            ),
            program_assign(
                fields.remainder_length.clone(),
                remainder(length.clone(), variable(&fields.size)),
            ),
            program_assign(fields.remaining.clone(), pointer.clone()),
            program_assign(
                fields.remaining_length.clone(),
                subtract(length, variable(&fields.remainder_length)),
            ),
            program_assign(
                fields.remainder.clone(),
                add(pointer, variable(&fields.remaining_length)),
            ),
        ] {
            result = program_seq(result, statement);
        }
        Ok(result)
    }

    pub(super) fn chunk_move(
        &mut self,
        target: &MirLocalId,
        source: &MirLocalId,
    ) -> Result<ProgramStatement, String> {
        let target_fields = self.mir_chunk_iterators.get(target);
        let source_fields = self.mir_chunk_iterators.get(source);
        if let (Some(destination), Some(origin)) = (target_fields, source_fields)
            && target != source
        {
            let mut result = program_skip();
            for (target, source) in destination.bindings().into_iter().zip(origin.bindings()) {
                result = program_seq(result, program_assign(target.clone(), variable(source)));
            }
            return Ok(result);
        }
        Err("invalid chunk move".into())
    }

    /// Whether the remaining slice contains a full chunk.
    pub(super) fn chunk_has_next(
        &self,
        iterator: &MirLocalId,
    ) -> Result<ProgramExpression, String> {
        Ok(self.chunk_iterator(iterator)?.has_next())
    }

    /// `next()`, as `core` runs it: `v.split_at(chunk_size)`, keeping the
    /// back as `v` and returning the front.
    /// `next` of a chunk iterator: the `Option` built in `option`, or, once
    /// the loop reads only its chunk, the chunk assigned to the slice local
    /// `payload`. When the `for` header's test decided whether it yields
    /// (`taken`), only that arm runs; the arm that does not yield is nothing.
    pub(super) fn chunk_next(
        &mut self,
        iterator: &MirLocalId,
        option: Option<&MirLocalId>,
        payload: Option<&MirLocalId>,
        taken: Option<bool>,
    ) -> Result<ProgramStatement, String> {
        use crate::kernel::program_expression::int32_literal;
        let Some(option) = option else {
            let fields = self.chunk_iterator(iterator)?;
            if taken == Some(false) {
                return Ok(program_skip());
            }
            let mut some = program_skip();
            if let Some(payload) = payload {
                let Some((length, constant)) = self.slices.get(payload).cloned() else {
                    return Err("chunk payload requires a byte-slice local".into());
                };
                some = program_seq(
                    program_assign(
                        self.binding(payload)?,
                        reference_view(
                            variable(&fields.remaining),
                            ProgramType::UInt8Pointer,
                            false,
                            constant,
                        ),
                    ),
                    program_assign(length, variable(&fields.size)),
                );
            }
            let some = program_seq(some, fields.advance());
            return Ok(match taken {
                Some(_) => some,
                None => program_if(fields.has_next(), some, program_skip()),
            });
        };
        let option = self.chunk_option(option)?;
        let fields = self.chunk_iterator(iterator)?;
        let mut some = program_assign(option.tag.clone(), int32_literal(1));
        for statement in [
            program_assign(option.pointer.clone(), variable(&fields.remaining)),
            program_assign(option.length.clone(), variable(&fields.size)),
            fields.advance(),
        ] {
            some = program_seq(some, statement);
        }
        Ok(program_if(
            fields.has_next(),
            some,
            program_assign(option.tag.clone(), int32_literal(0)),
        ))
    }

    pub(super) fn chunk_slice_checks(&self, value: &E) -> Result<ProgramStatement, String> {
        match value {
            E::ChunkOptionSlice { option } => {
                Ok(program_assert(crate::kernel::program_expression::equal(
                    variable(&self.chunk_option(option)?.tag),
                    crate::kernel::program_expression::int32_literal(1),
                )))
            }
            _ => Ok(program_skip()),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::languages::rust::schema::Place;

    #[test]
    fn chunk_iterator_fields_are_distinct_from_source_locals() {
        let mut export = crate::languages::rust::charon::decode(
            include_bytes!(
                "../../../../design/charon-trial/chunks/.click/captures/chunks/chunks.rs.ullbc"
            ),
            "chunks.rs",
            include_bytes!("../../../../design/charon-trial/chunks/chunks.rs"),
        )
        .unwrap();
        let function = export
            .functions
            .iter_mut()
            .find(|f| f.name == "walk")
            .unwrap();
        let mir = function.mir.as_mut().unwrap();
        let iterator = mir
            .locals
            .iter()
            .find(|local| local.value_type == Type::ChunkIterator)
            .unwrap();
        let colliding = ["v", "v_len", "rem", "rem_len", "chunk_size"].map(|field| Place {
            name: format!("{}_{field}", iterator.name).into(),
            value_type: Type::Usize,
            span: iterator.span.clone(),
        });
        mir.locals.extend(colliding);
        super::super::lower(&export).unwrap();
    }

    #[test]
    #[cfg(not(feature = "fast-gate"))]
    #[ignore = "nightly: replay both chunk Option outcomes"]
    fn chunk_option_fields_expand_and_replay() {
        use crate::languages::rust::schema::{MirStatement as S, MirTerminator};
        use crate::surface::{
            ProgramVerificationSession, expand_program_prepared_claim_source_by_label,
            without_implicit_solve_for_claim,
        };

        let mut export = crate::languages::rust::charon::decode(
            include_bytes!(
                "../../../../design/charon-trial/chunks/.click/captures/chunks/chunks.rs.ullbc"
            ),
            "chunks.rs",
            include_bytes!("../../../../design/charon-trial/chunks/chunks.rs"),
        )
        .unwrap();
        let mir = export
            .functions
            .iter_mut()
            .find(|f| f.name == "next_len")
            .unwrap()
            .mir
            .as_mut()
            .unwrap();

        // The ordinary importer binds the payload directly. Keep the Option
        // through the match here to exercise its lowering and tag check.
        let option = MirLocalId::from("chunk_option");
        let header = mir
            .blocks
            .iter()
            .position(|block| {
                matches!(
                    block.terminator,
                    MirTerminator::If {
                        condition: E::ChunkHasNext { .. },
                        ..
                    }
                )
            })
            .unwrap();
        let MirTerminator::If {
            condition,
            then_target,
            else_target,
        } = mir.blocks[header].terminator.clone()
        else {
            unreachable!()
        };
        let E::ChunkHasNext { iterator } = condition else {
            unreachable!()
        };
        mir.blocks[header].statements.push(S::ChunkNext {
            iterator,
            option: Some(option.clone()),
            payload: None,
            taken: None,
        });
        mir.blocks[header].terminator = MirTerminator::If {
            condition: E::ChunkOptionTag {
                option: option.clone(),
            },
            then_target,
            else_target,
        };
        for (target, yields) in [(then_target, true), (else_target, false)] {
            let statements = &mut mir.blocks[target].statements;
            let position = statements
                .iter()
                .position(|statement| matches!(statement, S::ChunkNext { .. }))
                .unwrap();
            let S::ChunkNext { payload, taken, .. } = statements.remove(position) else {
                unreachable!()
            };
            assert_eq!(taken, Some(yields));
            if let Some(name) = payload {
                statements.insert(
                    position,
                    S::Assign {
                        target: E::Local { name },
                        value: E::ChunkOptionSlice {
                            option: option.clone(),
                        },
                    },
                );
            } else {
                assert!(!yields);
            }
        }
        let span = mir.locals[0].span.clone();
        mir.locals.push(Place {
            name: option.clone(),
            value_type: Type::ChunkOption,
            span: span.clone(),
        });
        mir.locals
            .extend(["some", "pointer", "len"].map(|field| Place {
                name: format!("{option}_{field}").into(),
                value_type: Type::Usize,
                span: span.clone(),
            }));
        let prepared = crate::languages::rust::import::prepared_for_test(export).unwrap();

        for (length, result) in [(3u64, 0), (4, 4)] {
            let sidecar = format!(
                "verifying \"chunks.rs\"; fn next_len(bytes: &[u8]) -> usize {{ requires bytes.len() == {length}u64; ensures result == {result}u64; }} by {{ step_until(function.exit); close(); }}"
            );
            let claim = "next_len.contract";
            let expanded =
                expand_program_prepared_claim_source_by_label(&sidecar, &prepared, claim).unwrap();
            assert_ne!(expanded, sidecar);
            assert!(
                !expanded.contains("chunk_option") && !expanded.contains("<iterator option "),
                "{expanded}"
            );
            without_implicit_solve_for_claim(claim, || {
                ProgramVerificationSession::new_program_prepared(&expanded, &prepared)
                    .map(|_| ())
                    .map_err(|error| error.to_string())
            })
            .unwrap_or_else(|error| panic!("{error}\n{expanded}"));
        }
    }
}
