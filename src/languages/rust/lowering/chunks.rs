//! Shared `ChunksExact` state. The tail is fixed at construction; consuming
//! chunks advances only the cursor and remaining complete-byte range.
use super::*;

impl Context<'_> {
    pub(super) fn chunk_declare(
        &mut self,
        iterator: &str,
        slice: &E,
        size: &E,
    ) -> Result<CStatement, String> {
        if !matches!(slice, E::ChunkRemainder { .. })
            && !matches!(slice, E::Local { name } if self.slices.get(name).is_some_and(|(_, shared)| *shared))
        {
            return Err("chunks_exact requires a shared byte-slice local".into());
        }
        let (pointer, length) = self.slice_parts(slice)?;
        let (pointer_capture, pointer_name) = self.capture_operand(
            pointer,
            &Type::Reference {
                mutable: false,
                pointee: Box::new(Type::U8),
            },
        )?;
        let (length_capture, length_name) = self.capture_operand(length, &Type::Usize)?;
        let (size_prefix, size_value) = self.prepared_expr(size)?;
        let cursor = format!("{iterator}_cursor");
        let remaining = format!("{iterator}_remaining");
        let size_name = format!("{iterator}_size");
        let tail = format!("{iterator}_tail");
        let tail_len = format!("{iterator}_tail_len");
        if !self.chunk_iterators.insert(iterator.into()) {
            return Err("duplicate Rust chunk iterator".into());
        }
        for name in [iterator, &cursor, &remaining, &size_name, &tail, &tail_len] {
            if !self.locals.insert(name.into()) {
                return Err("Rust chunk iterator state identity collision".into());
            }
        }
        let mut result = c_seq(pointer_capture, c_seq(length_capture, size_prefix));
        for (name, value_type, constant) in [
            (&cursor, CType::UInt8Pointer, true),
            (&remaining, CType::Int32, false),
            (&size_name, CType::UInt64, false),
            (&tail, CType::UInt8Pointer, true),
            (&tail_len, CType::UInt64, false),
        ] {
            result = c_seq(
                result,
                c_declare_with_all_qualifiers(name, value_type, false, false, false, constant),
            );
        }
        self.chunk_initialize_values(result, iterator, size_value, &pointer_name, &length_name)
    }

    fn chunk_initialize_values(
        &self,
        mut result: CStatement,
        iterator: &str,
        size_value: CExpression,
        pointer_name: &str,
        length_name: &str,
    ) -> Result<CStatement, String> {
        let cursor = format!("{iterator}_cursor");
        let remaining = format!("{iterator}_remaining");
        let size_name = format!("{iterator}_size");
        let tail = format!("{iterator}_tail");
        let tail_len = format!("{iterator}_tail_len");
        result = c_seq(result, c_assign(&size_name, size_value));
        result = c_seq(
            result,
            c_labeled_assert(
                c_not(c_equal(c_variable(&size_name), c_uint64_literal(0))),
                "Rust chunks_exact zero size panic check",
            ),
        );
        result = c_seq(
            result,
            c_labeled_assert(
                c_less_equal(c_variable(length_name), c_uint64_literal(i32::MAX as u64)),
                "Rust chunk iterator memory-model length bound",
            ),
        );
        result = c_seq(
            result,
            c_assign(
                &tail_len,
                c_remainder(c_variable(length_name), c_variable(&size_name)),
            ),
        );
        // Both lengths are bounded by the original length. Preserve full-width
        // chunk sizes: a size larger than the input yields only a remainder.
        result = c_seq(
            result,
            c_assign(
                &remaining,
                c_cast(
                    c_cast(
                        c_subtract(c_variable(length_name), c_variable(&tail_len)),
                        CType::UInt32,
                    ),
                    CType::Int32,
                ),
            ),
        );
        result = c_seq(result, c_assign(&cursor, c_variable(pointer_name)));
        result = c_seq(
            result,
            c_assign(
                &tail,
                c_add(c_variable(pointer_name), c_variable(&remaining)),
            ),
        );
        Ok(result)
    }

    pub(super) fn chunk_for(
        &mut self,
        iterator: &str,
        binding: &super::super::schema::Place,
        body: &[S],
    ) -> Result<CStatement, String> {
        if !self.chunk_iterators.contains(iterator)
            || binding.value_type != (Type::ByteSlice { mutable: false })
        {
            return Err(
                "Rust chunk loop requires a ChunksExact iterator yielding shared byte slices"
                    .into(),
            );
        }
        let cursor = format!("{iterator}_cursor");
        let remaining = format!("{iterator}_remaining");
        let size = format!("{iterator}_size");
        let length = format!("{}_len", binding.name);
        for name in [&binding.name, &length] {
            if !self.locals.insert(name.clone()) {
                return Err("Rust chunk binding identity collision".into());
            }
        }
        self.slices
            .insert(binding.name.clone(), (length.clone(), true));
        let mut next = c_declare_with_all_qualifiers(
            &binding.name,
            CType::UInt8Pointer,
            false,
            false,
            false,
            true,
        );
        next = c_seq(next, c_declare(&length, CType::UInt64));
        next = c_seq(next, c_assign(&binding.name, c_variable(&cursor)));
        next = c_seq(next, c_assign(&length, c_variable(&size)));
        // The successful next guard bounds the size before pointer narrowing.
        next = c_seq(
            next,
            c_labeled_assert(
                c_less_equal(c_variable(&size), c_uint64_literal(i32::MAX as u64)),
                "Rust chunk iterator memory-model offset bound",
            ),
        );
        let step = c_cast(c_cast(c_variable(&size), CType::UInt32), CType::Int32);
        next = c_seq(
            next,
            c_assign(&cursor, c_add(c_variable(&cursor), step.clone())),
        );
        next = c_seq(
            next,
            c_assign(&remaining, c_subtract(c_variable(&remaining), step)),
        );
        let source_body = self.body(body)?;
        Ok(c_while(
            c_and(
                c_less_than(c_int32_literal(0), c_variable(&remaining)),
                c_and(
                    c_less_equal(c_variable(&size), c_uint64_literal(i32::MAX as u64)),
                    c_less_equal(
                        c_cast(c_cast(c_variable(&size), CType::UInt32), CType::Int32),
                        c_variable(&remaining),
                    ),
                ),
            ),
            Vec::new(),
            c_seq(next, source_body),
        ))
    }
}

impl Context<'_> {
    pub(super) fn chunk_storage(&mut self, name: &str, option: bool) -> Result<CStatement, String> {
        if !self.locals.insert(name.into()) {
            return Err("chunk state identity collision".into());
        }
        let fields = if option {
            self.chunk_options.insert(name.into());
            vec![
                ("some", CType::Int32, false),
                ("pointer", CType::UInt8Pointer, true),
                ("len", CType::UInt64, false),
            ]
        } else {
            self.chunk_iterators.insert(name.into());
            self.mir_chunk_iterators.insert(name.into());
            vec![
                ("cursor", CType::UInt8Pointer, true),
                ("remaining", CType::Int32, false),
                ("size", CType::UInt64, false),
                ("tail", CType::UInt8Pointer, true),
                ("tail_len", CType::UInt64, false),
                ("live", CType::Int32, false),
            ]
        };
        let mut result = c_skip();
        for (suffix, ty, constant) in fields {
            let field = format!("{name}_{suffix}");
            if !self.locals.insert(field.clone()) {
                return Err("chunk metadata identity collision".into());
            }
            result = c_seq(
                result,
                c_declare_with_all_qualifiers(field, ty, false, false, false, constant),
            );
        }
        Ok(c_seq(
            result,
            c_assign(
                format!("{name}_{}", if option { "some" } else { "live" }),
                c_int32_literal(0),
            ),
        ))
    }
    fn chunk_live(&self, iterator: &str) -> Result<CStatement, String> {
        if !self.mir_chunk_iterators.contains(iterator) {
            return Err("unknown MIR chunk iterator".into());
        }
        Ok(c_assert(c_equal(
            c_variable(format!("{iterator}_live")),
            c_int32_literal(1),
        )))
    }
    pub(super) fn chunk_initialize_mir(
        &mut self,
        iterator: &str,
        slice: &E,
        size: &E,
    ) -> Result<CStatement, String> {
        if !matches!(slice, E::Local { name } if self.slices.get(name).is_some_and(|(_, shared)| *shared))
        {
            return Err("chunks_exact requires a shared byte-slice local".into());
        }
        if !self.mir_chunk_iterators.contains(iterator) {
            return Err("unknown MIR chunk iterator".into());
        }
        let (pointer, length) = self.slice_parts(slice)?;
        let (p_capture, p) = self.capture_operand(
            pointer,
            &Type::Reference {
                mutable: false,
                pointee: Box::new(Type::U8),
            },
        )?;
        let (l_capture, l) = self.capture_operand(length, &Type::Usize)?;
        let (size_prefix, size) = self.prepared_expr(size)?;
        let prefix = c_seq(
            c_assert(c_equal(
                c_variable(format!("{iterator}_live")),
                c_int32_literal(0),
            )),
            c_seq(p_capture, c_seq(l_capture, size_prefix)),
        );
        let values = self.chunk_initialize_values(prefix, iterator, size, &p, &l)?;
        Ok(c_seq(
            values,
            c_assign(format!("{iterator}_live"), c_int32_literal(1)),
        ))
    }
    pub(super) fn chunk_move(&self, target: &str, source: &str) -> Result<CStatement, String> {
        if target == source || !self.mir_chunk_iterators.contains(target) {
            return Err("invalid chunk move destination".into());
        }
        let mut result = c_seq(
            self.chunk_live(source)?,
            c_assert(c_equal(
                c_variable(format!("{target}_live")),
                c_int32_literal(0),
            )),
        );
        for suffix in ["cursor", "remaining", "size", "tail", "tail_len"] {
            result = c_seq(
                result,
                c_assign(
                    format!("{target}_{suffix}"),
                    c_variable(format!("{source}_{suffix}")),
                ),
            );
        }
        Ok(c_seq(
            result,
            c_seq(
                c_assign(format!("{source}_live"), c_int32_literal(0)),
                c_assign(format!("{target}_live"), c_int32_literal(1)),
            ),
        ))
    }
    pub(super) fn chunk_has_next(&self, iterator: &str) -> Result<CExpression, String> {
        if !self.mir_chunk_iterators.contains(iterator) {
            return Err("unknown MIR chunk iterator".into());
        }
        let remaining = c_variable(format!("{iterator}_remaining"));
        let size = c_variable(format!("{iterator}_size"));
        Ok(c_and(
            c_less_than(c_int32_literal(0), remaining.clone()),
            c_and(
                c_less_equal(size.clone(), c_uint64_literal(i32::MAX as u64)),
                c_less_equal(c_cast(c_cast(size, CType::UInt32), CType::Int32), remaining),
            ),
        ))
    }
    pub(super) fn chunk_next(&self, iterator: &str, option: &str) -> Result<CStatement, String> {
        if !self.chunk_options.contains(option) {
            return Err("unknown chunk Option".into());
        }
        let cursor = format!("{iterator}_cursor");
        let remaining = format!("{iterator}_remaining");
        let size = c_variable(format!("{iterator}_size"));
        let step = c_cast(c_cast(size.clone(), CType::UInt32), CType::Int32);
        let some = c_seq(
            c_assign(format!("{option}_some"), c_int32_literal(1)),
            c_seq(
                c_assign(format!("{option}_pointer"), c_variable(&cursor)),
                c_seq(
                    c_assign(format!("{option}_len"), size),
                    c_seq(
                        c_assign(&cursor, c_add(c_variable(&cursor), step.clone())),
                        c_assign(&remaining, c_subtract(c_variable(&remaining), step)),
                    ),
                ),
            ),
        );
        Ok(c_seq(
            self.chunk_live(iterator)?,
            c_if(
                self.chunk_has_next(iterator)?,
                some,
                c_assign(format!("{option}_some"), c_int32_literal(0)),
            ),
        ))
    }
    pub(super) fn chunk_slice_checks(&self, value: &E) -> Result<CStatement, String> {
        match value {
            E::ChunkOptionSlice { option } if self.chunk_options.contains(option) => Ok(c_assert(
                c_equal(c_variable(format!("{option}_some")), c_int32_literal(1)),
            )),
            E::ChunkRemainder { iterator } if self.mir_chunk_iterators.contains(iterator) => {
                self.chunk_live(iterator)
            }
            _ => Ok(c_skip()),
        }
    }
}
