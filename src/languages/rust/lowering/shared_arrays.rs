//! A shared slice iterator, `core::slice::Iter<'_, T>`, is held as the slice
//! it still covers, what `iter.as_slice()` returns, and its length as read
//! by `iter.len()`. `core`'s iterator holds
//! the same slice as a start and an end pointer. `next` yields the element
//! at the cursor and moves the slice on by one, as `core`'s does.
use super::*;
use crate::languages::interface::SliceIteratorFields;
/// The cursor's pointer type, as a Rust reference to the element lowers.
fn pointer_type(element: &Type) -> Result<ProgramType, String> {
    if !element.is_integer() {
        return Err("shared array iterator requires an integer element".into());
    }
    Ok(scalar_type(&Type::Reference {
        mutable: false,
        pointee: Box::new(element.clone()),
    })?
    .to_kernel_type())
}

pub(super) struct SliceIteratorStorage {
    pub(super) element: ProgramType,
    pub(super) fields: SliceIteratorFields,
}

pub(super) struct SliceIteratorOptionStorage {
    element: ProgramType,
    pub(super) tag: BindingName,
    pub(super) pointer: BindingName,
}

/// Move the iterator on by one element.
pub(super) fn advance(fields: &SliceIteratorFields) -> ProgramStatement {
    use crate::kernel::program_expression::{add, subtract, uint64_literal, variable};
    program_seq(
        program_assign(
            fields.pointer.clone(),
            add(variable(fields.pointer.clone()), uint64_literal(1)),
        ),
        program_assign(
            fields.length.clone(),
            subtract(variable(fields.length.clone()), uint64_literal(1)),
        ),
    )
}

impl Context<'_> {
    /// `name = value` for a local `next` binds, as `assign` assigns a local:
    /// stored to its object when it is memory-backed.
    pub(super) fn bind_local(
        &mut self,
        name: &MirLocalId,
        value: ProgramExpression,
    ) -> Result<ProgramStatement, String> {
        if !self.locals.contains(name) {
            return Err(format!("unknown Rust local `{name}`"));
        }
        Ok(match self.memory_values.get(name).copied() {
            Some(value_type) => program_typed_store(
                self.address(&E::Local { name: name.clone() })?,
                value,
                value_type,
            ),
            None => program_assign(self.binding(name)?, value),
        })
    }

    pub(super) fn shared_array_iterator(
        &self,
        name: &MirLocalId,
    ) -> Result<&SliceIteratorStorage, String> {
        self.shared_array_iterators
            .get(name)
            .ok_or_else(|| "unknown shared iterator".into())
    }

    pub(super) fn shared_array_option(
        &self,
        name: &MirLocalId,
    ) -> Result<&SliceIteratorOptionStorage, String> {
        self.shared_array_options
            .get(name)
            .ok_or_else(|| "unknown shared iterator Option".into())
    }

    pub(super) fn shared_array_storage(
        &mut self,
        name: &MirLocalId,
        element: &Type,
        option: bool,
        owner: &LocalFunctionId,
        ordinal: u32,
    ) -> Result<ProgramStatement, String> {
        let pointer_type = pointer_type(element)?;
        let element = scalar_type(element)?.to_kernel_type();
        if !self.locals.insert(name.clone()) {
            return Err("shared iterator state identity collision".into());
        }
        if !option {
            let [pointer, length] =
                LocalBindingId::slice_iterator_fields(owner.clone(), ordinal, pointer_type)
                    .map(BindingName::from);
            self.shared_array_iterators.insert(
                name.clone(),
                SliceIteratorStorage {
                    element,
                    fields: SliceIteratorFields {
                        pointer: pointer.clone(),
                        length: length.clone(),
                    },
                },
            );
            return Ok(program_seq(
                program_declare_with_all_qualifiers(
                    pointer,
                    pointer_type,
                    false,
                    false,
                    false,
                    true,
                ),
                program_declare(length, ProgramType::UInt64),
            ));
        }

        let [tag, pointer] = LocalBindingId::iterator_option_fields(owner, ordinal, pointer_type)
            .map(BindingName::from);
        let result = program_seq(
            program_seq(
                program_declare(tag.clone(), ProgramType::Int32),
                program_assign(
                    tag.clone(),
                    crate::kernel::program_expression::int32_literal(0),
                ),
            ),
            program_declare_with_all_qualifiers(
                pointer.clone(),
                pointer_type,
                false,
                false,
                false,
                true,
            ),
        );
        self.shared_array_options.insert(
            name.clone(),
            SliceIteratorOptionStorage {
                element,
                tag,
                pointer,
            },
        );
        Ok(result)
    }

    /// `source.iter()`: the iterator covers the whole slice.
    pub(super) fn shared_array_initialize(
        &mut self,
        target: &MirLocalId,
        source: &E,
    ) -> Result<ProgramStatement, String> {
        let state = self.shared_array_iterator(target)?;
        let expected = state.element;
        let fields = state.fields.clone();
        let (pointer, length, element) = self.indexed_parts(source)?;
        if element != expected {
            return Err("shared array iterator source element mismatch".into());
        }
        let (p_capture, p) = self.capture_operand(
            pointer,
            &Type::Reference {
                mutable: false,
                pointee: Box::new(
                    indexed_element_type(element)
                        .ok_or("shared array iterator requires an integer element")?,
                ),
            },
        )?;
        let (l_capture, l) = self.capture_operand(length, &Type::Usize)?;
        Ok(program_seq(
            program_seq(p_capture, l_capture),
            program_seq(
                program_assign(fields.pointer, p),
                program_assign(fields.length, l),
            ),
        ))
    }

    /// Whether `next` yields: the slice it covers is not empty.
    pub(super) fn shared_array_has_next(
        &self,
        iterator: &MirLocalId,
    ) -> Result<ProgramExpression, String> {
        let length = self.shared_array_iterator(iterator)?.fields.length.clone();
        Ok(crate::kernel::program_expression::less_than(
            crate::kernel::program_expression::uint64_literal(0),
            crate::kernel::program_expression::variable(length),
        ))
    }

    pub(super) fn shared_array_move(
        &mut self,
        target: &MirLocalId,
        source: &MirLocalId,
    ) -> Result<ProgramStatement, String> {
        use crate::kernel::program_expression::variable;
        let target_fields = self.shared_array_iterators.get(target);
        let source_fields = self.shared_array_iterators.get(source);
        if let (Some(destination), Some(origin)) = (target_fields, source_fields)
            && target != source
            && destination.element == origin.element
        {
            return Ok(program_seq(
                program_assign(
                    destination.fields.pointer.clone(),
                    variable(origin.fields.pointer.clone()),
                ),
                program_assign(
                    destination.fields.length.clone(),
                    variable(origin.fields.length.clone()),
                ),
            ));
        }
        Err("invalid shared iterator move".into())
    }

    /// `next` of a slice iterator: the `Option` built in `option`, or, once
    /// the loop reads only its element, bind the address or copied integer
    /// to the typed `payload`. When the `for` header's test decided whether it yields
    /// (`taken`), only that arm runs; the arm that does not yield is nothing.
    pub(super) fn shared_array_next(
        &mut self,
        iterator: &MirLocalId,
        option: Option<&MirLocalId>,
        payload: Option<(&MirLocalId, &Type)>,
        taken: Option<bool>,
    ) -> Result<ProgramStatement, String> {
        match (option, payload) {
            (Some(option), None) => self.shared_array_next_with(iterator, option, program_skip()),
            (None, Some((payload, payload_type))) => {
                let state = self.shared_array_iterator(iterator)?;
                let fields = state.fields.clone();
                let element = state.element;
                if taken == Some(false) {
                    return Ok(program_skip());
                }
                use crate::kernel::program_expression::variable;
                let pointer = variable(fields.pointer.clone());
                let value = self.shared_array_yielded_value(pointer, element, payload_type)?;
                let bind = self.bind_local(payload, value)?;
                let some = program_seq(bind, advance(&fields));
                Ok(match taken {
                    Some(_) => some,
                    None => program_if(self.shared_array_has_next(iterator)?, some, program_skip()),
                })
            }
            // When nothing reads the result, only a yielding arm moves on.
            (None, None) if taken.is_some() => {
                let fields = &self.shared_array_iterator(iterator)?.fields;
                Ok(if taken == Some(true) {
                    advance(fields)
                } else {
                    program_skip()
                })
            }
            _ => Err("Rust slice next binds neither its Option nor its element".into()),
        }
    }

    /// The current element's reference, or its value for a copied pattern.
    pub(super) fn shared_array_yielded_value(
        &mut self,
        pointer: ProgramExpression,
        element: ProgramType,
        payload_type: &Type,
    ) -> Result<ProgramExpression, String> {
        match payload_type {
            Type::Reference {
                mutable: false,
                pointee,
            } if scalar_type(pointee)?.to_kernel_type() == element => Ok(pointer),
            ty if ty.is_integer() && scalar_type(ty)?.to_kernel_type() == element => {
                self.load_with_source(pointer, element, None)
            }
            _ => Err("Rust slice iterator payload type mismatch".into()),
        }
    }

    /// [`Self::shared_array_next`], also running `yielded` when it yields,
    /// before the iterator moves on.
    pub(super) fn shared_array_next_with(
        &self,
        iterator: &MirLocalId,
        option: &MirLocalId,
        yielded: ProgramStatement,
    ) -> Result<ProgramStatement, String> {
        let Some((state, destination)) = self
            .shared_array_iterators
            .get(iterator)
            .zip(self.shared_array_options.get(option))
            .filter(|(state, destination)| state.element == destination.element)
        else {
            return Err("shared iterator Option element mismatch".into());
        };
        use crate::kernel::program_expression::{int32_literal, variable};
        let mut some = program_assign(destination.tag.clone(), int32_literal(1));
        for statement in [
            program_assign(
                destination.pointer.clone(),
                variable(state.fields.pointer.clone()),
            ),
            yielded,
            advance(&state.fields),
        ] {
            some = program_seq(some, statement);
        }
        Ok(program_if(
            self.shared_array_has_next(iterator)?,
            some,
            program_assign(destination.tag.clone(), int32_literal(0)),
        ))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::languages::rust::schema::Place;

    #[test]
    fn slice_iterator_fields_are_distinct_from_source_locals() {
        let mut export = crate::languages::rust::charon::decode(
            include_bytes!(
                "../../../../design/charon-trial/slice-iter/.click/captures/sum/sum.rs.ullbc"
            ),
            "sum.rs",
            include_bytes!("../../../../design/charon-trial/slice-iter/sum.rs"),
        )
        .unwrap();
        let function = export
            .functions
            .iter_mut()
            .find(|f| f.name == "sum")
            .unwrap();
        let mir = function.mir.as_mut().unwrap();
        let iterator = mir
            .locals
            .iter()
            .find(|local| matches!(local.value_type, Type::SharedArrayIterator { .. }))
            .unwrap();
        let colliding = ["ptr", "len"].map(|field| Place {
            name: format!("{}_{field}", iterator.name).into(),
            value_type: Type::Usize,
            span: iterator.span.clone(),
        });
        mir.locals.extend(colliding);
        super::super::lower(&export).unwrap();
    }

    #[test]
    #[cfg(not(feature = "fast-gate"))]
    #[ignore = "nightly: replay retained slice iterator Options"]
    fn slice_iterator_option_fields_expand_and_replay() {
        use crate::languages::rust::schema::{MirStatement as S, MirTerminator as T};
        use crate::surface::{
            ProgramVerificationSession, expand_program_prepared_claim_source_by_label,
            without_implicit_solve_for_claim,
        };
        fn resize(ty: &mut Type, length: u64) {
            match ty {
                Type::Reference { pointee, .. } => resize(pointee, length),
                Type::Array { length: size, .. } => *size = length,
                _ => {}
            }
        }

        for (enumerated, length) in [(false, 0), (false, 4), (true, 0), (true, 4)] {
            let mut export = crate::languages::rust::charon::decode(
                include_bytes!("../../../../design/charon-trial/array-iteration/.click/captures/iteration/iteration.rs.ullbc"),
                "iteration.rs",
                include_bytes!("../../../../design/charon-trial/array-iteration/iteration.rs"),
            ).unwrap();
            export.functions.retain(|f| f.name == "signed");
            let function = &mut export.functions[0];
            let mir = function.mir.as_mut().unwrap();
            for local in function.parameters.iter_mut().chain(&mut mir.locals) {
                resize(&mut local.value_type, length);
            }
            // Retain a next result through its tag dispatch. The ordinary
            // importer binds the payload directly in this fixture.
            let option = MirLocalId::from("next_option");
            let header = mir
                .blocks
                .iter()
                .position(|block| {
                    matches!(
                        block.terminator,
                        T::If {
                            condition: E::SharedArrayHasNext { .. },
                            ..
                        }
                    )
                })
                .unwrap();
            let T::If {
                condition: E::SharedArrayHasNext { iterator },
                then_target,
                else_target,
            } = mir.blocks[header].terminator.clone()
            else {
                unreachable!()
            };

            let place = mir
                .locals
                .iter()
                .find(|local| local.name == iterator)
                .unwrap();
            let Type::SharedArrayIterator { element } = &place.value_type else {
                unreachable!()
            };
            let element = element.clone();
            let span = place.span.clone();
            let option_type = if enumerated {
                let target = MirLocalId::from("enumerated_iterator");
                mir.locals.push(Place {
                    name: target.clone(),
                    value_type: Type::EnumerateIterator {
                        element: element.clone(),
                    },
                    span: span.clone(),
                });
                mir.blocks[header].statements.push(S::EnumerateInitialize {
                    target: target.clone(),
                    source: iterator,
                });
                mir.blocks[header].statements.push(S::EnumerateNext {
                    iterator: target,
                    option: Some(option.clone()),
                    index: None,
                    element: None,
                    taken: None,
                });
                Type::EnumerateOption { element }
            } else {
                mir.blocks[header].statements.push(S::SharedArrayNext {
                    iterator,
                    option: Some(option.clone()),
                    payload: None,
                    taken: None,
                });
                Type::SharedArrayOption { element }
            };
            mir.blocks[header].terminator = T::If {
                condition: E::SharedArrayOptionTag {
                    option: option.clone(),
                },
                then_target,
                else_target,
            };
            for target in [then_target, else_target] {
                let statements = &mut mir.blocks[target].statements;
                let position = statements
                    .iter()
                    .position(|s| matches!(s, S::SharedArrayNext { .. }))
                    .unwrap();
                let S::SharedArrayNext { payload, taken, .. } = statements.remove(position) else {
                    unreachable!()
                };
                assert_eq!(taken, Some(target == then_target));
                if let Some(name) = payload {
                    statements.insert(
                        position,
                        S::Assign {
                            target: E::Local { name },
                            value: E::SharedArrayOptionElement {
                                option: option.clone(),
                            },
                        },
                    );
                    if enumerated {
                        statements.insert(
                            position + 1,
                            S::Assert {
                                condition: E::Binary {
                                    operator: "eq".into(),
                                    left_type: Type::Usize,
                                    right_type: Type::Usize,
                                    left: Box::new(E::EnumerateOptionIndex {
                                        option: option.clone(),
                                    }),
                                    right: Box::new(E::UsizeInteger { value: 0 }),
                                },
                                message: "first enumeration index".into(),
                            },
                        );
                    }
                } else {
                    assert_eq!(target, else_target);
                }
            }
            mir.locals.push(Place {
                name: option.clone(),
                value_type: option_type,
                span: span.clone(),
            });
            mir.locals
                .extend(["some", "pointer", "index"].map(|field| Place {
                    name: format!("{option}_{field}").into(),
                    value_type: Type::Usize,
                    span: span.clone(),
                }));

            let expected = if length == 0 { "0" } else { "old(words[0])" };
            let source = format!(
                r#"verifying "iteration.rs";
                fn signed(words: &[i32; {length}]) -> i32 {{
                    views words[0..{length}];
                    ensures result == {expected};
                }} by {{ step_until(function.exit); close(); }}"#
            );
            let prepared = crate::languages::rust::import::prepared_for_test(export).unwrap();
            let claim = "signed.contract";
            let expanded = expand_program_prepared_claim_source_by_label(&source, &prepared, claim)
                .unwrap_or_else(|error| panic!("{enumerated}, {length}: {}", error.report()));
            assert_ne!(source, expanded);
            assert!(
                !expanded.contains("next_option") && !expanded.contains("<iterator option "),
                "{expanded}"
            );
            without_implicit_solve_for_claim(claim, || {
                ProgramVerificationSession::new_program_prepared(&expanded, &prepared)
                    .map(|_| ())
                    .map_err(|error| error.report())
            })
            .unwrap_or_else(|error| panic!("{enumerated}, {length}: {error}\n{expanded}"));
        }
    }
}
