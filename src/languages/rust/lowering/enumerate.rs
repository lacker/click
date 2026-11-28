//! An enumerated slice iterator is `core`'s `Enumerate { iter, count }`:
//! the slice iterator's fields and its count, how many elements it has
//! yielded. Its `next` yields the slice iterator's element with the index
//! `count`, then counts it. Its `Option` holds the yielded element's address
//! and index.
use super::*;

impl Context<'_> {
    pub(super) fn enumerate_storage(
        &mut self,
        name: &MirLocalId,
        element: &Type,
        option: bool,
        owner: &LocalFunctionId,
        ordinal: u32,
    ) -> Result<ProgramStatement, String> {
        let storage = self.shared_array_storage(name, element, option, owner, ordinal)?;
        let field: BindingName = if option {
            LocalBindingId::iterator_option_index(owner, ordinal).into()
        } else {
            LocalBindingId::enumerate_count(owner.clone(), ordinal).into()
        };
        self.enumerate_fields.insert(name.clone(), field.clone());
        Ok(program_seq(
            storage,
            program_declare(field, ProgramType::UInt64),
        ))
    }

    pub(super) fn enumerate_count(&self, name: &MirLocalId) -> Result<BindingName, String> {
        self.enumerate_fields
            .get(name)
            .filter(|_| self.shared_array_iterators.contains_key(name))
            .cloned()
            .ok_or_else(|| "unknown enumerated iterator".into())
    }

    fn enumerate_index(&self, name: &MirLocalId) -> Result<BindingName, String> {
        self.enumerate_fields
            .get(name)
            .filter(|_| self.shared_array_options.contains_key(name))
            .cloned()
            .ok_or_else(|| "unknown enumerated iterator Option".into())
    }

    /// `target = source.enumerate()`: the slice iterator, which has yielded
    /// nothing yet as an enumeration.
    pub(super) fn enumerate_initialize(
        &mut self,
        target: &MirLocalId,
        source: &MirLocalId,
    ) -> Result<ProgramStatement, String> {
        let count = self.enumerate_count(target)?;
        if self.enumerate_fields.contains_key(source) {
            return Err("enumerate requires a slice iterator".into());
        }
        Ok(program_seq(
            self.shared_array_move(target, source)?,
            program_assign(count, crate::kernel::program_expression::uint64_literal(0)),
        ))
    }

    pub(super) fn enumerate_move(
        &mut self,
        target: &MirLocalId,
        source: &MirLocalId,
    ) -> Result<ProgramStatement, String> {
        let target_count = self.enumerate_count(target)?;
        let source_count = self.enumerate_count(source)?;
        Ok(program_seq(
            self.shared_array_move(target, source)?,
            program_assign(
                target_count,
                crate::kernel::program_expression::variable(source_count),
            ),
        ))
    }

    /// The slice iterator's `next`, which also yields the index `count` and
    /// counts the element.
    /// `next` of an enumerated slice iterator: the `Option` built in
    /// `option`, or, once the loop reads only what it yields, the index
    /// assigned to `index` and the element or its reference to `element`. When the
    /// `for` header's test decided whether it yields (`taken`), only that arm
    /// runs; the arm that does not yield is nothing.
    pub(super) fn enumerate_next(
        &mut self,
        iterator: &MirLocalId,
        option: Option<&MirLocalId>,
        index: Option<&MirLocalId>,
        element: Option<(&MirLocalId, &Type)>,
        taken: Option<bool>,
    ) -> Result<ProgramStatement, String> {
        use crate::kernel::program_expression::{add, uint64_literal, variable};
        let count = self.enumerate_count(iterator)?;
        let Some(option) = option else {
            if taken == Some(false) {
                return Ok(program_skip());
            }
            let state = self.shared_array_iterator(iterator)?;
            let fields = state.fields.clone();
            let element_type = state.element;
            let mut some = program_skip();
            if let Some(index) = index {
                some = program_seq(some, self.bind_local(index, variable(count.clone()))?);
            }
            some = program_seq(
                some,
                program_assign(count.clone(), add(variable(count), uint64_literal(1))),
            );
            if let Some((name, payload_type)) = element {
                let value = self.shared_array_yielded_value(
                    shared_arrays::cursor(&fields),
                    element_type,
                    payload_type,
                )?;
                some = program_seq(some, self.bind_local(name, value)?);
            }
            some = program_seq(some, shared_arrays::advance(&fields));
            return Ok(match taken {
                Some(_) => some,
                None => program_if(self.shared_array_has_next(iterator)?, some, program_skip()),
            });
        };
        let index = self.enumerate_index(option)?;
        let yielded = program_seq(
            program_assign(index, variable(count.clone())),
            program_assign(count.clone(), add(variable(count), uint64_literal(1))),
        );
        self.shared_array_next_with(iterator, option, yielded)
    }

    /// The index an enumerated iterator's `Some` holds.
    pub(super) fn enumerate_option_index(
        &self,
        option: &MirLocalId,
    ) -> Result<(ProgramStatement, ProgramExpression), String> {
        let index = self.enumerate_index(option)?;
        Ok((
            program_assert(crate::kernel::program_expression::equal(
                crate::kernel::program_expression::variable(&self.shared_array_option(option)?.tag),
                crate::kernel::program_expression::int32_literal(1),
            )),
            crate::kernel::program_expression::variable(index),
        ))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::languages::rust::schema::Place;

    #[test]
    fn enumerate_count_and_a_source_local_have_distinct_bindings() {
        let mut export = crate::languages::rust::charon::decode(
            include_bytes!(
                "../../../../design/charon-trial/enumerate/.click/captures/enumerate/enumerate.rs.ullbc"
            ),
            "enumerate.rs",
            include_bytes!("../../../../design/charon-trial/enumerate/enumerate.rs"),
        )
        .unwrap();
        let function = export
            .functions
            .iter_mut()
            .find(|f| f.name == "last_index")
            .unwrap();
        let mir = function.mir.as_mut().unwrap();
        let iterator = mir
            .locals
            .iter()
            .find(|local| matches!(local.value_type, Type::EnumerateIterator { .. }))
            .unwrap();
        mir.locals.push(Place {
            name: format!("{}_count", iterator.name).into(),
            value_type: Type::Usize,
            span: iterator.span.clone(),
        });

        // The source local used to hit the generated count's collision check.
        super::super::lower(&export).unwrap();
    }
}
