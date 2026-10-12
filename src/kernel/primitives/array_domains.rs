//! Compact, declared multidimensional scalar-array selections. Dimensions and
//! paths establish geometry only; every actual read/write still checks its
//! independent authority, initialization and lifetime.
use super::*;
use num_traits::ToPrimitive;

fn split_array_path(
    path: &[PointerDomainSelection],
) -> Option<(Vec<String>, &[PointerDomainSelection])> {
    let first = path
        .iter()
        .position(|part| matches!(part, PointerDomainSelection::Element(_)))
        .unwrap_or(path.len());
    let members = path[..first]
        .iter()
        .map(|part| match part {
            PointerDomainSelection::Member(name) => Some(name.clone()),
            _ => None,
        })
        .collect::<Option<Vec<_>>>()?;
    if path[first..]
        .iter()
        .any(|part| !matches!(part, PointerDomainSelection::Element(_)))
    {
        return None;
    }
    Some((members, &path[first..]))
}

fn array_element_geometry(element: CType, shape: &[u32]) -> Option<(CType, u32, u32)> {
    let (&count, tail) = shape.split_first()?;
    let selected = if tail.is_empty() {
        element
    } else {
        let cells = tail
            .iter()
            .try_fold(1u32, |product, n| product.checked_mul(*n))?;
        element.scalar_array_type(cells)?
    };
    let stride = selected.byte_width();
    (stride > 0).then_some((selected, stride, count))
}

/// Observe the complete machine value before scaling it outside its native
/// format. No mathematical index is truncated or rewritten into a wrapped word.
fn array_index_offset(index: &IntegerTerm, stride: u32) -> Option<PointerOffsetTerm> {
    match index {
        IntegerTerm::Constant(n) => Some(PointerOffsetTerm::Constant(
            n.to_i64()?.checked_mul(i64::from(stride))?,
        )),
        IntegerTerm::Machine(n) => match n.ty() {
            MachineIntegerType::Int32 => Some(PointerOffsetTerm::scale_int32(
                n.value().clone(),
                i64::from(stride),
            )),
            MachineIntegerType::Int64 | MachineIntegerType::UInt64 => {
                Some(PointerOffsetTerm::scale_int64(
                    n.value().clone(),
                    i64::from(stride),
                    n.ty() == MachineIntegerType::UInt64,
                ))
            }
            _ => None,
        },
        _ => None,
    }
}

struct ArraySelection {
    scalar: CType,
    shape: Arc<[u32]>,
    remaining: usize,
    base: Pointer,
    guards: Vec<ConditionTerm>,
}

impl ArraySelection {
    fn rows(mut self, rows: &[PointerDomainSelection]) -> Option<Self> {
        if rows.len() >= self.shape.len() {
            return None;
        }
        for part in rows {
            crate::instrumentation::record_deterministic_work(1);
            let PointerDomainSelection::Element(index) = part else {
                return None;
            };
            let (_, stride, count) =
                array_element_geometry(self.scalar, &self.shape[self.remaining..])?;
            self.guards
                .push(crate::kernel::eval::pointer_domains::domain_less_equal(
                    IntegerTerm::constant_i64(0),
                    index.as_ref().clone(),
                ));
            self.guards
                .push(crate::kernel::eval::pointer_domains::domain_less_than(
                    index.as_ref().clone(),
                    IntegerTerm::constant_i64(i64::from(count)),
                ));
            self.base.offset = PointerOffsetTerm::add(
                self.base.offset.clone(),
                array_index_offset(index, stride)?,
            );
            self.remaining += 1;
        }
        Some(self)
    }

    fn authenticate(&self, pointer: &CPointerValue) -> Option<Vec<ConditionTerm>> {
        let (base, element, stride, count) = match pointer.designation()? {
            PointerDesignation::Object {
                base,
                element_type,
                stride,
                count,
                ..
            }
            | PointerDesignation::InputSelected {
                base,
                element_type,
                stride,
                count,
                ..
            } => (base, *element_type, *stride, count),
            _ => return None,
        };
        let (held, held_stride, held_count) =
            array_element_geometry(self.scalar, &self.shape[self.remaining..])?;
        if element != held
            || stride != held_stride
            || *count != SharedIntegerTerm::from(IntegerTerm::constant_i64(i64::from(held_count)))
        {
            return None;
        }
        let mut guards = self.guards.clone();
        guards.push(ConditionTerm::pointer_equal(
            base.clone(),
            self.base.clone(),
        ));
        Some(guards)
    }
}

impl CMemory {
    fn object_array_selection(
        &self,
        pointer: &CPointerValue,
        assumptions: &PureFactContext,
    ) -> Option<ArraySelection> {
        let PointerDesignation::Object { root, path, .. } = pointer.designation()? else {
            return None;
        };
        if pointer.is_null()
            || self.is_ended_local_address(root)
            || self.is_deallocated_heap_address(root, assumptions)
        {
            return None;
        }
        let (members, rows) = split_array_path(path)?;
        let (scalar, count, shape, base) = match self
            .blocks
            .get(&root.block)
            .and_then(|block| block.declared_object.as_ref())
        {
            Some(CDeclaredObject::Array {
                element_type,
                count,
                shape,
            }) if members.is_empty() && root.offset.as_const() == Some(0) => (
                *element_type,
                *count,
                shape.clone().unwrap_or_else(|| Arc::from([*count])),
                root.clone(),
            ),
            Some(CDeclaredObject::Aggregate(layout)) if root.offset.as_const() == Some(0) => {
                if let Some((element, count)) = layout.scalar_array() {
                    if !members.is_empty() {
                        return None;
                    }
                    (element, count, Arc::from([count]), root.clone())
                } else {
                    let (element, count, shape) = layout.array_member_shape_at_path(&members)?;
                    (
                        element,
                        count,
                        shape,
                        root.offset_by_bytes(layout.member_at_path(&members)?.0),
                    )
                }
            }
            Some(_) => return None,
            None => {
                let layout = self.heap.object_input_domains.get(root)?;
                if let Some((element, count)) = layout.scalar_array() {
                    if !members.is_empty() {
                        return None;
                    }
                    (element, count, Arc::from([count]), root.clone())
                } else {
                    let (element, count, shape) = layout.array_member_shape_at_path(&members)?;
                    (
                        element,
                        count,
                        shape,
                        root.offset_by_bytes(layout.member_at_path(&members)?.0),
                    )
                }
            }
        };
        // Existing one-dimensional empty Rust arrays keep their zero extent;
        // newly retained multidimensional declarations require nonzero dims.
        if count != 0 || shape.as_ref() != [0].as_slice() {
            checked_scalar_array_shape(scalar, count, &shape)?;
        }
        ArraySelection {
            scalar,
            shape,
            remaining: 0,
            base,
            guards: vec![],
        }
        .rows(rows)
    }

    fn input_array_selection(
        &self,
        pointer: &CPointerValue,
        assumptions: &PureFactContext,
    ) -> Option<ArraySelection> {
        let PointerDesignation::InputSelected {
            input,
            origin,
            path,
            ..
        } = pointer.designation()?
        else {
            return None;
        };
        let (layout, prefix, index, _) = self.input_selection_parts(input, origin, path)?;
        let row = self.heap.native_record_inputs.get(input)?;
        let record_path = match &row.kind {
            CNativeInputKind::Record { .. } => path.as_ref(),
            CNativeInputKind::RecordPrefix { .. } => &path[1..],
            _ => return None,
        };
        let (members, rows) = split_array_path(record_path)?;
        let (scalar, count, shape) = layout.array_member_shape_at_path(&members)?;
        checked_scalar_array_shape(scalar, count, &shape)?;
        let mut base = origin.clone();
        base.offset = PointerOffsetTerm::add(
            base.offset,
            array_index_offset(&index, layout.size_bytes())?,
        );
        base = base.offset_by_bytes(layout.member_at_path(&members)?.0);
        let guards = vec![
            crate::kernel::eval::pointer_domains::domain_less_equal(
                IntegerTerm::constant_i64(0),
                prefix.as_ref().clone(),
            ),
            crate::kernel::eval::pointer_domains::domain_less_equal(
                prefix.as_ref().clone(),
                IntegerTerm::constant_i64(
                    crate::kernel::eval::pointer_domains::native_prefix_element_limit(
                        layout.size_bytes(),
                    ),
                ),
            ),
            crate::kernel::eval::pointer_domains::domain_less_equal(
                IntegerTerm::constant_i64(0),
                index.as_ref().clone(),
            ),
            crate::kernel::eval::pointer_domains::domain_less_than(
                index.as_ref().clone(),
                prefix.as_ref().clone(),
            ),
        ];
        let selection = ArraySelection {
            scalar,
            shape,
            remaining: 0,
            base,
            guards,
        }
        .rows(rows)?;
        // Query-time authentication is retained even if the current address is
        // displaced. Its descriptor base must still be the exact selected row.
        let _ = assumptions;
        Some(selection)
    }

    pub(in crate::kernel) fn authenticated_array_domain(
        &self,
        pointer: &CPointerValue,
        assumptions: &PureFactContext,
    ) -> Option<Vec<ConditionTerm>> {
        match pointer.designation()? {
            PointerDesignation::Object { .. } => self
                .object_array_selection(pointer, assumptions)?
                .authenticate(pointer),
            PointerDesignation::InputSelected { .. } => self
                .input_array_selection(pointer, assumptions)?
                .authenticate(pointer),
            _ => None,
        }
    }

    /// Select one declared row. Expression-provided dimensions must exactly
    /// equal the remaining declaration dimensions; they are not evidence.
    pub(in crate::kernel) fn guarded_array_row_pointer(
        &self,
        array: &CPointerValue,
        index: SharedIntegerTerm,
        element: CType,
        shape: &[u32],
        assumptions: &PureFactContext,
    ) -> Option<(CPointerValue, Vec<ConditionTerm>)> {
        let selected = match array.designation()? {
            PointerDesignation::Object { .. } => self.object_array_selection(array, assumptions)?,
            PointerDesignation::InputSelected { .. } => {
                self.input_array_selection(array, assumptions)?
            }
            _ => return None,
        };
        if selected.scalar != element
            || shape.len() < 2
            || &selected.shape[selected.remaining..] != shape
        {
            return None;
        }
        let mut guards = selected.authenticate(array)?;
        let (base, mut path) = match array.designation()? {
            PointerDesignation::Object { base, path, .. }
            | PointerDesignation::InputSelected { base, path, .. } => (base.clone(), path.to_vec()),
            _ => return None,
        };
        guards.push(ConditionTerm::pointer_equal(
            array.pointer().clone(),
            base.clone(),
        ));
        let (_, row_stride, _) = array_element_geometry(element, shape)?;
        let address = Pointer {
            block: base.block.clone(),
            offset: PointerOffsetTerm::add(base.offset, array_index_offset(&index, row_stride)?),
        };
        path.push(PointerDomainSelection::Element(index));
        let (child, stride, count) = array_element_geometry(element, &shape[1..])?;
        let designation = match array.designation()? {
            PointerDesignation::Object { root, .. } => PointerDesignation::Object {
                root: root.clone(),
                path: path.into(),
                base: address.clone(),
                element_type: child,
                stride,
                count: IntegerTerm::constant_i64(i64::from(count)).into(),
            },
            PointerDesignation::InputSelected { input, origin, .. } => {
                PointerDesignation::InputSelected {
                    input: input.clone(),
                    origin: origin.clone(),
                    path: path.into(),
                    base: address.clone(),
                    element_type: child,
                    stride,
                    count: IntegerTerm::constant_i64(i64::from(count)).into(),
                }
            }
            _ => return None,
        };
        let pointer = array
            .clone()
            .with_pointer(address)
            .with_designation(designation);
        guards.extend(self.authenticated_array_domain(&pointer, assumptions)?);
        Some((pointer, guards))
    }

    /// Reissue only the geometry of an actual selected array at its complete
    /// address. Member qualifiers and enclosing input/declaration identity stay.
    pub(in crate::kernel) fn guarded_declared_array_decay(
        &self,
        object: &CPointerValue,
        assumptions: &PureFactContext,
    ) -> Option<(CPointerValue, Vec<ConditionTerm>)> {
        let selected = match object.designation()? {
            PointerDesignation::Object { .. } => {
                self.object_array_selection(object, assumptions)?
            }
            PointerDesignation::InputSelected { .. } => {
                self.input_array_selection(object, assumptions)?
            }
            _ => return None,
        };
        if selected.remaining != 0 {
            return None;
        }
        let total = selected
            .shape
            .iter()
            .try_fold(1u32, |n, dimension| n.checked_mul(*dimension))?;
        let (original_type, original_stride, original_count) = match object.designation()? {
            PointerDesignation::Object {
                element_type,
                stride,
                count,
                ..
            }
            | PointerDesignation::InputSelected {
                element_type,
                stride,
                count,
                ..
            } => (*element_type, *stride, count),
            _ => return None,
        };
        let complete = original_type.array_element_and_count() == Some((selected.scalar, total))
            && original_stride == original_type.byte_width()
            && *original_count == SharedIntegerTerm::from(IntegerTerm::constant_i64(1));
        if !complete && selected.authenticate(object).is_none() {
            return None;
        }
        let (element, stride, count) = array_element_geometry(selected.scalar, &selected.shape)?;
        let pointer = match object.designation()? {
            PointerDesignation::Object {
                root, path, base, ..
            } => object
                .clone()
                .with_type(selected.scalar.pointer_to()?)
                .with_designation(PointerDesignation::Object {
                    root: root.clone(),
                    path: path.clone(),
                    base: base.clone(),
                    element_type: element,
                    stride,
                    count: IntegerTerm::constant_i64(i64::from(count)).into(),
                }),
            PointerDesignation::InputSelected {
                input,
                origin,
                path,
                base,
                ..
            } => object
                .clone()
                .with_type(selected.scalar.pointer_to()?)
                .with_designation(PointerDesignation::InputSelected {
                    input: input.clone(),
                    origin: origin.clone(),
                    path: path.clone(),
                    base: base.clone(),
                    element_type: element,
                    stride,
                    count: IntegerTerm::constant_i64(i64::from(count)).into(),
                }),
            _ => return None,
        };
        let mut guards = self.authenticated_array_domain(&pointer, assumptions)?;
        guards.push(ConditionTerm::pointer_equal(
            object.pointer().clone(),
            selected.base,
        ));
        Some((pointer, guards))
    }
}

impl CMemory {
    /// A constant address initializer retains a recipe from its actual source
    /// declaration. It grants no executable validity until the live runtime
    /// declaration independently authenticates this full carrier.
    pub(crate) fn static_array_declaration_recipe(
        root: Pointer,
        element: CType,
        count: u32,
        shape: &[u32],
    ) -> Option<CPointerValue> {
        checked_scalar_array_shape(element, count, shape)?;
        let (selected, stride, length) = array_element_geometry(element, shape)?;
        Some(
            CPointerValue::new(root.clone(), element.pointer_to()?).with_designation(
                PointerDesignation::Object {
                    root: root.clone(),
                    path: Arc::from([]),
                    base: root,
                    element_type: selected,
                    stride,
                    count: IntegerTerm::constant_i64(i64::from(length)).into(),
                },
            ),
        )
    }

    pub(crate) fn static_member_array_declaration_recipe(
        root: Pointer,
        layout: &CAggregateLayout,
        path: &[String],
    ) -> Option<CPointerValue> {
        if !layout.unions().is_empty() {
            return None;
        }
        let (element, _, shape) = layout.array_member_shape_at_path(path)?;
        let (selected, stride, count) = array_element_geometry(element, &shape)?;
        let base = root.offset_by_bytes(layout.member_at_path(path)?.0);
        Some(
            CPointerValue::new(base.clone(), element.pointer_to()?).with_designation(
                PointerDesignation::Object {
                    root,
                    path: path
                        .iter()
                        .cloned()
                        .map(PointerDomainSelection::Member)
                        .collect(),
                    base,
                    element_type: selected,
                    stride,
                    count: IntegerTerm::constant_i64(i64::from(count)).into(),
                },
            ),
        )
    }

    pub(crate) fn static_array_row_declaration_recipe(
        array: &CPointerValue,
        element: CType,
        shape: &[u32],
        index: u32,
    ) -> Option<CPointerValue> {
        if shape.len() < 2 || index >= shape[0] {
            return None;
        }
        let count = shape.iter().try_fold(1u32, |n, dim| n.checked_mul(*dim))?;
        checked_scalar_array_shape(element, count, shape)?;
        let (parent_type, parent_stride, parent_count) = array_element_geometry(element, shape)?;
        let PointerDesignation::Object {
            root,
            path,
            base,
            element_type,
            stride,
            count,
        } = array.designation()?
        else {
            return None;
        };
        if array.pointer() != base
            || *element_type != parent_type
            || *stride != parent_stride
            || *count != SharedIntegerTerm::from(IntegerTerm::constant_i64(i64::from(parent_count)))
        {
            return None;
        }
        let base = base.offset_by_bytes(index.checked_mul(parent_stride)?);
        let mut path = path.to_vec();
        path.push(PointerDomainSelection::Element(
            IntegerTerm::constant_i64(i64::from(index)).into(),
        ));
        let (child, stride, count) = array_element_geometry(element, &shape[1..])?;
        Some(array.clone().with_pointer(base.clone()).with_designation(
            PointerDesignation::Object {
                root: root.clone(),
                path: path.into(),
                base,
                element_type: child,
                stride,
                count: IntegerTerm::constant_i64(i64::from(count)).into(),
            },
        ))
    }
}

impl CMemory {
    /// A compact whole-array initializer/copy operates on actual declaration
    /// storage, not on an arbitrarily large scalar span from a selected row.
    pub(in crate::kernel) fn complete_declared_array_storage(
        &self,
        pointer: &CPointerValue,
        element: CType,
        count: u32,
        assumptions: &PureFactContext,
    ) -> Option<Vec<ConditionTerm>> {
        let selected = match pointer.designation()? {
            PointerDesignation::Object { .. } => {
                self.object_array_selection(pointer, assumptions)?
            }
            PointerDesignation::InputSelected { .. } => {
                self.input_array_selection(pointer, assumptions)?
            }
            _ => return None,
        };
        if selected.remaining != 0
            || selected.scalar != element
            || selected
                .shape
                .iter()
                .try_fold(1u32, |n, d| n.checked_mul(*d))?
                != count
        {
            return None;
        }
        let (_, mut guards) = self.guarded_declared_array_decay(pointer, assumptions)?;
        guards.push(ConditionTerm::pointer_equal(
            pointer.pointer().clone(),
            selected.base,
        ));
        Some(guards)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::eval::pointer_domains::{self, PointerDomainCheck, PointerDomainView};

    fn checked(guards: Vec<ConditionTerm>, context: &PureFactContext) -> bool {
        guards
            .iter()
            .all(|guard| context.decide(guard) == Some(true))
    }
    fn passes(query: Result<PointerDomainCheck, pointer_domains::PointerDomainRefusal>) -> bool {
        matches!(query,Ok(PointerDomainCheck::Checked(guards)) if checked(guards.clone(),&PureFactContext::new()))
    }
    fn matrix(rows: u32) -> (CMemory, CPointerValue) {
        let root = CMemory::local_pointer("row-domain");
        let memory = CMemory::new()
            .with_declared_array_block(root.block.clone(), CType::Int32, rows * 3)
            .unwrap()
            .with_declared_array_shape(&root.block, CType::Int32, rows * 3, &[rows, 3])
            .unwrap();
        let pointer = memory
            .declared_array_pointer(&root, CType::Int32, rows * 3)
            .unwrap();
        (memory, pointer)
    }

    #[test]
    fn declared_rows_keep_one_past_distinct_from_equal_address_next_row() {
        let _session = crate::kernel::VerificationSession::enter();
        let (memory, array) = matrix(2);
        let context = PureFactContext::new();
        let (first, guards) = memory
            .guarded_array_row_pointer(
                &array,
                IntegerTerm::constant_i64(0).into(),
                CType::Int32,
                &[2, 3],
                &context,
            )
            .unwrap();
        assert!(checked(guards, &context));
        let (second, guards) = memory
            .guarded_array_row_pointer(
                &array,
                IntegerTerm::constant_i64(1).into(),
                CType::Int32,
                &[2, 3],
                &context,
            )
            .unwrap();
        assert!(checked(guards, &context));
        let past = first
            .clone()
            .with_pointer(first.pointer().offset_by_bytes(12));
        assert_eq!(past.pointer(), second.pointer());
        assert!(!past.same_designation(&second));
        let state = CState::new().with_memory(memory.clone());
        assert!(passes(pointer_domains::checked_pointer_formation(
            &state,
            &first,
            past.pointer(),
            4,
            PointerDomainView::Typed,
            &context
        )));
        assert!(!passes(pointer_domains::checked_pointer_access(
            &state,
            &past,
            CType::Int32,
            4,
            PointerDomainView::Typed,
            &context
        )));
        assert!(passes(pointer_domains::checked_pointer_access(
            &state,
            &second,
            CType::Int32,
            4,
            PointerDomainView::Typed,
            &context
        )));
        assert!(!passes(pointer_domains::checked_pointer_formation(
            &state,
            &first,
            &first.pointer().offset_by_bytes(16),
            4,
            PointerDomainView::Typed,
            &context
        )));
        assert!(
            memory
                .complete_declared_array_storage(&array, CType::Int32, 6, &context)
                .is_some()
        );
        assert!(
            memory
                .complete_declared_array_storage(&first, CType::Int32, 6, &context)
                .is_none()
        );
        assert!(!memory.has_initialized_bytes_under(first.pointer(), 4, &context));
        let forged = match first.designation().unwrap() {
            PointerDesignation::Object {
                root, path, base, ..
            } => first.clone().with_designation(PointerDesignation::Object {
                root: root.clone(),
                path: path.clone(),
                base: base.clone(),
                element_type: CType::Int32,
                stride: 4,
                count: IntegerTerm::constant_i64(6).into(),
            }),
            _ => unreachable!(),
        };
        assert!(
            memory
                .authenticated_array_domain(&forged, &context)
                .is_none()
        );
        assert!(
            !memory
                .without_local_block(&array.block)
                .authenticated_pointer_domain_at_base(&first)
        );
    }

    #[test]
    fn array_row_shape_is_declaration_evidence_not_expression_geometry() {
        let _session = crate::kernel::VerificationSession::enter();
        let (memory, array) = matrix(2);
        let context = PureFactContext::new();
        for shape in [&[3, 2][..], &[1, 6], &[0, 3], &[2, 4]] {
            assert!(
                memory
                    .guarded_array_row_pointer(
                        &array,
                        IntegerTerm::constant_i64(0).into(),
                        CType::Int32,
                        shape,
                        &context
                    )
                    .is_none()
            );
        }
        assert!(
            CMemory::new()
                .with_block(array.block.clone(), 24)
                .with_declared_array_shape(&array.block, CType::Int32, 6, &[2, 3])
                .is_none()
        );
        assert!(
            memory
                .clone()
                .with_declared_array_shape(&array.block, CType::Int32, 6, &[3, 2])
                .is_none()
        );
        let recipe = CMemory::static_array_declaration_recipe(
            array.pointer().clone(),
            CType::Int32,
            6,
            &[3, 2],
        )
        .unwrap();
        assert!(
            memory
                .authenticated_array_domain(&recipe, &context)
                .is_none()
        );
        assert!(
            memory
                .guarded_array_row_pointer(
                    &array,
                    IntegerTerm::constant_i64(0).into(),
                    CType::UInt32,
                    &[2, 3],
                    &context
                )
                .is_none()
        );
    }

    #[test]
    fn native_input_row_selection_keeps_exact_key_and_parent_bounds() {
        let _session = crate::kernel::VerificationSession::enter();
        let layout = Arc::new(CAggregateLayout::new(
            28,
            4,
            vec![
                CAggregateField::new("values", 4, CType::Int32Array(6))
                    .with_array_shape(Some(&[2, 3])),
            ],
        ));
        let origin = CPointerValue::new(Pointer::symbolic(Variable(997_301)), CType::Int32Pointer)
            .with_designation(PointerDesignation::Unresolved(Variable(997_301)));
        let memory = CMemory::new()
            .with_native_record_input(origin.clone(), layout.clone())
            .unwrap();
        let context = PureFactContext::new();
        let selection = CAggregateMemberSelection {
            layout,
            path: vec!["values".into()].into(),
            value_type: CType::Int32Array(6),
        };
        let (member, guards) = memory
            .guarded_native_record_selection(&origin, &selection, &context)
            .unwrap();
        assert!(checked(guards, &context));
        let (array, guards) = memory
            .guarded_member_array_pointer(&member, &context)
            .unwrap();
        assert!(checked(guards, &context));
        let forged = match array.designation().unwrap() {
            PointerDesignation::InputSelected {
                input,
                origin,
                path,
                base,
                ..
            } => array
                .clone()
                .with_designation(PointerDesignation::InputSelected {
                    input: input.clone(),
                    origin: origin.clone(),
                    path: path.clone(),
                    base: base.clone(),
                    element_type: CType::Int32,
                    stride: 4,
                    count: IntegerTerm::constant_i64(6).into(),
                }),
            _ => unreachable!(),
        };
        assert!(
            memory
                .authenticated_input_selection(&forged, &context)
                .is_none()
        );
        let index = Bitvector32Term::Variable(Variable(997_302));
        let context = context
            .assume_condition(
                ConditionTerm::signed_less_equal(0u32.into(), index.clone()),
                true,
            )
            .assume_condition(
                ConditionTerm::signed_less_than(index.clone(), 2u32.into()),
                true,
            );
        let (row, guards) = memory
            .guarded_array_row_pointer(
                &array,
                IntegerTerm::Machine(SharedMachineIntegerTerm::intern(
                    MachineIntegerType::Int32,
                    index,
                ))
                .into(),
                CType::Int32,
                &[2, 3],
                &context,
            )
            .unwrap();
        assert!(checked(guards, &context));
        assert!(
            matches!(row.designation(),Some(PointerDesignation::InputSelected {input:CNativeInputIdentity::Unresolved(identity),path,..}) if *identity==Variable(997_301) && path.len()==2)
        );
        assert!(
            memory
                .authenticated_array_domain(&row, &PureFactContext::new())
                .unwrap()
                .iter()
                .any(|guard| PureFactContext::new().decide(guard) != Some(true))
        );
    }

    #[test]
    fn native_fixed_scalar_array_inputs_keep_one_dimensional_and_empty_geometry() {
        let _session = crate::kernel::VerificationSession::enter();
        for count in [0, 4] {
            let root = Pointer::symbolic(Variable(997_302 + u64::from(count)));
            let layout = CAggregateLayout::new_scalar_array(CType::Int32, count).unwrap();
            let memory = CMemory::new()
                .with_object_input_domain(root.clone(), &layout)
                .unwrap();
            let pointer =
                CMemory::aggregate_input_pointer(root.clone(), &layout, CType::Int32Pointer);
            assert!(memory.has_declared_array_domain(&pointer));
            assert!(memory.has_aggregate_object_domain(&pointer, &layout));
            assert!(
                memory
                    .declared_array_pointer(&root, CType::Int32, count)
                    .is_some()
            );
            assert!(!memory.has_initialized_bytes_under(&root, 4, &PureFactContext::new()));
            let incompatible =
                memory.with_declared_scalar_block(root.block.clone(), 4, CType::UInt32);
            assert!(!incompatible.authenticated_pointer_domain_at_base(&pointer));
        }
    }

    #[test]
    fn actual_row_evaluation_work_is_independent_of_unselected_rows() {
        let mut samples = Vec::new();
        for rows in [16, 1024, 1_000_000] {
            let _session = crate::kernel::VerificationSession::enter();
            let (memory, array) = matrix(rows);
            let state = CState::new().with_memory(memory);
            let expression = CExpression::ArrayRowAddress {
                array: Box::new(CExpression::Value(CValue::Pointer(array))),
                index: Box::new(CExpression::Value(int32(0))),
                element_type: CType::Int32,
                shape: Arc::from([rows, 3]),
            };
            let (paths, work) = crate::instrumentation::measure_deterministic_work(|| {
                let mut budget = crate::kernel::ExecutionBudget::beside_live_state();
                crate::kernel::eval::evaluate_c_expression_paths(
                    &state,
                    &expression,
                    &PureFactContext::new(),
                    &mut budget,
                )
                .unwrap()
            });
            assert!(
                matches!(paths.as_slice(),[path] if matches!(path.outcome,CExpressionOutcome::Value(CValue::Pointer(_))))
            );
            samples.push(work);
        }
        assert!(
            samples.windows(2).all(|pair| pair[0] == pair[1]),
            "{samples:?}"
        );
    }
}
