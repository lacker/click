//! Surface form of iterated guarded ownership.
//!
//! A resource body clause
//!
//! ```text
//! forall (k: int32) where lo <= k and k < hi {
//!     if g[k] == v { owns base[s * k + a..s * k + b]; }
//! }
//! ```
//!
//! is kept as written ([`IteratedResourceClause`]) for printing and
//! diagnostics. [`iterated_clause_shape`] reads the kernel's shape off it
//! once: the index bounds, the element base with its constant stride and
//! offsets, and the guard cell array with its compared value. Every lowering
//! goes through that one function, so the definition validation that runs it
//! first is the only place a malformed clause is refused.

use super::*;

/// The shape the kernel reads an iterated clause as. Expressions are C
/// fragments over the body's parameters and fields; none mentions the index.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(in crate::surface) struct IteratedClauseShape {
    pub(in crate::surface) lower: CExpression,
    pub(in crate::surface) upper: CExpression,
    pub(in crate::surface) element_base: CExpression,
    pub(in crate::surface) stride: u32,
    pub(in crate::surface) start_offset: i32,
    pub(in crate::surface) end_offset: i32,
    pub(in crate::surface) guard: Option<IteratedGuardShape>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(in crate::surface) struct IteratedGuardShape {
    pub(in crate::surface) base: CExpression,
    pub(in crate::surface) holds_when_equal: bool,
    pub(in crate::surface) value: CExpression,
}

/// An affine form `coefficient * index + constant` with integer constants.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Affine {
    coefficient: i64,
    constant: i64,
}

fn c_expression_constant(expression: &CExpression) -> Option<i64> {
    match expression {
        CExpression::Value(CValue::Int32(term)) => term.as_const().map(|value| value as i32 as i64),
        CExpression::Cast { expression, .. } => c_expression_constant(expression),
        _ => None,
    }
}

/// Reads `expression` as an affine function of `index` with constant
/// coefficients, or `None` when it is not one.
fn affine_in(expression: &CExpression, index: &str) -> Option<Affine> {
    if let Some(constant) = c_expression_constant(expression) {
        return Some(Affine {
            coefficient: 0,
            constant,
        });
    }
    match expression {
        CExpression::Variable(name) if name == index => Some(Affine {
            coefficient: 1,
            constant: 0,
        }),
        CExpression::Cast { expression, .. } => affine_in(expression, index),
        CExpression::Add(left, right) => {
            let (left, right) = (affine_in(left, index)?, affine_in(right, index)?);
            Some(Affine {
                coefficient: left.coefficient.checked_add(right.coefficient)?,
                constant: left.constant.checked_add(right.constant)?,
            })
        }
        CExpression::Subtract(left, right) => {
            let (left, right) = (affine_in(left, index)?, affine_in(right, index)?);
            Some(Affine {
                coefficient: left.coefficient.checked_sub(right.coefficient)?,
                constant: left.constant.checked_sub(right.constant)?,
            })
        }
        CExpression::Multiply(left, right) => {
            let (left, right) = (affine_in(left, index)?, affine_in(right, index)?);
            match (left.coefficient, right.coefficient) {
                (0, _) => Some(Affine {
                    coefficient: right.coefficient.checked_mul(left.constant)?,
                    constant: right.constant.checked_mul(left.constant)?,
                }),
                (_, 0) => Some(Affine {
                    coefficient: left.coefficient.checked_mul(right.constant)?,
                    constant: left.constant.checked_mul(right.constant)?,
                }),
                _ => None,
            }
        }
        _ => None,
    }
}

/// `base[index]` as the C fragment a comparison side lowers to: the base
/// pointer expression, when the load's address is exactly `base + index`.
fn indexed_load_base<'a>(expression: &'a CExpression, index: &str) -> Option<&'a CExpression> {
    match expression {
        CExpression::Index(base, offset) => {
            matches!(offset.as_ref(), CExpression::Variable(name) if name == index).then_some(base)
        }
        CExpression::TypedLoad { pointer, .. } | CExpression::Load(pointer) => {
            match pointer.as_ref() {
                CExpression::Add(base, offset) if matches!(offset.as_ref(), CExpression::Variable(name) if name == index) => {
                    Some(base)
                }
                CExpression::Index(..) => indexed_load_base(pointer, index),
                _ => None,
            }
        }
        CExpression::Cast { expression, .. } => indexed_load_base(expression, index),
        _ => None,
    }
}

fn side_as_c(expression: &ContractExpression) -> Result<CExpression, String> {
    resource_body_c_fragment(expression).ok_or_else(|| {
        format!(
            "`{}` is not a C expression",
            crate::surface::diagnostics::describe_contract_expression(expression)
        )
    })
}

fn is_index(expression: &CExpression, index: &str) -> bool {
    matches!(expression, CExpression::Variable(name) if name == index)
}

/// One bound of the `where` proposition: `Ok(Some((true, lo)))` for a lower
/// bound `lo <= k`, `Ok(Some((false, hi)))` for an upper bound `k < hi`.
fn range_bound(
    proposition: &ClickProposition,
    index: &str,
) -> Result<Option<(bool, CExpression)>, String> {
    let ClickProposition::Comparison {
        left,
        operator,
        right,
    } = proposition
    else {
        return Ok(None);
    };
    let (left, right) = (side_as_c(left)?, side_as_c(right)?);
    Ok(match operator {
        ComparisonOperator::LessEqual if is_index(&right, index) => Some((true, left)),
        ComparisonOperator::GreaterEqual if is_index(&left, index) => Some((true, right)),
        ComparisonOperator::LessThan if is_index(&left, index) => Some((false, right)),
        ComparisonOperator::GreaterThan if is_index(&right, index) => Some((false, left)),
        _ => None,
    })
}

/// The `where` proposition's bounds as written: `(lo, hi)` for `lo <= k and
/// k < hi` in any of the accepted spellings.
fn written_range_bounds(
    clause: &IteratedResourceClause,
) -> Option<(ContractExpression, ContractExpression)> {
    let index = clause.binder.as_str();
    let ClickProposition::And(first, second) = &clause.range else {
        return None;
    };
    let bound = |proposition: &ClickProposition| {
        let ClickProposition::Comparison {
            left,
            operator,
            right,
        } = proposition
        else {
            return None;
        };
        let at =
            |side: &ContractExpression| side_as_c(side).is_ok_and(|side| is_index(&side, index));
        match operator {
            ComparisonOperator::LessEqual if at(right) => Some((true, left.clone())),
            ComparisonOperator::GreaterEqual if at(left) => Some((true, right.clone())),
            ComparisonOperator::LessThan if at(left) => Some((false, right.clone())),
            ComparisonOperator::GreaterThan if at(right) => Some((false, left.clone())),
            _ => None,
        }
    };
    match (bound(first)?, bound(second)?) {
        ((true, lower), (false, upper)) | ((false, upper), (true, lower)) => Some((lower, upper)),
        _ => None,
    }
}

/// An unguarded iterated clause owns every element of its range, so it is
/// the plain range `owns base[lo..hi]` and lowers to exactly that. Only the
/// contiguous one-cell element `base[k..k + 1]` is accepted; any other
/// unguarded element is refused with the range spelling to write instead.
pub(in crate::surface) fn unguarded_iterated_clause_as_range(
    clause: &IteratedResourceClause,
) -> Result<ContractSegment, String> {
    let shape = iterated_clause_shape(clause)?;
    let (lower, upper) = written_range_bounds(clause).ok_or_else(|| {
        format!(
            "the index range must be written `lo <= {0} and {0} < hi`",
            clause.binder
        )
    })?;
    let ContractSegmentSurface::Range { base, .. } = &clause.element.surface else {
        return Err("an iterated element must be a range `base[start..end]`".to_string());
    };
    if (shape.stride, shape.start_offset, shape.end_offset) != (1, 0, 1) {
        return Err(format!(
            "an unguarded iterated clause owns every element, so it must own `base[{0}..{0} + 1]` and means `owns base[lo..hi]`; write the range directly for any other element shape",
            clause.binder
        ));
    }
    Ok(ContractSegment {
        state: clause.element.state,
        base: clause.element.base.clone(),
        start: shape.lower,
        end: shape.upper,
        surface: ContractSegmentSurface::Range {
            base: base.clone(),
            start: lower,
            end: upper,
        },
    })
}

/// Reads the kernel shape of one iterated clause, or says why the clause is
/// not one Click supports. This is the only place the shape is derived.
pub(in crate::surface) fn iterated_clause_shape(
    clause: &IteratedResourceClause,
) -> Result<IteratedClauseShape, String> {
    let index = clause.binder.as_str();
    let bounded = || {
        format!(
            "the index range must be written `lo <= {index} and {index} < hi` with bounds that do not mention `{index}`"
        )
    };
    let ClickProposition::And(first, second) = &clause.range else {
        return Err(bounded());
    };
    let (Some(first), Some(second)) = (range_bound(first, index)?, range_bound(second, index)?)
    else {
        return Err(bounded());
    };
    let (lower, upper) = match (first, second) {
        ((true, lower), (false, upper)) | ((false, upper), (true, lower)) => (lower, upper),
        _ => return Err(bounded()),
    };
    if crate::surface::validation::c_expression_uses_variable(&lower, index)
        || crate::surface::validation::c_expression_uses_variable(&upper, index)
    {
        return Err(bounded());
    }
    let element = &clause.element;
    if crate::surface::validation::c_expression_uses_variable(&element.base, index) {
        return Err(format!(
            "the element base must not depend on `{index}`; write the index in the range, `base[{index}..{index} + 1]`"
        ));
    }
    let affine = |expression: &CExpression, which: &str| {
        affine_in(expression, index).ok_or_else(|| {
            format!(
                "the element range's {which} must be `s * {index} + c` with integer constants `s` and `c`"
            )
        })
    };
    let (start, end) = (
        affine(&element.start, "start")?,
        affine(&element.end, "end")?,
    );
    if start.coefficient != end.coefficient || start.coefficient < 1 {
        return Err(format!(
            "the element range must advance by the same positive stride at both ends, as `base[{index}..{index} + 1]` does"
        ));
    }
    let width = end.constant - start.constant;
    if width < 1 {
        return Err(format!(
            "the element range at `{index}` is empty; an element must own at least one cell"
        ));
    }
    if width > start.coefficient {
        return Err(format!(
            "element ranges of different indices overlap: index `{index}` owns {width} cells but the next index starts {} cells later, so a cell would be owned twice; use a stride of at least {width} (for example `base[{width} * {index}..{width} * {index} + {width}]`)",
            start.coefficient
        ));
    }
    let (Ok(stride), Ok(start_offset), Ok(end_offset)) = (
        u32::try_from(start.coefficient),
        i32::try_from(start.constant),
        i32::try_from(end.constant),
    ) else {
        return Err("the element range's constants do not fit in `int32`".to_string());
    };
    let guard = clause
        .guard
        .as_ref()
        .map(|guard| {
            let refusal = || {
                format!(
                    "the guard must compare one guard cell at the index with a value, `g[{index}] == v` or `g[{index}] != v`"
                )
            };
            let ClickProposition::Comparison {
                left,
                operator,
                right,
            } = guard
            else {
                return Err(refusal());
            };
            let holds_when_equal = match operator {
                ComparisonOperator::Equal => true,
                ComparisonOperator::NotEqual => false,
                _ => return Err(refusal()),
            };
            let (left, right) = (side_as_c(left)?, side_as_c(right)?);
            let (base, value) = match (
                indexed_load_base(&left, index),
                indexed_load_base(&right, index),
            ) {
                (Some(base), None) => (base.clone(), right),
                (None, Some(base)) => (base.clone(), left),
                _ => return Err(refusal()),
            };
            if crate::surface::validation::c_expression_uses_variable(&base, index) || crate::surface::validation::c_expression_uses_variable(&value, index)
            {
                return Err(refusal());
            }
            Ok(IteratedGuardShape {
                base,
                holds_when_equal,
                value,
            })
        })
        .transpose()?;
    Ok(IteratedClauseShape {
        lower,
        upper,
        element_base: element.base.clone(),
        stride,
        start_offset,
        end_offset,
        guard,
    })
}

/// The clause as one quantified proposition, so parameter substitution can
/// reuse the hygienic binder handling of `forall`: the element segment rides
/// along as a `loadable(...)` atom and is read back by
/// [`iterated_clause_from_proposition`].
fn iterated_clause_as_proposition(clause: &IteratedResourceClause) -> ClickProposition {
    let element = ClickProposition::Loadable {
        segment: clause.element.clone(),
    };
    let body = match &clause.guard {
        Some(guard) => ClickProposition::And(
            Box::new(clause.range.clone()),
            Box::new(ClickProposition::And(
                Box::new(guard.clone()),
                Box::new(element),
            )),
        ),
        None => ClickProposition::And(Box::new(clause.range.clone()), Box::new(element)),
    };
    ClickProposition::ForAll {
        click_type: ClickType::C(C0Type::Int32),
        name: clause.binder.clone(),
        written_name: None,
        body: Box::new(body),
    }
}

fn iterated_clause_from_proposition(
    proposition: ClickProposition,
    template: &IteratedResourceClause,
) -> Result<IteratedResourceClause, String> {
    let malformed = || "iterated ownership clause changed shape under substitution".to_string();
    let ClickProposition::ForAll { name, body, .. } = proposition else {
        return Err(malformed());
    };
    let ClickProposition::And(range, rest) = *body else {
        return Err(malformed());
    };
    let (guard, element) = match (*rest, template.guard.is_some()) {
        (ClickProposition::And(guard, element), true) => (Some(*guard), *element),
        (element, false) => (None, element),
        _ => return Err(malformed()),
    };
    let ClickProposition::Loadable { segment } = element else {
        return Err(malformed());
    };
    Ok(IteratedResourceClause {
        owner: template.owner.clone(),
        binder: name,
        range: *range,
        guard,
        element: segment,
    })
}

/// Substitutes the body's parameters in one iterated clause. The index binder
/// is renamed first when a substituted value mentions its name.
pub(in crate::surface) fn substitute_iterated_clause(
    clause: &IteratedResourceClause,
    substitutions: &ContractSubstitutions<'_>,
) -> Result<IteratedResourceClause, String> {
    let substituted =
        substitute_click_proposition_in(&iterated_clause_as_proposition(clause), substitutions)?;
    iterated_clause_from_proposition(substituted, clause)
}

/// The kernel specification of one iterated clause in a resource body.
pub(in crate::surface) fn iterated_clause_to_spec(
    clause: &IteratedResourceClause,
    parameters: &[syntax::C0Parameter],
) -> Result<crate::kernel::CIteratedSpec, ClickError> {
    let shape = iterated_clause_shape(clause).map_err(ClickError::new)?;
    let guard = shape.guard.ok_or_else(|| {
        ClickError::new("an unguarded iterated ownership clause lowers to a plain memory range")
    })?;
    let element_width =
        contract_segment_element_width_for_result_type(parameters, &clause.element, None);
    Ok(crate::kernel::CIteratedSpec {
        owner: clause.owner.clone(),
        element: CMemorySegment::new(shape.element_base, shape.lower, shape.upper)
            .with_element_width(element_width),
        stride: shape.stride,
        start_offset: shape.start_offset,
        end_offset: shape.end_offset,
        guard_base: guard.base,
        guard_cell_type: crate::kernel::CType::Int32,
        guard_cell_width: 4,
        holds_when_equal: guard.holds_when_equal,
        guard_value: guard.value,
    })
}

/// Lowers one iterated clause at `state`: each expression of its shape is
/// read once through the kernel evaluator.
pub(in crate::surface) fn lower_iterated_clause_with_values(
    clause: &IteratedResourceClause,
    parameters: &[syntax::C0Parameter],
    values: &BTreeMap<String, CValue>,
    state: &CState,
    result: Option<&CValue>,
    assumptions: &PureFactContext,
) -> Result<CResourceFact, ClickError> {
    let shape = iterated_clause_shape(clause).map_err(ClickError::new)?;
    let guard = shape.guard.clone().ok_or_else(|| {
        ClickError::new("an unguarded iterated ownership clause lowers to a plain memory range")
    })?;
    let element_width =
        contract_segment_element_width_for_result_type(parameters, &clause.element, None);
    let array_refs = array_refs_for_parameters(parameters, values, state.memory());
    let evaluate = |expression: &CExpression, what: &str| {
        crate::surface::proof::evaluate_resource_fragment_through_kernel(
            expression,
            assumptions,
            values,
            &array_refs,
            state,
            result,
        )
        .map_err(|message| {
            ClickError::new(format!(
                "could not evaluate the {what} of the iterated ownership clause of `{}`: {message}",
                clause.owner
            ))
        })
    };
    let pointer = |value: CValue, what: &str| match value {
        CValue::Pointer(pointer) => Ok(pointer.into_pointer()),
        other => Err(ClickError::new(format!(
            "the {what} of the iterated ownership clause of `{}` evaluated to {other:?}, not a pointer",
            clause.owner
        ))),
    };
    let int32 = |value: CValue, what: &str| match value {
        CValue::Int32(term) => Ok(term),
        other => Err(ClickError::new(format!(
            "the {what} of the iterated ownership clause of `{}` evaluated to {other:?}, not an `int32`",
            clause.owner
        ))),
    };
    let element_base = pointer(
        evaluate(&shape.element_base, "element base")?,
        "element base",
    )?;
    let lower = int32(evaluate(&shape.lower, "lower bound")?, "lower bound")?;
    let upper = int32(evaluate(&shape.upper, "upper bound")?, "upper bound")?;
    let guard_base = pointer(evaluate(&guard.base, "guard base")?, "guard base")?;
    let guard_value = int32(evaluate(&guard.value, "guard value")?, "guard value")?;
    let iterated = crate::kernel::CIteratedMemory::new(
        &clause.owner,
        element_base,
        element_width,
        shape.stride,
        shape.start_offset,
        shape.end_offset,
        lower,
        upper,
        crate::kernel::CIteratedGuard::new(
            guard_base,
            crate::kernel::CType::Int32,
            4,
            guard.holds_when_equal,
            guard_value,
        ),
    )
    .ok_or_else(|| ClickError::new("iterated ownership clause has an invalid element shape"))?;
    Ok(CResourceFact::own(CResource::iterated(iterated)))
}

/// The clause as written, for printing and diagnostics.
pub(in crate::surface) fn describe_iterated_clause(clause: &IteratedResourceClause) -> String {
    let element = crate::surface::diagnostics::describe_contract_segment(&clause.element);
    let range = crate::surface::printing::source_click_proposition(&clause.range);
    match &clause.guard {
        Some(guard) => format!(
            "forall ({}: int32) where {range} {{ if {} {{ owns {element}; }} }}",
            clause.binder,
            crate::surface::printing::source_click_proposition(guard)
        ),
        None => format!(
            "forall ({}: int32) where {range} {{ owns {element}; }}",
            clause.binder
        ),
    }
}
