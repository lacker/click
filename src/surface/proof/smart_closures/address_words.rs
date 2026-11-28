//! Bounded discovery of explicit unsigned-word proofs around aligned addresses.
//! Reads and calls are opaque. Every simplification is a named word law or a
//! goal-local calculation; selected alignment facts are retained in applications.
use super::*;
use SyntaxTerm as E;

fn number(n: u64) -> E {
    E::ProgramExpression(ProgramExpression::Value(crate::kernel::uint64(
        OldMachineTerm::uint64_constant(n),
    )))
}
fn eq(a: E, b: E) -> SyntaxProposition {
    SyntaxProposition::Comparison {
        left: cast_word(a),
        operator: ComparisonOperator::Equal,
        right: cast_word(b),
    }
}
fn and(a: E, b: E) -> E {
    E::BitwiseAnd(Box::new(a), Box::new(b))
}
fn or(a: E, b: E) -> E {
    E::BitwiseOr(Box::new(a), Box::new(b))
}
fn add(a: E, b: E) -> E {
    E::Add(Box::new(a), Box::new(b))
}
fn sub(a: E, b: E) -> E {
    E::Subtract(Box::new(a), Box::new(b))
}

fn address(pointer: E) -> E {
    let mut result = cast_word(pointer);
    if let E::CUnary {
        lowered: ProgramExpression::Cast { integer_mode, .. },
        ..
    } = &mut result
    {
        *integer_mode = crate::kernel::IntegerCastMode::Standard;
    }
    result
}
fn cast_word(operand: E) -> E {
    // Native operators keep their authoritative C tree. A bare Surface Add
    // would otherwise be reinterpreted as an exact Integer operation.
    let native = crate::surface::lowering::contract_expression_as_program_expression(&operand);
    let lowered_operand = native
        .clone()
        .unwrap_or_else(|| ProgramExpression::Value(int32(0)));
    let operand = native.map(E::ProgramExpression).unwrap_or(operand);
    E::CUnary {
        operand: Box::new(operand),
        lowered: ProgramExpression::Cast {
            expression: Box::new(lowered_operand),
            target_type: ProgramType::UInt64,
            integer_mode: crate::kernel::IntegerCastMode::CConversion,
            pointee_struct: None,
            pointee_struct_size: None,
            pointee_volatile: false,
            pointee_constant: false,
            explicit_qualification: false,
        },
    }
}
fn address_pointer(e: &E) -> Option<E> {
    match e {
        E::Call { name, arguments } if name == "address" => arguments.first().cloned(),
        E::ProgramExpression(ProgramExpression::Cast {
            expression,
            target_type: ProgramType::UInt64,
            ..
        }) => Some(E::ProgramExpression(expression.as_ref().clone())),
        E::CUnary {
            operand,
            lowered:
                ProgramExpression::Cast {
                    target_type: ProgramType::UInt64,
                    ..
                },
        } => Some(operand.as_ref().clone()),
        _ => None,
    }
}
fn sum_operands(e: &E) -> Option<(E, E)> {
    match e {
        E::Add(a, b) => Some((a.as_ref().clone(), b.as_ref().clone())),
        E::ProgramExpression(ProgramExpression::Add(a, b)) => Some((
            E::ProgramExpression(a.as_ref().clone()),
            E::ProgramExpression(b.as_ref().clone()),
        )),
        _ => None,
    }
}
fn named_word(e: &E) -> bool {
    match e {
        E::Binding(_)
        | E::ProgramBinding(_)
        | E::Field { .. }
        | E::Index(..)
        | E::ArrayIndex { .. }
        | E::ProgramExpression(
            ProgramExpression::Variable(_)
            | ProgramExpression::Load(_)
            | ProgramExpression::TypedLoad { .. },
        )
        | E::CUnary {
            lowered: ProgramExpression::Load(_) | ProgramExpression::TypedLoad { .. },
            ..
        } => true,
        E::At { expression, .. } | E::Old(expression) => named_word(expression),
        _ => false,
    }
}

fn alignment_mask(expression: &E) -> Option<(E, &E)> {
    match expression {
        E::BitwiseAnd(base, mask) => Some((base.as_ref().clone(), mask)),
        E::At {
            selector,
            expression,
        } => {
            let (base, mask) = alignment_mask(expression)?;
            Some((
                E::At {
                    selector: selector.clone(),
                    expression: Box::new(base),
                },
                mask,
            ))
        }
        _ => None,
    }
}
struct Words<'p, 'a> {
    input: &'p Proof<'a>,
    alignments: Vec<(E, u64, SyntaxProposition)>,
    steps: Vec<ProofStep>,
    written_steps: usize,
    aliases: Vec<(E, E)>,
    active_aliases: std::collections::HashSet<usize>,
}
impl Words<'_, '_> {
    fn charge(&self, depth: usize) -> Result<(), ClickError> {
        if depth > 128
            || self.written_steps > 4096
            || crate::instrumentation::deadline_exceeded_with_work(1)
        {
            return Err(self
                .input
                .step_error("Address-word expansion reached its work, depth or 4096-step bound"));
        }
        Ok(())
    }
    fn constant(&self, e: &E) -> Result<Option<u64>, ClickError> {
        let value = self.input.capture_native_argument(e)?;
        let (ty, word) = match value.numeric_value() {
            ProgramValue::Int8(w) => (MachineIntegerType::Int8, w),
            ProgramValue::UInt8(w) => (MachineIntegerType::UInt8, w),
            ProgramValue::Int16(w) => (MachineIntegerType::Int16, w),
            ProgramValue::UInt16(w) => (MachineIntegerType::UInt16, w),
            ProgramValue::Int32(w) => (MachineIntegerType::Int32, w),
            ProgramValue::UInt32(w) => (MachineIntegerType::UInt32, w),
            ProgramValue::Int64(w) => (MachineIntegerType::Int64, w),
            ProgramValue::UInt64(w) => (MachineIntegerType::UInt64, w),
            ProgramValue::Int128(w) => (MachineIntegerType::Int128, w),
            ProgramValue::UInt128(w) => (MachineIntegerType::UInt128, w),
            _ => return Ok(None),
        };
        if ty == MachineIntegerType::UInt64 {
            return Ok(
                crate::kernel::proof::arithmetic_special::unsigned_word_constant_for_discovery(
                    crate::kernel::MachineOperandView::Old(word),
                ),
            );
        }
        let mask: BigInt = (BigInt::one() << 64usize) - BigInt::one();
        Ok(ty
            .constant_from_term(word)
            .and_then(|n| (n.to_integer() & mask).to_u64()))
    }
    fn same(&self, a: &E, b: &E) -> Result<bool, ClickError> {
        Ok(crate::kernel::proof::fact_reasoning::computes_leaf(
            &self.input.lower_cited_surface_proposition(
                &eq(a.clone(), b.clone()),
                "address-word identity",
            )?,
        ))
    }
    fn record(&mut self, a: E, b: E, body: Vec<ProofStep>) -> Result<(), ClickError> {
        self.charge(0)?;
        if a != b {
            self.written_steps = self.written_steps.saturating_add(body.len() + 2);
            self.charge(0)?;
            self.steps
                .push(super::super::wide_arithmetic::have(eq(a, b), body));
        }
        Ok(())
    }
    fn known(&mut self, a: E, b: E) -> Result<(), ClickError> {
        self.record(a, b, vec![ProofStep::Known])
    }
    fn law(
        &mut self,
        name: &str,
        arguments: Vec<E>,
        premises: Vec<SyntaxProposition>,
        a: E,
        b: E,
    ) -> Result<(), ClickError> {
        self.record(
            a,
            b,
            vec![
                ProofStep::ApplyPlannedTheorem {
                    application: TheoremApplication {
                        name: format!("click::integer::{name}"),
                        arguments,
                    },
                    premises,
                },
                ProofStep::Known,
            ],
        )
    }
    fn aligned(&mut self, base: &E, mask: u64) -> Result<Option<SyntaxProposition>, ClickError> {
        for (source, large, fact) in self.alignments.clone() {
            self.charge(0)?;
            if large & mask != mask || !self.same(base, &source)? {
                continue;
            }
            let result = eq(and(base.clone(), number(mask)), number(0));
            if mask != large {
                self.law(
                    "uint64_mask_subset",
                    vec![base.clone(), number(large), number(mask)],
                    vec![fact, eq(and(number(large), number(mask)), number(mask))],
                    and(base.clone(), number(mask)),
                    number(0),
                )?;
            }
            return Ok(Some(result));
        }
        Ok(None)
    }
    fn offset(&mut self, e: &E, depth: usize) -> Result<Option<E>, ClickError> {
        let Some(pointer) = address_pointer(e) else {
            return Ok(None);
        };
        let Some((base, index)) = sum_operands(&pointer) else {
            return Ok(None);
        };
        let ProgramValue::Pointer(p) = self.input.capture_native_argument(&base)? else {
            return Ok(None);
        };
        let (name, width) = match p.program_type() {
            ProgramType::UInt8Pointer => ("uint8", 1),
            ProgramType::Int8Pointer => ("int8", 1),
            ProgramType::UInt16Pointer => ("uint16", 2),
            ProgramType::Int16Pointer => ("int16", 2),
            ProgramType::UInt32Pointer => ("uint32", 4),
            ProgramType::Int32Pointer => ("int32", 4),
            ProgramType::UInt64Pointer => ("uint64", 8),
            ProgramType::Int64Pointer => ("int64", 8),
            ProgramType::Float32Pointer => ("float32", 4),
            ProgramType::Float64Pointer => ("float64", 8),
            _ => return Ok(None),
        };
        // Struct pointers use a scalar carrier too, but their element stride is
        // their record layout. Do not infer a scalar stride from that carrier.
        if p.object_class().is_some_and(|class| {
            !matches!(
                class,
                crate::kernel::effective_type::CAccessClass::Scalar(_)
            )
        }) {
            return Ok(None);
        }
        let index_type = match self.input.capture_native_argument(&index)? {
            ProgramValue::Int32(_) => "int32",
            ProgramValue::Int64(_) => "int64",
            _ => return Ok(None),
        };
        let bytes = E::Multiply(Box::new(cast_word(index.clone())), Box::new(number(width)));
        let result = add(address(base.clone()), bytes);
        self.law(
            &format!("{name}_pointer_add_address_{index_type}"),
            vec![base, index],
            vec![],
            e.clone(),
            result.clone(),
        )?;
        Ok(Some(self.normalize(&result, depth + 1)?))
    }
    // Returning paths can name an offset pointer as `result`. Discover the
    // constant displacement from a selected base, then retain both the exact
    // goal-local identity and the named element-offset application.
    fn relative_offset(&mut self, e: &E, depth: usize) -> Result<Option<E>, ClickError> {
        let Some(source) = address_pointer(e) else {
            return Ok(None);
        };
        let ProgramValue::Pointer(target) = self.input.capture_native_argument(&source)? else {
            return Ok(None);
        };
        for (base, _, _) in self.alignments.clone() {
            if self.same(e, &base)? {
                continue;
            }
            let Some(pointer) = address_pointer(&base) else {
                continue;
            };
            let ProgramValue::Pointer(p) = self.input.capture_native_argument(&pointer)? else {
                continue;
            };
            if p.program_type() != target.program_type()
                || p.object_class().is_some_and(|c| {
                    !matches!(c, crate::kernel::effective_type::CAccessClass::Scalar(_))
                })
            {
                continue;
            }
            let Some(bytes) =
                crate::kernel::proof::arithmetic_special::constant_pointer_byte_difference(
                    target.address(),
                    p.address(),
                )
            else {
                continue;
            };
            let width = match p.program_type() {
                ProgramType::Int8Pointer | ProgramType::UInt8Pointer => 1,
                ProgramType::Int16Pointer | ProgramType::UInt16Pointer => 2,
                ProgramType::Int32Pointer
                | ProgramType::UInt32Pointer
                | ProgramType::Float32Pointer => 4,
                ProgramType::Int64Pointer
                | ProgramType::UInt64Pointer
                | ProgramType::Float64Pointer => 8,
                _ => continue,
            };
            if bytes == 0 || bytes % width != 0 {
                continue;
            }
            let Ok(index) = i32::try_from(bytes / width) else {
                continue;
            };
            let expanded = address(add(
                pointer,
                E::ProgramExpression(ProgramExpression::Value(int32(OldMachineTerm::constant(
                    index as u32,
                )))),
            ));
            // This is discovery of an equality between already expressible
            // terms, not selection of a spelling for an unnamed kernel term.
            if !self.same(e, &expanded)? {
                continue;
            }
            self.known(e.clone(), expanded.clone())?;
            return self.offset(&expanded, depth + 1);
        }
        Ok(None)
    }
    /// Open a computed C value only over the exact operands named by this
    /// plan. An opaque unmatched operand is a search miss; its existing
    /// source name remains valid. This constructs an ordinary reflexive
    /// identity, not a new read term or a different memory state.
    fn project_word(
        &self,
        word: crate::kernel::MachineOperandView<'_>,
        atoms: &[(crate::kernel::SharedMachineIntegerTerm, E)],
        root: bool,
        depth: usize,
    ) -> Result<Option<E>, ClickError> {
        self.charge(depth)?;
        if let Some(value) = word.uint64_constant() {
            return Ok(Some(number(value)));
        }
        if !root {
            let key = word.retain(MachineIntegerType::UInt64);
            if let Some((_, source)) = atoms.iter().find(|(value, _)| *value == key) {
                return Ok(Some(source.clone()));
            }
        }
        let Some((MachineIntegerType::UInt64, op, [a, b])) = word.binary() else {
            return Ok(None);
        };
        if !matches!(
            op,
            MachineBinaryOp::Add
                | MachineBinaryOp::Subtract
                | MachineBinaryOp::Multiply
                | MachineBinaryOp::BitwiseAnd
                | MachineBinaryOp::BitwiseOr
        ) {
            return Ok(None);
        }
        let (Some(a), Some(b)) = (
            self.project_word(a, atoms, false, depth + 1)?,
            self.project_word(b, atoms, false, depth + 1)?,
        ) else {
            return Ok(None);
        };
        Ok(Some(match op {
            MachineBinaryOp::Add => add(a, b),
            MachineBinaryOp::Subtract => sub(a, b),
            MachineBinaryOp::Multiply => E::Multiply(Box::new(a), Box::new(b)),
            MachineBinaryOp::BitwiseAnd => and(a, b),
            MachineBinaryOp::BitwiseOr => or(a, b),
            _ => unreachable!(),
        }))
    }
    // Retain the address as the base and put only modular arithmetic in its tag.
    fn split(&self, value: &E) -> Result<Option<(E, E)>, ClickError> {
        for (base, _, _) in &self.alignments {
            if self.same(value, base)? {
                return Ok(Some((base.clone(), number(0))));
            }
            if let E::Add(a, b) = value {
                if self.same(a, base)? {
                    return Ok(Some((base.clone(), b.as_ref().clone())));
                }
                if self.same(b, base)? {
                    return Ok(Some((base.clone(), a.as_ref().clone())));
                }
            }
        }
        Ok(None)
    }
    fn normalize(&mut self, e: &E, depth: usize) -> Result<E, ClickError> {
        self.charge(depth)?;
        for i in 0..self.aliases.len() {
            if self.active_aliases.contains(&i) {
                continue;
            }
            let (from, to) = self.aliases[i].clone();
            if self.same(e, &from)? {
                self.active_aliases.insert(i);
                let result = self.normalize(&to, depth + 1);
                self.active_aliases.remove(&i);
                return result;
            }
        }
        // The local definitions retain their type. Do not reinterpret signed,
        // narrow or mathematical arithmetic as unsigned word arithmetic.
        if let Some(c) = self.constant(e)? {
            return Ok(number(c));
        }
        let native = self.input.capture_native_argument(e)?;
        let unsigned = match native.numeric_value() {
            ProgramValue::UInt64(word) => crate::kernel::MachineOperandView::Old(word)
                .binary()
                .is_some_and(|(ty, _, _)| ty == MachineIntegerType::UInt64),
            _ => false,
        };
        if let Some(offset) = self.offset(e, depth)? {
            return Ok(offset);
        }
        if let Some(offset) = self.relative_offset(e, depth)? {
            return Ok(offset);
        }
        if !unsigned {
            return Ok(e.clone());
        }
        if named_word(e)
            && let ProgramValue::UInt64(word) = native.numeric_value()
        {
            let mut atoms = Vec::new();
            for source in self
                .alignments
                .iter()
                .map(|(e, _, _)| e)
                .chain(self.aliases.iter().map(|(e, _)| e))
            {
                self.charge(0)?;
                let captured = self.input.capture_native_argument(source)?;
                if let ProgramValue::UInt64(value) = captured.numeric_value() {
                    atoms.push((
                        crate::kernel::MachineOperandView::Old(value)
                            .retain(MachineIntegerType::UInt64),
                        source.clone(),
                    ));
                }
            }
            if let Some(expanded) = self.project_word(
                crate::kernel::MachineOperandView::Old(word),
                &atoms,
                true,
                depth + 1,
            )? {
                self.known(e.clone(), expanded.clone())?;
                return self.normalize(&expanded, depth + 1);
            }
        }
        match e {
            E::CUnary {
                operand,
                lowered:
                    ProgramExpression::Cast {
                        target_type: ProgramType::UInt64,
                        ..
                    },
            } => self.normalize(operand, depth + 1),
            E::Add(a, b) | E::Subtract(a, b) => {
                let (a, b) = (self.normalize(a, depth + 1)?, self.normalize(b, depth + 1)?);
                let value = if matches!(e, E::Add(..)) {
                    add(a.clone(), b.clone())
                } else {
                    sub(a.clone(), b.clone())
                };
                if self.constant(&b)? == Some(0) {
                    self.known(value, a.clone())?;
                    return Ok(a);
                }
                if matches!(e, E::Add(..)) && self.constant(&a)? == Some(0) {
                    self.known(value, b.clone())?;
                    return Ok(b);
                }
                let form = if let Some((base, tag)) = self.split(&a)? {
                    Some((
                        base,
                        if matches!(e, E::Add(..)) {
                            add(tag, b.clone())
                        } else {
                            sub(tag, b.clone())
                        },
                    ))
                } else if matches!(e, E::Add(..)) {
                    self.split(&b)?
                        .map(|(base, tag)| (base, add(a.clone(), tag)))
                } else {
                    None
                };
                if let Some((base, tag)) = form {
                    let tag = self.normalize(&tag, depth + 1)?;
                    let result = if self.constant(&tag)? == Some(0) {
                        base
                    } else {
                        add(base, tag)
                    };
                    self.known(value, result.clone())?;
                    Ok(result)
                } else {
                    Ok(value)
                }
            }
            E::BitwiseAnd(a, b) => {
                // Source evaluation distributes a constant OR through a
                // literal mask before checking. Keep the proof in that same
                // shape, rather than emitting a rewrite of an erased subterm.
                if let Some(mask) = self.constant(b)?
                    && let E::BitwiseOr(x, y) = a.as_ref()
                {
                    for (value, bits) in [(x.as_ref(), y.as_ref()), (y.as_ref(), x.as_ref())] {
                        if let Some(bits) = self.constant(bits)? {
                            let distributed =
                                or(and(value.clone(), number(mask)), number(bits & mask));
                            self.law(
                                "uint64_and_or",
                                vec![value.clone(), number(bits), number(mask)],
                                vec![],
                                e.clone(),
                                distributed.clone(),
                            )?;
                            return self.normalize(&distributed, depth + 1);
                        }
                    }
                }
                let (a, b) = (self.normalize(a, depth + 1)?, self.normalize(b, depth + 1)?);
                let (inner, mask) = if let Some(m) = self.constant(&b)? {
                    (a, m)
                } else if let Some(m) = self.constant(&a)? {
                    self.law(
                        "uint64_and_commute",
                        vec![a.clone(), b.clone()],
                        vec![],
                        and(a.clone(), b.clone()),
                        and(b.clone(), a),
                    )?;
                    (b, m)
                } else {
                    return Ok(and(a, b));
                };
                self.mask(inner, mask, depth + 1)
            }
            E::BitwiseOr(a, b) => {
                let (a, b) = (self.normalize(a, depth + 1)?, self.normalize(b, depth + 1)?);
                if self.constant(&b)? == Some(0) {
                    self.law(
                        "uint64_or_zero",
                        vec![a.clone()],
                        vec![],
                        or(a.clone(), b),
                        a.clone(),
                    )?;
                    return Ok(a);
                }
                if self.constant(&a)? == Some(0) {
                    self.law(
                        "uint64_or_commute",
                        vec![a.clone(), b.clone()],
                        vec![],
                        or(a.clone(), b.clone()),
                        or(b.clone(), a),
                    )?;
                    self.law(
                        "uint64_or_zero",
                        vec![b.clone()],
                        vec![],
                        or(b.clone(), number(0)),
                        b.clone(),
                    )?;
                    return Ok(b);
                }
                for (base, bits, commute) in
                    [(a.clone(), b.clone(), false), (b.clone(), a.clone(), true)]
                {
                    if let E::BitwiseAnd(tag, mask) = &bits
                        && let Some(mask) = self.constant(mask)?
                        && let Some(fact) = self.aligned(&base, mask)?
                    {
                        if commute {
                            self.law(
                                "uint64_or_commute",
                                vec![a.clone(), b.clone()],
                                vec![],
                                or(a.clone(), b.clone()),
                                or(base.clone(), bits.clone()),
                            )?;
                        }
                        let result = add(base.clone(), bits.clone());
                        self.law(
                            "uint64_or_masked",
                            vec![base, tag.as_ref().clone(), number(mask)],
                            vec![fact],
                            or(if commute { b.clone() } else { a.clone() }, bits),
                            result.clone(),
                        )?;
                        return Ok(result);
                    }
                    if let Some(bits_value) = self.constant(&bits)?
                        && let Some((address, tag)) = self.split(&base)?
                    {
                        let alignment = bits_value
                            .checked_add(1)
                            .and_then(|v| v.checked_next_power_of_two());
                        if let Some(mask) = alignment.map(|v| v - 1)
                            && let Some(fact) = self.aligned(&address, mask)?
                        {
                            if commute {
                                self.law(
                                    "uint64_or_commute",
                                    vec![a.clone(), b.clone()],
                                    vec![],
                                    or(a.clone(), b.clone()),
                                    or(base.clone(), bits.clone()),
                                )?;
                            }
                            let sum = add(address.clone(), tag.clone());
                            self.known(base.clone(), sum.clone())?;
                            let result = add(address.clone(), or(tag.clone(), bits.clone()));
                            self.law(
                                "uint64_or_add_low",
                                vec![address, tag, bits.clone(), number(mask)],
                                vec![
                                    eq(and(number(mask), add(number(mask), number(1))), number(0)),
                                    fact,
                                    eq(and(bits.clone(), number(mask)), bits.clone()),
                                ],
                                or(sum, bits),
                                result.clone(),
                            )?;
                            return self.normalize(&result, depth + 1);
                        }
                    }
                }
                Ok(or(a, b))
            }
            _ => Ok(e.clone()),
        }
    }
    fn mask(&mut self, inner: E, mask: u64, depth: usize) -> Result<E, ClickError> {
        self.charge(depth)?;
        let original = and(inner.clone(), number(mask));
        if mask == 0 {
            self.law("uint64_and_zero", vec![inner], vec![], original, number(0))?;
            return Ok(number(0));
        }
        if let Some(fact) = self.aligned(&inner, mask)? {
            self.steps.push(super::super::wide_arithmetic::have(
                fact,
                vec![ProofStep::Known],
            ));
            return Ok(number(0));
        }
        if let E::BitwiseAnd(a, b) = &inner
            && let Some(m) = self.constant(b)?
        {
            let result = and(a.as_ref().clone(), number(m & mask));
            self.law(
                "uint64_and_associate",
                vec![a.as_ref().clone(), b.as_ref().clone(), number(mask)],
                vec![],
                original,
                result.clone(),
            )?;
            return self.normalize(&result, depth + 1);
        }
        if let E::BitwiseOr(a, b) = &inner {
            let result = or(
                and(a.as_ref().clone(), number(mask)),
                and(b.as_ref().clone(), number(mask)),
            );
            self.law(
                "uint64_and_or",
                vec![a.as_ref().clone(), b.as_ref().clone(), number(mask)],
                vec![],
                original,
                result.clone(),
            )?;
            return self.normalize(&result, depth + 1);
        }
        if let E::Multiply(value, factor) = &inner
            && mask & mask.wrapping_add(1) == 0
            && let Some(factor) = self.constant(factor)?
            && factor & mask == 0
        {
            self.law(
                "uint64_mask_multiple",
                vec![value.as_ref().clone(), number(factor), number(mask)],
                vec![
                    eq(and(number(mask), add(number(mask), number(1))), number(0)),
                    eq(and(number(factor), number(mask)), number(0)),
                ],
                original,
                number(0),
            )?;
            return Ok(number(0));
        }
        if let Some((base, tag)) = self.split(&inner)? {
            let low = mask & mask.wrapping_add(1) == 0;
            let high = (!mask) & (!mask).wrapping_add(1) == 0;
            let alignment_mask = if low { mask } else { !mask };
            if (low || high)
                && let Some(fact) = self.aligned(&base, alignment_mask)?
            {
                if high && self.constant(&tag)? == Some(0) {
                    self.law(
                        "uint64_mask_keep",
                        vec![base.clone(), number(mask)],
                        vec![fact],
                        original,
                        base.clone(),
                    )?;
                    return Ok(base);
                }
                let sum = add(base.clone(), tag.clone());
                self.known(inner, sum.clone())?;
                if high && !low {
                    let masked = self.mask(tag.clone(), mask, depth + 1)?;
                    if self.constant(&masked)? == Some(0) {
                        let guard = E::BitwiseNot(Box::new(number(mask)));
                        self.law(
                            "uint64_mask_add_clear",
                            vec![base.clone(), tag.clone(), number(mask)],
                            vec![
                                eq(and(guard.clone(), add(guard, number(1))), number(0)),
                                fact.clone(),
                                eq(and(tag, number(mask)), number(0)),
                            ],
                            and(sum, number(mask)),
                            base.clone(),
                        )?;
                        return Ok(base);
                    }
                }
                let result = if low {
                    and(tag.clone(), number(mask))
                } else {
                    add(base.clone(), and(tag.clone(), number(mask)))
                };
                let guard = if low {
                    number(mask)
                } else {
                    E::BitwiseNot(Box::new(number(mask)))
                };
                self.law(
                    if low {
                        "uint64_mask_add_low"
                    } else {
                        "uint64_mask_add_high"
                    },
                    vec![base, tag, number(mask)],
                    vec![
                        eq(and(guard.clone(), add(guard, number(1))), number(0)),
                        fact,
                    ],
                    and(sum, number(mask)),
                    result.clone(),
                )?;
                return self.normalize(&result, depth + 1);
            }
        }
        Ok(original)
    }
}
impl<'a> crate::kernel::search::ProofSearch<Proof<'a>> {
    /// Name the allocation underlying an aligned pointer read before using
    /// the intrinsic alignment of its concrete address.
    pub(in crate::surface::proof) fn try_recorded_allocation_alignment(
        input: &Proof<'a>,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_recorded_allocation_alignment");
        let Some((condition, _)) = input.goal().and_then(Proposition::old_condition) else {
            return Ok(None);
        };
        let Some((pointer, _)) =
            crate::kernel::proof::arithmetic_special::checked_pointer_alignment(condition)
        else {
            return Ok(None);
        };
        let Some(region) = input.premise_fixed_state_view().and_then(|view| {
            let storage = input
                .facts()
                .assumptions()
                .alignment_storage_address(pointer)?;
            view.fixed_state.recorded_states.allocation_result(&storage)
        }) else {
            return Ok(None);
        };
        let Some(SyntaxProposition::Comparison { left, right, .. }) = input.surface_goal() else {
            return Ok(None);
        };
        let Some(pointer_source) = [left, right].into_iter().find_map(|expression| {
            let (word, _) = alignment_mask(expression)?;
            address_pointer(&word)
        }) else {
            return Ok(None);
        };
        let equality = SyntaxProposition::Comparison {
            left: pointer_source,
            operator: ComparisonOperator::Equal,
            right: E::RegionAllocation(region),
        };
        let Some(rewritten) =
            attempt::candidate_outcome(input.driver().apply_step(ProofStep::Rewrite(equality)))?
        else {
            return Ok(None);
        };
        attempt::candidate_outcome(rewritten.driver().apply_step(ProofStep::Known))
    }

    pub(in crate::surface::proof) fn try_address_words_using(
        input: &Proof<'a>,
        premises: &[SyntaxProposition],
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_address_words_using");
        if let Some(goal) = input.goal()
            && goal.old_condition().is_some_and(|(condition, _)| {
                crate::kernel::proof::arithmetic_special::checked_pointer_alignment(condition)
                    .is_some()
            })
        {
            let mut selected = Vec::new();
            for premise in premises {
                let premise =
                    input.lower_cited_surface_proposition(premise, "alignment premise")?;
                if !input.facts().listed_premise_available(&premise, &[], false) {
                    return Ok(None);
                }
                selected.push(premise);
            }
            let facts = crate::kernel::proof::PureFactStore::from_ordered(&selected);
            if crate::kernel::proof::arithmetic_special::known_pointer_alignment(
                goal,
                facts.assumptions(),
            ) {
                return input.driver().apply_step(ProofStep::Known).map(Some);
            }
        }
        let native_word_goal = input.goal().is_some_and(|p| {
            let Proposition::ConditionIs(c, _) = p else {
                return false;
            };
            crate::kernel::machine_integer::comparison::structural_comparison_view(c.old_form())
                .is_some_and(|v| v.format.format().bits() == 64)
        });
        if !native_word_goal {
            return Ok(None);
        }
        let Some(SyntaxProposition::Comparison {
            left,
            right,
            operator,
        }) = input.surface_goal()
        else {
            return Ok(None);
        };
        let observe_word = |e: &E| -> Result<E, ClickError> {
            if let E::Call { name, arguments } = e
                && name == "to_integer"
                && let [operand] = arguments.as_slice()
                && matches!(
                    input.capture_native_argument(operand)?.numeric_value(),
                    ProgramValue::UInt64(_)
                )
            {
                Ok(operand.clone())
            } else {
                Ok(e.clone())
            }
        };
        let (left, right) = (observe_word(left)?, observe_word(right)?);
        let (left, right) = (&left, &right);
        let mut words = Words {
            input,
            alignments: Vec::new(),
            steps: Vec::new(),
            written_steps: 0,
            aliases: Vec::new(),
            active_aliases: std::collections::HashSet::new(),
        };
        for premise in premises {
            let k = input.lower_cited_surface_proposition(premise, "address-word premise")?;
            if !input.facts().listed_premise_available(&k, &[], false) {
                return Ok(None);
            }
            if let SyntaxProposition::Comparison {
                left,
                operator: ComparisonOperator::Equal,
                right,
            } = surface_comparison_with_anchored_operands(premise)
                && words.constant(&right)? == Some(0)
                && let Some((base, mask)) = alignment_mask(&left)
                && let Some(mask) = words.constant(mask)?
            {
                words.alignments.push((base, mask, premise.clone()));
            }
        }
        if words.alignments.is_empty() {
            return Ok(None);
        }
        for premise in premises {
            let kernel = input.lower_cited_surface_proposition(premise, "address-word relation")?;
            let word_relation = matches!(&kernel,Proposition::ConditionIs(c,true) if crate::kernel::machine_integer::comparison::structural_comparison_view(c.old_form()).is_some_and(|v|v.format.format().bits()==64));
            if !word_relation {
                continue;
            }
            if let SyntaxProposition::Comparison {
                left,
                operator: ComparisonOperator::Equal,
                right,
            } = premise
            {
                if named_word(left) {
                    words.aliases.push((left.clone(), right.clone()));
                } else if named_word(right) {
                    words.aliases.push((right.clone(), left.clone()));
                }
            }
        }
        let a = words.normalize(left, 0)?;
        let b = words.normalize(right, 0)?;
        let final_goal = SyntaxProposition::Comparison {
            left: cast_word(a.clone()),
            operator: *operator,
            right: cast_word(b.clone()),
        };
        let distinct_tags = if *operator == ComparisonOperator::NotEqual {
            match (words.split(&a)?, words.split(&b)?) {
                (Some((base, x)), Some((other, y)))
                    if words.same(&base, &other)?
                        && words
                            .constant(&x)?
                            .zip(words.constant(&y)?)
                            .is_some_and(|(x, y)| x != y) =>
                {
                    Some((base, x, y))
                }
                _ => None,
            }
        } else {
            None
        };
        if !crate::kernel::proof::fact_reasoning::computes_leaf(
            &input
                .lower_cited_surface_proposition(&final_goal, "address-word final calculation")?,
        ) && distinct_tags.is_none()
        {
            return Ok(None);
        }
        for (original, normal) in [(left, a), (right, b)] {
            if !words.same(original, &normal)? {
                words.known(original.clone(), normal.clone())?;
                words
                    .steps
                    .push(ProofStep::Rewrite(eq(original.clone(), normal)));
            }
        }
        if let Some((base, x, y)) = distinct_tags {
            let distinct = SyntaxProposition::Comparison {
                left: cast_word(x.clone()),
                operator: ComparisonOperator::NotEqual,
                right: cast_word(y.clone()),
            };
            words.steps.push(super::super::wide_arithmetic::have(
                distinct,
                vec![ProofStep::Known],
            ));
            words.steps.push(ProofStep::ApplyPlannedTheorem {
                application: TheoremApplication {
                    name: "click::integer::uint64_add_distinct".into(),
                    arguments: vec![base, x.clone(), y.clone()],
                },
                premises: vec![SyntaxProposition::Comparison {
                    left: cast_word(x),
                    operator: ComparisonOperator::NotEqual,
                    right: cast_word(y),
                }],
            });
        }
        let mut proof = input.clone();
        for step in words.steps {
            if proof.focused_discharged() {
                return Ok(Some(proof));
            }
            proof = super::super::without_implicit_solve(|| match step {
                ProofStep::Have {
                    proposition,
                    proof: body,
                } => {
                    let mut scope = proof.driver().open_have(proposition)?;
                    for step in body.steps() {
                        if scope.is_complete() {
                            break;
                        }
                        scope = scope.driver().apply_step(step.clone())?;
                    }
                    if !scope.is_complete() {
                        scope = scope.driver().apply_step(ProofStep::Known)?;
                    }
                    scope.join()
                }
                step => proof.driver().apply_step(step),
            })?;
        }
        if proof.focused_discharged() {
            return Ok(Some(proof));
        }
        // Transport the identities above through the goal, then calculate the
        // remaining modular affine equality (including distinct constant tags).
        Ok(proof.driver().apply_step(ProofStep::Known).ok())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn unsigned_word_law_declarations_match_an_independent_modular_oracle() {
        fn value(e: &E, values: &BTreeMap<String, u64>) -> u64 {
            match e {
                E::Binding(name)
                | E::ProgramExpression(ProgramExpression::Variable(
                    crate::kernel::BindingName::Named(name),
                )) => values[name],
                E::IntegerLiteral(n) => n.parse().unwrap(),
                E::ProgramExpression(ProgramExpression::Value(ProgramValue::UInt64(n))) => {
                    n.uint64_as_const().unwrap()
                }
                E::Call { name, arguments } if name == "to_integer" => value(&arguments[0], values),
                E::CUnary {
                    operand,
                    lowered:
                        ProgramExpression::Cast {
                            target_type: ProgramType::UInt64,
                            ..
                        },
                } => value(operand, values),
                E::Add(a, b) => value(a, values).wrapping_add(value(b, values)),
                E::Subtract(a, b) => value(a, values).wrapping_sub(value(b, values)),
                E::Multiply(a, b) => value(a, values).wrapping_mul(value(b, values)),
                E::BitwiseAnd(a, b) => value(a, values) & value(b, values),
                E::BitwiseOr(a, b) => value(a, values) | value(b, values),
                E::BitwiseNot(a) => !value(a, values),
                _ => panic!("unexpected word-law expression: {e:?}"),
            }
        }
        fn integer(e: &E, values: &BTreeMap<String, u64>) -> BigInt {
            match e {
                E::Call { name, arguments } if name == "to_integer" => {
                    BigInt::from(value(&arguments[0], values))
                }
                E::Add(a, b) => integer(a, values) + integer(b, values),
                E::Multiply(a, b) => integer(a, values) * integer(b, values),
                _ => BigInt::from(value(e, values)),
            }
        }
        fn holds(p: &SyntaxProposition, values: &BTreeMap<String, u64>) -> bool {
            let SyntaxProposition::Comparison {
                left,
                operator,
                right,
            } = p
            else {
                panic!("unexpected word-law proposition: {p:?}")
            };
            let (a, b) = (integer(left, values), integer(right, values));
            match operator {
                ComparisonOperator::Equal => a == b,
                ComparisonOperator::NotEqual => a != b,
                _ => panic!("unexpected word-law relation"),
            }
        }
        let library = crate::surface::standard_library_theorem_definitions().unwrap();
        let samples = [
            0,
            1,
            2,
            3,
            4,
            7,
            8,
            15,
            16,
            u64::MAX,
            u64::MAX - 1,
            u64::MAX - 3,
            1 << 63,
        ];
        for name in [
            "uint64_and_commute",
            "uint64_and_associate",
            "uint64_or_commute",
            "uint64_and_or",
            "uint64_and_zero",
            "uint64_or_zero",
            "uint64_or_disjoint",
            "uint64_mask_add_low",
            "uint64_mask_add_high",
            "uint64_or_add_low",
            "uint64_mask_multiple",
            "uint64_mask_keep",
            "uint64_mask_add_clear",
            "uint64_add_distinct",
            "uint64_add_subtract_cancel",
            "uint64_mask_subset",
            "uint64_or_masked",
        ] {
            let law = library
                .iter()
                .find(|law| law.name() == format!("click::integer::{name}"))
                .unwrap();
            let mut applicable = 0;
            for mut index in 0..samples.len().pow(law.parameters().len() as u32) {
                let values = law
                    .parameters()
                    .iter()
                    .map(|p| {
                        let n = samples[index % samples.len()];
                        index /= samples.len();
                        (p.name().to_owned(), n)
                    })
                    .collect();
                if law.requires().iter().all(|r| {
                    let Requirement::Proposition(p) = r else {
                        panic!("resource word-law requirement")
                    };
                    holds(p, &values)
                }) {
                    applicable += 1;
                    for ensure in law.ensures() {
                        let Ensure::Proposition(p) = ensure.ensure() else {
                            panic!("resource word-law conclusion")
                        };
                        assert!(holds(p, &values), "{name}: {values:?}");
                    }
                }
            }
            assert!(applicable > 0, "vacuous word-law oracle: {name}");
        }
    }
}
