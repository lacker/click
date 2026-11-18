//! Parsing file-scope declarations: global scalars, arrays and aggregates, their initializers and inferred lengths, and their registration.

use super::*;

impl Parser {
    pub(super) fn global_declaration_ahead(&mut self) -> Result<bool, CSyntaxError> {
        let saved_position = self.position;
        if self.peek_ident() == Some("extern") {
            self.position += 1;
        }
        if !self.is_type_start() {
            self.position = saved_position;
            return Ok(false);
        }
        // Lookahead must recognize declaration-only return types without
        // granting their value semantics. The actual object/header parser
        // still decides whether that type is permitted at the chosen site.
        self.parse_type_with_anonymous_struct(false, true, true)?;
        let is_global =
            matches!(self.peek(), Some(Token::Ident(_))) && self.peek_n(1) != Some(&Token::LParen);
        self.position = saved_position;
        Ok(is_global)
    }

    pub(super) fn parse_global_declaration(&mut self) -> Result<(), CSyntaxError> {
        let is_file_static = if self.peek_ident() == Some("static") {
            self.position += 1;
            true
        } else {
            false
        };
        let is_extern = if self.peek_ident() == Some("extern") {
            self.position += 1;
            true
        } else {
            false
        };
        if is_file_static && is_extern {
            return Err(self.error_here(
                "file-scope declarations may use either `static` or `extern`, not both",
            ));
        }
        let parsed_type = self.parse_type()?;
        if parsed_type.function_pointer_signature.is_some() {
            return Err(self.error_here("global function-pointer objects are not supported"));
        }
        let struct_pointer_name = parsed_type
            .struct_name
            .as_ref()
            .filter(|_| parsed_type.interface_type.is_pointer())
            .cloned();
        let aggregate_struct = if is_plain_struct_type(&parsed_type) {
            if parsed_type.is_volatile {
                return Err(self.error_here(
                    "the small volatile model does not support volatile aggregate globals",
                ));
            }
            let struct_name = parsed_type
                .struct_name
                .clone()
                .expect("plain struct global carries a struct name");
            let layout = self.scalar_struct_value_layout(&struct_name)?;
            Some((struct_name, layout))
        } else {
            self.validate_volatile_type(&parsed_type)?;
            if (parsed_type.struct_name.is_some() && struct_pointer_name.is_none())
                || parsed_type.enum_name.is_some()
                || parsed_type.union_name.is_some()
                || (struct_pointer_name.is_none()
                    && !parsed_type.interface_type.is_supported_static_scalar())
            {
                return Err(self.error_here(
                    "file-scope declarations currently support only scalar integer, floating-point, struct-pointer, or supported struct globals",
                ));
            }
            None
        };
        if self.header_mode && !is_extern {
            return Err(self.error_here(
                "C headers may declare globals only with `extern`; put the definition in a source file",
            ));
        }

        loop {
            let declaration_site = self.here();
            let name = self.expect_ident("global name")?;
            let hosted_stdout = name == "stdout"
                && declaration_site
                    .and_then(|site| site.origin)
                    .is_some_and(|origin| origin.filename.as_ref() == "<stdio.h>")
                && is_extern
                && parsed_type.is_constant
                && parsed_type.interface_type == InterfaceType::Int32Pointer
                && struct_pointer_name.as_deref() == Some("__click_c_stdio_FILE");
            let kernel_name = if hosted_stdout {
                HOSTED_STDOUT_BINDING.into()
            } else if is_file_static {
                self.file_static_kernel_name(&name)
            } else {
                name.clone().into()
            };
            if let Some((struct_name, layout)) = &aggregate_struct {
                if self.peek() == Some(&Token::LBracket) {
                    let mut array_length = self
                        .parse_global_array_length(&name)?
                        .expect("aggregate array has an array suffix");
                    let mut inferred_initializer = None;
                    if matches!(&array_length, GlobalArrayLength::Incomplete(shape) if shape.is_empty())
                        && !is_extern
                        && self.peek() == Some(&Token::Equal)
                    {
                        self.position += 1;
                        let (length, initializer) = self
                            .parse_aggregate_array_initializer_with_bound(
                                &name,
                                struct_name,
                                layout,
                                None,
                            )?;
                        array_length = GlobalArrayLength::Complete(vec![length]);
                        inferred_initializer = Some(initializer);
                    }
                    let declaration = match array_length {
                        GlobalArrayLength::Complete(shape) => {
                            if shape.len() != 1 {
                                return Err(self.error_here(
                                    "multidimensional aggregate arrays are not supported yet",
                                ));
                            }
                            let length = shape[0];
                            let has_initializer = inferred_initializer.is_some()
                                || self.peek() == Some(&Token::Equal);
                            let initializer = if let Some(initializer) = inferred_initializer {
                                Some(initializer)
                            } else if has_initializer {
                                if is_extern {
                                    return Err(self.error_here(
                                        "`extern` aggregate global array declarations may not have an initializer",
                                    ));
                                }
                                self.position += 1;
                                Some(self.parse_aggregate_array_initializer(
                                    &name,
                                    struct_name,
                                    layout,
                                    length,
                                )?)
                            } else if is_extern {
                                None
                            } else {
                                Some(Vec::new())
                            };
                            let tentative = !has_initializer && !is_extern;
                            initializer
                                .map(|initializer| {
                                    CGlobalAggregateArray::definition(
                                        name.clone(),
                                        kernel_name.clone(),
                                        struct_name.clone(),
                                        layout.clone(),
                                        length,
                                        initializer,
                                        is_file_static,
                                    )
                                })
                                .unwrap_or_else(|| {
                                    CGlobalAggregateArray::declaration(
                                        name.clone(),
                                        kernel_name.clone(),
                                        struct_name.clone(),
                                        layout.clone(),
                                        Some(length),
                                        is_file_static,
                                    )
                                })
                                .with_constant(parsed_type.is_constant)
                                .with_tentative(tentative)
                        }
                        GlobalArrayLength::Incomplete(incomplete_shape) => {
                            if !incomplete_shape.is_empty() {
                                return Err(self.error_here(
                                    "incomplete multidimensional aggregate arrays are not supported yet",
                                ));
                            }
                            if !is_extern {
                                return Err(self.error_here(
                                    "incomplete aggregate array definitions are not supported yet",
                                ));
                            }
                            if self.peek() == Some(&Token::Equal) {
                                return Err(self.error_here(
                                    "incomplete external aggregate array declarations may not have an initializer",
                                ));
                            }
                            CGlobalAggregateArray::declaration(
                                name.clone(),
                                kernel_name.clone(),
                                struct_name.clone(),
                                layout.clone(),
                                None,
                                is_file_static,
                            )
                            .with_constant(parsed_type.is_constant)
                        }
                    };
                    self.register_global_aggregate_array_declaration(name.clone(), declaration)?;
                    if let Some(length) = self
                        .global_aggregate_arrays
                        .get(&name)
                        .and_then(CGlobalAggregateArray::array_length)
                    {
                        let bytes = length
                            .checked_mul(layout.size_bytes())
                            .expect("validated aggregate global array size");
                        self.variable_types
                            .insert(kernel_name.clone(), InterfaceType::UInt8Array(bytes));
                        self.variable_array_shapes
                            .insert(kernel_name.clone(), vec![length]);
                        self.incomplete_array_names.remove(&kernel_name.clone());
                    } else {
                        self.variable_types
                            .insert(kernel_name.clone(), InterfaceType::UInt8Pointer);
                        self.variable_array_shapes.remove(&kernel_name.clone());
                        self.incomplete_array_names.insert(kernel_name.clone());
                    }
                    self.variable_structs
                        .insert(kernel_name.clone(), struct_name.clone());
                    if parsed_type.is_constant {
                        self.variable_constants.insert(kernel_name.clone());
                    }
                    if self.peek() == Some(&Token::Comma) {
                        self.position += 1;
                        continue;
                    }
                    break;
                }
                let has_initializer = self.peek() == Some(&Token::Equal);
                let initializer = if has_initializer {
                    if is_extern {
                        return Err(self.error_here(
                            "`extern` aggregate global declarations may not have an initializer",
                        ));
                    }
                    self.position += 1;
                    Some(self.parse_aggregate_initializer(&name, struct_name)?)
                } else if is_extern {
                    None
                } else {
                    Some(Vec::new())
                };
                let tentative = !has_initializer && !is_extern;
                let declaration = if let Some(initializer) = initializer {
                    CGlobalAggregate::definition(
                        name.clone(),
                        kernel_name.clone(),
                        struct_name.clone(),
                        layout.clone(),
                        initializer,
                        is_file_static,
                    )
                } else {
                    CGlobalAggregate::declaration(
                        name.clone(),
                        kernel_name.clone(),
                        struct_name.clone(),
                        layout.clone(),
                        is_file_static,
                    )
                }
                .with_constant(parsed_type.is_constant);
                let declaration = declaration.with_tentative(tentative);
                self.register_global_aggregate_declaration(name.clone(), declaration)?;
                self.variable_struct_values
                    .insert(kernel_name.clone(), struct_name.clone());
                self.variable_types
                    .insert((name.clone()).into(), record_value_type(layout));
                self.variable_structs
                    .insert((name.clone()).into(), struct_name.clone());
                if parsed_type.is_constant {
                    self.variable_constants.insert((name.clone()).into());
                }
                if kernel_name.named() != Some(name.as_str()) {
                    self.variable_types
                        .insert(kernel_name.clone(), record_value_type(layout));
                    self.variable_structs
                        .insert(kernel_name, struct_name.clone());
                }
                if self.peek() == Some(&Token::Comma) {
                    self.position += 1;
                    continue;
                }
                break;
            }
            let parsed_array_length = self.parse_global_array_length(&name)?;
            let mut inferred_initializer = None;
            let mut incomplete_tentative = false;
            let array_length = match parsed_array_length {
                Some(GlobalArrayLength::Incomplete(incomplete_shape)) if !is_extern => {
                    if self.peek() != Some(&Token::Equal) {
                        if !incomplete_shape.is_empty() && is_file_static {
                            return Err(self.error_here(
                                "incomplete multidimensional file-scope static arrays are not supported yet",
                            ));
                        }
                        incomplete_tentative = true;
                        Some(GlobalArrayLength::Incomplete(incomplete_shape))
                    } else if incomplete_shape.is_empty() {
                        self.position += 1;
                        let initializer = self.parse_inferred_global_array_initializer(
                            &name,
                            parsed_type.interface_type,
                            parsed_type.pointee_constant,
                        )?;
                        let length = initializer.length();
                        if length == 0 {
                            return Err(self.error_here(format!(
                                "inferred file-scope array `{name}` requires a non-empty initializer"
                            )));
                        }
                        inferred_initializer = Some(initializer);
                        Some(GlobalArrayLength::Complete(vec![length]))
                    } else {
                        self.position += 1;
                        let (shape, initializer) = self
                            .parse_inferred_multidimensional_global_array_initializer(
                                &name,
                                parsed_type.interface_type,
                                &incomplete_shape,
                            )?;
                        inferred_initializer = Some(initializer);
                        Some(GlobalArrayLength::Complete(shape))
                    }
                }
                other => other,
            };
            if array_length.is_some()
                && array_type_for_element(parsed_type.interface_type, 1).is_none()
            {
                return Err(self.error_here(
                    "file-scope array element type requires a modeled array pointer type",
                ));
            }
            if parsed_type.is_volatile && array_length.is_some() {
                return Err(self.error_here(
                    "the small volatile model supports only direct scalar integer objects",
                ));
            }
            if let Some(array_length) = array_length {
                if let Some(struct_name) = &struct_pointer_name {
                    self.variable_structs
                        .insert(kernel_name.clone(), struct_name.clone());
                }
                match array_length {
                    GlobalArrayLength::Complete(shape) => {
                        // The block's byte size, not only its element count,
                        // must fit the layout width.
                        let length = array_shape_element_count(&shape)
                            .filter(|length| {
                                length
                                    .checked_mul(parsed_type.interface_type.abi_size_bytes())
                                    .is_some()
                            })
                            .ok_or_else(|| {
                                self.error_here(format!(
                                    "file-scope array dimensions are too large for `{name}`"
                                ))
                            })?;
                        let has_initializer =
                            inferred_initializer.is_some() || self.peek() == Some(&Token::Equal);
                        let initializer = if has_initializer {
                            if is_extern {
                                return Err(self.error_here(
                                "`extern` global array declarations may not have an initializer",
                            ));
                            }
                            if let Some(initializer) = inferred_initializer {
                                Some(initializer)
                            } else {
                                self.position += 1;
                                Some(self.parse_global_array_initializer(
                                    &name,
                                    parsed_type.interface_type,
                                    &shape,
                                )?)
                            }
                        } else if is_extern {
                            None
                        } else {
                            Some(CArrayInitializer::zeroed(
                                length,
                                parsed_type.interface_type,
                            ))
                        };
                        let tentative = !has_initializer && !is_extern;
                        self.register_global_array_declaration(
                            name.clone(),
                            parsed_type.interface_type,
                            initializer
                                .map(|initializer| {
                                    CGlobalArray::definition(
                                        name.clone(),
                                        kernel_name.clone(),
                                        parsed_type.interface_type,
                                        shape.clone(),
                                        initializer,
                                        is_file_static,
                                    )
                                    .with_constant(parsed_type.is_constant)
                                    .with_tentative(tentative)
                                })
                                .unwrap_or_else(|| {
                                    CGlobalArray::declaration(
                                        name.clone(),
                                        kernel_name.clone(),
                                        parsed_type.interface_type,
                                        Some(shape.clone()),
                                        None,
                                        is_file_static,
                                    )
                                    .with_constant(parsed_type.is_constant)
                                }),
                        )?;
                        self.variable_types.insert(
                            kernel_name.clone(),
                            array_type_for_element(parsed_type.interface_type, length)
                                .expect("validated global array element type"),
                        );
                        self.variable_array_shapes
                            .insert(kernel_name.clone(), shape);
                        self.incomplete_array_names.remove(&kernel_name.clone());
                    }
                    GlobalArrayLength::Incomplete(incomplete_shape) => {
                        if self.peek() == Some(&Token::Equal) {
                            return Err(self.error_here(
                                "incomplete external array declarations may not have an initializer",
                            ));
                        }
                        self.register_global_array_declaration(
                            name.clone(),
                            parsed_type.interface_type,
                            CGlobalArray::declaration(
                                name.clone(),
                                kernel_name.clone(),
                                parsed_type.interface_type,
                                None,
                                Some(incomplete_shape),
                                is_file_static,
                            )
                            .with_constant(parsed_type.is_constant)
                            .with_tentative(incomplete_tentative),
                        )?;
                        if let Some(shape) = self
                            .global_arrays
                            .get(&name)
                            .and_then(CGlobalArray::index_shape)
                        {
                            let length = array_shape_element_count(&shape)
                                .expect("validated global array shape");
                            self.variable_types.insert(
                                kernel_name.clone(),
                                array_type_for_element(parsed_type.interface_type, length)
                                    .expect("validated global array element type"),
                            );
                            self.variable_array_shapes
                                .insert(kernel_name.clone(), shape);
                            self.incomplete_array_names.remove(&kernel_name.clone());
                        } else {
                            let element_pointer = parsed_type
                                .interface_type
                                .pointer_type()
                                .expect("validated incomplete external array element type");
                            self.variable_types
                                .insert(kernel_name.clone(), element_pointer);
                            self.variable_array_shapes.remove(&kernel_name.clone());
                            self.incomplete_array_names.insert(kernel_name.clone());
                        }
                    }
                }
            } else {
                let has_initializer = self.peek() == Some(&Token::Equal);
                let initializer = if has_initializer {
                    if is_extern {
                        return Err(self.error_here(
                            "`extern` global declarations may not have an initializer",
                        ));
                    }
                    self.position += 1;
                    let initializer = self.parse_expression()?;
                    let initializer = normalize_static_initializer(
                        self,
                        parsed_type.interface_type,
                        parsed_type.pointee_constant,
                        &initializer,
                        "global",
                        false,
                    )?;
                    Some(initializer)
                } else if is_extern {
                    None
                } else {
                    Some(zero_initializer(parsed_type.interface_type))
                };
                let tentative = !has_initializer && !is_extern;
                self.register_global_declaration(
                    name.clone(),
                    parsed_type.interface_type,
                    initializer
                        .map(|initializer| {
                            if is_file_static {
                                CGlobal::file_static_definition(
                                    name.clone(),
                                    kernel_name.clone(),
                                    parsed_type.interface_type,
                                    struct_pointer_name.clone(),
                                    initializer,
                                )
                                .with_volatile(parsed_type.object_is_volatile())
                                .with_pointee_volatile(parsed_type.pointee_is_volatile())
                                .with_constant(parsed_type.is_constant)
                                .with_pointee_constant(parsed_type.pointee_constant)
                                .with_tentative(tentative)
                            } else {
                                CGlobal::definition(
                                    name.clone(),
                                    parsed_type.interface_type,
                                    struct_pointer_name.clone(),
                                    initializer,
                                )
                                .with_volatile(parsed_type.object_is_volatile())
                                .with_pointee_volatile(parsed_type.pointee_is_volatile())
                                .with_constant(parsed_type.is_constant)
                                .with_pointee_constant(parsed_type.pointee_constant)
                                .with_tentative(tentative)
                            }
                        })
                        .unwrap_or_else(|| {
                            let mut global = CGlobal::declaration(
                                name.clone(),
                                parsed_type.interface_type,
                                struct_pointer_name.clone(),
                            )
                            .with_volatile(parsed_type.object_is_volatile())
                            .with_pointee_volatile(parsed_type.pointee_is_volatile())
                            .with_constant(parsed_type.is_constant)
                            .with_pointee_constant(parsed_type.pointee_constant);
                            if hosted_stdout {
                                global.hosted_stdout = true;
                                global.kernel_name = kernel_name.clone();
                            }
                            global
                        }),
                )?;
                self.variable_types
                    .insert(kernel_name.clone(), parsed_type.interface_type);
                if let Some(struct_name) = &struct_pointer_name {
                    self.variable_structs
                        .insert(kernel_name, struct_name.clone());
                }
            }
            if self.peek() != Some(&Token::Comma) {
                break;
            }
            self.position += 1;
            if is_extern && self.peek() == Some(&Token::Equal) {
                return Err(
                    self.error_here("`extern` global declarations may not have an initializer")
                );
            }
        }
        self.expect(Token::Semicolon)
    }

    pub(super) fn parse_inferred_global_array_initializer(
        &mut self,
        name: &str,
        element_type: InterfaceType,
        pointee_constant: bool,
    ) -> Result<CArrayInitializer, CSyntaxError> {
        self.expect(Token::LBrace)?;
        // A designator positions the next value; the array's length is one
        // past its largest initialized index (C11 6.7.9p22), and an element
        // no initializer names is zero.
        let mut values = BTreeMap::new();
        let mut next_index = 0u32;
        if self.peek() != Some(&Token::RBrace) {
            loop {
                if self.peek() == Some(&Token::LBracket) {
                    self.position += 1;
                    next_index =
                        self.parse_constant_designator_index("inferred file-scope scalar array")?;
                    self.expect(Token::RBracket)?;
                    self.expect(Token::Equal)?;
                }
                if values.contains_key(&next_index) {
                    return Err(self.error_here(format!(
                        "duplicate designator for inferred file-scope scalar array `{name}[{next_index}]`"
                    )));
                }
                let value = self.parse_expression()?;
                values.insert(
                    next_index,
                    normalize_static_initializer(
                        self,
                        element_type,
                        pointee_constant,
                        &value,
                        "global",
                        false,
                    )?,
                );
                next_index = next_index.checked_add(1).ok_or_else(|| {
                    self.error_here(format!(
                        "inferred file-scope scalar array `{name}` has too many initializers"
                    ))
                })?;
                match self.peek() {
                    Some(Token::Comma) => {
                        self.position += 1;
                        if self.peek() == Some(&Token::RBrace) {
                            break;
                        }
                    }
                    Some(Token::RBrace) => break,
                    Some(token) => {
                        return Err(self.error_here(format!(
                            "expected `,` or `}}` in inferred file-scope scalar array `{name}` initializer, got {}",
                            token.describe()
                        )));
                    }
                    None => {
                        return Err(self.error_here(format!(
                            "expected `,` or `}}` in inferred file-scope scalar array `{name}` initializer, got end of input"
                        )));
                    }
                }
            }
        }
        self.expect(Token::RBrace)?;
        let length = values
            .last_key_value()
            .map_or(0, |(index, _)| index.saturating_add(1));
        Ok(CArrayInitializer::new(length, element_type, values))
    }

    pub(super) fn parse_inferred_multidimensional_global_array_initializer(
        &mut self,
        name: &str,
        element_type: InterfaceType,
        inner_shape: &[u32],
    ) -> Result<(Vec<u32>, CArrayInitializer), CSyntaxError> {
        self.expect(Token::LBrace)?;
        let mut values = Vec::new();
        let mut next = 0u32;
        let mut outer_length = 0u32;
        if self.peek() == Some(&Token::RBrace) {
            self.position += 1;
            return Err(self.error_here(format!(
                "inferred file-scope multidimensional array `{name}` requires a non-empty initializer"
            )));
        }
        loop {
            if self.peek() != Some(&Token::LBrace) {
                return Err(self.error_here(format!(
                    "nested initializer for inferred file-scope multidimensional array `{name}` expects `{}` groups",
                    inner_shape.len()
                )));
            }
            self.parse_sparse_array_initializer_level(
                name,
                inner_shape,
                0,
                &mut values,
                &mut next,
            )?;
            outer_length = outer_length.checked_add(1).ok_or_else(|| {
                self.error_here(format!(
                    "inferred file-scope multidimensional array `{name}` has too many initializer rows"
                ))
            })?;
            match self.peek() {
                Some(Token::Comma) => {
                    self.position += 1;
                    if self.peek() == Some(&Token::RBrace) {
                        break;
                    }
                }
                Some(Token::RBrace) => break,
                Some(token) => {
                    return Err(self.error_here(format!(
                        "expected `,` or `}}` in inferred file-scope multidimensional array `{name}` initializer, got {}",
                        token.describe()
                    )));
                }
                None => {
                    return Err(self.error_here(format!(
                        "expected `,` or `}}` in inferred file-scope multidimensional array `{name}` initializer, got end of input"
                    )));
                }
            }
        }
        self.expect(Token::RBrace)?;
        let mut shape = Vec::with_capacity(inner_shape.len() + 1);
        shape.push(outer_length);
        shape.extend_from_slice(inner_shape);
        let length = array_shape_element_count(&shape).ok_or_else(|| {
            self.error_here(format!(
                "inferred file-scope multidimensional array `{name}` dimensions are too large"
            ))
        })?;
        let initializer =
            self.normalized_array_initializer(element_type, length, values, "global", false)?;
        Ok((shape, initializer))
    }

    pub(super) fn parse_global_array_length(
        &mut self,
        name: &str,
    ) -> Result<Option<GlobalArrayLength>, CSyntaxError> {
        if self.peek() != Some(&Token::LBracket) {
            return Ok(None);
        }
        self.position += 1;
        if self.peek() == Some(&Token::RBracket) {
            self.position += 1;
            let mut incomplete_shape = Vec::new();
            while self.peek() == Some(&Token::LBracket) {
                self.position += 1;
                let length = match self.peek().cloned() {
                    Some(Token::Number(number)) => {
                        self.position += 1;
                        let length =
                            parse_integer_literal_magnitude(&number).map_err(|reason| {
                                self.error_at_previous(format!(
                                    "invalid file-scope array length `{number}`: {reason}"
                                ))
                            })?;
                        u32::try_from(length).map_err(|_| {
                            self.error_at_previous(format!(
                                "file-scope array length `{number}` is out of range"
                            ))
                        })?
                    }
                    Some(token) => {
                        return Err(self.error_at_previous(format!(
                            "expected positive file-scope array length, got {}",
                            token.describe()
                        )));
                    }
                    None => {
                        return Err(self.error_here(
                            "expected positive file-scope array length, got end of input",
                        ));
                    }
                };
                if length == 0 {
                    return Err(self.error_at_previous(format!(
                        "file-scope array `{name}` must have positive length"
                    )));
                }
                incomplete_shape.push(length);
                self.expect(Token::RBracket)?;
            }
            return Ok(Some(GlobalArrayLength::Incomplete(incomplete_shape)));
        }
        let mut dimensions = Vec::new();
        loop {
            let length = match self.peek().cloned() {
                Some(Token::Number(number)) => {
                    self.position += 1;
                    let length = parse_integer_literal_magnitude(&number).map_err(|reason| {
                        self.error_at_previous(format!(
                            "invalid file-scope array length `{number}`: {reason}"
                        ))
                    })?;
                    u32::try_from(length).map_err(|_| {
                        self.error_at_previous(format!(
                            "file-scope array length `{number}` is out of range"
                        ))
                    })?
                }
                Some(token) => {
                    return Err(self.error_at_previous(format!(
                        "expected positive file-scope array length, got {}",
                        token.describe()
                    )));
                }
                None => {
                    return Err(self.error_here(
                        "expected positive file-scope array length, got end of input",
                    ));
                }
            };
            if length == 0 {
                return Err(self.error_at_previous(format!(
                    "file-scope array `{name}` must have positive length"
                )));
            }
            dimensions.push(length);
            self.expect(Token::RBracket)?;
            if self.peek() != Some(&Token::LBracket) {
                break;
            }
            self.position += 1;
        }
        Ok(Some(GlobalArrayLength::Complete(dimensions)))
    }

    pub(super) fn parse_global_array_initializer(
        &mut self,
        name: &str,
        element_type: InterfaceType,
        shape: &[u32],
    ) -> Result<CArrayInitializer, CSyntaxError> {
        let length = array_shape_element_count(shape).expect("validated global array shape");
        if shape.len() == 1 {
            self.parse_scalar_array_initializer(name, element_type, false, length, false)
        } else {
            let mut values = Vec::new();
            let mut next = 0u32;
            self.parse_sparse_array_initializer_level(name, shape, 0, &mut values, &mut next)?;
            self.normalized_array_initializer(element_type, length, values, "global", false)
        }
    }

    /// The initializer of `length` elements of `element_type` whose written
    /// elements are `values`, ascending by index, each normalized as a
    /// static initializer of `storage`.
    pub(super) fn normalized_array_initializer(
        &self,
        element_type: InterfaceType,
        length: u32,
        values: Vec<(u32, CExpression)>,
        storage: &str,
        static_local: bool,
    ) -> Result<CArrayInitializer, CSyntaxError> {
        let values = values
            .into_iter()
            .map(|(index, value)| {
                normalize_static_initializer(
                    self,
                    element_type,
                    false,
                    &value,
                    storage,
                    static_local,
                )
                .map(|value| (index, value))
            })
            .collect::<Result<Vec<_>, _>>()?;
        Ok(CArrayInitializer::new(length, element_type, values))
    }

    pub(super) fn parse_scalar_array_initializer(
        &mut self,
        name: &str,
        element_type: InterfaceType,
        pointee_constant: bool,
        length: u32,
        static_local: bool,
    ) -> Result<CArrayInitializer, CSyntaxError> {
        let context = if static_local {
            "static local scalar array"
        } else {
            "file-scope scalar array"
        };
        self.expect(Token::LBrace)?;
        let mut values = BTreeMap::new();
        let mut next_element_index = 0u32;
        if self.peek() != Some(&Token::RBrace) {
            loop {
                let element_index = if self.peek() == Some(&Token::LBracket) {
                    self.position += 1;
                    let index = self.parse_scalar_array_designator(name, length, context)?;
                    self.expect(Token::Equal)?;
                    next_element_index = index
                        .checked_add(1)
                        .expect("validated scalar array designator index");
                    index
                } else {
                    if next_element_index >= length {
                        return Err(self.error_here(format!(
                            "too many initializers for {context} `{name}[{length}]`"
                        )));
                    }
                    let index = next_element_index;
                    next_element_index = next_element_index
                        .checked_add(1)
                        .expect("validated scalar array initializer index");
                    index
                };
                if values.contains_key(&element_index) {
                    return Err(self.error_here(format!(
                        "duplicate designator for {context} `{name}[{element_index}]`"
                    )));
                }
                let value = self.parse_expression()?;
                let value = if static_local {
                    normalize_static_initializer(
                        self,
                        element_type,
                        pointee_constant,
                        &value,
                        "static local",
                        true,
                    )?
                } else {
                    normalize_static_initializer(
                        self,
                        element_type,
                        pointee_constant,
                        &value,
                        "global",
                        false,
                    )?
                };
                values.insert(element_index, value);
                match self.peek() {
                    Some(Token::Comma) => {
                        self.position += 1;
                        if self.peek() == Some(&Token::RBrace) {
                            break;
                        }
                    }
                    Some(Token::RBrace) => break,
                    Some(token) => {
                        return Err(self.error_here(format!(
                            "expected `,` or `}}` in {context} `{name}` initializer, got {}",
                            token.describe()
                        )));
                    }
                    None => {
                        return Err(self.error_here(format!(
                            "expected `,` or `}}` in {context} `{name}` initializer, got end of input"
                        )));
                    }
                }
            }
        }
        self.expect(Token::RBrace)?;
        Ok(CArrayInitializer::new(length, element_type, values))
    }

    pub(super) fn parse_scalar_array_designator(
        &mut self,
        name: &str,
        length: u32,
        context: &str,
    ) -> Result<u32, CSyntaxError> {
        let index = self.parse_constant_designator_index(context)?;
        self.expect(Token::RBracket)?;
        if index >= length {
            return Err(self.error_here(format!(
                "{context} designator index `{index}` is out of bounds for `{name}[{length}]`"
            )));
        }
        Ok(index)
    }

    /// An array designator's index: an integer constant expression, such as
    /// a literal, a character constant or an enumeration constant
    /// (C11 6.7.9p6), that is nonnegative.
    pub(super) fn parse_constant_designator_index(
        &mut self,
        context: &str,
    ) -> Result<u32, CSyntaxError> {
        let expression = self.parse_conditional()?;
        let index = match evaluate_static_integer_expression(&expression) {
            Ok(StaticIntegerValue::Signed { value, .. }) => u32::try_from(value).ok(),
            Ok(StaticIntegerValue::Unsigned { value, .. }) => u32::try_from(value).ok(),
            Err(_) => {
                return Err(self.error_at_previous(format!(
                    "{context} designators require an integer constant expression"
                )));
            }
        };
        index.ok_or_else(|| {
            self.error_at_previous(format!(
                "{context} designator index is negative or out of range"
            ))
        })
    }

    pub(super) fn register_global_declaration(
        &mut self,
        name: String,
        interface_type: InterfaceType,
        declaration: CGlobal,
    ) -> Result<(), CSyntaxError> {
        if self.function_declarations.contains_key(&name)
            || self.global_arrays.contains_key(&name)
            || self.global_aggregates.contains_key(&name)
            || self.global_aggregate_arrays.contains_key(&name)
        {
            return Err(self.error_here(format!(
                "global `{name}` conflicts with a function or array declaration"
            )));
        }
        if let Some(previous) = self.globals.get(&name) {
            if previous.interface_type != interface_type
                || previous.struct_name != declaration.struct_name
            {
                return Err(
                    self.error_here(format!("conflicting declarations for global `{name}`"))
                );
            }
            if previous.is_volatile() != declaration.is_volatile() {
                return Err(self.error_here(format!(
                    "conflicting volatile qualifiers for global `{name}`"
                )));
            }
            if previous.is_constant() != declaration.is_constant() {
                return Err(
                    self.error_here(format!("conflicting const qualifiers for global `{name}`"))
                );
            }
            if previous.pointee_is_constant() != declaration.pointee_is_constant() {
                return Err(self.error_here(format!(
                    "conflicting pointee const qualifiers for global `{name}`"
                )));
            }
            if previous.is_file_static() != declaration.is_file_static() {
                return Err(self.error_here(format!(
                    "conflicting linkage declarations for global `{name}`"
                )));
            }
            if previous.is_initialized_definition() && declaration.is_initialized_definition() {
                return Err(self.error_here(format!("duplicate definition of global `{name}`")));
            }
        }
        let merged = match self.globals.get(&name) {
            Some(previous) if previous.is_initialized_definition() => previous.clone(),
            Some(_) if declaration.is_initialized_definition() => declaration,
            Some(previous) if previous.is_tentative() => previous.clone(),
            Some(previous) if previous.hosted_stdout => previous.clone(),
            _ => declaration,
        };
        self.globals.insert(name, merged);
        Ok(())
    }

    pub(super) fn register_global_array_declaration(
        &mut self,
        name: String,
        element_type: InterfaceType,
        declaration: CGlobalArray,
    ) -> Result<(), CSyntaxError> {
        if self.function_declarations.contains_key(&name)
            || self.globals.contains_key(&name)
            || self.global_aggregates.contains_key(&name)
            || self.global_aggregate_arrays.contains_key(&name)
        {
            return Err(self.error_here(format!(
                "global `{name}` conflicts with a function or scalar global declaration"
            )));
        }
        if let Some(previous) = self.global_arrays.get(&name) {
            if previous.element_type != element_type
                || !array_shapes_compatible(previous, &declaration)
            {
                return Err(self.error_here(format!(
                    "conflicting declarations for global array `{name}`"
                )));
            }
            if previous.is_constant() != declaration.is_constant() {
                return Err(self.error_here(format!(
                    "conflicting const qualifiers for global array `{name}`"
                )));
            }
            if previous.is_file_static() != declaration.is_file_static() {
                return Err(self.error_here(format!(
                    "conflicting linkage declarations for global array `{name}`"
                )));
            }
            if previous.is_initialized_definition() && declaration.is_initialized_definition() {
                return Err(
                    self.error_here(format!("duplicate definition of global array `{name}`"))
                );
            }
        }
        let merged = merge_global_array_declarations(self.global_arrays.get(&name), declaration);
        self.global_arrays.insert(name, merged);
        Ok(())
    }

    pub(super) fn register_global_aggregate_declaration(
        &mut self,
        name: String,
        declaration: CGlobalAggregate,
    ) -> Result<(), CSyntaxError> {
        if self.function_declarations.contains_key(&name)
            || self.globals.contains_key(&name)
            || self.global_arrays.contains_key(&name)
            || self.global_aggregate_arrays.contains_key(&name)
        {
            return Err(self.error_here(format!(
                "global `{name}` conflicts with a function or scalar declaration"
            )));
        }
        if let Some(previous) = self.global_aggregates.get(&name) {
            if previous.struct_name() != declaration.struct_name()
                || previous.layout() != declaration.layout()
            {
                return Err(self.error_here(format!(
                    "conflicting declarations for aggregate global `{name}`"
                )));
            }
            if previous.is_constant() != declaration.is_constant() {
                return Err(self.error_here(format!(
                    "conflicting const qualifiers for aggregate global `{name}`"
                )));
            }
            if previous.is_file_static() != declaration.is_file_static() {
                return Err(self.error_here(format!(
                    "conflicting linkage declarations for aggregate global `{name}`"
                )));
            }
            if previous.is_initialized_definition() && declaration.is_initialized_definition() {
                return Err(
                    self.error_here(format!("duplicate definition of aggregate global `{name}`"))
                );
            }
        }
        let merged = match self.global_aggregates.get(&name) {
            Some(previous) if previous.is_initialized_definition() => previous.clone(),
            Some(_) if declaration.is_initialized_definition() => declaration,
            Some(previous) if previous.is_tentative() => previous.clone(),
            _ => declaration,
        };
        self.global_aggregates.insert(name, merged);
        Ok(())
    }

    pub(super) fn register_global_aggregate_array_declaration(
        &mut self,
        name: String,
        declaration: CGlobalAggregateArray,
    ) -> Result<(), CSyntaxError> {
        if self.function_declarations.contains_key(&name)
            || self.globals.contains_key(&name)
            || self.global_arrays.contains_key(&name)
            || self.global_aggregates.contains_key(&name)
        {
            return Err(self.error_here(format!(
                "global `{name}` conflicts with a function or non-array declaration"
            )));
        }
        if let Some(previous) = self.global_aggregate_arrays.get(&name) {
            if previous.struct_name() != declaration.struct_name()
                || previous.layout() != declaration.layout()
                || !array_lengths_compatible(previous.array_length(), declaration.array_length())
            {
                return Err(self.error_here(format!(
                    "conflicting declarations for aggregate global array `{name}`"
                )));
            }
            if previous.is_constant() != declaration.is_constant() {
                return Err(self.error_here(format!(
                    "conflicting const qualifiers for aggregate global array `{name}`"
                )));
            }
            if previous.is_file_static() != declaration.is_file_static() {
                return Err(self.error_here(format!(
                    "conflicting linkage declarations for aggregate global array `{name}`"
                )));
            }
            if previous.is_initialized_definition() && declaration.is_initialized_definition() {
                return Err(self.error_here(format!(
                    "duplicate definition of aggregate global array `{name}`"
                )));
            }
        }
        let merged = match self.global_aggregate_arrays.get(&name) {
            Some(previous) if previous.is_initialized_definition() => previous.clone(),
            Some(_) if declaration.is_initialized_definition() => declaration,
            Some(previous) if previous.is_tentative() => previous.clone(),
            _ => declaration,
        };
        self.global_aggregate_arrays.insert(name, merged);
        Ok(())
    }
}
