//! The Rust spelling of a sidecar: `fn` signatures, `impl` blocks, slices,
//! references, lifetimes and `as` casts, admitted when a `verifying` source
//! is Rust.

use super::*;

impl Parser {
    /// A Rust sidecar states its signature as Rust does:
    /// `fn name(a: T, b: U) -> R`, with references, slices, and methods in
    /// `impl` blocks. C-shaped function contracts are refused for Rust sources.
    #[inline(never)]
    pub(super) fn parse_rust_function_signature(
        &mut self,
    ) -> Result<ParsedFunctionSignature, ClickError> {
        if !self.verifies_rust() {
            return Err(self.error(
                "a `fn` signature is the Rust spelling; a C or C++ source's contract is written `type name(type parameter, ...)`",
            ));
        }
        if self.pending_contract_name.is_some() {
            return Err(self.error(
                "a named contract does not take a `fn` signature yet; write `contract type Name(type parameter, ...)`",
            ));
        }
        self.expect_ident_spelling("fn")?;
        let path = self.expect_rust_path("function name")?;
        self.skip_rust_lifetime_parameters()?;
        let name = if self.rust_impl_type.is_some() {
            // A method's own name; an item inside it, `compute::LIMIT`,
            // follows as the importer writes path segments.
            crate::languages::rust::names::method_path_name(
                &path.iter().map(String::as_str).collect::<Vec<_>>(),
            )
        } else {
            crate::languages::rust::names::path_name(
                &path.iter().map(String::as_str).collect::<Vec<_>>(),
            )
        };
        self.expect(Token::LParen)?;
        let mut parameters = Vec::new();
        let mut struct_params = BTreeMap::new();
        // A method is the function `Type_name`, and its receiver is the
        // first parameter, a pointer to the type named `self`.
        let name = match self.rust_impl_type.clone() {
            Some(impl_type) => {
                if let Some(receiver) = self.parse_rust_receiver(&impl_type)? {
                    let parsed = self.parse_parameter_array_suffix("self".into(), receiver)?;
                    if let Some(struct_name) = parsed.struct_name {
                        struct_params.insert(parsed.parameter.name.clone(), struct_name);
                    }
                    parameters.push(parsed.parameter);
                    if self.peek() == Some(&Token::Comma) {
                        self.position += 1;
                    }
                }
                match &self.rust_impl_method_suffix {
                    Some(suffix) => format!("{impl_type}_{name}_{suffix}"),
                    None => self.rust_inherent_method(&impl_type, &name)?,
                }
            }
            None => name,
        };
        let mut rust_slice_parameters = Vec::new();
        while self.peek() != Some(&Token::RParen) {
            let parameter_name = self.expect_ident("parameter name")?;
            self.expect(Token::Colon)?;
            if let Some(element) = self.parse_rust_slice_type()? {
                // `bytes: &[T]` is the pointer and length Rust passes. The
                // sidecar names the slice once and reads `bytes.len()`.
                let length = format!("{parameter_name}_len");
                self.rust_slice_params.insert(parameter_name.clone());
                rust_slice_parameters.push(parameter_name.clone());
                parameters.push(
                    self.parse_parameter_array_suffix(parameter_name, element)?
                        .parameter,
                );
                let length_type = ParsedType {
                    c_type: C0Type::UInt64,
                    struct_name: None,
                    struct_pointer: false,
                    constant: false,
                    pointee_constant: false,
                    reference: false,
                };
                parameters.push(
                    self.parse_parameter_array_suffix(length, length_type)?
                        .parameter,
                );
                if self.peek() != Some(&Token::Comma) {
                    break;
                }
                self.position += 1;
                continue;
            }
            let parsed_type = self.parse_rust_type()?;
            let parsed = self.parse_parameter_array_suffix(parameter_name, parsed_type)?;
            if let Some(struct_name) = parsed.struct_name {
                struct_params.insert(parsed.parameter.name.clone(), struct_name);
            }
            parameters.push(parsed.parameter);
            if self.peek() != Some(&Token::Comma) {
                break;
            }
            self.position += 1;
        }
        self.expect(Token::RParen)?;
        let parsed_return_type = if self.peek() == Some(&Token::Arrow) {
            self.position += 1;
            self.parse_rust_type()?
        } else {
            ParsedType {
                c_type: C0Type::Void,
                struct_name: None,
                struct_pointer: false,
                constant: false,
                pointee_constant: false,
                reference: false,
            }
        };
        let return_type = match parsed_return_type.struct_name.as_deref() {
            Some(struct_name) => self.scalar_struct_value_type(struct_name)?,
            None => parsed_return_type.c_type,
        };
        let diverges = if self.peek_ident() == Some("diverges") {
            self.position += 1;
            true
        } else {
            false
        };
        Ok(ParsedFunctionSignature {
            signature: FunctionSignature {
                return_type,
                return_pointee_constant: false,
                return_reference: false,
                name,
                parameters,
                exceptional_type: None,
                diverges,
                declared_loadable_bytes: Vec::new(),
                rust_spelling: super::RustSignatureSpelling::rust(rust_slice_parameters),
            },
            struct_params,
            struct_array_params: BTreeSet::new(),
            reference_params: BTreeSet::new(),
            return_struct_name: parsed_return_type.struct_name,
        })
    }

    /// `impl Type { ... }` or `impl Trait for Type { ... }`: each `fn` inside
    /// is the method's contract and proof. A trait method is named by its
    /// type, as the imported function is.
    #[inline(never)]
    pub(super) fn parse_rust_impl_block(
        &mut self,
        function_blocks: &mut Vec<FunctionBlock>,
    ) -> Result<(), ClickError> {
        self.expect_ident_spelling("impl")?;
        let mut impl_path = self.expect_rust_path("type name")?;
        let suffix = self.parse_rust_trait_argument()?;
        let mut inherent = true;
        if self.peek_ident() == Some("for") {
            self.position += 1;
            impl_path = self.expect_rust_path("type name")?;
            inherent = false;
        } else if suffix.is_some() {
            return Err(self.error("a trait with a type argument is implemented `for` a type"));
        }
        self.expect(Token::LBrace)?;
        let segments: Vec<&str> = impl_path.iter().map(String::as_str).collect();
        let impl_type = crate::languages::rust::names::path_name(&segments);
        // An inherent block is taken to be in its type's module.
        let impl_module = (inherent && segments.len() > 1).then(|| {
            segments[..segments.len() - 1]
                .iter()
                .fold("__rust_q".to_string(), |encoded, segment| {
                    format!("{encoded}_I{}_{segment}", segment.len())
                })
        });
        let suffix = suffix.map(|(reference, mutable, name)| {
            let name = if name == "Self" {
                impl_type.clone()
            } else {
                name
            };
            let scalar = matches!(
                name.as_str(),
                "i32" | "u8" | "u16" | "u32" | "usize" | "bool"
            );
            match (reference, scalar) {
                (false, true) => name,
                (false, false) => format!("value_{}{name}", name.len()),
                (true, _) => format!("ref_{}{name}", if mutable { "mut_" } else { "" }),
            }
        });
        let previous = self.rust_impl_type.replace(impl_type);
        let previous_suffix = std::mem::replace(&mut self.rust_impl_method_suffix, suffix);
        let previous_module = std::mem::replace(&mut self.rust_impl_module, impl_module);
        let mut result = Ok(());
        while self.peek() != Some(&Token::RBrace) {
            if self.peek_ident() != Some("fn") {
                result = Err(self.error("an `impl` block holds `fn` contracts"));
                break;
            }
            match self.parse_function_block(false) {
                Ok(block) => function_blocks.push(block),
                Err(error) => {
                    result = Err(error);
                    break;
                }
            }
        }
        self.rust_impl_type = previous;
        self.rust_impl_method_suffix = previous_suffix;
        self.rust_impl_module = previous_module;
        result?;
        self.expect(Token::RBrace)?;
        Ok(())
    }

    /// The imported function an inherent method of a type named by a path
    /// is. The importer names it by the module its `impl` block is in,
    /// which Rust does not write, so the one imported function that is this
    /// method of this type is found by the rest of its name. Rust allows a
    /// type one inherent method of a name, so there is at most one. With
    /// no import to consult, or none found, the block is taken to be in its
    /// type's module.
    #[inline(never)]
    pub(super) fn rust_inherent_method(
        &self,
        impl_type: &str,
        method: &str,
    ) -> Result<String, ClickError> {
        let Some(module) = self.rust_impl_module.as_deref() else {
            return Ok(crate::languages::rust::names::inherent_method_name(
                None, impl_type, method,
            ));
        };
        let suffix =
            crate::languages::rust::names::inherent_method_name(Some(""), impl_type, method);
        let mut found = self
            .local_struct_pointers_by_function
            .keys()
            .filter(|name| name.starts_with("__rust_q") && name.ends_with(&suffix));
        match (found.next(), found.next()) {
            (Some(name), None) => Ok(name.clone()),
            (Some(_), Some(_)) => Err(self.error(format!(
                "the import has more than one method `{method}` of this type"
            ))),
            (None, _) => Ok(crate::languages::rust::names::inherent_method_name(
                Some(module),
                impl_type,
                method,
            )),
        }
    }

    /// A Rust path, `name` or `crate_name::module::name`, as its segments.
    #[inline(never)]
    pub(super) fn expect_rust_path(&mut self, what: &str) -> Result<Vec<String>, ClickError> {
        let mut segments = vec![self.expect_ident(what)?];
        while self.peek() == Some(&Token::ColonColon) {
            self.position += 1;
            segments.push(self.expect_ident(what)?);
        }
        Ok(segments)
    }

    /// A Rust path as the name the importer gives the item it names.
    #[inline(never)]
    pub(super) fn expect_rust_path_name(&mut self, what: &str) -> Result<String, ClickError> {
        let path = self.expect_rust_path(what)?;
        Ok(crate::languages::rust::names::path_name(
            &path.iter().map(String::as_str).collect::<Vec<_>>(),
        ))
    }

    /// A lifetime, `'a` in `&'a T`, which a contract does not use.
    pub(super) fn skip_rust_lifetime(&mut self) {
        if matches!(self.peek(), Some(Token::Lifetime(_))) {
            self.position += 1;
        }
    }

    /// The generic parameters after a function's name, `<'a, 'b: 'a>`, when
    /// they are all lifetimes. The importer refuses a generic function, so a
    /// type parameter is refused here too.
    pub(super) fn skip_rust_lifetime_parameters(&mut self) -> Result<(), ClickError> {
        if self.peek() != Some(&Token::LessThan) {
            return Ok(());
        }
        self.position += 1;
        loop {
            let Some(Token::Lifetime(_)) = self.peek() else {
                return Err(self.error(
                    "a `fn` signature's generic parameters may only be lifetimes, such as `<'a>`; a generic function is not supported",
                ));
            };
            self.position += 1;
            if self.peek() == Some(&Token::Colon) {
                self.position += 1;
                while matches!(self.peek(), Some(Token::Lifetime(_))) {
                    self.position += 1;
                    if self.peek() != Some(&Token::Plus) {
                        break;
                    }
                    self.position += 1;
                }
            }
            if self.peek() == Some(&Token::Comma) {
                self.position += 1;
            }
            if self.peek() == Some(&Token::GreaterThan) {
                self.position += 1;
                return Ok(());
            }
        }
    }

    /// The type argument of an operator trait, `<u32>`, `<&Lanes>` or
    /// `<Self>`: whether it is a reference, whether that is mutable, and
    /// the type's name. The caller turns it into the suffix the Rust
    /// importer gives the implementation's methods (`rhs_name` in
    /// `src/languages/rust/charon/assignment_operators.rs`): a scalar by its
    /// name, a record by value as `value_<length><name>`, and a reference as
    /// `ref_` or `ref_mut_` and what it refers to. `None`, with nothing
    /// consumed, for a trait without one.
    #[inline(never)]
    pub(super) fn parse_rust_trait_argument(
        &mut self,
    ) -> Result<Option<(bool, bool, String)>, ClickError> {
        if self.peek() != Some(&Token::LessThan) {
            return Ok(None);
        }
        self.position += 1;
        let reference = self.peek() == Some(&Token::Amp);
        if reference {
            self.position += 1;
            self.skip_rust_lifetime();
        }
        let mutable = reference && self.peek_ident() == Some("mut");
        if mutable {
            self.position += 1;
        }
        let name = self.expect_rust_path_name("type name")?;
        self.expect(Token::GreaterThan)?;
        Ok(Some((reference, mutable, name)))
    }

    /// A method's receiver: `&self`, `&mut self` or `self`, as the type of
    /// the parameter it is. `None`, with nothing consumed, for an associated
    /// function that takes no receiver.
    pub(super) fn parse_rust_receiver(
        &mut self,
        impl_type: &str,
    ) -> Result<Option<ParsedType>, ClickError> {
        let start = self.position;
        let reference = self.peek() == Some(&Token::Amp);
        if reference {
            self.position += 1;
            self.skip_rust_lifetime();
        }
        let mutable = reference && self.peek_ident() == Some("mut");
        if mutable {
            self.position += 1;
        }
        if self.peek_ident() != Some("self") {
            self.position = start;
            return Ok(None);
        }
        self.position += 1;
        Ok(Some(ParsedType {
            c_type: C0Type::Int32Pointer,
            struct_name: Some(impl_type.to_string()),
            struct_pointer: reference,
            constant: false,
            pointee_constant: reference && !mutable,
            reference: false,
        }))
    }

    /// `&[T]` or `&mut [T]` with a scalar element, as the pointer to its
    /// first element; `None`, with nothing consumed, for any other type.
    #[inline(never)]
    pub(super) fn parse_rust_slice_type(&mut self) -> Result<Option<ParsedType>, ClickError> {
        if self.peek() != Some(&Token::Amp) {
            return Ok(None);
        }
        let lifetime = usize::from(matches!(self.peek_next(), Some(Token::Lifetime(_))));
        let mutable =
            self.tokens.get(self.position + 1 + lifetime) == Some(&Token::Ident("mut".into()));
        let bracket = self.position + 1 + lifetime + usize::from(mutable);
        if self.tokens.get(bracket) != Some(&Token::LBracket) {
            return Ok(None);
        }
        // `&[T; N]` is a reference to an array, not a slice.
        if self.tokens.get(bracket + 2) == Some(&Token::Semicolon) {
            return Ok(None);
        }
        self.position = bracket + 1;
        let spelling = self.expect_ident("slice element type")?;
        let Some(c_type) = rust_scalar_type(&spelling).and_then(C0Type::pointer_type) else {
            return Err(self.error(format!(
                "a slice of `{spelling}` in a `fn` signature is not supported; the Rust importer reads slices of scalars only"
            )));
        };
        self.expect(Token::RBracket)?;
        Ok(Some(ParsedType {
            c_type,
            struct_name: None,
            struct_pointer: false,
            constant: false,
            pointee_constant: !mutable,
            reference: false,
        }))
    }

    /// `name.len()` where `name` is a slice parameter: consumes `.len()` and
    /// answers the length's own name.
    pub(super) fn take_rust_slice_len(&mut self, name: &str) -> Option<String> {
        if !self.rust_slice_params.contains(name)
            || self.peek() != Some(&Token::Dot)
            || self.peek_next() != Some(&Token::Ident("len".into()))
            || self.tokens.get(self.position + 2) != Some(&Token::LParen)
            || self.tokens.get(self.position + 3) != Some(&Token::RParen)
        {
            return None;
        }
        self.position += 4;
        Some(format!("{name}_len"))
    }

    /// `&T` and `&mut T` in a signature. The parameter is the pointer that
    /// carries the reference, as Rust's own `value` is: the contract names
    /// the referent `*value` and a field `parent.left`. `&T` is a pointer to
    /// a constant referent. The contract still states `views` or `owns`.
    #[inline(never)]
    pub(super) fn parse_rust_reference_type(&mut self) -> Result<ParsedType, ClickError> {
        self.expect(Token::Amp)?;
        self.skip_rust_lifetime();
        let mutable = if self.peek_ident() == Some("mut") {
            self.position += 1;
            true
        } else {
            false
        };
        if matches!(self.peek(), Some(Token::Amp | Token::LParen)) {
            return Err(self.error(
                "a reference to a reference or to `()` in a `fn` signature is not supported; the Rust importer refuses it",
            ));
        }
        // `&[T; N]` is the pointer to the array's first element. The length
        // is the type's, so the contract writes it: `views words[0..N]`.
        let array = self.peek() == Some(&Token::LBracket);
        if array {
            self.position += 1;
        }
        let spelling = self.expect_rust_path_name("type")?;
        if array {
            self.expect(Token::Semicolon)?;
            // The length is a constant expression; the importer checks it.
            while !matches!(self.peek(), Some(Token::RBracket) | None) {
                self.position += 1;
            }
            self.expect(Token::RBracket)?;
            if rust_scalar_type(&spelling).is_none() {
                return Err(self.error(format!(
                    "an array of `{spelling}` in a `fn` signature is not supported; the Rust importer reads arrays of scalars only"
                )));
            }
        }
        Ok(match rust_scalar_type(&spelling) {
            Some(scalar) => {
                let Some(c_type) = scalar.pointer_type() else {
                    return Err(self.error(format!(
                        "a reference to `{spelling}` is not supported in a `fn` signature"
                    )));
                };
                ParsedType {
                    c_type,
                    struct_name: None,
                    struct_pointer: false,
                    constant: false,
                    pointee_constant: !mutable,
                    reference: false,
                }
            }
            None => ParsedType {
                c_type: C0Type::Int32Pointer,
                struct_name: Some(spelling),
                struct_pointer: true,
                constant: false,
                pointee_constant: !mutable,
                reference: false,
            },
        })
    }

    /// A Rust type in a signature: an integer or float type, `bool`, `()`,
    /// or a struct by name.
    pub(super) fn parse_rust_type(&mut self) -> Result<ParsedType, ClickError> {
        let scalar = |c_type| ParsedType {
            c_type,
            struct_name: None,
            struct_pointer: false,
            constant: false,
            pointee_constant: false,
            reference: false,
        };
        if self.peek() == Some(&Token::LParen) {
            self.position += 1;
            self.expect(Token::RParen)?;
            return Ok(scalar(C0Type::Void));
        }
        if self.peek() == Some(&Token::Amp) {
            return self.parse_rust_reference_type();
        }
        if self.peek() == Some(&Token::LBracket) {
            return Err(self.error(
                "an array or slice passed by value in a `fn` signature is not supported; the Rust importer refuses it",
            ));
        }
        let spelling = self.expect_rust_path_name("type")?;
        Ok(match rust_scalar_type(&spelling) {
            Some(c_type) => scalar(c_type),
            None => ParsedType {
                c_type: C0Type::Int32Pointer,
                struct_name: Some(spelling),
                struct_pointer: false,
                constant: false,
                pointee_constant: false,
                reference: false,
            },
        })
    }

    /// `expr as T` in a Rust sidecar is the scalar cast `(T)expr`. It binds
    /// tighter than a binary operator and looser than a unary one, as in
    /// Rust. `as` followed by anything but a scalar type is left for the
    /// clause that owns it (`intro() as name`).
    #[inline(never)]
    pub(super) fn parse_rust_casts(
        &mut self,
        mut operand: ContractExpression,
    ) -> Result<ContractExpression, ClickError> {
        while self.verifies_rust()
            && self.peek_ident() == Some("as")
            && matches!(
                self.peek_next(),
                Some(Token::Ident(name)) if rust_scalar_type(name).is_some()
            )
        {
            self.position += 1;
            let target = self.expect_ident("type")?;
            let target_type = rust_scalar_type(&target)
                .expect("checked above")
                .to_kernel_type();
            let Some(expression) = contract_expression_as_c_fragment(&operand) else {
                return Err(self.error("scalar cast expects a current C expression; put old(...) around the whole cast for an entry-state value"));
            };
            // Keep the same operand-bearing representation as a C-style
            // scalar cast, including its proof-expression identity.
            operand = ContractExpression::CUnary {
                operand: Box::new(operand),
                lowered: CExpression::Cast {
                    expression: Box::new(expression),
                    target_type,
                    integer_mode: crate::kernel::CIntegerCastMode::Standard,
                    pointee_struct: None,
                    pointee_volatile: false,
                    pointee_constant: false,
                    explicit_qualification: false,
                },
            };
        }
        Ok(operand)
    }
}

/// The C0 type a Rust scalar type name denotes.
fn rust_scalar_type(name: &str) -> Option<C0Type> {
    Some(match name {
        "bool" => C0Type::Bool,
        "i8" => C0Type::Int8,
        "i16" => C0Type::Int16,
        "i32" => C0Type::Int32,
        "i64" | "isize" => C0Type::Int64,
        "i128" => C0Type::Int128,
        "u8" => C0Type::UInt8,
        "u16" => C0Type::UInt16,
        "u32" => C0Type::UInt32,
        "u64" | "usize" => C0Type::UInt64,
        "u128" => C0Type::UInt128,
        "f32" => C0Type::Float32,
        "f64" => C0Type::Float64,
        _ => return None,
    })
}

pub(super) fn rust_signature_hint(parsed: &ParsedFunctionSignature) -> Option<String> {
    let signature = &parsed.signature;
    if !parsed.struct_params.is_empty() || parsed.return_struct_name.is_some() {
        return None;
    }
    let scalar_name = |c_type| {
        [
            "bool", "i8", "i16", "i32", "isize", "i128", "u8", "u16", "u32", "usize", "u128",
            "f32", "f64",
        ]
        .into_iter()
        .find(|name| rust_scalar_type(name) == Some(c_type))
    };
    let name = crate::languages::rust::names::rust_display_name(&signature.name)
        .unwrap_or_else(|| signature.name.clone());
    // An importer name that is no path, or an operator method's qualified
    // form, has no `fn` spelling.
    if name.starts_with("__rust_q") || name.starts_with('<') {
        return None;
    }
    let mut parameters = Vec::new();
    let mut index = 0;
    while let Some(parameter) = signature.parameters.get(index) {
        let spelling = if let Some(pointee) = parameter.c_type().pointee_type() {
            let reference = if parameter.pointee_constant {
                "&"
            } else {
                "&mut "
            };
            let base = scalar_name(pointee)?;
            let slice = signature.parameters.get(index + 1).is_some_and(|length| {
                length.name == format!("{}_len", parameter.name)
                    && length.c_type() == C0Type::UInt64
            });
            if slice {
                index += 1;
                format!("{reference}[{base}]")
            } else {
                format!("{reference}{base}")
            }
        } else {
            scalar_name(parameter.c_type())?.to_string()
        };
        parameters.push(format!("{}: {spelling}", parameter.name));
        index += 1;
    }
    let return_type = if signature.return_type == C0Type::Void {
        String::new()
    } else {
        format!(" -> {}", scalar_name(signature.return_type)?)
    };
    Some(format!("fn {name}({}){return_type}", parameters.join(", ")))
}
