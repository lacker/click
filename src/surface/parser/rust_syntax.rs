//! The Rust spelling of a sidecar: `fn` signatures, `impl` blocks, slices,
//! references, lifetimes and `as` casts, admitted when a `verifying` source
//! is Rust.

use super::*;

/// The Click library module that specifies Rust's `Vec<T>`.
const VEC_MODULE: &str = "library/rust/vec.click";

/// The importer name of the crate trait at `path` with type `arguments`:
/// `traits::Shape`, or `traits::Scale<i32>`.
fn trait_instance_name(path: &[String], arguments: &[String]) -> String {
    let mut name = crate::languages::rust::names::path_name(
        &path.iter().map(String::as_str).collect::<Vec<_>>(),
    );
    for argument in arguments {
        crate::languages::rust::names::push_type_argument(&mut name, argument);
    }
    name
}

/// A Rust sidecar's crate functions named as values, `Doubling(f)` with `f`
/// written `crate_name::twice`, as the address of the function the importer
/// names: `&` and the importer name, which reads as C's `&twice`. A path
/// names a function value only where it is no call, `step` callee or item
/// head (none followed by `(`), no type (none followed by `<`) and no
/// prefix of a longer path; and only when the import has the function.
pub(super) fn rewrite_function_values<V>(
    tokens: Vec<Token>,
    positions: Vec<SourcePosition>,
    functions: &BTreeMap<String, V>,
) -> (Vec<Token>, Vec<SourcePosition>) {
    let mut out_tokens = Vec::with_capacity(tokens.len());
    let mut out_positions = Vec::with_capacity(positions.len());
    let mut index = 0;
    while index < tokens.len() {
        if let Some(Token::Ident(first)) = tokens.get(index)
            && tokens.get(index + 1) == Some(&Token::ColonColon)
            && !matches!(
                index.checked_sub(1).map(|at| &tokens[at]),
                Some(Token::ColonColon)
            )
        {
            let mut segments = vec![first.as_str()];
            let mut end = index + 1;
            while tokens.get(end) == Some(&Token::ColonColon)
                && let Some(Token::Ident(segment)) = tokens.get(end + 1)
            {
                segments.push(segment);
                end += 2;
            }
            let name = crate::languages::rust::names::path_name(&segments);
            if !matches!(
                tokens.get(end),
                Some(Token::LParen | Token::LessThan | Token::ColonColon)
            ) && !(tokens.get(end) == Some(&Token::Dot)
                && matches!(index.checked_sub(1).and_then(|at| tokens.get(at)), Some(Token::Ident(word)) if word == "fn"))
                && functions.contains_key(&name)
            {
                out_tokens.push(Token::Amp);
                out_positions.push(positions[index].clone());
                out_tokens.push(Token::Ident(name));
                out_positions.push(positions[index].clone());
                index = end;
                continue;
            }
        }
        out_tokens.push(tokens[index].clone());
        out_positions.push(positions[index].clone());
        index += 1;
    }
    (out_tokens, out_positions)
}

impl Parser {
    fn parse_rust_closure_contract_name(&mut self, owner: &str) -> Result<String, ClickError> {
        use crate::languages::rust::source_statements::{ClosureExpression, ClosureSite};
        let mut statements = Vec::new();
        while self.chained_region_follows(&["statement"]) {
            self.expect(Token::Dot)?;
            self.expect_ident_spelling("statement")?;
            self.expect(Token::LParen)?;
            statements.push(self.expect_number("statement index")?);
            self.expect(Token::RParen)?;
        }
        self.expect(Token::Dot)?;
        let expression = if self.peek_ident() == Some("initializer") {
            self.position += 1;
            ClosureExpression::Initializer
        } else {
            self.expect_ident_spelling("call")?;
            self.expect(Token::LParen)?;
            let call = self.expect_number("call index")?;
            self.expect(Token::RParen)?;
            self.expect(Token::Dot)?;
            self.expect_ident_spelling("argument")?;
            self.expect(Token::LParen)?;
            let argument = self.expect_number("argument index")?;
            self.expect(Token::RParen)?;
            ClosureExpression::Argument { call, argument }
        };
        Ok(ClosureSite {
            statements,
            expression,
        }
        .contract_name(owner))
    }

    /// Read a Rust signature, including a closure's written expression path.
    #[inline(never)]
    pub(super) fn parse_rust_function_signature(
        &mut self,
    ) -> Result<ParsedFunctionSignature, ClickError> {
        if !self.verifies_rust() {
            return Err(self.error(
                "a `fn` signature is the Rust spelling; a C or C++ source's contract is written `type name(type parameter, ...)`",
            ));
        }
        let written_instance = self.rust_written_instances.contains(&self.position);
        self.expect_ident_spelling("fn")?;
        let binding = self
            .current_reference_binding
            .as_ref()
            .map(ToString::to_string);
        let path = if binding.is_some() {
            Vec::new()
        } else {
            self.expect_rust_path("function name")?
        };
        self.rust_trait_type_parameters.clear();
        // A generic function's instance, written out at its types,
        // `fn cells::read<i32>(...)`, is named with them.
        let instance_arguments = self.rust_instance_arguments(written_instance);
        if !instance_arguments.is_empty() && !written_instance {
            return Err(self.error(
                "a generic function's instance has its generic function's contract at its \
                 types; write the contract once, on the generic function",
            ));
        }
        let callable_parameters = if instance_arguments.is_empty() {
            self.parse_rust_generic_parameters()?
        } else {
            BTreeMap::new()
        };
        let name = if let Some(binding) = binding {
            binding
        } else if self.rust_impl_type.is_some() || self.rust_trait_interface.is_some() {
            // A method's own name; an item inside it, `compute::LIMIT`,
            // follows as the importer writes path segments.
            crate::languages::rust::names::method_path_name(
                &path.iter().map(String::as_str).collect::<Vec<_>>(),
            )
        } else {
            trait_instance_name(&path, &instance_arguments)
        };
        let mut name = name;
        while self.chained_region_follows(&["statement"]) {
            name = self.parse_rust_closure_contract_name(&name)?;
        }
        self.expect(Token::LParen)?;
        let mut parameters = Vec::new();
        let mut struct_params = BTreeMap::new();
        // The importer encodes a method's receiver type and declaration path
        // in its identity. Its receiver is the first parameter, named `self`.
        let name = match self.rust_impl_type.clone() {
            // A trait interface does not know the receiver's concrete fields.
            // Declared object state is handled by `rewrite_trait_objects`.
            None if let Some(interface) = self.rust_trait_interface.clone() => {
                let Some(mut receiver) = self.parse_rust_receiver("")? else {
                    return Err(
                        self.error("a trait method's interface takes `&self` or `&mut self`")
                    );
                };
                if !receiver.struct_pointer {
                    return Err(
                        self.error("a trait method's interface takes `&self` or `&mut self`")
                    );
                }
                receiver.struct_name = None;
                receiver.struct_pointer = false;
                parameters.push(
                    self.parse_parameter_array_suffix("self".into(), receiver)?
                        .parameter,
                );
                if self.peek() == Some(&Token::Comma) {
                    self.position += 1;
                }
                let mut encoded = interface;
                crate::languages::rust::names::push_path_segment(&mut encoded, &name);
                encoded
            }
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
                if self.rust_impl_destruct && name != "drop_glue" {
                    return Err(
                        self.error("an `impl Destruct` block declares `fn drop_glue(&mut self)`")
                    );
                }
                match (&self.rust_impl_trait, &self.rust_impl_method_suffix) {
                    (None, _) if self.rust_impl_destruct => {
                        crate::languages::rust::names::RustDestructor { record: impl_type }
                            .contract_name()
                    }
                    (Some(trait_name), _) => crate::languages::rust::names::trait_method_name(
                        &impl_type, trait_name, &name,
                    ),
                    (None, Some(suffix)) => format!("{impl_type}_{name}_{suffix}"),
                    (None, None) => self.rust_inherent_method(
                        self.rust_impl_module.as_deref(),
                        &impl_type,
                        &name,
                    )?,
                }
            }
            None => name,
        };
        let mut rust_slice_parameters = Vec::new();
        while self.peek() != Some(&Token::RParen) {
            let parameter_name = self.expect_ident("parameter name")?;
            self.expect(Token::Colon)?;
            let lifetime = usize::from(matches!(self.peek_next(), Some(Token::Lifetime(_))));
            let mutable = self.peek() == Some(&Token::Amp)
                && self.tokens.get(self.position + 1 + lifetime)
                    == Some(&Token::Ident("mut".into()));
            if let Some(slice_type) = self.take_rust_slice_value_type()? {
                // `bytes: &[T]` is one slice, as Rust passes it: its data
                // pointer and its length (`design/rust-slice-values.md`,
                // step 3b). The sidecar reads `bytes.len()`, `bytes[i]` and
                // `bytes.as_ptr()`.
                self.rust_slice_params.insert(
                    parameter_name.clone(),
                    slice_type == InterfaceType::Slice(crate::kernel::SliceElement::Str),
                );
                rust_slice_parameters.push(parameter_name.clone());
                parameters.push(FunctionParameter::rust_slice(
                    parameter_name,
                    slice_type,
                    !mutable,
                ));
                if self.peek() != Some(&Token::Comma) {
                    break;
                }
                self.position += 1;
                continue;
            }
            let dyn_fn = self.peek() == Some(&Token::Amp)
                && matches!(self.tokens.get(self.position + 1), Some(Token::Ident(word)) if word == "dyn")
                && matches!(self.tokens.get(self.position + 2), Some(Token::Ident(word)) if word == "Fn");
            // `f: F` of a `<F: Fn(i32) -> i32>` parameter.
            if let Some(word) = self.peek_ident()
                && let Some((interface_type, signature)) = callable_parameters.get(word).cloned()
                && matches!(self.peek_next(), Some(Token::Comma | Token::RParen))
            {
                self.position += 1;
                parameters.push(FunctionParameter {
                    click_type: ClickType::Program(interface_type),
                    name: parameter_name,
                    struct_name: None,
                    function_pointer_signature: Some(signature),
                    constant: false,
                    pointee_constant: false,
                    reference: false,
                });
                if self.peek() != Some(&Token::Comma) {
                    break;
                }
                self.position += 1;
                continue;
            }
            let impl_fn = self.peek_ident() == Some("impl");
            if dyn_fn
                || impl_fn
                || (self.peek_ident() == Some("fn") && self.peek_next() == Some(&Token::LParen))
            {
                let (interface_type, signature) = if dyn_fn {
                    self.parse_rust_dyn_fn_type()?
                } else if impl_fn {
                    self.parse_rust_impl_fn_type()?
                } else {
                    self.parse_rust_fn_pointer_type()?
                };
                parameters.push(FunctionParameter {
                    click_type: ClickType::Program(interface_type),
                    name: parameter_name,
                    struct_name: None,
                    function_pointer_signature: Some(signature),
                    constant: false,
                    pointee_constant: false,
                    reference: false,
                });
                if self.peek() != Some(&Token::Comma) {
                    break;
                }
                self.position += 1;
                continue;
            }
            let parsed_type = self.parse_rust_type()?;
            self.record_rust_vec_param(&parameter_name, parsed_type.interface_type);
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
            // `-> &[T]` is one slice, as a slice parameter is
            // (`design/rust-slice-values.md`, step 3c): the contract reads
            // `result.len()`, `result[i]` and `result.as_ptr()`.
            if let Some(slice_type) = self.take_rust_slice_value_type()? {
                self.rust_slice_params.insert(
                    "result".into(),
                    slice_type == InterfaceType::Slice(crate::kernel::SliceElement::Str),
                );
                ParsedType {
                    interface_type: slice_type,
                    struct_name: None,
                    struct_pointer: false,
                    constant: false,
                    pointee_constant: false,
                    reference: false,
                }
            } else {
                let parsed = self.parse_rust_type()?;
                self.record_rust_vec_param("result", parsed.interface_type);
                parsed
            }
        } else {
            ParsedType {
                interface_type: InterfaceType::Void,
                struct_name: None,
                struct_pointer: false,
                constant: false,
                pointee_constant: false,
                reference: false,
            }
        };
        // A box result, `-> Box<crate::S>`, is the struct's address.
        let return_type = match parsed_return_type.struct_name.as_deref() {
            Some(struct_name) if !parsed_return_type.struct_pointer => {
                self.scalar_struct_value_type(struct_name)?
            }
            _ => parsed_return_type.interface_type,
        };
        let diverges = if self.peek_ident() == Some("diverges") {
            self.position += 1;
            true
        } else {
            false
        };
        self.record_abstract_pointer_params(&parameters);
        Ok(ParsedFunctionSignature {
            signature: FunctionSignature {
                c_source: None,
                return_type,
                return_struct_name: parsed_return_type.struct_name.clone(),
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
            aggregate_result: false,
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
        let written = self.rust_written_instances.contains(&self.position);
        self.expect_ident_spelling("impl")?;
        // A generic implementation, `impl<T> traits::Keep<T> for Echo`, is
        // verified once for every type: its type parameters are abstract
        // types in the block.
        let generic = self.parse_rust_impl_parameters()?;
        let previous_abstract = std::mem::replace(
            &mut self.rust_abstract_type_parameters,
            generic.iter().cloned().collect(),
        );
        let result = self.parse_rust_impl_block_after_generics(function_blocks, written);
        self.rust_abstract_type_parameters = previous_abstract;
        result
    }

    /// `written` when the block is a generic struct's instance the token pass
    /// wrote out: its methods are `extern fn`s.
    fn parse_rust_impl_block_after_generics(
        &mut self,
        function_blocks: &mut Vec<FunctionBlock>,
        written: bool,
    ) -> Result<(), ClickError> {
        let mut impl_path = self.expect_rust_path("type name")?;
        // A crate trait's instance, `traits::Scale<i32>`, is named with its
        // type arguments; the standard library's operator traits take one.
        let instance = if impl_path.len() > 1 {
            self.parse_rust_type_arguments()?
        } else {
            Vec::new()
        };
        let suffix = self.parse_rust_trait_argument()?;
        let mut inherent = true;
        let mut destruct = false;
        // A crate trait is named by its path, as a crate type is; the
        // standard library's traits by their own names.
        let mut impl_trait = None;
        let mut for_instance = None;
        if self.peek_ident() == Some("for") {
            self.position += 1;
            destruct = impl_path == ["Destruct"];
            if suffix.is_none() && impl_path.len() > 1 {
                impl_trait = Some(trait_instance_name(&impl_path, &instance));
            }
            impl_path = self.expect_rust_path("type name")?;
            // A generic struct implementing the trait, `for cells::Wrap<T>`,
            // is the instance its arguments name.
            let for_arguments = if impl_path.len() > 1 {
                self.parse_rust_type_arguments()?
            } else {
                Vec::new()
            };
            if !for_arguments.is_empty() {
                for_instance = Some(trait_instance_name(&impl_path, &for_arguments));
            }
            inherent = false;
        } else if suffix.is_some() {
            return Err(self.error("a trait with a type argument is implemented `for` a type"));
        } else if !instance.is_empty()
            && !written
            && !instance
                .iter()
                .all(|argument| self.rust_abstract_type_parameters.contains(argument))
        {
            return Err(self.error(
                "a generic struct's methods are written once, `impl<T> crate_name::Cell<T>`; \
                 an instance's methods have their contracts at its types",
            ));
        }
        // A written instance at abstract types, from generic code, reads
        // them as abstract types.
        if written {
            self.rust_abstract_type_parameters.extend(
                instance
                    .iter()
                    .filter(|argument| {
                        !rust_generic_traits::INSTANCE_SCALARS.contains(&argument.as_str())
                    })
                    .cloned(),
            );
        }
        self.expect(Token::LBrace)?;
        let segments: Vec<&str> = impl_path.iter().map(String::as_str).collect();
        // A generic struct's `impl` type is the instance it names,
        // `Cell<T>` or `Cell<i32>`.
        let impl_type = if inherent {
            trait_instance_name(&impl_path, &instance)
        } else if let Some(for_instance) = for_instance {
            for_instance
        } else {
            crate::languages::rust::names::path_name(&segments)
        };
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
        let previous_trait = std::mem::replace(&mut self.rust_impl_trait, impl_trait);
        let previous_destruct = std::mem::replace(&mut self.rust_impl_destruct, destruct);
        let previous_suffix = std::mem::replace(&mut self.rust_impl_method_suffix, suffix);
        let previous_module = std::mem::replace(&mut self.rust_impl_module, impl_module);
        let mut result = Ok(());
        while self.peek() != Some(&Token::RBrace) {
            let external =
                self.in_interface_file() || (written && self.peek_ident() == Some("extern"));
            if self.peek_ident() != Some("fn") && !external {
                result = Err(self.error("an `impl` block holds `fn` contracts"));
                break;
            }
            // The method's own name, which names its interface in the trait.
            let method = match self.tokens.get(self.position + 1 + usize::from(external)) {
                Some(Token::Ident(method)) => Some(method.clone()),
                _ => None,
            };
            match self.parse_function_block(external) {
                Ok(block) => {
                    if let (Some(trait_name), Some(method)) = (&self.rust_impl_trait, method)
                        && !self.rust_object_traits.contains(trait_name)
                    {
                        let mut interface = trait_name.clone();
                        crate::languages::rust::names::push_path_segment(&mut interface, &method);
                        self.rust_trait_implementations
                            .push((block.signature().name().to_string(), interface));
                    }
                    function_blocks.push(block)
                }
                Err(error) => {
                    result = Err(error);
                    break;
                }
            }
        }
        self.rust_impl_type = previous;
        self.rust_impl_trait = previous_trait;
        self.rust_impl_destruct = previous_destruct;
        self.rust_impl_method_suffix = previous_suffix;
        self.rust_impl_module = previous_module;
        result?;
        self.expect(Token::RBrace)?;
        Ok(())
    }

    /// Whether `clause` is the object a trait method's receiver holds, which
    /// the token rewrite gives a trait whose object carries state.
    fn is_object_handle(&self, clause: &ResourceClause) -> bool {
        let Some(trait_name) = &self.rust_trait_interface else {
            return false;
        };
        let ResourceClause::Named { resource, .. } = clause else {
            return false;
        };
        matches!(resource.as_ref(), ResourceClause::Declared { name, .. }
            if *name == rust_trait_objects::object_family(trait_name))
    }

    /// `trait traits::Shape { ... }`: each `fn` inside is the interface of
    /// that method of the crate trait, whose contract every implementation
    /// must refine and a call through the trait assumes. A required method's
    /// is an external declaration; a default method's is written with the
    /// proof of its default body.
    #[inline(never)]
    pub(super) fn parse_rust_trait_block(
        &mut self,
        function_blocks: &mut Vec<FunctionBlock>,
    ) -> Result<(), ClickError> {
        self.expect_ident_spelling("trait")?;
        let path = self.expect_rust_path("trait name")?;
        if path.len() < 2 {
            return Err(self.error(
                "a crate trait is named by its path, as the crate writes it: `trait crate_name::Shape`",
            ));
        }
        let arguments = self.parse_rust_type_arguments()?;
        let interface = trait_instance_name(&path, &arguments);
        // A block naming the trait's type parameters is the generic block,
        // read once with each parameter an abstract type; one naming scalar
        // types is an instance's. The token pass has written each instance
        // out already.
        let scalars = arguments
            .iter()
            .filter(|argument| {
                super::rust_generic_traits::INSTANCE_SCALARS.contains(&argument.as_str())
            })
            .count();
        if scalars != 0 && scalars != arguments.len() {
            return Err(self.error(
                "a crate trait's `trait` block names its type parameters, `trait crate_name::Scale<T>`, or an instance's scalar types, `trait crate_name::Scale<i32>`",
            ));
        }
        let abstract_parameters = if scalars == 0 {
            arguments.iter().cloned().collect()
        } else {
            BTreeSet::new()
        };
        let previous_abstract =
            std::mem::replace(&mut self.rust_abstract_type_parameters, abstract_parameters);
        self.expect(Token::LBrace)?;
        let previous = self.rust_trait_interface.replace(interface);
        let mut result = Ok(());
        while self.peek() != Some(&Token::RBrace) {
            if self.peek_ident() != Some("fn") {
                result = Err(self.error("a `trait` block holds `fn` interfaces"));
                break;
            }
            // A sidecar may verify the default body. An interface file
            // only declares the method's contract.
            let external = self.in_interface_file() || !self.rust_trait_method_has_proof();
            match self.parse_function_block(external) {
                // Nor does it hold any of the receiver's resources.
                Ok(block)
                    if block.requires().iter().any(|requirement| {
                        matches!(requirement, Requirement::Resource(clause)
                            if !self.is_object_handle(clause))
                    }) || block.ensures().iter().any(|clause| {
                        matches!(clause.ensure(), Ensure::Resource(resource)
                                if !self.is_object_handle(resource))
                    }) =>
                {
                    result = Err(self.error(
                        "a trait method's interface holds no resources: it reads nothing through `self`, whose type it does not know",
                    ));
                    break;
                }
                Ok(block) => function_blocks.push(block),
                Err(error) => {
                    result = Err(error);
                    break;
                }
            }
        }
        self.rust_trait_interface = previous;
        self.rust_abstract_type_parameters = previous_abstract;
        result?;
        self.expect(Token::RBrace)?;
        Ok(())
    }

    /// A generic `impl` block's type parameters, `<T>` or `<T: Copy +
    /// Clone>`, by name; none when no `<` follows. A parameter's bounds are
    /// `Copy` and `Clone`, which a proof does not read.
    fn parse_rust_impl_parameters(&mut self) -> Result<Vec<String>, ClickError> {
        let mut parameters = Vec::new();
        if self.peek() != Some(&Token::LessThan) {
            return Ok(parameters);
        }
        self.position += 1;
        loop {
            parameters.push(self.expect_ident("type parameter")?);
            if self.peek() == Some(&Token::Colon) {
                self.position += 1;
                loop {
                    match self.peek_ident() {
                        Some("Copy" | "Clone") => self.position += 1,
                        _ => {
                            return Err(self.error(
                                "an abstract type parameter's bounds are `Copy` and `Clone`",
                            ));
                        }
                    }
                    if self.peek() != Some(&Token::Plus) {
                        break;
                    }
                    self.position += 1;
                }
            }
            match self.peek() {
                Some(Token::Comma) => self.position += 1,
                _ => break,
            }
        }
        self.expect(Token::GreaterThan)?;
        Ok(parameters)
    }

    /// A generic crate trait's or a path's type arguments, `<i32>` or `<T,
    /// U>`, each a name; none when no `<` follows.
    pub(super) fn parse_rust_type_arguments(&mut self) -> Result<Vec<String>, ClickError> {
        let mut arguments = Vec::new();
        if self.peek() != Some(&Token::LessThan) {
            return Ok(arguments);
        }
        self.position += 1;
        loop {
            // A shared reference to a scalar, `&u8`: the item a slice
            // iterator yields, `Option<&u8>`.
            if self.peek() == Some(&Token::Amp) {
                self.position += 1;
                // A shared slice, `&[u8]`: the chunk a `chunks_exact`
                // iterator yields, `Option<&[u8]>`.
                if self.peek() == Some(&Token::LBracket) {
                    self.position += 1;
                    let element = self.expect_ident("type argument")?;
                    if rust_scalar_type(&element).is_none() {
                        return Err(self.error(
                            "a slice type argument is a shared slice of a scalar, `&[u8]`",
                        ));
                    }
                    self.expect(Token::RBracket)?;
                    arguments.push(format!("&[{element}]"));
                    match self.peek() {
                        Some(Token::Comma) => {
                            self.position += 1;
                            continue;
                        }
                        _ => break,
                    }
                }
                let pointee = self.expect_ident("type argument")?;
                if rust_scalar_type(&pointee).is_none() {
                    return Err(self.error(
                        "a reference type argument is a shared reference to a scalar, `&u8`",
                    ));
                }
                arguments.push(format!("&{pointee}"));
            } else {
                arguments.push(self.expect_ident("type argument")?);
            }
            match self.peek() {
                Some(Token::Comma) => self.position += 1,
                _ => break,
            }
        }
        // `>>` closes this list and the one around it, `<S: traits::Scale<i32>>`.
        if self.peek() == Some(&Token::ShiftRight) {
            self.tokens[self.position] = Token::GreaterThan;
            return Ok(arguments);
        }
        self.expect(Token::GreaterThan)?;
        Ok(arguments)
    }

    /// Whether the trait method at the parser's position is written with a
    /// proof, `fn twice(&self) -> i32 { ... } by { ... }`: the clause block,
    /// the first brace outside the signature's parentheses, is followed by
    /// `by`.
    fn rust_trait_method_has_proof(&self) -> bool {
        let mut parentheses = 0usize;
        let mut index = self.position;
        while let Some(token) = self.tokens.get(index) {
            match token {
                Token::LParen => parentheses += 1,
                Token::RParen => parentheses = parentheses.saturating_sub(1),
                Token::LBrace if parentheses == 0 => break,
                Token::Semicolon | Token::RBrace if parentheses == 0 => return false,
                _ => {}
            }
            index += 1;
        }
        let mut braces = 0usize;
        while let Some(token) = self.tokens.get(index) {
            match token {
                Token::LBrace => braces += 1,
                Token::RBrace => {
                    braces -= 1;
                    if braces == 0 {
                        return matches!(self.tokens.get(index + 1), Some(Token::Ident(word)) if word == "by");
                    }
                }
                _ => {}
            }
            index += 1;
        }
        false
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
        module: Option<&str>,
        impl_type: &str,
        method: &str,
    ) -> Result<String, ClickError> {
        let Some(module) = module else {
            return Ok(crate::languages::rust::names::inherent_method_name(
                None, impl_type, method,
            ));
        };
        let suffix =
            crate::languages::rust::names::inherent_method_name(Some(""), impl_type, method);
        let methods = self.rust_inherent_methods.get_or_init(|| {
            let mut methods = BTreeMap::new();
            for name in self.local_struct_pointers_by_function.keys() {
                if let Some(suffix) = crate::languages::rust::names::impl_item_suffix(name) {
                    methods
                        .entry(suffix.to_owned())
                        .and_modify(|entry| *entry = None)
                        .or_insert_with(|| Some(name.clone()));
                }
            }
            methods
        });
        match methods.get(&suffix) {
            Some(Some(name)) => Ok(name.clone()),
            Some(None) => Err(self.error(format!(
                "the import has more than one method `{method}` of this type"
            ))),
            None => Ok(crate::languages::rust::names::inherent_method_name(
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

    /// A type's path and any type arguments, as the importer names an
    /// instance of a generic struct: `cells::Cell<T>` or `cells::Cell<i32>`.
    fn expect_rust_type_name(&mut self, what: &str) -> Result<String, ClickError> {
        let path = self.expect_rust_path(what)?;
        let arguments = if rust_scalar_type(&path.join("::")).is_none() {
            self.parse_rust_type_arguments()?
        } else {
            Vec::new()
        };
        if let [argument] = arguments.as_slice()
            && crate::languages::rust::names::is_option_path(
                &path.iter().map(String::as_str).collect::<Vec<_>>(),
            )
        {
            return Ok(crate::languages::rust::names::option_type_name(argument));
        }
        if let [ok, err] = arguments.as_slice()
            && crate::languages::rust::names::is_result_path(
                &path.iter().map(String::as_str).collect::<Vec<_>>(),
            )
        {
            return Ok(crate::languages::rust::names::result_type_name(ok, err));
        }
        if let [element] = arguments.as_slice()
            && crate::languages::rust::names::is_vec_path(
                &path.iter().map(String::as_str).collect::<Vec<_>>(),
            )
        {
            return Ok(crate::languages::rust::names::vec_type_name(element));
        }
        Ok(trait_instance_name(&path, &arguments))
    }

    /// The scalar type arguments after a function's name, `<i32>`, that
    /// name a generic function's instance, with the list consumed; none,
    /// with nothing consumed, otherwise.
    ///
    /// A `written` instance may be at abstract types too, `fn
    /// cells::read<T>(...)` called from generic code: those are abstract
    /// type parameters in its signature.
    fn rust_instance_arguments(&mut self, written: bool) -> Vec<String> {
        if self.peek() != Some(&Token::LessThan) {
            return Vec::new();
        }
        let mut arguments = Vec::new();
        let mut index = self.position + 1;
        loop {
            match self.tokens.get(index) {
                Some(Token::Ident(argument))
                    if written
                        || rust_generic_traits::INSTANCE_SCALARS.contains(&argument.as_str()) =>
                {
                    arguments.push(argument.clone());
                }
                _ => return Vec::new(),
            }
            match self.tokens.get(index + 1) {
                Some(Token::Comma) => index += 2,
                Some(Token::GreaterThan) => break,
                _ => return Vec::new(),
            }
        }
        self.position = index + 2;
        // A written instance is at any scalar, `Option::unwrap<i64>`, or
        // crate type, `Box::drop<Node>`; any other argument is abstract.
        for argument in &arguments {
            if rust_scalar_type(argument).is_none()
                && !self.struct_layouts.contains_key(argument)
                && !self.rust_enum_types.contains_key(argument)
            {
                self.rust_abstract_type_parameters.insert(argument.clone());
            }
        }
        arguments
    }

    /// A lifetime, `'a` in `&'a T`, which a contract does not use.
    pub(super) fn skip_rust_lifetime(&mut self) {
        if matches!(self.peek(), Some(Token::Lifetime(_))) {
            self.position += 1;
        }
    }

    /// A call step's Rust callee after its first segment `first`: the rest
    /// of its path and type arguments. A receiver's type arguments precede
    /// the final method name, as in `crate_name::Stack::<u32>::push`.
    pub(super) fn rust_step_callee(
        &mut self,
        first: String,
    ) -> Result<(String, Option<String>), ClickError> {
        let mut path = vec![first];
        while self.peek() == Some(&Token::ColonColon) && self.peek_next() != Some(&Token::LessThan)
        {
            self.position += 1;
            path.push(self.expect_ident("function name")?);
        }
        if self.peek() == Some(&Token::ColonColon) {
            self.position += 1;
        }
        let arguments = self.rust_instance_arguments(true);
        if !arguments.is_empty() && self.peek() == Some(&Token::ColonColon) {
            self.position += 1;
            let method = self.expect_ident("method name")?;
            let impl_type = trait_instance_name(&path, &arguments);
            let module = (path.len() > 1).then(|| {
                crate::languages::rust::names::qualified_name(
                    path[..path.len() - 1].iter().map(String::as_str),
                )
            });
            let callee = self.rust_inherent_method(module.as_deref(), &impl_type, &method)?;
            let written = format!("{}::<{}>::{method}", path.join("::"), arguments.join(", "));
            return Ok((callee, Some(written)));
        }
        let callee = trait_instance_name(&path, &arguments);
        let written = if !arguments.is_empty() {
            Some(format!("{}<{}>", path.join("::"), arguments.join(", ")))
        } else {
            (path.len() > 1).then(|| path.join("::"))
        };
        Ok((callee, written))
    }

    /// The generic parameters after a function's name: lifetimes, `<'a, 'b:
    /// 'a>`, which a contract does not use, and callable type parameters,
    /// `<F: Fn(i32) -> i32>`, by name. The importer refuses other generic
    /// functions, so other type parameters are refused here too.
    #[allow(clippy::type_complexity)]
    pub(super) fn parse_rust_generic_parameters(
        &mut self,
    ) -> Result<
        BTreeMap<
            String,
            (
                InterfaceType,
                crate::languages::interface::CallbackInterface,
            ),
        >,
        ClickError,
    > {
        let mut callable = BTreeMap::new();
        if self.peek() != Some(&Token::LessThan) {
            return Ok(callable);
        }
        self.position += 1;
        loop {
            // A type parameter bound by nothing a proof reads, `T` or `T:
            // Copy`, is an abstract type: the function is verified once for
            // every type.
            if let Some(word) = self.peek_ident()
                && word != "Fn"
                && (matches!(self.peek_next(), Some(Token::Comma | Token::GreaterThan))
                    || self.peek_next() == Some(&Token::Colon)
                        && matches!(
                            self.tokens.get(self.position + 2),
                            Some(Token::Ident(bound)) if bound == "Copy" || bound == "Clone"
                        ))
            {
                let name = word.to_string();
                self.position += 1;
                if self.peek() == Some(&Token::Colon) {
                    self.position += 1;
                    loop {
                        match self.peek_ident() {
                            Some("Copy" | "Clone") => self.position += 1,
                            _ => {
                                return Err(self.error(
                                    "an abstract type parameter's bounds are `Copy` and `Clone`",
                                ));
                            }
                        }
                        if self.peek() != Some(&Token::Plus) {
                            break;
                        }
                        self.position += 1;
                    }
                }
                if callable.contains_key(&name)
                    || self.rust_trait_type_parameters.contains(&name)
                    || !self.rust_abstract_type_parameters.insert(name)
                {
                    return Err(self.error("a type parameter is declared twice"));
                }
                if self.peek() == Some(&Token::Comma) {
                    self.position += 1;
                }
                if self.peek() == Some(&Token::GreaterThan) {
                    self.position += 1;
                    return Ok(callable);
                }
                continue;
            }
            if let Some(word) = self.peek_ident()
                && self.peek_next() == Some(&Token::Colon)
            {
                let name = word.to_string();
                self.position += 2;
                // `T: traits::Shape`: a crate trait, named by its path.
                if self.peek_ident() != Some("Fn") && self.peek_next() == Some(&Token::ColonColon) {
                    self.expect_rust_path("trait name")?;
                    self.parse_rust_type_arguments()?;
                    if callable.contains_key(&name) || !self.rust_trait_type_parameters.insert(name)
                    {
                        return Err(self.error("a type parameter is declared twice"));
                    }
                    if self.peek() == Some(&Token::Comma) {
                        self.position += 1;
                    }
                    if self.peek() == Some(&Token::GreaterThan) {
                        self.position += 1;
                        return Ok(callable);
                    }
                    continue;
                }
                if self.peek_ident() != Some("Fn") {
                    return Err(self.error(
                        "a `fn` signature's type parameter is supported only with an `Fn(...) -> ...` bound or a crate trait's, such as `<T: crate_name::Shape>`",
                    ));
                }
                self.position += 1;
                let signature = self.parse_rust_callable_signature()?;
                if callable.insert(name, signature).is_some() {
                    return Err(self.error("a type parameter is declared twice"));
                }
                if self.peek() == Some(&Token::Comma) {
                    self.position += 1;
                }
                if self.peek() == Some(&Token::GreaterThan) {
                    self.position += 1;
                    return Ok(callable);
                }
                continue;
            }
            let Some(Token::Lifetime(_)) = self.peek() else {
                return Err(self.error(
                    "a `fn` signature's generic parameters may only be lifetimes, such as `<'a>`, and `Fn` type parameters, such as `<F: Fn(i32) -> i32>`",
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
                return Ok(callable);
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
            interface_type: InterfaceType::Int32Pointer,
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
        // `&str` is a shared slice of the UTF-8 bytes it refers to, as the
        // importer reads it.
        if !mutable && self.tokens.get(bracket) == Some(&Token::Ident("str".into())) {
            self.position = bracket + 1;
            return Ok(Some(ParsedType {
                interface_type: rust_scalar_type("u8")
                    .and_then(InterfaceType::pointer_type)
                    .expect("a byte pointer"),
                struct_name: None,
                struct_pointer: false,
                constant: false,
                pointee_constant: true,
                reference: false,
            }));
        }
        if self.tokens.get(bracket) != Some(&Token::LBracket) {
            return Ok(None);
        }
        // `&[T; N]` is a reference to an array, not a slice.
        if self.tokens.get(bracket + 2) == Some(&Token::Semicolon) {
            return Ok(None);
        }
        self.position = bracket + 1;
        let spelling = self.expect_ident("slice element type")?;
        let Some(interface_type) =
            rust_scalar_type(&spelling).and_then(InterfaceType::pointer_type)
        else {
            return Err(self.error(format!(
                "a slice of `{spelling}` in a `fn` signature is not supported; the Rust importer reads slices of scalars only"
            )));
        };
        self.expect(Token::RBracket)?;
        Ok(Some(ParsedType {
            interface_type,
            struct_name: None,
            struct_pointer: false,
            constant: false,
            pointee_constant: !mutable,
            reference: false,
        }))
    }

    /// `name.len()` where `name` is a slice parameter: consumes `.len()` and
    /// answers the length's own name.
    /// Records `name` as a `Vec` parameter, or `result` as a `Vec` result,
    /// when `interface_type` is the library's `Vec<T>` or a reference to it, and
    /// brings in the library module that specifies it.
    fn record_rust_vec_param(&mut self, name: &str, interface_type: InterfaceType) {
        let (InterfaceType::Parameter(value_type) | InterfaceType::ParameterPointer(value_type)) =
            interface_type
        else {
            return;
        };
        if !matches!(super::generics::primitive_instance_of(value_type.name()), Some((primitive, _)) if primitive == "Vec")
        {
            return;
        }
        self.rust_vec_params.insert(
            name.to_string(),
            matches!(interface_type, InterfaceType::ParameterPointer(_)),
        );
        self.implied_library_modules.insert(VEC_MODULE);
    }

    /// `v.len()` or `v[i]` of a `Vec` parameter: `vec::len(v)` or
    /// `vec::get(v, i)`, of `*v` for a reference, as Rust reads through one.
    pub(super) fn take_rust_vec_method(
        &mut self,
        name: &str,
    ) -> Result<Option<SyntaxTerm>, ClickError> {
        let Some(&reference) = self.rust_vec_params.get(name) else {
            return Ok(None);
        };
        let vector = if reference {
            SyntaxTerm::ProgramExpression(ProgramExpression::Load(Box::new(
                ProgramExpression::Variable(name.into()),
            )))
        } else {
            SyntaxTerm::ProgramExpression(ProgramExpression::Variable((name.to_string()).into()))
        };
        if self.peek() == Some(&Token::Dot)
            && self.peek_next() == Some(&Token::Ident("len".into()))
            && self.tokens.get(self.position + 2) == Some(&Token::LParen)
            && self.tokens.get(self.position + 3) == Some(&Token::RParen)
        {
            self.position += 4;
            return Ok(Some(SyntaxTerm::Call {
                name: "click::rust::vec::len".to_string(),
                arguments: vec![vector],
            }));
        }
        if self.peek() == Some(&Token::LBracket) {
            self.position += 1;
            let index = self.parse_contract_expression()?;
            self.expect(Token::RBracket)?;
            return Ok(Some(SyntaxTerm::Call {
                name: "click::rust::vec::get".to_string(),
                arguments: vec![vector, index],
            }));
        }
        Ok(None)
    }

    /// `iter.<accessor>`, Rust's own accessors of a loop's iterator
    /// (`iter.len()`, `iter.as_slice()`, a range's `iter.start`): inside a
    /// `loop` block, read from the iterator that loop advances, which the
    /// loop phase binds; with `loop_index`, `loop(i).iter`, that loop's,
    /// read here. The cursor sits after `iter`. `iter.as_slice()` reads as a
    /// slice parameter does, its data: `iter.as_slice().len()` is
    /// `iter.len()`.
    pub(super) fn take_rust_iterator_method(
        &mut self,
        name: &str,
        loop_index: Option<usize>,
    ) -> Result<Option<SyntaxTerm>, ClickError> {
        if !self.verifies_rust() || name != "iter" {
            return Ok(None);
        }
        let accessor_at = |parser: &Self, at: usize| -> Option<(String, usize)> {
            let Some(Token::Dot) = parser.tokens.get(at) else {
                return None;
            };
            let Some(Token::Ident(name)) = parser.tokens.get(at + 1) else {
                return None;
            };
            let call = parser.tokens.get(at + 2) == Some(&Token::LParen)
                && parser.tokens.get(at + 3) == Some(&Token::RParen);
            Some(if call {
                (format!("{name}()"), 4)
            } else {
                (name.clone(), 2)
            })
        };
        let at = self.position;
        let accessor = accessor_at(self, at).map(|(accessor, width)| {
            // `iter.as_slice().len()` is `iter.len()`, its data pointer is
            // `iter.as_slice().as_ptr()`, and a slice field's length is
            // `iter.v.len()`. An index `iter.as_slice()[i]` reads through
            // the data pointer, as a slice parameter's does.
            match accessor_at(self, at + width) {
                Some((next, more)) if accessor == "as_slice()" && next == "len()" => {
                    (next, width + more)
                }
                Some((next, more)) if accessor == "as_slice()" && next == "as_ptr()" => {
                    (format!("{accessor}.{next}"), width + more)
                }
                None if accessor == "as_slice()"
                    && self.tokens.get(at + width) == Some(&Token::LBracket) =>
                {
                    ("as_slice().as_ptr()".to_string(), width)
                }
                Some((next, more))
                    if matches!(accessor.as_str(), "v" | "rem") && next == "len()" =>
                {
                    (format!("{accessor}.len()"), width + more)
                }
                _ => (accessor, width),
            }
        });
        let accessor = accessor.filter(|(accessor, _)| {
            crate::surface::RUST_ITERATOR_ACCESSORS.contains(&accessor.as_str())
        });
        let Some(index) = loop_index else {
            if self.loop_block_depth == 0 {
                // Outside a loop, `iter` is the program's own name.
                return Ok(None);
            }
            // A crate's own iterator is the program's local `iter`, a struct
            // whose fields a proof reads as written.
            let user_iterator = self.rust_loop_iterators.iter().flatten().any(|iterator| {
                iterator.kind == crate::languages::interface::RustIteratorKind::User
            });
            if accessor.is_none() && user_iterator {
                return Ok(None);
            }
            let Some((accessor, width)) = accessor else {
                return Err(self.error(
                    "inside a loop, `iter` is the loop's iterator, read through Rust's own \
                     accessors (`iter.len()`, `iter.as_slice()`, a range's `iter.start`); a \
                     Rust local named `iter` is `program::iter`",
                ));
            };
            self.position += width;
            return Ok(Some(SyntaxTerm::Binding(format!("iter.{accessor}"))));
        };
        let Some((accessor, width)) = accessor else {
            return Ok(None);
        };
        let Some(iterator) = self.rust_loop_iterators.get(index).cloned().flatten() else {
            return Err(self.error(format!(
                "loop {index} advances no iterator, so `loop({index}).iter` names nothing"
            )));
        };
        self.position += width;
        crate::surface::rust_iterator_method(&iterator, &accessor)
            .map(Some)
            .map_err(|message| self.error(message))
    }

    /// `name.len()` or `name.as_ptr()` where `name` is a Rust `fn`'s slice
    /// parameter or slice local: consumes the method and answers the
    /// component it reads, `SliceLength(name)` or `SliceData(name)`, of the
    /// one slice the program binding holds (`design/rust-slice-values.md`,
    /// step 3b). The binding is resolved where the expression is read, as
    /// any program variable is, so a local that hides a parameter is read.
    pub(super) fn take_rust_slice_method(
        &mut self,
        name: &str,
        qualified: bool,
    ) -> Option<SyntaxTerm> {
        if self.peek() != Some(&Token::Dot)
            || self.tokens.get(self.position + 2) != Some(&Token::LParen)
            || self.tokens.get(self.position + 3) != Some(&Token::RParen)
            || !self.is_rust_slice_name(name)
        {
            return None;
        }
        let length = match self.peek_next() {
            Some(Token::Ident(method)) if method == "len" => true,
            Some(Token::Ident(method)) if method == "as_ptr" => false,
            _ => return None,
        };
        self.position += 4;
        // A slice local that may hide a slice parameter of its spelling is
        // read, in a proof or when qualified, as the program resolves it
        // where it is read, its innermost live declaration (`program::name`).
        // Any other slice name is its current C value.
        if (qualified || self.proof_nesting > 0)
            && self.rust_slice_locals.contains(name)
            && self.rust_slice_params.contains_key(name)
        {
            let string = self.rust_slice_params.get(name) == Some(&true);
            let method = match (length, string) {
                (true, false) => crate::surface::RUST_SLICE_LEN,
                (false, false) => crate::surface::RUST_SLICE_AS_PTR,
                (true, true) => crate::surface::RUST_STR_LEN,
                (false, true) => crate::surface::RUST_STR_AS_PTR,
            };
            return Some(SyntaxTerm::Call {
                name: method.to_string(),
                arguments: vec![SyntaxTerm::ProgramBinding(name.to_string())],
            });
        }
        let slice = Box::new(ProgramExpression::Variable(name.into()));
        Some(SyntaxTerm::ProgramExpression(if length {
            ProgramExpression::SliceLength(slice)
        } else {
            ProgramExpression::SliceData(slice)
        }))
    }

    /// Whether `name` names a Rust `fn`'s slice parameter, or, in its proof,
    /// one of its slice locals.
    pub(super) fn is_rust_slice_name(&self, name: &str) -> bool {
        self.rust_slice_params.contains_key(name) || self.rust_slice_locals.contains(name)
    }

    /// Refuses `+` or `-` on a Rust slice read, `bytes + k`: the slice is
    /// one value, and its data pointer is `bytes.as_ptr()`.
    pub(super) fn refuse_rust_slice_arithmetic(
        &self,
        operand: &SyntaxTerm,
    ) -> Result<(), ClickError> {
        if self.rust_slice_data(operand).is_none() {
            return Ok(());
        }
        let written = crate::surface::diagnostics::describe_contract_expression(operand);
        Err(self
            .error(format!(
                "`{written}` is a slice, not a pointer: pointer arithmetic is written on its data pointer, `.as_ptr()`, as in `{}.as_ptr() + k`",
                written
                    .trim_start_matches("old(")
                    .trim_end_matches(')')
            ))
            .with_kind(ClickErrorKind::Type))
    }

    /// The data pointer of the Rust slice `expression` reads, `bytes`,
    /// `old(bytes)` or `at(point, bytes)`: `bytes.as_ptr()` read where the
    /// slice is. `None` for any other expression.
    pub(super) fn rust_slice_data(&self, expression: &SyntaxTerm) -> Option<SyntaxTerm> {
        match expression {
            SyntaxTerm::ProgramExpression(
                slice @ ProgramExpression::Variable(crate::kernel::BindingName::Named(name)),
            ) if self.is_rust_slice_name(name) => Some(SyntaxTerm::ProgramExpression(
                ProgramExpression::SliceData(Box::new(slice.clone())),
            )),
            SyntaxTerm::Old(inner) => Some(SyntaxTerm::Old(Box::new(self.rust_slice_data(inner)?))),
            SyntaxTerm::At {
                selector,
                expression,
            } => Some(SyntaxTerm::At {
                selector: selector.clone(),
                expression: Box::new(self.rust_slice_data(expression)?),
            }),
            _ => None,
        }
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
        // `&T` of an abstract type parameter is a pointer to one value of
        // it: the contract names the referent `*value`.
        if let Some(name) = self.peek_ident()
            && self.rust_abstract_type_parameters.contains(name)
            && !matches!(self.peek_next(), Some(Token::ColonColon))
        {
            let parameter = crate::kernel::TypeParameterName::intern(name);
            self.position += 1;
            return Ok(ParsedType {
                interface_type: InterfaceType::ParameterPointer(parameter),
                struct_name: None,
                struct_pointer: false,
                constant: false,
                pointee_constant: !mutable,
                reference: false,
            });
        }
        // `&dyn traits::Shape`, or `&T` for a crate trait's type parameter:
        // a value of a type the function does not know, whose fields it
        // cannot name.
        let dyn_trait = self.peek_ident() == Some("dyn");
        if dyn_trait {
            self.position += 1;
            self.expect_rust_path("trait name")?;
            self.parse_rust_type_arguments()?;
        }
        if dyn_trait
            || matches!(self.peek_ident(), Some(name) if self.rust_trait_type_parameters.contains(name))
                && !matches!(self.peek_next(), Some(Token::ColonColon))
        {
            if !dyn_trait {
                self.position += 1;
            }
            return Ok(ParsedType {
                interface_type: InterfaceType::Int32Pointer,
                struct_name: None,
                struct_pointer: false,
                constant: false,
                pointee_constant: !mutable,
                reference: false,
            });
        }
        // `&[T; N]` is the pointer to the array's first element. The length
        // is the type's, so the contract writes it: `views words[0..N]`.
        let array = self.peek() == Some(&Token::LBracket);
        if array {
            self.position += 1;
        }
        let spelling = self.expect_rust_type_name("type")?;
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
        // A reference to an enum, `&mut Option<u32>`, is a pointer to one
        // spec value, as a reference to a type parameter's value is.
        if !array && let Some(enum_type) = self.rust_enum_types.get(&spelling).copied() {
            return Ok(ParsedType {
                interface_type: InterfaceType::ParameterPointer(enum_type),
                struct_name: None,
                struct_pointer: false,
                constant: false,
                pointee_constant: !mutable,
                reference: false,
            });
        }
        Ok(match rust_scalar_type(&spelling) {
            Some(scalar) => {
                let Some(interface_type) = scalar.pointer_type() else {
                    return Err(self.error(format!(
                        "a reference to `{spelling}` is not supported in a `fn` signature"
                    )));
                };
                ParsedType {
                    interface_type,
                    struct_name: None,
                    struct_pointer: false,
                    constant: false,
                    pointee_constant: !mutable,
                    reference: false,
                }
            }
            None => ParsedType {
                interface_type: InterfaceType::Int32Pointer,
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
    /// A function-pointer type, `fn(i32, u32) -> bool`, of scalar parameters
    /// and a scalar or unit result.
    /// A `&dyn Fn(i32) -> i32`, a callable value of the same type as the
    /// `fn` pointer of its parameters and result.
    fn parse_rust_dyn_fn_type(
        &mut self,
    ) -> Result<
        (
            InterfaceType,
            crate::languages::interface::CallbackInterface,
        ),
        ClickError,
    > {
        self.expect(Token::Amp)?;
        self.skip_rust_lifetime();
        self.expect_ident_spelling("dyn")?;
        if self.peek_ident() != Some("Fn") {
            return Err(self.error("a `&dyn` parameter is supported only for `Fn(...) -> ...`"));
        }
        self.position += 1;
        self.parse_rust_callable_signature()
    }

    /// An `impl Fn(i32) -> i32`, a callable value as `&dyn Fn` is.
    fn parse_rust_impl_fn_type(
        &mut self,
    ) -> Result<
        (
            InterfaceType,
            crate::languages::interface::CallbackInterface,
        ),
        ClickError,
    > {
        self.expect_ident_spelling("impl")?;
        if self.peek_ident() != Some("Fn") {
            return Err(self.error("an `impl` parameter is supported only for `Fn(...) -> ...`"));
        }
        self.position += 1;
        self.parse_rust_callable_signature()
    }

    fn parse_rust_fn_pointer_type(
        &mut self,
    ) -> Result<
        (
            InterfaceType,
            crate::languages::interface::CallbackInterface,
        ),
        ClickError,
    > {
        self.expect_ident_spelling("fn")?;
        self.parse_rust_callable_signature()
    }

    /// The parameter list and result of a callable type, after `fn` or `Fn`.
    fn parse_rust_callable_signature(
        &mut self,
    ) -> Result<
        (
            InterfaceType,
            crate::languages::interface::CallbackInterface,
        ),
        ClickError,
    > {
        self.expect(Token::LParen)?;
        let mut parameters = Vec::new();
        while self.peek() != Some(&Token::RParen) {
            let parsed = self.parse_rust_type()?;
            if parsed.interface_type == InterfaceType::Void
                || parsed.interface_type.is_pointer()
                || parsed.reference
            {
                return Err(self.error("a `fn` pointer type takes scalar parameters"));
            }
            parameters.push(crate::languages::interface::CallbackParameter::new(
                parsed.interface_type,
                None,
                false,
            ));
            if self.peek() != Some(&Token::Comma) {
                break;
            }
            self.position += 1;
        }
        self.expect(Token::RParen)?;
        let result = if self.peek() == Some(&Token::Arrow) {
            self.position += 1;
            let parsed = self.parse_rust_type()?;
            if parsed.interface_type.is_pointer() || parsed.reference {
                return Err(self.error("a `fn` pointer type returns a scalar or `()`"));
            }
            parsed.interface_type
        } else {
            InterfaceType::Void
        };
        let signature =
            crate::languages::interface::CallbackInterface::new(result, None, parameters, false);
        Ok((signature.pointer_type(), signature))
    }

    pub(super) fn parse_rust_type(&mut self) -> Result<ParsedType, ClickError> {
        let scalar = |interface_type| ParsedType {
            interface_type,
            struct_name: None,
            struct_pointer: false,
            constant: false,
            pointee_constant: false,
            reference: false,
        };
        if self.peek() == Some(&Token::LParen) && self.peek_next() == Some(&Token::RParen) {
            self.position += 2;
            return Ok(scalar(InterfaceType::Void));
        }
        // A tuple, `(A, B)`, is a Click type, but a program value of one is
        // not supported yet (`design/tuples.md`, step T2).
        if self.peek() == Some(&Token::LParen) {
            let at = self.error_context();
            let components =
                self.parse_tuple_components(|parser| parser.parse_rust_type().map(|_| ()))?;
            return Err(self.error_at(
                at,
                format!(
                    "a tuple of {} components is not supported as a program value yet: a `fn` \
                     signature cannot take or return a tuple, though a contract or a pure \
                     function may use one",
                    components.len()
                ),
            ));
        }
        if self.peek() == Some(&Token::Amp) {
            return self.parse_rust_reference_type();
        }
        if self.peek() == Some(&Token::LBracket) {
            return Err(self.error(
                "an array or slice passed by value in a `fn` signature is not supported; the Rust importer refuses it",
            ));
        }
        if let Some(name) = self.peek_ident()
            && self.rust_abstract_type_parameters.contains(name)
            && self.peek_next() != Some(&Token::ColonColon)
        {
            let parameter = crate::kernel::TypeParameterName::intern(name);
            self.position += 1;
            return Ok(scalar(InterfaceType::Parameter(parameter)));
        }
        if let Some(name) = self.peek_ident()
            && let Some(enum_type) = self.rust_enum_types.get(name).copied()
            && self.peek_next() != Some(&Token::ColonColon)
        {
            self.position += 1;
            return Ok(scalar(InterfaceType::Parameter(enum_type)));
        }
        // A box of a crate struct, `Box<crate::S>`, is its address, and an
        // option of one, `Option<Box<crate::S>>`, the address or null.
        let word = |offset: usize, expected: &str| matches!(self.tokens.get(self.position + offset), Some(Token::Ident(w)) if w == expected);
        let less =
            |offset: usize| self.tokens.get(self.position + offset) == Some(&Token::LessThan);
        let boxed = if word(0, "Box") && less(1) {
            Some(false)
        } else if word(0, "Option") && less(1) && word(2, "Box") && less(3) {
            Some(true)
        } else {
            None
        };
        if let Some(option) = boxed {
            self.position += if option { 4 } else { 2 };
            let spelling = self.expect_rust_type_name("boxed type")?;
            for _ in 0..1 + usize::from(option) {
                if self.peek() == Some(&Token::ShiftRight) {
                    self.tokens[self.position] = Token::GreaterThan;
                } else {
                    self.expect(Token::GreaterThan)?;
                }
            }
            return Ok(ParsedType {
                interface_type: InterfaceType::Int32Pointer,
                struct_name: Some(spelling),
                struct_pointer: true,
                constant: false,
                pointee_constant: false,
                reference: false,
            });
        }
        let spelling = self.expect_rust_type_name("type")?;
        // An instance of a library enum, `Option<u32>`, by its importer name.
        if let Some(enum_type) = self.rust_enum_types.get(&spelling).copied() {
            return Ok(scalar(InterfaceType::Parameter(enum_type)));
        }
        Ok(match rust_scalar_type(&spelling) {
            Some(interface_type) => scalar(interface_type),
            None => ParsedType {
                interface_type: InterfaceType::Int32Pointer,
                struct_name: Some(spelling),
                struct_pointer: false,
                constant: false,
                pointee_constant: false,
                reference: false,
            },
        })
    }

    /// `&[T]`, `&mut [T]` or `&str` of a scalar `T` where a Rust sidecar
    /// writes a value's type: a pure function's parameter or result, a
    /// theorem binder, an enum field or a type argument such as
    /// `Option<&[u8]>`. It is the built-in slice type, `Slice<T>` or `Str`,
    /// one value (`design/rust-slice-values.md`), which is returned.
    pub(super) fn take_rust_slice_value_type(
        &mut self,
    ) -> Result<Option<InterfaceType>, ClickError> {
        if !self.verifies_rust() || self.peek() != Some(&Token::Amp) {
            return Ok(None);
        }
        let start = self.position;
        let lifetime = usize::from(matches!(self.peek_next(), Some(Token::Lifetime(_))));
        let string = self.tokens.get(start + 1 + lifetime) == Some(&Token::Ident("str".into()));
        let Some(parsed) = self.parse_rust_slice_type()? else {
            self.position = start;
            return Ok(None);
        };
        self.implied_library_modules.insert(super::SLICE_MODULE);
        if string {
            self.implied_library_modules.insert(super::STR_MODULE);
            return Ok(Some(InterfaceType::Slice(crate::kernel::SliceElement::Str)));
        }
        let slice = crate::kernel::SliceElement::of_thin_pointer_type(
            parsed.interface_type.to_kernel_type(),
        )
        .ok_or_else(|| self.error("a slice's element type must be a scalar"))?;
        Ok(Some(InterfaceType::Slice(slice)))
    }

    /// The type of a Click binder in a Rust sidecar, spelled as Rust does:
    /// a scalar (`u8`, `i32`, `usize`, `bool`, ...) or a raw pointer to one
    /// or to a crate struct, `*const T` or `*mut T`. A pure function, predicate or theorem takes
    /// values: a fn's slice `bytes` passes the pointer to its first element,
    /// so a function over its bytes takes `bytes: *const u8` and a `usize`
    /// length. `None`, with nothing consumed, for anything else, which the
    /// shared spellings read.
    #[inline(never)]
    pub(super) fn parse_rust_click_type(&mut self) -> Result<Option<ParsedType>, ClickError> {
        if !self.verifies_rust() {
            return Ok(None);
        }
        if self.peek() == Some(&Token::Amp) {
            return Err(self.error(
                "a pure function, predicate or theorem takes values, not references; write a pointer `*const T` or `*mut T`, or a slice `&[T]`",
            ));
        }
        let scalar = |interface_type, pointee_constant| ParsedType {
            interface_type,
            struct_name: None,
            struct_pointer: false,
            constant: false,
            pointee_constant,
            reference: false,
        };
        if self.peek() == Some(&Token::Star) {
            let mutable = match self.peek_next() {
                Some(Token::Ident(word)) if word == "const" => false,
                Some(Token::Ident(word)) if word == "mut" => true,
                _ => return Err(self.error("a Rust pointer type is `*const T` or `*mut T`")),
            };
            self.position += 2;
            // A raw pointer to a value of an abstract type parameter,
            // `*mut T`, as a `fn` signature reads `&mut T`.
            if let Some(name) = self.peek_ident()
                && self.rust_abstract_type_parameters.contains(name)
                && self.peek_next() != Some(&Token::ColonColon)
            {
                let parameter = crate::kernel::TypeParameterName::intern(name);
                self.position += 1;
                return Ok(Some(ParsedType {
                    interface_type: InterfaceType::ParameterPointer(parameter),
                    struct_name: None,
                    struct_pointer: false,
                    constant: false,
                    pointee_constant: !mutable,
                    reference: false,
                }));
            }
            // A raw pointer to a crate struct, `*const crate::S`, as a
            // `fn` signature reads its references to one.
            if self
                .peek_ident()
                .is_some_and(|word| rust_scalar_type(word).is_none())
            {
                let spelling = self.expect_rust_type_name("pointee type")?;
                return Ok(Some(ParsedType {
                    interface_type: InterfaceType::Int32Pointer,
                    struct_name: Some(spelling),
                    struct_pointer: true,
                    constant: false,
                    pointee_constant: !mutable,
                    reference: false,
                }));
            }
            let spelling = self.expect_ident("pointee type")?;
            let Some(interface_type) = rust_scalar_type(&spelling)
                .filter(|pointee| *pointee != InterfaceType::Bool)
                .and_then(InterfaceType::pointer_type)
            else {
                return Err(self.error(format!(
                    "a pointer to `{spelling}` is not a Click binder type; a Rust sidecar's binder may point at an integer or float scalar"
                )));
            };
            return Ok(Some(scalar(interface_type, !mutable)));
        }
        // A Rust function's abstract type parameter is the C type its values
        // have in the program, so `Option<T>` names the program's instance.
        if let Some(name) = self.peek_ident()
            && self.rust_abstract_type_parameters.contains(name)
            && self.peek_next() != Some(&Token::ColonColon)
        {
            let parameter = crate::kernel::TypeParameterName::intern(name);
            self.position += 1;
            return Ok(Some(scalar(InterfaceType::Parameter(parameter), false)));
        }
        let Some(interface_type) = self.peek_ident().and_then(rust_scalar_type) else {
            return Ok(None);
        };
        self.position += 1;
        Ok(Some(scalar(interface_type, false)))
    }

    /// `expr as T` in a Rust sidecar is the scalar cast `(T)expr`. It binds
    /// tighter than a binary operator and looser than a unary one, as in
    /// Rust. `as` followed by anything but a scalar type is left for the
    /// clause that owns it (for example `verifying "f.c" as f`).
    #[inline(never)]
    /// The casts after a unary operand, `e as T`, left to right. Click's
    /// cast is written after its operand: an integer target bare,
    /// `x as uint32`, a pointer target parenthesized, `p as (uint8 *)` or
    /// `p as (struct node *)`. A Rust source's sidecar also writes Rust's
    /// scalar names, `x as u32`. An `as` followed by anything else is left
    /// for the clause that owns it (for example `verifying "f.c" as f`).
    pub(super) fn parse_casts(
        &mut self,
        mut operand: SyntaxTerm,
    ) -> Result<SyntaxTerm, ClickError> {
        loop {
            if self.peek_ident() != Some("as") {
                return Ok(operand);
            }
            match self.peek_next() {
                Some(Token::Ident(name)) if click_numeric_cast_type(name).is_some() => {
                    let target_type = click_numeric_cast_type(name).expect("checked above");
                    self.position += 2;
                    operand = self.lower_click_cast(target_type, operand)?;
                    continue;
                }
                // Click's untyped pointer is one name, so its cast target is
                // bare, `p as Pointer`, as a numeric one is.
                Some(Token::Ident(name)) if name == UNTYPED_POINTER_TYPE => {
                    self.position += 2;
                    operand = self.lower_click_cast(ProgramType::Pointer, operand)?;
                    continue;
                }
                Some(Token::LParen) => {
                    self.position += 1;
                    if let Some(cast) = self.peek_struct_pointer_cast() {
                        self.consume_struct_pointer_cast(&cast)?;
                        operand = self.lower_struct_pointer_cast(cast, operand)?;
                        continue;
                    }
                    if self.starts_contract_scalar_cast() {
                        self.position += 1;
                        let (target_type, constant, volatile) = self.parse_click_cast_type()?;
                        if !target_type.is_pointer() {
                            return Err(self.error(
                                "a numeric cast target is written without parentheses: `e as uint32`; only a pointer target is parenthesized, `e as (uint8 *)`",
                            ));
                        }
                        self.expect(Token::RParen)?;
                        operand = self.lower_qualified_click_cast(
                            target_type,
                            constant,
                            volatile,
                            operand,
                        )?;
                        continue;
                    }
                    self.position -= 1;
                    return Ok(operand);
                }
                Some(Token::Ident(name))
                    if self.verifies_rust() && rust_scalar_type(name).is_some() => {}
                _ => return Ok(operand),
            }
            self.position += 1;
            let target = self.expect_ident("type")?;
            if target == "bool" {
                return Err(self
                    .error("Rust does not cast to `bool`; compare with zero instead, `(x != 0)`"));
            }
            let target_type = rust_scalar_type(&target)
                .expect("checked above")
                .to_kernel_type();
            // An integer cast consumes the value its operand observes, as a
            // Click-spelled integer cast does: the operand may read
            // historical `old(...)` and `at(...)` values, or be a value of
            // the Click library such as `iter.len()`. Other targets stay
            // current C expressions.
            let integer_target = matches!(
                target_type,
                ProgramType::Int8
                    | ProgramType::Int16
                    | ProgramType::Int32
                    | ProgramType::UInt8
                    | ProgramType::UInt16
                    | ProgramType::UInt32
                    | ProgramType::Int64
                    | ProgramType::UInt64
                    | ProgramType::Int128
                    | ProgramType::UInt128
            );
            let expression = match contract_expression_as_program_expression(&operand) {
                Some(expression) => expression,
                None if integer_target => ProgramExpression::Value(int32(0)),
                None => return Err(self.error("scalar cast expects a current C expression; put old(...) around the whole cast for an entry-state value")),
            };
            // Keep the same operand-bearing representation as a C-style
            // scalar cast, including its proof-expression identity.
            operand = SyntaxTerm::CUnary {
                operand: Box::new(operand),
                lowered: ProgramExpression::Cast {
                    expression: Box::new(expression),
                    target_type,
                    integer_mode: crate::kernel::IntegerCastMode::CConversion,
                    pointee_struct: None,
                    pointee_struct_size: None,
                    pointee_volatile: false,
                    pointee_constant: false,
                    explicit_qualification: false,
                },
            };
        }
    }
}

/// The name of Click's untyped pointer type, [`ProgramType::Pointer`].
pub(super) const UNTYPED_POINTER_TYPE: &str = "Pointer";

/// The numeric type a bare Click cast target names, `x as uint32` or `x as float`.
pub(super) fn click_numeric_cast_type(name: &str) -> Option<ProgramType> {
    Some(match name {
        "float" => ProgramType::Float32,
        "double" => ProgramType::Float64,
        "int8" => ProgramType::Int8,
        "uint8" => ProgramType::UInt8,
        "int16" => ProgramType::Int16,
        "uint16" => ProgramType::UInt16,
        "int32" => ProgramType::Int32,
        "uint32" => ProgramType::UInt32,
        "int64" => ProgramType::Int64,
        "uint64" => ProgramType::UInt64,
        "int128" => ProgramType::Int128,
        "uint128" => ProgramType::UInt128,
        _ => return None,
    })
}

/// The C type a Rust scalar type name denotes.
impl Parser {}

pub(super) fn rust_scalar_type(name: &str) -> Option<InterfaceType> {
    Some(match name {
        "bool" => InterfaceType::Bool,
        "i8" => InterfaceType::Int8,
        "i16" => InterfaceType::Int16,
        "i32" => InterfaceType::Int32,
        "i64" | "isize" => InterfaceType::Int64(LongRank::Long),
        "i128" => InterfaceType::Int128,
        "u8" => InterfaceType::UInt8,
        "u16" => InterfaceType::UInt16,
        "u32" => InterfaceType::UInt32,
        "u64" | "usize" => InterfaceType::UInt64(LongRank::Long),
        "u128" => InterfaceType::UInt128,
        "f32" => InterfaceType::Float32,
        "f64" => InterfaceType::Float64,
        _ => return None,
    })
}

pub(super) fn rust_signature_hint(parsed: &ParsedFunctionSignature) -> Option<String> {
    let signature = &parsed.signature;
    if !parsed.struct_params.is_empty() || parsed.return_struct_name.is_some() {
        return None;
    }
    let scalar_name = |interface_type| {
        [
            "bool", "i8", "i16", "i32", "isize", "i128", "u8", "u16", "u32", "usize", "u128",
            "f32", "f64",
        ]
        .into_iter()
        .find(|name| rust_scalar_type(name) == Some(interface_type))
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
        let spelling = if let Some(pointee) = parameter.interface_type().pointee_type() {
            let reference = if parameter.pointee_constant {
                "&"
            } else {
                "&mut "
            };
            let base = scalar_name(pointee)?;
            let slice = signature.parameters.get(index + 1).is_some_and(|length| {
                // This diagnostic is for rejected C-shaped Rust signatures.
                // Recognize the old spelling only to suggest its replacement.
                length.name.strip_suffix("_len") == Some(parameter.name.as_str())
                    && matches!(length.interface_type(), InterfaceType::UInt64(_))
            });
            if slice {
                index += 1;
                format!("{reference}[{base}]")
            } else {
                format!("{reference}{base}")
            }
        } else {
            scalar_name(parameter.interface_type())?.to_string()
        };
        parameters.push(format!("{}: {spelling}", parameter.name));
        index += 1;
    }
    let return_type = if signature.return_type == InterfaceType::Void {
        String::new()
    } else {
        format!(" -> {}", scalar_name(signature.return_type)?)
    };
    Some(format!("fn {name}({}){return_type}", parameters.join(", ")))
}
