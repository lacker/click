use super::*;

impl CParameter {
    pub fn new(name: impl Into<String>, c_type: CType) -> Self {
        Self {
            name: name.into(),
            c_type,
            aggregate_layout: None,
            volatile: false,
            pointee_volatile: false,
            constant: false,
            pointee_constant: false,
        }
    }

    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn c_type(&self) -> CType {
        self.c_type
    }

    pub fn aggregate_layout(&self) -> Option<&CAggregateLayout> {
        self.aggregate_layout.as_ref()
    }

    pub fn is_volatile(&self) -> bool {
        self.volatile
    }

    pub fn pointee_is_volatile(&self) -> bool {
        self.pointee_volatile
    }

    pub fn is_constant(&self) -> bool {
        self.constant
    }

    pub fn pointee_is_constant(&self) -> bool {
        self.pointee_constant
    }

    pub fn with_volatile(mut self, volatile: bool) -> Self {
        self.volatile = volatile;
        self
    }

    pub fn with_pointee_volatile(mut self, pointee_volatile: bool) -> Self {
        self.pointee_volatile = pointee_volatile;
        self
    }

    pub fn with_constant(mut self, constant: bool) -> Self {
        self.constant = constant;
        self
    }

    pub fn with_pointee_constant(mut self, pointee_constant: bool) -> Self {
        self.pointee_constant = pointee_constant;
        self
    }

    pub fn with_aggregate_layout(mut self, layout: CAggregateLayout) -> Self {
        self.aggregate_layout = Some(layout);
        self
    }
}

impl CGlobal {
    pub fn new(name: impl Into<String>, c_type: CType, initial_value: CValue) -> Self {
        let name = name.into();
        Self::new_with_kernel_name(name.clone(), name, c_type, initial_value)
    }

    pub fn new_with_kernel_name(
        source_name: impl Into<String>,
        kernel_name: impl Into<String>,
        c_type: CType,
        initial_value: CValue,
    ) -> Self {
        assert!(
            matches!(
                c_type,
                CType::Int16
                    | CType::Int32
                    | CType::UInt8
                    | CType::UInt16
                    | CType::UInt32
                    | CType::Float32
                    | CType::Float64
                    | CType::Int16Pointer
                    | CType::UInt16Pointer
                    | CType::Int32Pointer
                    | CType::UInt8Pointer
                    | CType::UInt32Pointer
                    | CType::Int64Pointer
                    | CType::UInt64Pointer
                    | CType::Float32Pointer
                    | CType::Float64Pointer
                    | CType::Int16PointerPointer
                    | CType::UInt16PointerPointer
                    | CType::Int32PointerPointer
                    | CType::UInt8PointerPointer
                    | CType::UInt32PointerPointer
                    | CType::Int64PointerPointer
                    | CType::UInt64PointerPointer
                    | CType::Float32PointerPointer
                    | CType::Float64PointerPointer
            ),
            "C globals currently support scalar integer, floating-point, and pointer types"
        );
        assert_eq!(
            initial_value.c_type(),
            c_type,
            "C global initializer must match its declared type"
        );
        Self {
            source_name: source_name.into(),
            kernel_name: kernel_name.into(),
            c_type,
            initial_value,
            volatile: false,
            constant: false,
        }
    }

    pub fn name(&self) -> &str {
        &self.source_name
    }

    pub fn kernel_name(&self) -> &str {
        &self.kernel_name
    }

    pub fn c_type(&self) -> CType {
        self.c_type
    }

    pub fn initial_value(&self) -> &CValue {
        &self.initial_value
    }

    pub fn is_volatile(&self) -> bool {
        self.volatile
    }

    pub fn with_volatile(mut self, volatile: bool) -> Self {
        self.volatile = volatile;
        self
    }

    pub fn is_constant(&self) -> bool {
        self.constant
    }

    pub fn with_constant(mut self, constant: bool) -> Self {
        self.constant = constant;
        self
    }
}

impl CGlobalArray {
    pub fn new_with_kernel_name(
        source_name: impl Into<String>,
        kernel_name: impl Into<String>,
        element_type: CType,
        length: u32,
        initial_values: Vec<CValue>,
    ) -> Self {
        assert!(
            matches!(
                element_type,
                CType::Int16 | CType::Int32 | CType::UInt8 | CType::UInt16 | CType::UInt32
            ),
            "C global arrays currently support scalar integer element types only"
        );
        assert!(length > 0, "C global arrays must have positive length");
        assert_eq!(
            initial_values.len(),
            length as usize,
            "C global array initializer must cover its declared length"
        );
        assert!(
            initial_values
                .iter()
                .all(|value| value.c_type() == element_type),
            "C global array initializers must match their declared element type"
        );
        Self {
            source_name: source_name.into(),
            kernel_name: kernel_name.into(),
            element_type,
            length,
            initial_values,
            constant: false,
        }
    }

    pub fn name(&self) -> &str {
        &self.source_name
    }

    pub fn kernel_name(&self) -> &str {
        &self.kernel_name
    }

    pub fn element_type(&self) -> CType {
        self.element_type
    }

    pub fn length(&self) -> u32 {
        self.length
    }

    pub fn initial_values(&self) -> &[CValue] {
        &self.initial_values
    }

    pub fn is_constant(&self) -> bool {
        self.constant
    }

    pub fn with_constant(mut self, constant: bool) -> Self {
        self.constant = constant;
        self
    }
}

impl CGlobalAggregate {
    pub fn new(
        source_name: impl Into<String>,
        kernel_name: impl Into<String>,
        layout: CAggregateLayout,
        initializers: Vec<CAggregateInitializer>,
    ) -> Self {
        assert!(
            layout.size_bytes() > 0,
            "C global aggregates must have positive size"
        );
        assert!(
            !layout.fields().is_empty(),
            "C global aggregates must have at least one modeled field"
        );
        Self {
            source_name: source_name.into(),
            kernel_name: kernel_name.into(),
            layout,
            initializers,
            constant: false,
        }
    }

    pub fn source_name(&self) -> &str {
        &self.source_name
    }

    pub fn kernel_name(&self) -> &str {
        &self.kernel_name
    }

    pub fn layout(&self) -> &CAggregateLayout {
        &self.layout
    }

    pub fn initializers(&self) -> &[CAggregateInitializer] {
        &self.initializers
    }

    pub fn is_constant(&self) -> bool {
        self.constant
    }

    pub fn with_constant(mut self, constant: bool) -> Self {
        self.constant = constant;
        self
    }
}

impl CGlobalAggregateArray {
    pub fn new(
        source_name: impl Into<String>,
        kernel_name: impl Into<String>,
        layout: CAggregateLayout,
        length: u32,
        initializers: Vec<CAggregateInitializer>,
    ) -> Self {
        assert!(
            length > 0,
            "C global aggregate arrays must have positive length"
        );
        assert!(
            layout.size_bytes() > 0,
            "C global aggregate arrays must have positive element size"
        );
        assert!(
            !layout.fields().is_empty(),
            "C global aggregate arrays must have at least one modeled field"
        );
        Self {
            source_name: source_name.into(),
            kernel_name: kernel_name.into(),
            layout,
            length,
            initializers,
            constant: false,
        }
    }

    pub fn source_name(&self) -> &str {
        &self.source_name
    }

    pub fn kernel_name(&self) -> &str {
        &self.kernel_name
    }

    pub fn layout(&self) -> &CAggregateLayout {
        &self.layout
    }

    pub fn length(&self) -> u32 {
        self.length
    }

    pub fn initializers(&self) -> &[CAggregateInitializer] {
        &self.initializers
    }

    pub fn is_constant(&self) -> bool {
        self.constant
    }

    pub fn with_constant(mut self, constant: bool) -> Self {
        self.constant = constant;
        self
    }
}

impl CStaticLocal {
    pub fn new(
        source_name: impl Into<String>,
        kernel_name: impl Into<String>,
        c_type: CType,
        initial_value: CValue,
    ) -> Self {
        assert!(
            matches!(
                c_type,
                CType::Int16
                    | CType::Int32
                    | CType::UInt8
                    | CType::UInt16
                    | CType::UInt32
                    | CType::Float32
                    | CType::Float64
            ),
            "C static locals currently support scalar integer and floating-point types only"
        );
        assert_eq!(
            initial_value.c_type(),
            c_type,
            "C static local initializer must match its declared type"
        );
        Self {
            source_name: source_name.into(),
            kernel_name: kernel_name.into(),
            c_type,
            initial_value,
            volatile: false,
            constant: false,
        }
    }

    pub fn source_name(&self) -> &str {
        &self.source_name
    }

    pub fn kernel_name(&self) -> &str {
        &self.kernel_name
    }

    pub fn c_type(&self) -> CType {
        self.c_type
    }

    pub fn initial_value(&self) -> &CValue {
        &self.initial_value
    }

    pub fn is_volatile(&self) -> bool {
        self.volatile
    }

    pub fn with_volatile(mut self, volatile: bool) -> Self {
        self.volatile = volatile;
        self
    }

    pub fn is_constant(&self) -> bool {
        self.constant
    }

    pub fn with_constant(mut self, constant: bool) -> Self {
        self.constant = constant;
        self
    }
}

impl CStaticArray {
    pub fn new(
        source_name: impl Into<String>,
        kernel_name: impl Into<String>,
        element_type: CType,
        length: u32,
        initial_values: Vec<CValue>,
    ) -> Self {
        assert!(
            matches!(
                element_type,
                CType::Int16 | CType::Int32 | CType::UInt8 | CType::UInt16 | CType::UInt32
            ),
            "C static local arrays currently support scalar integer element types only"
        );
        assert!(
            length > 0,
            "C static local arrays must have positive length"
        );
        assert_eq!(
            initial_values.len(),
            length as usize,
            "C static local array initializer must cover its declared length"
        );
        assert!(
            initial_values
                .iter()
                .all(|value| value.c_type() == element_type),
            "C static local array initializers must match their declared element type"
        );
        Self {
            source_name: source_name.into(),
            kernel_name: kernel_name.into(),
            element_type,
            length,
            initial_values,
            constant: false,
        }
    }

    pub fn source_name(&self) -> &str {
        &self.source_name
    }

    pub fn kernel_name(&self) -> &str {
        &self.kernel_name
    }

    pub fn element_type(&self) -> CType {
        self.element_type
    }

    pub fn length(&self) -> u32 {
        self.length
    }

    pub fn initial_values(&self) -> &[CValue] {
        &self.initial_values
    }

    pub fn is_constant(&self) -> bool {
        self.constant
    }

    pub fn with_constant(mut self, constant: bool) -> Self {
        self.constant = constant;
        self
    }
}

impl CStaticAggregate {
    pub fn new(
        source_name: impl Into<String>,
        kernel_name: impl Into<String>,
        layout: CAggregateLayout,
        initializers: Vec<CAggregateInitializer>,
    ) -> Self {
        assert!(
            layout.size_bytes() > 0,
            "C static aggregates must have positive size"
        );
        assert!(
            !layout.fields().is_empty(),
            "C static aggregates must have at least one modeled field"
        );
        Self {
            source_name: source_name.into(),
            kernel_name: kernel_name.into(),
            layout,
            initializers,
            constant: false,
        }
    }

    pub fn source_name(&self) -> &str {
        &self.source_name
    }

    pub fn kernel_name(&self) -> &str {
        &self.kernel_name
    }

    pub fn layout(&self) -> &CAggregateLayout {
        &self.layout
    }

    pub fn initializers(&self) -> &[CAggregateInitializer] {
        &self.initializers
    }

    pub fn is_constant(&self) -> bool {
        self.constant
    }

    pub fn with_constant(mut self, constant: bool) -> Self {
        self.constant = constant;
        self
    }
}

impl CStaticAggregateArray {
    pub fn new(
        source_name: impl Into<String>,
        kernel_name: impl Into<String>,
        layout: CAggregateLayout,
        length: u32,
        initializers: Vec<CAggregateInitializer>,
    ) -> Self {
        assert!(
            length > 0,
            "C static aggregate arrays must have positive length"
        );
        assert!(
            layout.size_bytes() > 0,
            "C static aggregate arrays must have positive element size"
        );
        assert!(
            !layout.fields().is_empty(),
            "C static aggregate arrays must have at least one modeled field"
        );
        Self {
            source_name: source_name.into(),
            kernel_name: kernel_name.into(),
            layout,
            length,
            initializers,
            constant: false,
        }
    }

    pub fn source_name(&self) -> &str {
        &self.source_name
    }

    pub fn kernel_name(&self) -> &str {
        &self.kernel_name
    }

    pub fn layout(&self) -> &CAggregateLayout {
        &self.layout
    }

    pub fn length(&self) -> u32 {
        self.length
    }

    pub fn initializers(&self) -> &[CAggregateInitializer] {
        &self.initializers
    }

    pub fn is_constant(&self) -> bool {
        self.constant
    }

    pub fn with_constant(mut self, constant: bool) -> Self {
        self.constant = constant;
        self
    }
}

impl CStringLiteral {
    pub fn new(name: impl Into<String>, bytes: Vec<u8>) -> Self {
        assert_eq!(
            bytes.last(),
            Some(&0),
            "C string literals require a NUL terminator"
        );
        Self {
            name: name.into(),
            bytes,
        }
    }

    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn bytes(&self) -> &[u8] {
        &self.bytes
    }
}

impl CFunction {
    pub fn new(
        return_type: CType,
        name: impl Into<String>,
        parameters: Vec<CParameter>,
        body: CStatement,
    ) -> Self {
        Self {
            return_type,
            return_aggregate_layout: None,
            name: name.into(),
            inline_body: false,
            parameters,
            source_body: body.clone(),
            body,
            resource_requires: Vec::new(),
            resource_ensures: Vec::new(),
            resource_constructors: Vec::new(),
            contract_requires: Vec::new(),
            contract_ensures: Vec::new(),
            contract_mutable: Vec::new(),
            contract_effect_claim_required: false,
            contract_claims: Vec::new(),
            opaque_contract_supported: true,
            composite_resource_definitions: Vec::new(),
            predicate_unfoldings: Vec::new(),
            global_variables: Vec::new(),
            global_arrays: Vec::new(),
            static_variables: Vec::new(),
            static_storage: std::sync::Arc::new(CFunctionStaticStorage {
                static_arrays: Vec::new(),
                global_aggregates: Vec::new(),
                global_aggregate_arrays: Vec::new(),
                static_aggregates: Vec::new(),
                static_aggregate_arrays: Vec::new(),
            }),
            string_literals: Vec::new(),
        }
    }

    pub fn with_global_variables(mut self, global_variables: Vec<CGlobal>) -> Self {
        self.global_variables = global_variables;
        self
    }

    pub fn with_global_arrays(mut self, global_arrays: Vec<CGlobalArray>) -> Self {
        self.global_arrays = global_arrays;
        self
    }

    pub fn with_global_aggregates(mut self, global_aggregates: Vec<CGlobalAggregate>) -> Self {
        let mut static_storage = (*self.static_storage).clone();
        static_storage.global_aggregates = global_aggregates;
        self.static_storage = std::sync::Arc::new(static_storage);
        self
    }

    pub fn with_global_aggregate_arrays(
        mut self,
        global_aggregate_arrays: Vec<CGlobalAggregateArray>,
    ) -> Self {
        let mut static_storage = (*self.static_storage).clone();
        static_storage.global_aggregate_arrays = global_aggregate_arrays;
        self.static_storage = std::sync::Arc::new(static_storage);
        self
    }

    pub fn with_static_variables(mut self, static_variables: Vec<CStaticLocal>) -> Self {
        self.static_variables = static_variables;
        self
    }

    pub fn with_static_arrays(mut self, static_arrays: Vec<CStaticArray>) -> Self {
        let mut static_storage = (*self.static_storage).clone();
        static_storage.static_arrays = static_arrays;
        self.static_storage = std::sync::Arc::new(static_storage);
        self
    }

    pub fn with_static_aggregates(mut self, static_aggregates: Vec<CStaticAggregate>) -> Self {
        let mut static_storage = (*self.static_storage).clone();
        static_storage.static_aggregates = static_aggregates;
        self.static_storage = std::sync::Arc::new(static_storage);
        self
    }

    pub fn with_static_aggregate_arrays(
        mut self,
        static_aggregate_arrays: Vec<CStaticAggregateArray>,
    ) -> Self {
        let mut static_storage = (*self.static_storage).clone();
        static_storage.static_aggregate_arrays = static_aggregate_arrays;
        self.static_storage = std::sync::Arc::new(static_storage);
        self
    }

    pub fn with_string_literals(mut self, string_literals: Vec<CStringLiteral>) -> Self {
        self.string_literals = string_literals;
        self
    }

    pub fn with_source_body(mut self, source_body: CStatement) -> Self {
        self.source_body = source_body;
        self
    }

    pub fn with_resource_summary(
        mut self,
        requires: Vec<CResourceSpec>,
        ensures: Vec<CResourceSpec>,
    ) -> Self {
        self.resource_requires = requires;
        self.resource_ensures = ensures;
        self
    }

    pub fn with_resource_constructors(mut self, constructors: Vec<CResourceSpec>) -> Self {
        self.resource_constructors = constructors;
        self
    }

    pub fn with_contract(
        mut self,
        requires: Vec<SpecProposition>,
        ensures: Vec<SpecProposition>,
        mutable: Vec<CMemorySegment>,
        claims: Vec<CFunctionContractClaim>,
        opaque_supported: bool,
    ) -> Self {
        self.contract_requires = requires;
        self.contract_ensures = ensures;
        self.contract_mutable = mutable;
        self.contract_effect_claim_required = !self.contract_mutable.is_empty();
        self.contract_claims = claims;
        self.opaque_contract_supported = opaque_supported;
        self
    }

    /// Marks the mutable frame as inferred from consumed resource ownership.
    /// Such a frame is part of the resource transition, not an omitted
    /// function-level Effect claim. This narrow crate-level escape hatch is
    /// used by the surface lowering; external kernel callers retain the
    /// default requirement that a nonempty frame have an Effect claim.
    pub(crate) fn with_resource_derived_mutable_frame(mut self) -> Self {
        self.contract_effect_claim_required = false;
        self
    }

    pub fn with_composite_resource_definitions(
        mut self,
        definitions: Vec<CCompositeResourceDefinition>,
    ) -> Self {
        self.composite_resource_definitions = definitions;
        self
    }

    pub fn with_predicate_unfoldings(mut self, unfoldings: Vec<CPredicateUnfolding>) -> Self {
        self.predicate_unfoldings = unfoldings;
        self
    }

    pub fn return_type(&self) -> CType {
        self.return_type
    }

    pub fn return_aggregate_layout(&self) -> Option<&CAggregateLayout> {
        self.return_aggregate_layout.as_ref()
    }

    pub fn with_return_aggregate_layout(mut self, layout: CAggregateLayout) -> Self {
        self.return_aggregate_layout = Some(layout);
        self
    }

    pub fn name(&self) -> &str {
        &self.name
    }

    pub(crate) fn with_inline_body(mut self) -> Self {
        self.inline_body = true;
        self
    }

    pub(crate) fn has_inline_body(&self) -> bool {
        self.inline_body
    }

    pub fn parameters(&self) -> &[CParameter] {
        &self.parameters
    }

    pub fn global_variables(&self) -> &[CGlobal] {
        &self.global_variables
    }

    pub fn global_arrays(&self) -> &[CGlobalArray] {
        &self.global_arrays
    }

    pub fn global_aggregates(&self) -> &[CGlobalAggregate] {
        self.static_storage.global_aggregates.as_slice()
    }

    pub fn global_aggregate_arrays(&self) -> &[CGlobalAggregateArray] {
        self.static_storage.global_aggregate_arrays.as_slice()
    }

    pub fn static_variables(&self) -> &[CStaticLocal] {
        &self.static_variables
    }

    pub fn static_arrays(&self) -> &[CStaticArray] {
        self.static_storage.static_arrays.as_slice()
    }

    pub fn static_aggregates(&self) -> &[CStaticAggregate] {
        self.static_storage.static_aggregates.as_slice()
    }

    pub fn static_aggregate_arrays(&self) -> &[CStaticAggregateArray] {
        self.static_storage.static_aggregate_arrays.as_slice()
    }

    pub fn string_literals(&self) -> &[CStringLiteral] {
        &self.string_literals
    }

    pub(crate) fn function_pointer_type(&self) -> CType {
        CType::FunctionPointer(CType::function_pointer_signature(
            self.return_type,
            &self
                .parameters
                .iter()
                .map(CParameter::c_type)
                .collect::<Vec<_>>(),
        ))
    }

    pub fn body(&self) -> &CStatement {
        &self.body
    }

    pub fn source_body(&self) -> &CStatement {
        &self.source_body
    }

    pub fn resource_requires(&self) -> &[CResourceSpec] {
        &self.resource_requires
    }

    pub fn resource_ensures(&self) -> &[CResourceSpec] {
        &self.resource_ensures
    }

    pub fn resource_constructors(&self) -> &[CResourceSpec] {
        &self.resource_constructors
    }

    pub fn contract_requires(&self) -> &[SpecProposition] {
        &self.contract_requires
    }

    pub fn contract_ensures(&self) -> &[SpecProposition] {
        &self.contract_ensures
    }

    pub fn contract_mutable(&self) -> &[CMemorySegment] {
        &self.contract_mutable
    }

    pub(crate) fn contract_effect_claim_required(&self) -> bool {
        self.contract_effect_claim_required
    }

    pub fn contract_claims(&self) -> &[CFunctionContractClaim] {
        &self.contract_claims
    }

    pub fn opaque_contract_supported(&self) -> bool {
        self.opaque_contract_supported
    }

    pub fn composite_resource_definitions(&self) -> &[CCompositeResourceDefinition] {
        &self.composite_resource_definitions
    }

    pub fn predicate_unfoldings(&self) -> &[CPredicateUnfolding] {
        &self.predicate_unfoldings
    }
}

impl CPredicateUnfolding {
    pub fn new(predicate: SpecProposition, body: SpecProposition) -> Self {
        Self { predicate, body }
    }

    pub fn predicate(&self) -> &SpecProposition {
        &self.predicate
    }

    pub fn body(&self) -> &SpecProposition {
        &self.body
    }
}

impl CCompositeResourceDefinition {
    pub fn new(
        name: impl Into<String>,
        parameters: Vec<CParameter>,
        condition: Option<SpecProposition>,
        recursive: bool,
        contains: Vec<CResourceSpec>,
        facts: Vec<SpecProposition>,
    ) -> Self {
        Self {
            name: name.into(),
            parameters,
            condition,
            recursive,
            counted_population: false,
            contains,
            facts,
        }
    }

    pub fn counted_population(
        name: impl Into<String>,
        parameters: Vec<CParameter>,
        condition: Option<SpecProposition>,
        contains: Vec<CResourceSpec>,
        facts: Vec<SpecProposition>,
    ) -> Self {
        Self {
            name: name.into(),
            parameters,
            condition,
            recursive: false,
            counted_population: true,
            contains,
            facts,
        }
    }

    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn parameters(&self) -> &[CParameter] {
        &self.parameters
    }

    pub fn condition(&self) -> Option<&SpecProposition> {
        self.condition.as_ref()
    }

    pub fn is_recursive(&self) -> bool {
        self.recursive
    }

    pub fn is_counted_population(&self) -> bool {
        self.counted_population
    }

    pub fn needs_outcome_resource_transfer(&self) -> bool {
        self.recursive || self.counted_population
    }

    pub fn contains(&self) -> &[CResourceSpec] {
        &self.contains
    }

    pub fn facts(&self) -> &[SpecProposition] {
        &self.facts
    }
}

impl CFunctionContractClaim {
    pub fn body_safety() -> Self {
        Self {
            key: CFunctionContractClaimKey::BodySafety,
            target: CFunctionContractClaimTarget::BodySafety,
        }
    }

    pub fn effect(index: usize) -> Self {
        Self {
            key: CFunctionContractClaimKey::Effect(index),
            target: CFunctionContractClaimTarget::Effect,
        }
    }

    pub fn ensure_proposition(source_index: usize, contract_index: usize) -> Self {
        Self {
            key: CFunctionContractClaimKey::Ensure(source_index),
            target: CFunctionContractClaimTarget::EnsureProposition(contract_index),
        }
    }

    pub fn ensure_resource(source_index: usize, resource_index: usize) -> Self {
        Self {
            key: CFunctionContractClaimKey::Ensure(source_index),
            target: CFunctionContractClaimTarget::EnsureResource(resource_index),
        }
    }

    pub fn key(&self) -> &CFunctionContractClaimKey {
        &self.key
    }

    pub fn target(&self) -> &CFunctionContractClaimTarget {
        &self.target
    }
}

impl CLoopInvariantCheck {
    pub fn new(
        proposition: SpecProposition,
        entry_context: Option<String>,
        preservation_context: Option<String>,
    ) -> Self {
        Self {
            proposition,
            entry_context,
            preservation_context,
        }
    }

    pub fn proposition(&self) -> &SpecProposition {
        &self.proposition
    }

    pub fn entry_context(&self) -> Option<&str> {
        self.entry_context.as_deref()
    }

    pub fn preservation_context(&self) -> Option<&str> {
        self.preservation_context.as_deref()
    }
}

impl CLoopEffectCheck {
    pub fn new(effect: CLoopEffect, context: Option<String>) -> Self {
        Self {
            effect,
            span: CLoopEffectSpan::Step,
            context,
        }
    }

    pub fn new_with_span(
        effect: CLoopEffect,
        span: CLoopEffectSpan,
        context: Option<String>,
    ) -> Self {
        Self {
            effect,
            span,
            context,
        }
    }

    pub fn effect(&self) -> &CLoopEffect {
        &self.effect
    }

    pub fn span(&self) -> CLoopEffectSpan {
        self.span
    }

    pub fn context(&self) -> Option<&str> {
        self.context.as_deref()
    }
}

impl CMemorySegment {
    pub fn new(base: CExpression, start: CExpression, end: CExpression) -> Self {
        Self {
            base,
            start,
            end,
            element_width: 4,
            guard: None,
        }
    }

    pub fn with_element_width(mut self, element_width: u32) -> Self {
        self.element_width = element_width;
        self
    }

    pub fn element_width(&self) -> u32 {
        self.element_width
    }

    pub fn with_guard(mut self, guard: SpecProposition) -> Self {
        self.guard = Some(guard);
        self
    }

    pub fn guard(&self) -> Option<&SpecProposition> {
        self.guard.as_ref()
    }
}

impl CMemoryRange {
    pub fn new(base: Pointer, start: Bitvector32Term, end: Bitvector32Term) -> Self {
        Self::new_with_element_width(base, start, end, 4)
    }

    /// Constructs a range with an explicit logical element width.
    ///
    /// `new` remains the compatibility constructor for the historical
    /// int32-only kernel callers. New ranges produced from typed C input
    /// should use this constructor instead.
    pub(crate) fn new_with_element_width(
        base: Pointer,
        start: Bitvector32Term,
        end: Bitvector32Term,
        element_width: u32,
    ) -> Self {
        assert!(element_width > 0, "memory element width must be positive");
        Self {
            base,
            start,
            end,
            element_width,
        }
    }

    /// Returns this element-indexed range as a physical byte footprint.
    ///
    /// `CMemoryRange` deliberately keeps its public bounds in element units:
    /// those are the units used by resource clauses such as `p[0..n]`.
    /// Callers that need to compare the actual memory occupied by a range can
    /// use this bounded, derived view without introducing a second resource
    /// representation. The returned pointer is the first byte of the range;
    /// the second value is its byte length.
    pub(crate) fn byte_footprint(&self) -> (Pointer, Bitvector32Term) {
        let element_count = Bitvector32Term::subtract(self.end.clone(), self.start.clone());
        (
            self.base
                .offset_by_elements(self.start.clone(), self.element_width),
            Bitvector32Term::multiply(element_count, Bitvector32Term::Constant(self.element_width)),
        )
    }

    pub fn element_width(&self) -> u32 {
        self.element_width
    }

    /// Rebuilds a range with different bounds while preserving its element
    /// coordinate system.
    pub(crate) fn with_bounds(
        &self,
        base: Pointer,
        start: Bitvector32Term,
        end: Bitvector32Term,
    ) -> Self {
        Self::new_with_element_width(base, start, end, self.element_width)
    }

    pub fn base(&self) -> &Pointer {
        &self.base
    }

    pub fn start(&self) -> &Bitvector32Term {
        &self.start
    }

    pub fn end(&self) -> &Bitvector32Term {
        &self.end
    }
}

impl CFunctionSpecification {
    pub fn new(
        state: CState,
        arguments: Vec<CExpression>,
        requires: Vec<Proposition>,
        outcome: CFunctionOutcome,
    ) -> Self {
        Self {
            state,
            arguments,
            requires,
            outcome,
        }
    }

    pub fn state(&self) -> &CState {
        &self.state
    }

    pub fn arguments(&self) -> &[CExpression] {
        &self.arguments
    }

    pub fn requires(&self) -> &[Proposition] {
        &self.requires
    }

    pub fn outcome(&self) -> &CFunctionOutcome {
        &self.outcome
    }
}

impl CExecutionEnvironment {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn with_function(mut self, function: CFunction) -> Self {
        std::sync::Arc::make_mut(&mut self.functions).insert(function.name().to_string(), function);
        self.variable_index = CExecutionEnvironmentVariableIndex::default();
        self
    }

    pub fn with_external_function_rule(mut self, rule: CExternalFunctionRule) -> Self {
        std::sync::Arc::make_mut(&mut self.external_function_rules)
            .insert(rule.function.name().to_string(), rule);
        self.variable_index = CExecutionEnvironmentVariableIndex::default();
        self
    }

    pub fn get_function(&self, name: &str) -> Option<&CFunction> {
        self.functions.get(name)
    }

    pub(in crate::kernel) fn get_external_function_rule(
        &self,
        name: &str,
    ) -> Option<&CExternalFunctionRule> {
        self.external_function_rules.get(name)
    }

    pub fn with_verified_function_rule(mut self, rule: CVerifiedFunctionRule) -> Self {
        std::sync::Arc::make_mut(&mut self.verified_function_rules)
            .insert(rule.function.name().to_string(), rule);
        self.variable_index = CExecutionEnvironmentVariableIndex::default();
        self
    }

    pub fn with_verified_function_termination_rules(
        mut self,
        rules: impl IntoIterator<Item = CVerifiedFunctionTerminationRule>,
    ) -> Self {
        for rule in rules {
            std::sync::Arc::make_mut(&mut self.verified_function_termination_rules)
                .insert(rule.function.name().to_string(), rule);
        }
        self.variable_index = CExecutionEnvironmentVariableIndex::default();
        self
    }

    pub fn has_verified_function_termination(&self, name: &str) -> bool {
        self.verified_function_termination_rules.contains_key(name)
    }

    pub fn without_verified_function_rule(mut self, name: &str) -> Self {
        std::sync::Arc::make_mut(&mut self.verified_function_rules).remove(name);
        self.variable_index = CExecutionEnvironmentVariableIndex::default();
        self
    }

    pub(in crate::kernel) fn get_verified_function_rule(
        &self,
        name: &str,
    ) -> Option<&CVerifiedFunctionRule> {
        self.verified_function_rules.get(name)
    }

    pub(crate) fn verified_function_rules(&self) -> Vec<CVerifiedFunctionRule> {
        self.verified_function_rules.values().cloned().collect()
    }

    pub fn with_verified_loop_rules(
        mut self,
        rules: impl IntoIterator<Item = CVerifiedLoopRule>,
    ) -> Self {
        std::sync::Arc::make_mut(&mut self.verified_loop_rules).extend(rules);
        self.variable_index = CExecutionEnvironmentVariableIndex::default();
        self
    }

    #[cfg(test)]
    pub(crate) fn shares_project_storage_with(&self, other: &Self) -> bool {
        std::sync::Arc::ptr_eq(&self.functions, &other.functions)
            && std::sync::Arc::ptr_eq(
                &self.external_function_rules,
                &other.external_function_rules,
            )
            && std::sync::Arc::ptr_eq(
                &self.verified_function_rules,
                &other.verified_function_rules,
            )
            && std::sync::Arc::ptr_eq(
                &self.verified_function_termination_rules,
                &other.verified_function_termination_rules,
            )
    }

    #[cfg(test)]
    pub(crate) fn shares_all_storage_with(&self, other: &Self) -> bool {
        self.shares_project_storage_with(other)
            && std::sync::Arc::ptr_eq(&self.verified_loop_rules, &other.verified_loop_rules)
            && self
                .variable_index
                .shares_storage_with(&other.variable_index)
    }

    pub(in crate::kernel) fn applicable_verified_loop_rule(
        &self,
        state: &CState,
        statement: &CStatement,
        assumptions: &PureFactContext,
    ) -> Option<&CVerifiedLoopRule> {
        self.verified_loop_rules.iter().find(|rule| {
            let statement_matches = rule.loop_statement == *statement;
            let assumptions_match = rule
                .required_assumptions
                .pure_facts()
                .iter()
                .all(|required| {
                    assumptions.pure_facts().contains(required)
                        || assumptions.proves(required)
                        || match required {
                            Proposition::CMemoryLoadable {
                                memory,
                                base,
                                bytes,
                            } => {
                                memory_snapshots_proven_equal_at_pointer(
                                    memory,
                                    state.memory(),
                                    base,
                                    assumptions,
                                ) && (bytes.as_const().is_some_and(|bytes| {
                                    resource_context_has_read(
                                        state.resources(),
                                        base,
                                        bytes,
                                        assumptions,
                                    )
                                }) || resource_context_has_symbolic_int32_range_read(
                                    state.resources(),
                                    base,
                                    bytes,
                                    assumptions,
                                ))
                            }
                            _ => false,
                        }
                });
            let state_matches = rule.symbolic_entry_state.locals == state.locals
                && rule.symbolic_entry_state.memory == state.memory
                && crate::kernel::api::contract_certification::resource_contexts_definitionally_equal_with_definitions(
                    &rule.composite_resource_definitions,
                    rule.symbolic_entry_state.memory(),
                    rule.symbolic_entry_state.resources(),
                    state.memory(),
                    state.resources(),
                    assumptions,
                );
            state_matches && statement_matches && assumptions_match
        })
    }
}

impl CVerifiedLoopRule {
    pub(crate) fn with_loop_index(mut self, loop_index: usize) -> Self {
        self.loop_index = Some(loop_index);
        self
    }

    pub fn with_composite_resource_definitions(
        mut self,
        definitions: impl IntoIterator<Item = CCompositeResourceDefinition>,
    ) -> Self {
        self.composite_resource_definitions.extend(definitions);
        self
    }
}

impl CTerminationError {
    pub fn message(&self) -> &str {
        &self.message
    }
}

impl std::fmt::Display for CTerminationError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.message.fmt(formatter)
    }
}

impl std::error::Error for CTerminationError {}
