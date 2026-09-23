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
                CType::Bool
                    | CType::Int8
                    | CType::Int16
                    | CType::Int32
                    | CType::UInt8
                    | CType::UInt16
                    | CType::UInt32
                    | CType::Int64
                    | CType::UInt64
                    | CType::Float32
                    | CType::Float64
                    | CType::Int8Pointer
                    | CType::Int16Pointer
                    | CType::UInt16Pointer
                    | CType::Int32Pointer
                    | CType::UInt8Pointer
                    | CType::UInt32Pointer
                    | CType::Int64Pointer
                    | CType::UInt64Pointer
                    | CType::Float32Pointer
                    | CType::Float64Pointer
                    | CType::Int8PointerPointer
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
            pointee_volatile: false,
            constant: false,
            pointee_constant: false,
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

    pub fn pointee_is_volatile(&self) -> bool {
        self.pointee_volatile
    }

    pub fn with_pointee_volatile(mut self, pointee_volatile: bool) -> Self {
        self.pointee_volatile = pointee_volatile;
        self
    }

    pub fn is_constant(&self) -> bool {
        self.constant
    }

    pub fn with_constant(mut self, constant: bool) -> Self {
        self.constant = constant;
        self
    }

    pub fn pointee_is_constant(&self) -> bool {
        self.pointee_constant
    }

    pub fn with_pointee_constant(mut self, pointee_constant: bool) -> Self {
        self.pointee_constant = pointee_constant;
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
                CType::Int8
                    | CType::Int16
                    | CType::Int32
                    | CType::UInt8
                    | CType::UInt16
                    | CType::UInt32
                    | CType::Int64
                    | CType::UInt64
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
            !layout.fields().is_empty() || !layout.unions().is_empty(),
            "C global aggregates must have at least one modeled field or union"
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
            !layout.fields().is_empty() || !layout.unions().is_empty(),
            "C global aggregate arrays must have at least one modeled field or union"
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
                CType::Bool
                    | CType::Int8
                    | CType::Int16
                    | CType::Int32
                    | CType::UInt8
                    | CType::UInt16
                    | CType::UInt32
                    | CType::Float32
                    | CType::Float64
                    | CType::Int8Pointer
                    | CType::Int16Pointer
                    | CType::UInt16Pointer
                    | CType::Int32Pointer
                    | CType::UInt8Pointer
                    | CType::UInt32Pointer
                    | CType::Int64Pointer
                    | CType::UInt64Pointer
                    | CType::Float32Pointer
                    | CType::Float64Pointer
                    | CType::Int8PointerPointer
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
            "C static locals currently support scalar integer, floating-point, and pointer types"
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
            pointee_volatile: false,
            constant: false,
            pointee_constant: false,
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

    pub fn pointee_is_volatile(&self) -> bool {
        self.pointee_volatile
    }

    pub fn with_pointee_volatile(mut self, pointee_volatile: bool) -> Self {
        self.pointee_volatile = pointee_volatile;
        self
    }

    pub fn is_constant(&self) -> bool {
        self.constant
    }

    pub fn with_constant(mut self, constant: bool) -> Self {
        self.constant = constant;
        self
    }

    pub fn pointee_is_constant(&self) -> bool {
        self.pointee_constant
    }

    pub fn with_pointee_constant(mut self, pointee_constant: bool) -> Self {
        self.pointee_constant = pointee_constant;
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
                CType::Int8
                    | CType::Int16
                    | CType::Int32
                    | CType::UInt8
                    | CType::UInt16
                    | CType::UInt32
                    | CType::Int64
                    | CType::UInt64
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
            !layout.fields().is_empty() || !layout.unions().is_empty(),
            "C static aggregates must have at least one modeled field or union"
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
            !layout.fields().is_empty() || !layout.unions().is_empty(),
            "C static aggregate arrays must have at least one modeled field or union"
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

impl CFunctionContractInterface {
    pub(crate) fn new(return_type: CType, parameters: Vec<CParameter>) -> Self {
        Self {
            return_type,
            return_pointee_constant: false,
            return_aggregate_layout: None,
            exceptional_signature: CExceptionalSignature::None,
            parameters,
            proof_parameters: Default::default(),
            resource_requires: Vec::new(),
            resource_ensures: Vec::new(),
            resource_constructors: Vec::new(),
            contract_requires: Vec::new(),
            contract_requirement_sources: ContractRequirementSources::default(),
            contract_ensures: Vec::new(),
            exceptional_ensures: Vec::new(),
            contract_mutable: Vec::new(),
            contract_effect_claim_required: false,
            resource_derived_mutable_frame: false,
            resource_derived_frame_mixed: false,
            contract_claims: Vec::new(),
            opaque_contract_supported: true,
            composite_resource_definitions: Vec::new(),
            predicate_unfoldings: Vec::new(),
            recursion_measure: None,
        }
    }

    pub fn return_type(&self) -> CType {
        self.return_type
    }

    pub fn return_pointee_is_constant(&self) -> bool {
        self.return_pointee_constant
    }

    pub fn return_aggregate_layout(&self) -> Option<&CAggregateLayout> {
        self.return_aggregate_layout.as_ref()
    }

    pub fn parameters(&self) -> &[CParameter] {
        &self.parameters
    }

    pub(crate) fn exceptional_signature(&self) -> CExceptionalSignature {
        self.exceptional_signature
    }

    pub(crate) fn proof_parameters(&self) -> &[CResourceSpec] {
        &self.proof_parameters
    }

    pub(crate) fn with_proof_parameters(mut self, parameters: Vec<CResourceSpec>) -> Self {
        self.proof_parameters = parameters.into();
        self
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

    /// The declared expression `decreases` measure, if the function has one.
    pub fn recursion_measure(&self) -> Option<&CRankingComponent> {
        self.recursion_measure.as_ref()
    }

    pub(crate) fn contract_requirement_sources(&self) -> &[Option<usize>] {
        self.contract_requirement_sources.as_slice()
    }

    pub(crate) fn contract_requirement_source(&self, index: usize) -> Option<Option<usize>> {
        self.contract_requirement_sources
            .as_slice()
            .get(index)
            .copied()
    }

    pub fn contract_ensures(&self) -> &[SpecProposition] {
        &self.contract_ensures
    }

    pub(crate) fn exceptional_ensures(&self) -> &[SpecProposition] {
        &self.exceptional_ensures
    }

    pub fn contract_mutable(&self) -> &[CMemorySegment] {
        &self.contract_mutable
    }

    pub(crate) fn contract_effect_claim_required(&self) -> bool {
        self.contract_effect_claim_required
    }

    pub(crate) fn resource_derived_mutable_frame(&self) -> bool {
        self.resource_derived_mutable_frame
    }

    pub(crate) fn resource_derived_frame_mixed(&self) -> bool {
        self.resource_derived_frame_mixed
    }

    pub fn contract_claims(&self) -> &[CFunctionContractClaim] {
        &self.contract_claims
    }

    pub fn opaque_contract_supported(&self) -> bool {
        self.opaque_contract_supported && self.exceptional_signature.is_empty()
    }

    /// Whether this interface is representable by a body-certified direct
    /// call rule. The first exceptional slice deliberately remains narrower
    /// than ordinary opaque contracts: only the checked scalar channel and
    /// pure clauses cross the boundary. Resource and mutable-effect transfer,
    /// named contracts, external assumptions, and indirect application stay
    /// on the normal-only `opaque_contract_supported` path.
    pub(crate) fn verified_direct_contract_supported(&self) -> bool {
        if self.exceptional_signature.is_empty() {
            return self.opaque_contract_supported();
        }
        self.opaque_contract_supported
            && self.exceptional_signature == CExceptionalSignature::Int32
            && self.proof_parameters.is_empty()
            && self.resource_requires.is_empty()
            && self.resource_ensures.is_empty()
            && self.resource_constructors.is_empty()
            && self.contract_mutable.is_empty()
            && !self.contract_effect_claim_required
            && !self.resource_derived_mutable_frame
            && !self.resource_derived_frame_mixed
            && self.composite_resource_definitions.is_empty()
            && self.predicate_unfoldings.is_empty()
    }

    pub fn composite_resource_definitions(&self) -> &[CCompositeResourceDefinition] {
        &self.composite_resource_definitions
    }

    pub fn predicate_unfoldings(&self) -> &[CPredicateUnfolding] {
        &self.predicate_unfoldings
    }

    pub(crate) fn function_pointer_type(&self) -> CType {
        CType::FunctionPointer(
            CType::qualified_function_pointer_signature_with_exceptional_outcome(
                self.return_type(),
                self.return_pointee_is_constant(),
                &self
                    .parameters()
                    .iter()
                    .map(|parameter| (parameter.c_type(), parameter.pointee_is_constant()))
                    .collect::<Vec<_>>(),
                self.exceptional_signature(),
            ),
        )
    }

    /// Compare exactly the semantic interface, including normalized resource
    /// role/snapshot metadata, while ignoring its nominal contract name.
    pub(crate) fn exactly_matches(&self, other: &Self) -> bool {
        self.return_type == other.return_type
            && self.return_pointee_constant == other.return_pointee_constant
            && self.return_aggregate_layout == other.return_aggregate_layout
            && self.exceptional_signature == other.exceptional_signature
            && self.parameters == other.parameters
            && self.proof_parameters == other.proof_parameters
            && self.resource_requires == other.resource_requires
            && self.resource_ensures == other.resource_ensures
            && self.resource_constructors == other.resource_constructors
            && self.contract_requires == other.contract_requires
            && self.contract_ensures == other.contract_ensures
            && self.exceptional_ensures == other.exceptional_ensures
            && self.contract_mutable == other.contract_mutable
            && self.contract_effect_claim_required == other.contract_effect_claim_required
            && self.resource_derived_mutable_frame == other.resource_derived_mutable_frame
            && self.resource_derived_frame_mixed == other.resource_derived_frame_mixed
            && self.composite_resource_definitions == other.composite_resource_definitions
            && self.predicate_unfoldings == other.predicate_unfoldings
            && self.recursion_measure == other.recursion_measure
    }

    /// Compare the signature and resource vocabulary used by automatic
    /// callback formation. Proof binders and behavioral clauses are checked by
    /// their dedicated refinement judgments.
    pub(crate) fn has_compatible_signature_and_resource_vocabulary(&self, other: &Self) -> bool {
        self.has_compatible_signature_and_composite_vocabulary(other)
            && self.proof_parameters.is_empty()
    }

    pub(crate) fn has_compatible_signature_and_composite_vocabulary(&self, other: &Self) -> bool {
        self.return_type == other.return_type
            && self.return_pointee_constant == other.return_pointee_constant
            && self.return_aggregate_layout == other.return_aggregate_layout
            && self.exceptional_signature == other.exceptional_signature
            && self.parameters.len() == other.parameters.len()
            && self
                .parameters
                .iter()
                .zip(&other.parameters)
                .all(|(left, right)| {
                    left.c_type == right.c_type
                        && left.aggregate_layout == right.aggregate_layout
                        && left.volatile == right.volatile
                        && left.pointee_volatile == right.pointee_volatile
                        && left.constant == right.constant
                        && left.pointee_constant == right.pointee_constant
                })
            && self.resource_constructors == other.resource_constructors
            && self.composite_resource_definitions == other.composite_resource_definitions
    }

    pub(crate) fn has_same_predicate_unfoldings(&self, other: &Self) -> bool {
        self.predicate_unfoldings == other.predicate_unfoldings
    }
}

impl CFunction {
    pub(crate) fn with_program_entry(mut self) -> Self {
        self.program_entry = true;
        self
    }

    pub fn is_program_entry(&self) -> bool {
        self.program_entry
    }

    pub fn new(
        return_type: CType,
        name: impl Into<String>,
        parameters: Vec<CParameter>,
        body: CStatement,
    ) -> Self {
        Self {
            program_entry: false,
            name: name.into(),
            inline_body: false,
            source_body: body.clone(),
            body,
            control_targets: std::sync::Arc::new(BTreeMap::new()),
            contract_interface: CFunctionContractInterface::new(return_type, parameters),
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

    pub(crate) fn with_control_targets(
        mut self,
        control_targets: BTreeMap<CControlTargetId, CControlTarget>,
    ) -> Self {
        self.control_targets = std::sync::Arc::new(control_targets);
        self
    }

    pub(crate) fn with_control_targets_from(mut self, source: &Self) -> Self {
        self.control_targets = source.control_targets.clone();
        self
    }

    pub(crate) fn control_target(&self, target: CControlTargetId) -> Option<&CControlTarget> {
        self.control_targets.get(&target)
    }

    pub(crate) fn control_target_count(&self) -> usize {
        self.control_targets.len()
    }

    pub(crate) fn with_body(mut self, body: CStatement) -> Self {
        self.body = body;
        self
    }

    pub fn with_resource_summary(
        mut self,
        requires: Vec<CResourceSpec>,
        ensures: Vec<CResourceSpec>,
    ) -> Self {
        self.contract_interface.resource_requires = requires;
        self.contract_interface.resource_ensures = ensures;
        self
    }

    pub fn with_resource_constructors(mut self, constructors: Vec<CResourceSpec>) -> Self {
        self.contract_interface.resource_constructors = constructors;
        self
    }

    /// Internal staging hook for importers and tests. No source frontend opts
    /// into the exceptional channel yet.
    #[allow(dead_code)]
    pub(crate) fn with_int32_exceptional_outcome(mut self) -> Self {
        self.contract_interface.exceptional_signature = CExceptionalSignature::Int32;
        self
    }

    /// Internal staging hook for the exceptional postcondition family. The
    /// payload is available to these propositions through the kernel's
    /// exceptional-result binding.
    #[allow(dead_code)]
    pub(crate) fn with_exceptional_ensures(mut self, ensures: Vec<SpecProposition>) -> Self {
        self.contract_interface.exceptional_ensures = ensures;
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
        self.contract_interface.contract_requires = requires;
        self.contract_interface.contract_requirement_sources =
            ContractRequirementSources(vec![None; self.contract_interface.contract_requires.len()]);
        self.contract_interface.contract_ensures = ensures;
        self.contract_interface.contract_mutable = mutable;
        self.contract_interface.resource_derived_frame_mixed = false;
        self.contract_interface.contract_effect_claim_required =
            !self.contract_interface.contract_mutable.is_empty();
        self.contract_interface.resource_derived_mutable_frame = false;
        self.contract_interface.contract_claims = claims;
        self.contract_interface.opaque_contract_supported = opaque_supported;
        self
    }

    /// Records the function's declared expression `decreases` measure.
    ///
    /// The measure is part of the contract interface, so it is part of this
    /// function's semantic identity: a verified rule, and every claim bound
    /// to it, names the function that declared the measure, and a function
    /// that declares none is a different `CFunction`.
    pub fn with_recursion_measure(mut self, measure: CRankingComponent) -> Self {
        self.contract_interface.recursion_measure = Some(measure);
        self
    }

    pub(crate) fn with_contract_requirement_sources(mut self, sources: Vec<Option<usize>>) -> Self {
        assert_eq!(
            sources.len(),
            self.contract_interface.contract_requires.len(),
            "contract requirement source map must match lowered requirements"
        );
        self.contract_interface.contract_requirement_sources = ContractRequirementSources(sources);
        self
    }

    #[cfg(test)]
    pub(crate) fn without_test_contract_requirement_sources(mut self) -> Self {
        self.contract_interface.contract_requirement_sources =
            ContractRequirementSources::default();
        self
    }

    /// Marks the mutable frame as inferred from consumed resource ownership.
    /// Such a frame is part of the resource transition, not an omitted
    /// function-level Effect claim. This narrow crate-level escape hatch is
    /// used by the surface lowering; external kernel callers retain the
    /// default requirement that a nonempty frame have an Effect claim.
    /// Mark the function's write footprint as derived from its resources.
    /// The footprint itself is never stored: the kernel projects it from the
    /// checked resource transition whenever it is needed, so no lowered
    /// segment list can disagree with it. An explicit effect segment beside
    /// a resource-derived frame is a mixed interface, refused when the
    /// projection is asked for.
    pub(crate) fn with_resource_derived_mutable_frame(mut self) -> Self {
        self.contract_interface.contract_effect_claim_required = false;
        self.contract_interface.resource_derived_frame_mixed =
            !self.contract_interface.contract_mutable.is_empty();
        self.contract_interface.resource_derived_mutable_frame = true;
        self
    }

    pub fn with_composite_resource_definitions(
        mut self,
        mut definitions: Vec<CCompositeResourceDefinition>,
    ) -> Self {
        definitions.sort_by(|left, right| left.name().cmp(right.name()));
        self.contract_interface.composite_resource_definitions = definitions;
        self
    }

    pub(crate) fn composite_resource_definition(
        &self,
        name: &str,
    ) -> Option<&CCompositeResourceDefinition> {
        self.contract_interface
            .composite_resource_definitions
            .binary_search_by(|definition| definition.name().cmp(name))
            .ok()
            .map(|index| &self.contract_interface.composite_resource_definitions[index])
    }

    pub fn with_predicate_unfoldings(mut self, unfoldings: Vec<CPredicateUnfolding>) -> Self {
        self.contract_interface.predicate_unfoldings = unfoldings;
        self
    }

    pub fn return_type(&self) -> CType {
        self.contract_interface.return_type()
    }

    pub fn with_return_pointee_constant(mut self, constant: bool) -> Self {
        self.contract_interface.return_pointee_constant = constant;
        self
    }

    pub fn return_pointee_is_constant(&self) -> bool {
        self.contract_interface.return_pointee_is_constant()
    }

    pub fn return_aggregate_layout(&self) -> Option<&CAggregateLayout> {
        self.contract_interface.return_aggregate_layout()
    }

    pub fn with_return_aggregate_layout(mut self, layout: CAggregateLayout) -> Self {
        self.contract_interface.return_aggregate_layout = Some(layout);
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
        self.contract_interface.parameters()
    }

    pub(crate) fn pop_parameter(&mut self) -> Option<CParameter> {
        self.contract_interface.parameters.pop()
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
        self.contract_interface.function_pointer_type()
    }

    pub(crate) fn exceptional_signature(&self) -> CExceptionalSignature {
        self.contract_interface.exceptional_signature()
    }

    pub fn body(&self) -> &CStatement {
        &self.body
    }

    pub fn source_body(&self) -> &CStatement {
        &self.source_body
    }

    pub fn resource_requires(&self) -> &[CResourceSpec] {
        self.contract_interface.resource_requires()
    }

    pub fn resource_ensures(&self) -> &[CResourceSpec] {
        self.contract_interface.resource_ensures()
    }

    pub fn resource_constructors(&self) -> &[CResourceSpec] {
        self.contract_interface.resource_constructors()
    }

    pub fn contract_requires(&self) -> &[SpecProposition] {
        self.contract_interface.contract_requires()
    }

    pub(crate) fn pop_contract_requirement(&mut self) -> Option<SpecProposition> {
        self.contract_interface.contract_requires.pop()
    }

    pub fn contract_ensures(&self) -> &[SpecProposition] {
        self.contract_interface.contract_ensures()
    }

    pub(crate) fn exceptional_ensures(&self) -> &[SpecProposition] {
        self.contract_interface.exceptional_ensures()
    }

    pub fn contract_mutable(&self) -> &[CMemorySegment] {
        self.contract_interface.contract_mutable()
    }

    pub(crate) fn contract_effect_claim_required(&self) -> bool {
        self.contract_interface.contract_effect_claim_required()
    }

    pub(crate) fn resource_derived_mutable_frame(&self) -> bool {
        self.contract_interface.resource_derived_mutable_frame()
    }

    pub fn contract_claims(&self) -> &[CFunctionContractClaim] {
        self.contract_interface.contract_claims()
    }

    pub fn opaque_contract_supported(&self) -> bool {
        self.contract_interface.opaque_contract_supported()
            && !statement_contains_internal_throw(&self.body)
    }

    pub(crate) fn verified_direct_contract_supported(&self) -> bool {
        self.contract_interface.verified_direct_contract_supported()
            && (self.exceptional_signature().is_empty()
                || self.exceptional_signature() == CExceptionalSignature::Int32)
            && (!self.has_internal_exceptional_outcome()
                || !self.exceptional_signature().is_empty())
    }

    pub(crate) fn has_internal_exceptional_outcome(&self) -> bool {
        statement_contains_internal_throw(&self.body)
    }

    pub fn composite_resource_definitions(&self) -> &[CCompositeResourceDefinition] {
        self.contract_interface.composite_resource_definitions()
    }

    pub fn predicate_unfoldings(&self) -> &[CPredicateUnfolding] {
        self.contract_interface.predicate_unfoldings()
    }

    /// The body-independent contract carrier used by direct calls, callback
    /// applications, refinement, and certification.
    pub fn contract_interface(&self) -> &CFunctionContractInterface {
        &self.contract_interface
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
    pub(crate) fn with_instance_schema(mut self, schema: Option<ResourceFieldSchema>) -> Self {
        self.instance_schema = schema;
        self
    }

    pub(crate) fn instance_field_schema(&self) -> Option<&ResourceFieldSchema> {
        self.instance_schema.as_ref()
    }

    pub(crate) fn with_resource_match_body(mut self, body: Option<CResourceMatchBody>) -> Self {
        self.matched = body;
        self
    }
    pub fn new(
        name: impl Into<String>,
        parameters: Vec<CParameter>,
        condition: Option<SpecProposition>,
        recursive: bool,
        contains: Vec<CResourceSpec>,
        facts: Vec<SpecProposition>,
    ) -> Self {
        let fact_source_indices = (0..facts.len()).collect();
        Self {
            instance_schema: None,
            matched: None,
            name: name.into(),
            parameters,
            witnesses: Vec::new(),
            condition,
            recursive,
            matched_recursive: false,
            counted_population: false,
            facts_claim_liveness: false,
            contains,
            facts,
            fact_source_indices,
        }
    }

    pub fn with_witnesses(mut self, witnesses: Vec<CParameter>) -> Self {
        self.witnesses = witnesses;
        self
    }

    pub(crate) fn with_fact_source_indices(mut self, indices: Vec<usize>) -> Self {
        self.fact_source_indices = indices;
        self
    }

    pub(crate) fn fact_source_index(&self, compiled_index: usize) -> Option<usize> {
        self.fact_source_indices.get(compiled_index).copied()
    }

    pub fn with_liveness_facts(mut self, facts_claim_liveness: bool) -> Self {
        self.facts_claim_liveness = facts_claim_liveness;
        self
    }

    /// Whether a stable loan of this composite may carry its body facts:
    /// recovery restores the exact escrowed head, so a fact is re-asserted
    /// precisely as folded, which is sound when everything the fact depends
    /// on is stable for the loan. The body's memory and tokens are; a
    /// resource population the caller may consume elsewhere and the
    /// liveness of storage the fact names are not (D12).
    pub fn facts_are_loan_stable(&self) -> bool {
        !self.counted_population && !self.facts_claim_liveness
    }

    pub fn witnesses(&self) -> &[CParameter] {
        &self.witnesses
    }

    pub fn counted_population(
        name: impl Into<String>,
        parameters: Vec<CParameter>,
        condition: Option<SpecProposition>,
        contains: Vec<CResourceSpec>,
        facts: Vec<SpecProposition>,
    ) -> Self {
        let fact_source_indices = (0..facts.len()).collect();
        Self {
            instance_schema: None,
            matched: None,
            name: name.into(),
            parameters,
            witnesses: Vec::new(),
            condition,
            recursive: false,
            matched_recursive: false,
            counted_population: true,
            facts_claim_liveness: false,
            contains,
            facts,
            fact_source_indices,
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

    /// Whether this definition contains an instance of itself, wherever the
    /// child clause is written.
    ///
    /// A matched definition keeps its children inside the arms, so the
    /// `recursive` flag — which describes the unmatched memory body that
    /// instance fold/unfold rewrites — never sees them. Callers that ask about
    /// the definition rather than about that body (expansion cycle guards,
    /// certification-cache and eager-expansion declines, structural measures)
    /// must see a matched `tree_at` as recursive too.
    pub fn is_recursive(&self) -> bool {
        self.recursive || self.matched_recursive
    }

    pub(crate) fn with_matched_recursion(mut self, matched_recursive: bool) -> Self {
        self.matched_recursive = matched_recursive;
        self
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

    #[allow(dead_code)]
    pub(crate) fn exceptional_ensure_proposition(
        source_index: usize,
        contract_index: usize,
    ) -> Self {
        Self {
            key: CFunctionContractClaimKey::ExceptionalEnsure(source_index),
            target: CFunctionContractClaimTarget::ExceptionalEnsureProposition(contract_index),
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
            origin: CLoopEffectOrigin::Unspecified,
            validated_ranges: None,
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
            origin: CLoopEffectOrigin::Unspecified,
            validated_ranges: None,
        }
    }

    pub fn new_with_origin(
        effect: CLoopEffect,
        span: CLoopEffectSpan,
        origin: CLoopEffectOrigin,
        context: Option<String>,
    ) -> Self {
        Self {
            effect,
            span,
            context,
            origin,
            validated_ranges: None,
        }
    }

    pub(crate) fn with_validated_ranges(mut self, ranges: Vec<CMemoryRange>) -> Self {
        self.validated_ranges = Some(ranges);
        self
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

    pub fn origin(&self) -> CLoopEffectOrigin {
        self.origin
    }

    pub(crate) fn validated_ranges(&self) -> Option<&[CMemoryRange]> {
        self.validated_ranges.as_deref()
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
        (
            self.base
                .offset_by_elements(self.start.clone(), self.element_width),
            memory_range_byte_count(self.start.clone(), self.end.clone(), self.element_width),
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

/// Convert a logical element range to a physical byte count in the kernel's
/// 32-bit memory model. Callers must carry
/// [`memory_range_byte_count_guards`] whenever the range is supplied by a
/// contract or resource clause, since the arithmetic itself is modular.
pub(crate) fn memory_range_byte_count(
    start: Bitvector32Term,
    end: Bitvector32Term,
    element_width: u32,
) -> Bitvector32Term {
    assert!(element_width > 0, "memory element width must be positive");
    let element_count = canonical_subtract(end, start);
    canonical_multiply(element_count, Bitvector32Term::Constant(element_width))
}

fn canonical_subtract(left: Bitvector32Term, right: Bitvector32Term) -> Bitvector32Term {
    match (&left, &right) {
        (Bitvector32Term::Constant(left), Bitvector32Term::Constant(right)) => {
            Bitvector32Term::Constant(left.wrapping_sub(*right))
        }
        (_, Bitvector32Term::Constant(0)) => left,
        _ if left == right => Bitvector32Term::Constant(0),
        (
            Bitvector32Term::Add(left_base, left_addend),
            Bitvector32Term::Add(right_base, right_addend),
        ) if left_base == right_base => {
            canonical_subtract(left_addend.as_ref().clone(), right_addend.as_ref().clone())
        }
        _ => Bitvector32Term::Subtract(Box::new(left), Box::new(right)),
    }
}

fn canonical_multiply(left: Bitvector32Term, right: Bitvector32Term) -> Bitvector32Term {
    match (&left, &right) {
        (Bitvector32Term::Constant(left), Bitvector32Term::Constant(right)) => {
            Bitvector32Term::Constant(left.wrapping_mul(*right))
        }
        (_, Bitvector32Term::Constant(1)) => left,
        (Bitvector32Term::Constant(1), _) => right,
        (_, Bitvector32Term::Constant(0)) | (Bitvector32Term::Constant(0), _) => {
            Bitvector32Term::Constant(0)
        }
        _ => Bitvector32Term::Multiply(Box::new(left), Box::new(right)),
    }
}

/// The largest element count a range of `element_width`-byte elements may have
/// and still name a valid 32-bit byte extent. This is the bound the `fits`
/// guard below states, and the one definition of it: a rule that needs the
/// same bound reads it here rather than recomputing the division.
pub(crate) fn memory_range_element_count_limit(element_width: u32) -> u32 {
    assert!(element_width > 0, "memory element width must be positive");
    u32::MAX / element_width
}

/// A range's element count as a term: the same difference
/// [`memory_range_byte_count`] scales, unscaled.
pub(crate) fn memory_range_element_count(range: &CMemoryRange) -> Bitvector32Term {
    canonical_subtract(range.end().clone(), range.start().clone())
}

/// Whether that limit constrains a nonnegative `int32` element count at all.
/// For one- and two-byte elements it does not: `i32::MAX` elements of two
/// bytes still fit a `u32` byte extent, so nonnegativity is the whole
/// condition and a second guard would be a fact every count already has.
pub(crate) fn element_count_limit_constrains_int32(element_width: u32) -> bool {
    memory_range_element_count_limit(element_width) < i32::MAX as u32
}

/// The valid-byte-extent condition written over a range's element count, in
/// the spelling a proof can state.
///
/// This is [`memory_range_byte_count_guards`] for a caller that holds the
/// count rather than the two endpoints, and it is the same condition. Over a
/// count the unsigned `fits` comparison becomes a signed one, because
/// `0 <= count` already pins the count below `2^31` and the limit is itself
/// below `2^31` for every element width past two bytes; over two endpoints it
/// cannot, since `a <= b` signed leaves `b - a` free to wrap and that is the
/// hazard the unsigned form exists for.
///
/// Click's surface has no unsigned comparison, so this is also the only form
/// of the condition a user can write down, and the form every diagnostic about
/// a missing extent should print.
pub(crate) fn memory_range_element_count_guards(
    element_count: Bitvector32Term,
    element_width: u32,
) -> Vec<Proposition> {
    assert!(element_width > 0, "memory element width must be positive");
    let mut guards = vec![Proposition::ConditionIs(
        ConditionTerm::signed_less_equal(Bitvector32Term::Constant(0), element_count.clone()),
        true,
    )];
    if element_count_limit_constrains_int32(element_width) {
        guards.push(Proposition::ConditionIs(
            ConditionTerm::signed_less_equal(
                element_count,
                Bitvector32Term::Constant(memory_range_element_count_limit(element_width)),
            ),
            true,
        ));
    }
    guards
}

/// Whether a logical element range is usable as a 32-bit physical byte
/// extent, and what it takes.
///
/// Constant endpoints are decided here. Symbolic ones carry the two side
/// conditions a caller must establish. One definition, so a constant range and
/// a symbolic one cannot disagree about what fits.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum MemoryRangeExtent {
    /// Constant endpoints forming a forward range that fits: nothing to prove.
    ConstantValid,
    /// Constant endpoints that do not. `element_count` is the true difference
    /// `end - start` in `i64`, which is negative for a reversed range, and
    /// `byte_limit` is the largest byte extent a `u32` count can name.
    ConstantInvalid { element_count: i64, byte_limit: u32 },
    /// Symbolic endpoints: these propositions are the side conditions.
    Guards(Vec<Proposition>),
}

/// The side conditions needed before a logical element range can be used as
/// a 32-bit physical byte extent. Ranges must be forward and fit in `u32`
/// bytes after scaling by their element width.
pub(crate) fn memory_range_byte_count_extent(
    start: Bitvector32Term,
    end: Bitvector32Term,
    element_width: u32,
) -> MemoryRangeExtent {
    assert!(element_width > 0, "memory element width must be positive");
    if let (Some(start), Some(end)) = (start.as_const(), end.as_const()) {
        // The endpoints are `int32` values held as `u32` bits. Take their true
        // difference in `i64`: subtracting the bit patterns underflows for a
        // negative start, which panicked here in debug and wrapped silently in
        // release, admitting a range that does not fit as a valid extent. The
        // bound below is the same one the symbolic `fits` guard states, since
        // `count <= u32::MAX / w` and `count * w <= u32::MAX` agree on
        // nonnegative integers.
        let element_count = i64::from(end as i32) - i64::from(start as i32);
        let byte_count = element_count.saturating_mul(i64::from(element_width));
        if element_count >= 0 && byte_count <= i64::from(u32::MAX) {
            return MemoryRangeExtent::ConstantValid;
        }
        return MemoryRangeExtent::ConstantInvalid {
            element_count,
            byte_limit: u32::MAX,
        };
    }
    let forward = ConditionTerm::signed_less_equal(start.clone(), end.clone());
    let element_count = canonical_subtract(end, start);
    let fits = ConditionTerm::unsigned_less_equal(
        element_count,
        Bitvector32Term::Constant(memory_range_element_count_limit(element_width)),
    );
    MemoryRangeExtent::Guards(vec![
        Proposition::ConditionIs(forward, true),
        Proposition::ConditionIs(fits, true),
    ])
}

/// The element width a byte extent was scaled by, when it is a product with a
/// positive constant factor. A segment `p[x..y]` of `w`-byte elements lowers
/// its extent to `(y - x) * w`, so recovering `w` is what lets an extent be
/// read back at element granularity. The inverse of
/// [`memory_range_byte_count`], on the term only: it neither simplifies nor
/// consults facts.
pub(crate) fn scaled_extent_element_width(bytes: &Bitvector32Term) -> Option<u32> {
    let Bitvector32Term::Multiply(left, right) = bytes else {
        return None;
    };
    match (left.as_ref(), right.as_ref()) {
        (Bitvector32Term::Constant(width), _) | (_, Bitvector32Term::Constant(width))
            if *width > 0 =>
        {
            Some(*width)
        }
        _ => None,
    }
}

/// The byte-count guards a stated range-loadable proposition carries.
///
/// A surface `loadable(p[a..b])` means two things at once: that `a..b` is a
/// valid 32-bit byte extent, and that those bytes are loadable. The kernel
/// proposition holds only the second, as the byte count `(b - a) * w`, so the
/// first has to travel beside it. Recovering it from the lowered proposition
/// keeps one definition for both directions of that meaning: wherever such a
/// proposition is assumed these are available with it, and wherever it is a
/// premise a proof must supply these are owed with it. Deriving them here,
/// from the proposition alone, is what makes the two sides agree without a
/// per-site rule about where the proposition came from.
///
/// The guards are stated over the extent's element count, which is the form
/// the loadability rules read it back in and the form a proof can write: for
/// `p[a..b]` the count term is `b - a`, so `0 <= b - a` and
/// `b - a <= u32::MAX / w` are the two facts, and for `p[0..n]` they are over
/// `n` itself.
///
/// Conjunctions are walked, because a `requires` clause is written as one.
/// A quantifier or an implication is not: a guard over a bound variable is not
/// a fact about anything the surrounding scope can state. A byte count that is
/// not a scaled element range carries nothing — a constant cell width and a
/// block size are already true counts of bytes.
pub(crate) fn stated_loadable_extent_guards(proposition: &Proposition) -> Vec<Proposition> {
    let mut guards = Vec::new();
    collect_stated_loadable_extent_guards(proposition, &mut guards, false);
    guards
}

/// [`stated_loadable_extent_guards`] in every spelling of the same condition.
///
/// Contract and resource lowering states a stated range's guards over the
/// range's two endpoints, where the `fits` half has to be an unsigned
/// comparison; the element-count form above states the same condition in the
/// signed spelling a proof can write. A consumer asking "is this condition
/// available here" has to accept either, because which one is present depends
/// on the lowering that installed the range, not on what the range means. A
/// consumer asking a proof to *establish* the condition asks for the count
/// form only, since that is the one the surface can spell.
pub(crate) fn stated_loadable_extent_guard_spellings(
    proposition: &Proposition,
) -> Vec<Proposition> {
    let mut guards = Vec::new();
    collect_stated_loadable_extent_guards(proposition, &mut guards, true);
    guards
}

fn collect_stated_loadable_extent_guards(
    proposition: &Proposition,
    guards: &mut Vec<Proposition>,
    every_spelling: bool,
) {
    match proposition {
        Proposition::And(left, right) => {
            collect_stated_loadable_extent_guards(left, guards, every_spelling);
            collect_stated_loadable_extent_guards(right, guards, every_spelling);
        }
        Proposition::CMemoryLoadable { bytes, .. } => {
            let Some(element_width) = scaled_extent_element_width(bytes) else {
                return;
            };
            let Some(element_count) =
                crate::kernel::reasoning::element_count_from_bytes(bytes, element_width)
            else {
                return;
            };
            let endpoints = if every_spelling {
                memory_range_byte_count_guards(
                    Bitvector32Term::Constant(0),
                    element_count.clone(),
                    element_width,
                )
            } else {
                Vec::new()
            };
            for guard in memory_range_element_count_guards(element_count, element_width)
                .into_iter()
                .chain(endpoints)
            {
                if !guards.contains(&guard) {
                    guards.push(guard);
                }
            }
        }
        _ => {}
    }
}

/// Public range bounds in signed arithmetic. Two-byte and wider elements
/// have a maximum count no larger than `i32::MAX`, so their unsigned byte
/// bound is equivalent to these signed count guards plus forward endpoints.
/// Byte ranges can span more than `i32::MAX` elements and retain the exact
/// endpoint form instead.
pub(crate) fn memory_range_extent_guards(range: &CMemoryRange) -> Vec<Proposition> {
    match memory_range_byte_count_extent(
        range.start().clone(),
        range.end().clone(),
        range.element_width(),
    ) {
        MemoryRangeExtent::ConstantValid => Vec::new(),
        MemoryRangeExtent::ConstantInvalid { .. } => vec![Proposition::ConditionIs(
            ConditionTerm::Constant(false),
            true,
        )],
        MemoryRangeExtent::Guards(guards) if range.element_width() == 1 => guards,
        MemoryRangeExtent::Guards(_) => {
            let mut guards = vec![Proposition::ConditionIs(
                ConditionTerm::signed_less_equal(range.start().clone(), range.end().clone()),
                true,
            )];
            for guard in memory_range_element_count_guards(
                memory_range_element_count(range),
                range.element_width(),
            ) {
                if !guards.contains(&guard) {
                    guards.push(guard);
                }
            }
            guards
        }
    }
}

/// Equivalent forms retained with an actual held range. The original endpoint
/// form serves memory reasoning; the signed form is available to proof text.
pub(crate) fn memory_range_extent_guard_spellings(range: &CMemoryRange) -> Vec<Proposition> {
    let mut guards = memory_range_byte_count_guards(
        range.start().clone(),
        range.end().clone(),
        range.element_width(),
    );
    for guard in memory_range_extent_guards(range) {
        if !guards.contains(&guard) {
            guards.push(guard);
        }
    }
    guards
}

/// Proof-facing bounds included in a separation proposition. Assuming it and
/// proving it use the same list; neither direction may drop a bound.
/// Bound variables under quantifiers or implications stay in their own scope.
pub(crate) fn stated_separation_extent_bounds(proposition: &Proposition) -> Vec<Proposition> {
    let mut guards = Vec::new();
    for range in stated_separation_memory_ranges(proposition) {
        for guard in memory_range_extent_guards(range) {
            if !guards.contains(&guard) {
                guards.push(guard);
            }
        }
    }
    guards
}

/// Endpoint-form validity guards for a stated separation. Lowering uses these
/// to diagnose ranges already known invalid; the equivalent signed form from
/// [`stated_separation_extent_bounds`] becomes part of the separation proposition.
/// Composite and token atoms carry no endpoints. Quantifiers and implications
/// are not traversed, so their local bounds cannot escape into the outer scope.
pub(crate) fn stated_separation_extent_guards(proposition: &Proposition) -> Vec<Proposition> {
    let mut guards = Vec::new();
    for range in stated_separation_memory_ranges(proposition) {
        for guard in memory_range_byte_count_guards(
            range.start().clone(),
            range.end().clone(),
            range.element_width(),
        ) {
            if !guards.contains(&guard) {
                guards.push(guard);
            }
        }
    }
    guards
}

/// The memory ranges a stated separation names, in the order they are written.
///
/// The one place that decides which ranges a separation's extent meaning is
/// about. [`stated_separation_extent_guards`] states their guards, and the
/// lowering that owes those guards reads the same ranges back so it can name
/// a constant-invalid one in its refusal rather than reporting only that a
/// path disappeared.
fn stated_separation_memory_ranges(proposition: &Proposition) -> Vec<&CMemoryRange> {
    let mut ranges = Vec::new();
    collect_stated_separation_memory_ranges(proposition, &mut ranges);
    ranges
}

fn collect_stated_separation_memory_ranges<'a>(
    proposition: &'a Proposition,
    ranges: &mut Vec<&'a CMemoryRange>,
) {
    match proposition {
        Proposition::And(left, right) => {
            collect_stated_separation_memory_ranges(left, ranges);
            collect_stated_separation_memory_ranges(right, ranges);
        }
        Proposition::CResourceSeparate { left, right } => {
            for resource in [left, right] {
                if let CResource::Memory(range) = resource {
                    ranges.push(range);
                }
            }
        }
        _ => {}
    }
}

/// [`memory_range_byte_count_extent`] as a flat guard list: an invalid
/// constant range becomes the impossible guard, which refuses wherever the
/// caller discharges guards.
pub(crate) fn memory_range_byte_count_guards(
    start: Bitvector32Term,
    end: Bitvector32Term,
    element_width: u32,
) -> Vec<Proposition> {
    match memory_range_byte_count_extent(start, end, element_width) {
        MemoryRangeExtent::ConstantValid => Vec::new(),
        MemoryRangeExtent::ConstantInvalid { .. } => vec![Proposition::ConditionIs(
            ConditionTerm::Constant(false),
            true,
        )],
        MemoryRangeExtent::Guards(guards) => guards,
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

impl CFunctionContract {
    const PREDICATE_PREFIX: &'static str = "__click_function_contract::";

    pub(crate) fn with_proof_parameters(mut self, parameters: Vec<CResourceSpec>) -> Self {
        self.interface = self.interface.with_proof_parameters(parameters);
        self
    }

    pub fn new(name: impl Into<String>, function: CFunction) -> Option<Self> {
        if function.has_internal_exceptional_outcome() {
            return None;
        }
        let name = name.into();
        Self::from_interface_with_callee_name(
            name,
            function.name().to_string(),
            function.contract_interface().clone(),
        )
    }

    fn from_interface_with_callee_name(
        name: String,
        callee_name: String,
        interface: CFunctionContractInterface,
    ) -> Option<Self> {
        (interface.opaque_contract_supported()
            && interface.resource_constructors().is_empty()
            && !name.is_empty())
        .then_some(Self {
            name,
            callee_name,
            interface,
        })
    }

    pub fn name(&self) -> &str {
        &self.name
    }

    pub(crate) fn callee_name(&self) -> &str {
        &self.callee_name
    }

    pub fn function_pointer_type(&self) -> CType {
        self.interface().function_pointer_type()
    }

    pub fn predicate_name(&self) -> String {
        Self::predicate_name_for(&self.name)
    }

    pub fn predicate_name_for(name: &str) -> String {
        format!("{}{name}", Self::PREDICATE_PREFIX)
    }

    pub(crate) fn surface_name_from_predicate(name: &str) -> Option<&str> {
        name.strip_prefix(Self::PREDICATE_PREFIX)
    }

    pub(crate) fn proof_parameters(&self) -> &[CResourceSpec] {
        self.interface.proof_parameters()
    }

    /// First-slice formation rule: a concrete target must expose exactly the
    /// same normalized interface. Behavioral refinement is intentionally a
    /// later rule; exact equality is restrictive but sound.
    pub(crate) fn exactly_matches(&self, function: &CFunction) -> bool {
        self.proof_parameters().is_empty()
            && self
                .interface
                .exactly_matches(function.contract_interface())
    }

    /// Checks the portion of a callback interface that behavioral refinement
    /// does not vary. Parameter names are binders, but their types, layouts,
    /// and qualifiers remain part of the signature. Whether a mutable frame
    /// was certified by an explicit effect claim or inferred from resource
    /// ownership is proof metadata, not part of the behavioral interface.
    pub(crate) fn has_compatible_signature_and_resource_vocabulary(
        &self,
        function: &CFunction,
    ) -> bool {
        self.interface
            .has_compatible_signature_and_resource_vocabulary(function.contract_interface())
    }

    /// The same interface check without the proof-parameter restriction.
    ///
    /// Automatic concrete-pointer formation may cross a proof-parameter
    /// contract, but only after it has separately established that the
    /// binding between the two declarations is forced. The explicit
    /// `unfold(Name)` route keeps refusing proof parameters: its proof block
    /// has no way to introduce the instances.
    pub(crate) fn has_compatible_signature_and_composite_vocabulary(
        &self,
        function: &CFunction,
    ) -> bool {
        self.interface
            .has_compatible_signature_and_composite_vocabulary(function.contract_interface())
    }

    /// Opaque predicate identities may be compared definitionally only when
    /// an explicit refinement proof names the definitions it unfolds.
    pub(crate) fn has_same_predicate_unfoldings(&self, function: &CFunction) -> bool {
        self.interface
            .has_same_predicate_unfoldings(function.contract_interface())
    }

    /// The body-independent interface selected by this nominal contract.
    pub fn interface(&self) -> &CFunctionContractInterface {
        &self.interface
    }
}

fn statement_contains_internal_throw(statement: &CStatement) -> bool {
    match statement {
        CStatement::Throw(_) => true,
        CStatement::ForStep { step, .. } => statement_contains_internal_throw(step),
        CStatement::Seq(first, second) => {
            statement_contains_internal_throw(first) || statement_contains_internal_throw(second)
        }
        CStatement::TryCatchInt32 {
            try_body, handler, ..
        } => {
            statement_contains_internal_throw(try_body)
                || statement_contains_internal_throw(handler)
        }
        CStatement::If {
            then_branch,
            else_branch,
            ..
        } => {
            statement_contains_internal_throw(then_branch)
                || statement_contains_internal_throw(else_branch)
        }
        CStatement::While { body, .. } => statement_contains_internal_throw(body),
        CStatement::Switch { cases, .. } => cases
            .iter()
            .any(|case| statement_contains_internal_throw(&case.body)),
        CStatement::Skip
        | CStatement::Break
        | CStatement::Continue
        | CStatement::Goto { .. }
        | CStatement::Declare { .. }
        | CStatement::DeclareAggregate { .. }
        | CStatement::CopyAggregate { .. }
        | CStatement::Assign { .. }
        | CStatement::CallAssign { .. }
        | CStatement::Call { .. }
        | CStatement::HeapAllocate { .. }
        | CStatement::HeapFree { .. }
        | CStatement::Assert { .. }
        | CStatement::Return(_)
        | CStatement::Store { .. }
        | CStatement::TypedStore { .. }
        | CStatement::Update { .. } => false,
    }
}

impl CExecutionEnvironment {
    pub(crate) fn with_modeled_pthread_binding(
        mut self,
        binding: Option<crate::languages::c::thread_runtime::ModeledPthreadBinding>,
    ) -> Self {
        self.modeled_pthread_binding = binding;
        self
    }

    /// Selects a call rule for one proof-local statement transition. All
    /// project tables and their variable index remain shared.
    pub(crate) fn with_selected_call_contract(mut self, name: &str) -> Self {
        self.selected_call_contract = Some(std::sync::Arc::from(name));
        self.selected_call_resource_arguments = None;
        self
    }

    pub(crate) fn with_selected_call_resource_arguments(
        mut self,
        arguments: Vec<Variable>,
    ) -> Self {
        self.selected_call_resource_arguments = Some(arguments.into());
        self
    }

    /// Selects the binder transport for one ordinary C call to `function`.
    /// The map is the only source of bindings for that call.
    pub(crate) fn with_selected_call_binders(
        mut self,
        function: &str,
        arity: usize,
        bindings: BTreeMap<Variable, Variable>,
    ) -> Self {
        self.selected_call_binders = Some(std::sync::Arc::new(CCallBinderTransport {
            function: std::sync::Arc::from(function),
            arity,
            bindings: std::sync::Arc::new(bindings),
        }));
        self
    }
    pub fn new() -> Self {
        Self::default()
    }

    pub fn with_function(mut self, function: CFunction) -> Self {
        std::sync::Arc::make_mut(&mut self.functions).insert(function.name().to_string(), function);
        self.variable_index = CExecutionEnvironmentVariableIndex::default();
        self
    }

    pub fn with_function_contract(mut self, contract: CFunctionContract) -> Self {
        std::sync::Arc::make_mut(&mut self.function_contracts)
            .insert(contract.name().to_string(), contract);
        self.variable_index = CExecutionEnvironmentVariableIndex::default();
        self
    }

    pub(crate) fn get_function_contract(&self, name: &str) -> Option<&CFunctionContract> {
        self.function_contracts.get(name)
    }

    pub fn with_external_function_rule(mut self, rule: CExternalFunctionRule) -> Self {
        std::sync::Arc::make_mut(&mut self.external_function_rules)
            .insert(rule.function.name().to_string(), rule);
        self.variable_index = CExecutionEnvironmentVariableIndex::default();
        self
    }

    pub(crate) fn without_external_function_rule(mut self, name: &str) -> Self {
        std::sync::Arc::make_mut(&mut self.external_function_rules).remove(name);
        self.variable_index = CExecutionEnvironmentVariableIndex::default();
        self
    }

    pub fn get_function(&self, name: &str) -> Option<&CFunction> {
        self.functions.get(name)
    }

    /// Every function body the project links. C termination reads a body with
    /// no verified rule as a call-graph node in two cases: a `static inline`
    /// helper a verified body calls, and a contract-less function whose
    /// address is taken, which a resolved function pointer executes in place.
    pub fn linked_functions(&self) -> Vec<&CFunction> {
        self.functions.values().collect()
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

    pub(in crate::kernel) fn get_verified_function_termination_rule(
        &self,
        name: &str,
    ) -> Option<&CVerifiedFunctionTerminationRule> {
        self.verified_function_termination_rules.get(name)
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

    /// Installs the recursion anchor for the function being certified.
    ///
    /// There is no public constructor for [`CRecursionAnchor`], so this is
    /// reached only through
    /// [`crate::kernel::c_execution_environment_with_recursion_anchor`],
    /// which derives the anchor from the function's own declared measure.
    pub(in crate::kernel) fn with_recursion_anchor(mut self, anchor: CRecursionAnchor) -> Self {
        self.recursion_anchor = Some(std::sync::Arc::new(anchor));
        self.variable_index = CExecutionEnvironmentVariableIndex::default();
        self
    }

    /// Enables proof-only case splitting at verified conditional-resource
    /// call boundaries. The flag is part of the environment identity so a
    /// checked artifact produced with one call policy cannot be reused under
    /// another.
    pub(crate) fn with_conditional_resource_cases(mut self) -> Self {
        self.allow_conditional_resource_cases = true;
        self.variable_index = CExecutionEnvironmentVariableIndex::default();
        self
    }

    pub(crate) fn allows_conditional_resource_cases(&self) -> bool {
        self.allow_conditional_resource_cases
    }

    pub(crate) fn has_conditional_resource_effects(&self) -> bool {
        self.functions.values().any(|function| {
            function
                .resource_ensures()
                .iter()
                .any(|resource| resource.guard().is_some())
        }) || self.function_contracts.values().any(|contract| {
            contract
                .interface()
                .resource_ensures()
                .iter()
                .any(|resource| resource.guard().is_some())
        }) || self.external_function_rules.values().any(|rule| {
            rule.function
                .resource_ensures()
                .iter()
                .any(|resource| resource.guard().is_some())
        }) || self.verified_function_rules.values().any(|rule| {
            rule.function
                .resource_ensures()
                .iter()
                .any(|resource| resource.guard().is_some())
        })
    }

    pub(in crate::kernel) fn recursion_anchor(&self) -> Option<&CRecursionAnchor> {
        self.recursion_anchor.as_deref()
    }

    /// The shared anchor handle, for a certified artifact that has to record
    /// which anchor it was produced under.
    pub(in crate::kernel) fn recursion_anchor_handle(
        &self,
    ) -> Option<std::sync::Arc<CRecursionAnchor>> {
        self.recursion_anchor.clone()
    }

    #[cfg(test)]
    pub(crate) fn shares_project_storage_with(&self, other: &Self) -> bool {
        std::sync::Arc::ptr_eq(&self.functions, &other.functions)
            && std::sync::Arc::ptr_eq(&self.function_contracts, &other.function_contracts)
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

    /// Whether `rule` may stand in for a loop stepped under this environment.
    ///
    /// A summary answers for everything its body owed. When this environment
    /// carries a recursion anchor, a self-call inside the loop owes the
    /// descent, and only a rule whose own body was stepped under the same
    /// anchor has already paid it. A rule certified without it, or under a
    /// different one, would let the summary swallow the call silently, so it
    /// does not apply here. A loop that does not call the anchored function
    /// owes nothing either way and is unaffected.
    fn loop_rule_answers_for_recursion(&self, rule: &CVerifiedLoopRule) -> bool {
        let Some(anchor) = self.recursion_anchor() else {
            return true;
        };
        !crate::kernel::termination::statement_calls_function(
            &rule.loop_statement,
            anchor.function(),
        ) || rule.recursion_anchor.as_deref() == Some(anchor)
    }

    /// Whether every verified loop rule here answers for the recursion this
    /// environment anchors, so a refusal can say that rather than leaving an
    /// unexplained inapplicable rule at the step over the loop.
    ///
    /// Work is this environment's own loop rules and their loop statements,
    /// which are the certified function's own loops, and only when it declares
    /// a measure at all; nothing project-wide is scanned.
    pub(in crate::kernel) fn verified_loop_rules_answer_for_recursion(&self) -> bool {
        self.recursion_anchor.is_none()
            || self
                .verified_loop_rules
                .iter()
                .all(|rule| self.loop_rule_answers_for_recursion(rule))
    }

    pub(in crate::kernel) fn applicable_verified_loop_rule(
        &self,
        state: &CState,
        statement: &CStatement,
        assumptions: &PureFactContext,
    ) -> Option<&CVerifiedLoopRule> {
        self.verified_loop_rules.iter().find(|rule| {
            let statement_matches =
                rule.loop_statement == *statement && self.loop_rule_answers_for_recursion(rule);
            let assumptions_match = rule
                .required_assumptions
                .pure_facts()
                .iter()
                .all(|required| {
                    // A rule's prerequisite must be exactly available here:
                    // an indexed fact lookup, or the retained memory rule
                    // below that re-establishes loadability from this state's
                    // own memory and read authority. Selecting a rule by
                    // searching the ambient context for a proof of its
                    // prerequisites is kernel proof planning.
                    assumptions.proves_exact(required)
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
                                }) || resource_context_has_symbolic_range_read(
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
    pub(crate) fn loop_invariant_correspondence(
        &self,
        path_index: usize,
    ) -> &[(usize, Proposition)] {
        self.paths[path_index]
            .loop_invariant_correspondence
            .0
            .as_deref()
            .unwrap_or_default()
    }

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
