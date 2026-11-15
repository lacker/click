use super::*;
use crate::kernel::binary_node;
use crate::kernel::binary_term;
use crate::kernel::{CompareRelation, MachineIntegerType};
use crate::kernel::{MachineCastSpelling, MachineTerm};
use crate::kernel::{bits32_constant, constant_i64, constant_u32, int32_constant, int64_constant};

impl ProgramParameter {
    pub fn new(name: impl Into<String>, program_type: ProgramType) -> Self {
        Self {
            name: name.into(),
            program_type,
            aggregate_layout: None,
            volatile: false,
            pointee_volatile: false,
            constant: false,
            pointee_constant: false,
            pointee_class: None,
            slice_length_parameter: None,
            fixed_reference_extent: None,
        }
    }

    pub fn name(&self) -> &str {
        &self.name
    }

    pub(crate) fn with_slice_length_parameter(mut self, parameter: usize) -> Self {
        self.slice_length_parameter = Some(parameter);
        self
    }

    pub(crate) fn with_fixed_reference_extent(mut self, bytes: u32) -> Self {
        self.fixed_reference_extent = Some(bytes);
        self
    }

    pub fn program_type(&self) -> ProgramType {
        self.program_type
    }

    pub fn aggregate_layout(&self) -> Option<&AggregateLayout> {
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

    /// The class of the object a pointer parameter designates
    /// (`design/effective-types.md`).
    pub fn with_pointee_class(
        mut self,
        pointee_class: Option<crate::kernel::effective_type::CAccessClass>,
    ) -> Self {
        self.pointee_class = pointee_class;
        self
    }

    pub fn pointee_class(&self) -> Option<crate::kernel::effective_type::CAccessClass> {
        self.pointee_class.clone()
    }

    pub fn with_aggregate_layout(mut self, layout: AggregateLayout) -> Self {
        self.aggregate_layout = Some(layout);
        self
    }
}

impl Global {
    pub fn new(
        name: impl Into<String>,
        program_type: ProgramType,
        initial_value: ProgramValue,
    ) -> Self {
        let name = name.into();
        Self::new_with_kernel_name(name.clone(), name, program_type, initial_value)
    }

    pub fn new_with_kernel_name(
        source_name: impl Into<String>,
        kernel_name: impl Into<String>,
        program_type: ProgramType,
        initial_value: ProgramValue,
    ) -> Self {
        assert!(
            matches!(
                program_type,
                ProgramType::Bool
                    | ProgramType::Int8
                    | ProgramType::Int16
                    | ProgramType::Int32
                    | ProgramType::UInt8
                    | ProgramType::UInt16
                    | ProgramType::UInt32
                    | ProgramType::Int64
                    | ProgramType::UInt64
                    | ProgramType::Float32
                    | ProgramType::Float64
                    | ProgramType::Int8Pointer
                    | ProgramType::Int16Pointer
                    | ProgramType::UInt16Pointer
                    | ProgramType::Int32Pointer
                    | ProgramType::UInt8Pointer
                    | ProgramType::UInt32Pointer
                    | ProgramType::Int128Pointer
                    | ProgramType::Int64Pointer
                    | ProgramType::UInt128Pointer
                    | ProgramType::UInt64Pointer
                    | ProgramType::Float32Pointer
                    | ProgramType::Float64Pointer
                    | ProgramType::Int8PointerPointer
                    | ProgramType::Int16PointerPointer
                    | ProgramType::UInt16PointerPointer
                    | ProgramType::Int32PointerPointer
                    | ProgramType::UInt8PointerPointer
                    | ProgramType::UInt32PointerPointer
                    | ProgramType::Int128PointerPointer
                    | ProgramType::Int64PointerPointer
                    | ProgramType::UInt128PointerPointer
                    | ProgramType::UInt64PointerPointer
                    | ProgramType::Float32PointerPointer
                    | ProgramType::Float64PointerPointer
            ),
            "C globals currently support scalar integer, floating-point, and pointer types"
        );
        assert_eq!(
            initial_value.program_type(),
            program_type,
            "C global initializer must match its declared type"
        );
        Self {
            source_name: source_name.into(),
            kernel_name: kernel_name.into(),
            program_type,
            initial_value,
            volatile: false,
            pointee_volatile: false,
            constant: false,
            pointee_constant: false,
            declared_class: None,
        }
    }

    /// Records the class the frontend gives the object.
    pub fn with_declared_class(
        mut self,
        class: Option<crate::kernel::effective_type::CAccessClass>,
    ) -> Self {
        // A class the kernel type already gives is not stored, so a
        // declaration lowered with and without the frontend's knowledge
        // stays one declaration.
        let derived =
            crate::kernel::effective_type::CAccessClass::of_kernel_type(self.program_type);
        self.declared_class = class.filter(|class| derived.as_ref() != Some(class));
        self
    }

    /// The class the object's block records: the frontend's, or what the
    /// kernel type gives.
    pub fn declared_class(&self) -> Option<crate::kernel::effective_type::CAccessClass> {
        self.declared_class.clone().or_else(|| {
            crate::kernel::effective_type::CAccessClass::of_kernel_type(self.program_type)
        })
    }

    pub fn name(&self) -> &str {
        &self.source_name
    }

    pub fn kernel_name(&self) -> &str {
        &self.kernel_name
    }

    pub fn program_type(&self) -> ProgramType {
        self.program_type
    }

    pub fn initial_value(&self) -> &ProgramValue {
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

impl GlobalArray {
    pub fn new_with_kernel_name(
        source_name: impl Into<String>,
        kernel_name: impl Into<String>,
        element_type: ProgramType,
        length: u32,
        initial_values: impl Into<ArrayContents>,
    ) -> Self {
        assert!(
            matches!(
                element_type,
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
            ) || element_type.is_pointer(),
            "C global arrays require supported scalar or pointer elements"
        );
        assert!(length > 0, "C global arrays must have positive length");
        let initial_values = initial_values.into();
        assert_eq!(
            initial_values.length(),
            length,
            "C global array initializer must cover its declared length"
        );
        assert!(
            initial_values
                .values()
                .all(|value| value.program_type() == element_type),
            "C global array initializers must match their declared element type"
        );
        Self {
            source_name: source_name.into(),
            kernel_name: kernel_name.into(),
            element_type,
            length,
            initial_values,
            constant: false,
            declared_class: None,
        }
    }

    /// Records the class the frontend gives the object.
    pub fn with_declared_class(
        mut self,
        class: Option<crate::kernel::effective_type::CAccessClass>,
    ) -> Self {
        // A class the kernel type already gives is not stored, so a
        // declaration lowered with and without the frontend's knowledge
        // stays one declaration.
        let derived =
            crate::kernel::effective_type::CAccessClass::of_kernel_type(self.element_type);
        self.declared_class = class.filter(|class| derived.as_ref() != Some(class));
        self
    }

    /// The class the object's block records: the frontend's, or what the
    /// kernel type gives.
    pub fn declared_class(&self) -> Option<crate::kernel::effective_type::CAccessClass> {
        self.declared_class.clone().or_else(|| {
            crate::kernel::effective_type::CAccessClass::of_kernel_type(self.element_type)
        })
    }

    pub fn name(&self) -> &str {
        &self.source_name
    }

    pub fn kernel_name(&self) -> &str {
        &self.kernel_name
    }

    pub fn element_type(&self) -> ProgramType {
        self.element_type
    }

    pub fn length(&self) -> u32 {
        self.length
    }

    pub fn initial_values(&self) -> &ArrayContents {
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

impl GlobalAggregate {
    pub fn new(
        source_name: impl Into<String>,
        kernel_name: impl Into<String>,
        layout: AggregateLayout,
        initializers: Vec<AggregateInitializer>,
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
            declared_class: None,
        }
    }

    /// Records the class the frontend gives the object.
    pub fn with_declared_class(
        mut self,
        class: Option<crate::kernel::effective_type::CAccessClass>,
    ) -> Self {
        self.declared_class = class;
        self
    }

    /// The class the object's block records: the frontend's, or what the
    /// kernel type gives.
    pub fn declared_class(&self) -> Option<crate::kernel::effective_type::CAccessClass> {
        self.declared_class.clone()
    }

    pub fn source_name(&self) -> &str {
        &self.source_name
    }

    pub fn kernel_name(&self) -> &str {
        &self.kernel_name
    }

    pub fn layout(&self) -> &AggregateLayout {
        &self.layout
    }

    pub fn initializers(&self) -> &[AggregateInitializer] {
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

impl GlobalAggregateArray {
    pub fn new(
        source_name: impl Into<String>,
        kernel_name: impl Into<String>,
        layout: AggregateLayout,
        length: u32,
        initializers: Vec<AggregateInitializer>,
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
            declared_class: None,
        }
    }

    /// Records the class the frontend gives the object.
    pub fn with_declared_class(
        mut self,
        class: Option<crate::kernel::effective_type::CAccessClass>,
    ) -> Self {
        self.declared_class = class;
        self
    }

    /// The class the object's block records: the frontend's, or what the
    /// kernel type gives.
    pub fn declared_class(&self) -> Option<crate::kernel::effective_type::CAccessClass> {
        self.declared_class.clone()
    }

    pub fn source_name(&self) -> &str {
        &self.source_name
    }

    pub fn kernel_name(&self) -> &str {
        &self.kernel_name
    }

    pub fn layout(&self) -> &AggregateLayout {
        &self.layout
    }

    pub fn length(&self) -> u32 {
        self.length
    }

    pub fn initializers(&self) -> &[AggregateInitializer] {
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

impl StaticLocal {
    pub fn new(
        source_name: impl Into<String>,
        kernel_name: impl Into<String>,
        program_type: ProgramType,
        initial_value: ProgramValue,
    ) -> Self {
        assert!(
            matches!(
                program_type,
                ProgramType::Bool
                    | ProgramType::Int8
                    | ProgramType::Int16
                    | ProgramType::Int32
                    | ProgramType::UInt8
                    | ProgramType::UInt16
                    | ProgramType::UInt32
                    | ProgramType::Float32
                    | ProgramType::Float64
                    | ProgramType::Int8Pointer
                    | ProgramType::Int16Pointer
                    | ProgramType::UInt16Pointer
                    | ProgramType::Int32Pointer
                    | ProgramType::UInt8Pointer
                    | ProgramType::UInt32Pointer
                    | ProgramType::Int128Pointer
                    | ProgramType::Int64Pointer
                    | ProgramType::UInt128Pointer
                    | ProgramType::UInt64Pointer
                    | ProgramType::Float32Pointer
                    | ProgramType::Float64Pointer
                    | ProgramType::Int8PointerPointer
                    | ProgramType::Int16PointerPointer
                    | ProgramType::UInt16PointerPointer
                    | ProgramType::Int32PointerPointer
                    | ProgramType::UInt8PointerPointer
                    | ProgramType::UInt32PointerPointer
                    | ProgramType::Int128PointerPointer
                    | ProgramType::Int64PointerPointer
                    | ProgramType::UInt128PointerPointer
                    | ProgramType::UInt64PointerPointer
                    | ProgramType::Float32PointerPointer
                    | ProgramType::Float64PointerPointer
            ),
            "C static locals currently support scalar integer, floating-point, and pointer types"
        );
        assert_eq!(
            initial_value.program_type(),
            program_type,
            "C static local initializer must match its declared type"
        );
        Self {
            source_name: source_name.into(),
            kernel_name: kernel_name.into(),
            program_type,
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

    pub fn program_type(&self) -> ProgramType {
        self.program_type
    }

    pub fn initial_value(&self) -> &ProgramValue {
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

impl StaticArray {
    pub fn new(
        source_name: impl Into<String>,
        kernel_name: impl Into<String>,
        element_type: ProgramType,
        length: u32,
        initial_values: impl Into<ArrayContents>,
    ) -> Self {
        assert!(
            matches!(
                element_type,
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
            ) || element_type.is_pointer(),
            "C static local arrays require supported scalar or pointer elements"
        );
        assert!(
            length > 0,
            "C static local arrays must have positive length"
        );
        let initial_values = initial_values.into();
        assert_eq!(
            initial_values.length(),
            length,
            "C static local array initializer must cover its declared length"
        );
        assert!(
            initial_values
                .values()
                .all(|value| value.program_type() == element_type),
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

    pub fn element_type(&self) -> ProgramType {
        self.element_type
    }

    pub fn length(&self) -> u32 {
        self.length
    }

    pub fn initial_values(&self) -> &ArrayContents {
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

impl StaticAggregate {
    pub fn new(
        source_name: impl Into<String>,
        kernel_name: impl Into<String>,
        layout: AggregateLayout,
        initializers: Vec<AggregateInitializer>,
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

    pub fn layout(&self) -> &AggregateLayout {
        &self.layout
    }

    pub fn initializers(&self) -> &[AggregateInitializer] {
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

impl StaticAggregateArray {
    pub fn new(
        source_name: impl Into<String>,
        kernel_name: impl Into<String>,
        layout: AggregateLayout,
        length: u32,
        initializers: Vec<AggregateInitializer>,
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

    pub fn layout(&self) -> &AggregateLayout {
        &self.layout
    }

    pub fn length(&self) -> u32 {
        self.length
    }

    pub fn initializers(&self) -> &[AggregateInitializer] {
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

impl StringLiteral {
    pub fn new(name: impl Into<String>, bytes: Vec<u8>) -> Self {
        assert_eq!(
            bytes.last(),
            Some(&0),
            "C string literals require a NUL terminator"
        );
        Self {
            name: name.into(),
            bytes,
            element_type: ProgramType::UInt8,
        }
    }

    /// A literal whose elements are plain `char` of the given signedness'
    /// kernel type, `UInt8` or `Int8`.
    pub fn with_element_type(mut self, element_type: ProgramType) -> Self {
        assert!(
            matches!(element_type, ProgramType::UInt8 | ProgramType::Int8),
            "C string literal elements are character cells"
        );
        self.element_type = element_type;
        self
    }

    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn bytes(&self) -> &[u8] {
        &self.bytes
    }

    pub fn element_type(&self) -> ProgramType {
        self.element_type
    }

    /// The cell value the literal stores for byte `byte`.
    pub(crate) fn element_value(&self, byte: u8) -> ProgramValue {
        match self.element_type {
            ProgramType::Int8 => crate::kernel::int8(byte as i8 as i32 as u32),
            _ => crate::kernel::uint8(u32::from(byte)),
        }
    }
}

impl FunctionContractInterface {
    pub(crate) fn new(return_type: ProgramType, parameters: Vec<ProgramParameter>) -> Self {
        Self {
            return_type,
            return_pointee_constant: false,
            return_pointee_class: None,
            object_type_requirements: Default::default(),
            return_object_type_guarantee: None,
            return_aggregate_layout: None,
            aggregate_return_mode: AggregateReturnMode::Copy,
            construction_parameter: None,
            exceptional_signature: ExceptionalSignature::None,
            parameters,
            proof_parameters: Default::default(),
            value_parameters: Vec::new(),
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
            ordinary_abstract_families: Vec::new(),
            predicate_unfoldings: Vec::new(),
            recursion_measure: Vec::new(),
            recursion_peers: Vec::new(),
            recursion_binder: None,
        }
    }

    fn refresh_object_types(&mut self) {
        self.object_type_requirements = crate::kernel::object_types::declared_requirements(self);
        self.return_object_type_guarantee =
            crate::kernel::object_types::declared_return_class(self);
    }

    pub(crate) fn object_type_requirements(&self) -> &ObjectTypeRequirements {
        &self.object_type_requirements
    }

    pub fn return_type(&self) -> ProgramType {
        self.return_type
    }

    pub fn return_pointee_is_constant(&self) -> bool {
        self.return_pointee_constant
    }

    pub fn return_pointee_class(&self) -> Option<crate::kernel::effective_type::CAccessClass> {
        self.return_pointee_class.clone()
    }

    pub fn return_aggregate_layout(&self) -> Option<&AggregateLayout> {
        self.return_aggregate_layout.as_ref()
    }

    pub fn aggregate_return_mode(&self) -> AggregateReturnMode {
        self.aggregate_return_mode
    }

    /// An ordinary pointer parameter whose selected object is initialized on return.
    pub fn construction_parameter(&self) -> Option<(usize, &AggregateLayout)> {
        self.construction_parameter
            .as_ref()
            .map(|(index, layout)| (*index, layout))
    }

    pub fn parameters(&self) -> &[ProgramParameter] {
        &self.parameters
    }

    pub(crate) fn exceptional_signature(&self) -> ExceptionalSignature {
        self.exceptional_signature
    }

    pub(crate) fn proof_parameters(&self) -> &[ResourceSpec] {
        &self.proof_parameters
    }

    pub(crate) fn with_proof_parameters(mut self, parameters: Vec<ResourceSpec>) -> Self {
        self.proof_parameters = parameters.into();
        self
    }

    pub(crate) fn value_parameters(&self) -> &[ProgramParameter] {
        &self.value_parameters
    }

    /// This interface with its last `count` parameters as value parameters:
    /// a named contract lowers its `let amount: int32;` declarations after
    /// its call parameters.
    pub(crate) fn with_trailing_value_parameters(mut self, count: usize) -> Option<Self> {
        let call_count = self.parameters.len().checked_sub(count)?;
        self.value_parameters = self.parameters.split_off(call_count);
        self.refresh_object_types();
        Some(self)
    }

    pub(crate) fn with_leading_value_parameters(mut self, count: usize) -> Option<Self> {
        if count > self.parameters.len() {
            return None;
        }
        let call_parameters = self.parameters.split_off(count);
        self.value_parameters = std::mem::replace(&mut self.parameters, call_parameters);
        self.refresh_object_types();
        Some(self)
    }

    pub fn resource_requires(&self) -> &[ResourceSpec] {
        &self.resource_requires
    }

    pub fn resource_ensures(&self) -> &[ResourceSpec] {
        &self.resource_ensures
    }

    pub fn resource_constructors(&self) -> &[ResourceSpec] {
        &self.resource_constructors
    }

    pub fn contract_requires(&self) -> &[SpecProposition] {
        &self.contract_requires
    }

    /// The declared expression `decreases` measure, if the function has one.
    pub fn recursion_measure(&self) -> Option<&[RankingComponent]> {
        (!self.recursion_measure.is_empty()).then_some(self.recursion_measure.as_slice())
    }

    /// The other members of this function's recursive component that its
    /// expression measure ranks calls to, sorted.
    pub fn recursion_peers(&self) -> &[String] {
        &self.recursion_peers
    }

    /// The binder a call-ranked structural `decreases t` measure names.
    pub fn recursion_binder(&self) -> Option<&str> {
        self.recursion_binder.as_deref()
    }

    /// Whether this function's recursion is ranked by obligations at its
    /// calls: an expression measure, or a call-ranked structural binder.
    pub fn has_call_ranked_recursion(&self) -> bool {
        !self.recursion_measure.is_empty() || self.recursion_binder.is_some()
    }

    /// The identity of a resource requirement's named instance binder.
    pub(crate) fn resource_binder_identity(&self, binder: &str) -> Option<Variable> {
        self.resource_requires
            .iter()
            .find_map(|requirement| match requirement.term() {
                ResourceTerm::Instance {
                    identity,
                    binder: name,
                    ..
                } if name == binder => Some(*identity),
                _ => None,
            })
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

    pub fn contract_mutable(&self) -> &[MemorySegment] {
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

    pub fn contract_claims(&self) -> &[FunctionContractClaim] {
        &self.contract_claims
    }

    pub fn opaque_contract_supported(&self) -> bool {
        self.opaque_contract_supported && self.exceptional_signature.is_empty()
    }

    /// Whether this interface can be applied as a modular call: a direct
    /// call, an external declaration, or a named contract a call through a
    /// pointer is made under. A throwing interface is narrower than an
    /// ordinary one: only the checked scalar channel and pure clauses cross
    /// the boundary, with no resource or mutable-effect transfer.
    pub(crate) fn verified_direct_contract_supported(&self) -> bool {
        if self.exceptional_signature.is_empty() {
            return self.opaque_contract_supported();
        }
        self.opaque_contract_supported
            && self.exceptional_signature == ExceptionalSignature::Int32
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

    pub fn composite_resource_definitions(&self) -> &[CompositeResourceDefinition] {
        &self.composite_resource_definitions
    }

    pub(crate) fn composite_resource_definition(
        &self,
        name: &str,
    ) -> Option<&CompositeResourceDefinition> {
        self.composite_resource_definitions
            .binary_search_by(|definition| definition.name().cmp(name))
            .ok()
            .map(|index| &self.composite_resource_definitions[index])
    }

    /// Whether `name` is an abstract family declared without `authorized`.
    pub(crate) fn is_ordinary_abstract_family(&self, name: &str) -> bool {
        self.ordinary_abstract_families
            .binary_search_by(|family| family.as_str().cmp(name))
            .is_ok()
    }

    pub fn predicate_unfoldings(&self) -> &[PredicateUnfolding] {
        &self.predicate_unfoldings
    }

    /// The type of a pointer to a function with this interface. Whether the
    /// function may throw is not part of it: a C pointer type cannot say, and
    /// a call through a pointer may throw exactly when the contract it is
    /// called under, or its known target's own interface, says so.
    pub(crate) fn function_pointer_type(&self) -> ProgramType {
        ProgramType::FunctionPointer(ProgramType::qualified_function_pointer_signature(
            self.return_type(),
            self.return_pointee_is_constant(),
            &self
                .parameters()
                .iter()
                .map(|parameter| (parameter.program_type(), parameter.pointee_is_constant()))
                .collect::<Vec<_>>(),
        ))
    }

    /// Compare exactly the semantic interface, including normalized resource
    /// role/snapshot metadata, while ignoring its nominal contract name.
    pub(crate) fn exactly_matches(&self, other: &Self) -> bool {
        self.return_type == other.return_type
            && self.return_pointee_constant == other.return_pointee_constant
            && self.return_aggregate_layout == other.return_aggregate_layout
            && self.aggregate_return_mode == other.aggregate_return_mode
            && self.construction_parameter == other.construction_parameter
            && self.exceptional_signature == other.exceptional_signature
            && self.parameters == other.parameters
            && self.proof_parameters == other.proof_parameters
            && self.value_parameters == other.value_parameters
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
            && self.recursion_peers == other.recursion_peers
            && self.recursion_binder == other.recursion_binder
    }

    /// Compare the signature and resource vocabulary used by automatic
    /// callback formation. Proof binders and behavioral clauses are checked by
    /// their dedicated refinement judgments.
    pub(crate) fn has_compatible_signature_and_resource_vocabulary(&self, other: &Self) -> bool {
        self.has_compatible_signature_and_composite_vocabulary(other)
            && self.proof_parameters.is_empty()
    }

    pub(crate) fn has_compatible_signature_and_composite_vocabulary(&self, other: &Self) -> bool {
        self.aggregate_return_mode == AggregateReturnMode::Copy
            && self.construction_parameter.is_none()
            && self.return_type == other.return_type
            && self.return_pointee_constant == other.return_pointee_constant
            && self.return_aggregate_layout == other.return_aggregate_layout
            && self.aggregate_return_mode == other.aggregate_return_mode
            && self.construction_parameter == other.construction_parameter
            // A function that never throws implements a contract that may.
            && (other.exceptional_signature.is_empty()
                || self.exceptional_signature == other.exceptional_signature)
            && self.parameters.len() == other.parameters.len()
            && self
                .parameters
                .iter()
                .zip(&other.parameters)
                .all(|(left, right)| {
                    left.program_type == right.program_type
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

impl ProgramFunction {
    pub(crate) fn with_program_entry(mut self) -> Self {
        self.program_entry = true;
        self
    }

    pub fn is_program_entry(&self) -> bool {
        self.program_entry
    }

    pub fn new(
        return_type: ProgramType,
        name: impl Into<String>,
        parameters: Vec<ProgramParameter>,
        body: ProgramStatement,
    ) -> Self {
        Self {
            program_entry: false,
            name: name.into(),
            inline_body: false,
            source_body: body.clone(),
            body,
            control_targets: std::sync::Arc::new(BTreeMap::new()),
            contract_interface: Arc::new(FunctionContractInterface::new(return_type, parameters)),
            global_variables: Vec::new(),
            global_arrays: Vec::new(),
            static_variables: Vec::new(),
            static_storage: std::sync::Arc::new(FunctionStaticStorage {
                static_arrays: Vec::new(),
                global_aggregates: Vec::new(),
                global_aggregate_arrays: Vec::new(),
                static_aggregates: Vec::new(),
                static_aggregate_arrays: Vec::new(),
            }),
            string_literals: Vec::new(),
            address_taken_locals: AddressTakenLocals::default(),
        }
    }

    pub fn with_global_variables(mut self, global_variables: Vec<Global>) -> Self {
        self.global_variables = global_variables;
        self
    }

    pub fn with_global_arrays(mut self, global_arrays: Vec<GlobalArray>) -> Self {
        self.global_arrays = global_arrays;
        self
    }

    pub fn with_global_aggregates(mut self, global_aggregates: Vec<GlobalAggregate>) -> Self {
        let mut static_storage = (*self.static_storage).clone();
        static_storage.global_aggregates = global_aggregates;
        self.static_storage = std::sync::Arc::new(static_storage);
        self
    }

    pub fn with_global_aggregate_arrays(
        mut self,
        global_aggregate_arrays: Vec<GlobalAggregateArray>,
    ) -> Self {
        let mut static_storage = (*self.static_storage).clone();
        static_storage.global_aggregate_arrays = global_aggregate_arrays;
        self.static_storage = std::sync::Arc::new(static_storage);
        self
    }

    pub fn with_static_variables(mut self, static_variables: Vec<StaticLocal>) -> Self {
        self.static_variables = static_variables;
        self
    }

    pub fn with_static_arrays(mut self, static_arrays: Vec<StaticArray>) -> Self {
        let mut static_storage = (*self.static_storage).clone();
        static_storage.static_arrays = static_arrays;
        self.static_storage = std::sync::Arc::new(static_storage);
        self
    }

    pub fn with_static_aggregates(mut self, static_aggregates: Vec<StaticAggregate>) -> Self {
        let mut static_storage = (*self.static_storage).clone();
        static_storage.static_aggregates = static_aggregates;
        self.static_storage = std::sync::Arc::new(static_storage);
        self
    }

    pub fn with_static_aggregate_arrays(
        mut self,
        static_aggregate_arrays: Vec<StaticAggregateArray>,
    ) -> Self {
        let mut static_storage = (*self.static_storage).clone();
        static_storage.static_aggregate_arrays = static_aggregate_arrays;
        self.static_storage = std::sync::Arc::new(static_storage);
        self
    }

    pub fn with_string_literals(mut self, string_literals: Vec<StringLiteral>) -> Self {
        self.string_literals = string_literals;
        self
    }

    pub fn with_source_body(mut self, source_body: ProgramStatement) -> Self {
        self.source_body = source_body;
        self
    }

    pub(crate) fn with_control_targets(
        mut self,
        control_targets: BTreeMap<ControlTargetId, ControlTarget>,
    ) -> Self {
        self.control_targets = std::sync::Arc::new(control_targets);
        self
    }

    pub(crate) fn with_control_targets_from(mut self, source: &Self) -> Self {
        self.control_targets = source.control_targets.clone();
        self
    }

    pub(crate) fn control_target(&self, target: ControlTargetId) -> Option<&ControlTarget> {
        self.control_targets.get(&target)
    }

    pub(crate) fn control_target_count(&self) -> usize {
        self.control_targets.len()
    }

    pub(crate) fn with_body(mut self, body: ProgramStatement) -> Self {
        self.body = body;
        self.address_taken_locals = AddressTakenLocals::default();
        self
    }

    /// Proof-only body annotations do not change a checked function entry.
    /// Every other part of its semantic identity must still match. The
    /// exhaustive pattern makes new function metadata opt into this check.
    pub(in crate::kernel) fn has_same_entry_and_source(&self, other: &Self) -> bool {
        let Self {
            program_entry,
            name,
            inline_body,
            body: _,
            source_body,
            control_targets,
            contract_interface,
            global_variables,
            global_arrays,
            static_variables,
            static_storage,
            string_literals,
            address_taken_locals: _,
        } = self;
        *program_entry == other.program_entry
            && name == &other.name
            && *inline_body == other.inline_body
            && source_body == &other.source_body
            && control_targets == &other.control_targets
            && contract_interface == &other.contract_interface
            && global_variables == &other.global_variables
            && global_arrays == &other.global_arrays
            && static_variables == &other.static_variables
            && static_storage == &other.static_storage
            && string_literals == &other.string_literals
    }

    pub fn with_resource_summary(
        mut self,
        requires: Vec<ResourceSpec>,
        ensures: Vec<ResourceSpec>,
    ) -> Self {
        Arc::make_mut(&mut self.contract_interface).resource_requires = requires;
        Arc::make_mut(&mut self.contract_interface).resource_ensures = ensures;
        self
    }

    pub fn with_resource_constructors(mut self, constructors: Vec<ResourceSpec>) -> Self {
        Arc::make_mut(&mut self.contract_interface).resource_constructors = constructors;
        self
    }

    /// Internal staging hook for importers and tests. No source frontend opts
    /// into the exceptional channel yet.
    pub(crate) fn with_int32_exceptional_outcome(mut self) -> Self {
        Arc::make_mut(&mut self.contract_interface).exceptional_signature =
            ExceptionalSignature::Int32;
        self
    }

    /// Internal staging hook for the exceptional postcondition family. The
    /// payload is available to these propositions through the kernel's
    /// exceptional-result binding.
    pub(crate) fn with_exceptional_ensures(mut self, ensures: Vec<SpecProposition>) -> Self {
        Arc::make_mut(&mut self.contract_interface).exceptional_ensures = ensures;
        Arc::make_mut(&mut self.contract_interface).refresh_object_types();
        self
    }

    pub fn with_contract(
        mut self,
        requires: Vec<SpecProposition>,
        ensures: Vec<SpecProposition>,
        mutable: Vec<MemorySegment>,
        claims: Vec<FunctionContractClaim>,
        opaque_supported: bool,
    ) -> Self {
        Arc::make_mut(&mut self.contract_interface).contract_requires = requires;
        Arc::make_mut(&mut self.contract_interface).contract_requirement_sources =
            ContractRequirementSources(vec![None; self.contract_interface.contract_requires.len()]);
        Arc::make_mut(&mut self.contract_interface).contract_ensures = ensures;
        Arc::make_mut(&mut self.contract_interface).contract_mutable = mutable;
        Arc::make_mut(&mut self.contract_interface).resource_derived_frame_mixed = false;
        Arc::make_mut(&mut self.contract_interface).contract_effect_claim_required =
            !self.contract_interface.contract_mutable.is_empty();
        Arc::make_mut(&mut self.contract_interface).resource_derived_mutable_frame = false;
        Arc::make_mut(&mut self.contract_interface).contract_claims = claims;
        Arc::make_mut(&mut self.contract_interface).opaque_contract_supported = opaque_supported;
        Arc::make_mut(&mut self.contract_interface).refresh_object_types();
        self
    }

    /// Records the function's declared expression `decreases` measure.
    ///
    /// The measure is part of the contract interface, so it is part of this
    /// function's semantic identity: a verified rule, and every claim bound
    /// to it, names the function that declared the measure, and a function
    /// that declares none is a different `ProgramFunction`.
    pub fn with_recursion_measure(mut self, measure: Vec<RankingComponent>) -> Self {
        Arc::make_mut(&mut self.contract_interface).recursion_measure = measure;
        self
    }

    /// Declares the other members of this function's recursive component.
    /// They are part of the interface, and so of this function's identity:
    /// the anchor a certification builds from the interface ranks calls to
    /// exactly these functions.
    /// Declares a structural `decreases t` measure ranked at each call.
    pub fn with_recursion_binder(mut self, binder: Option<String>) -> Self {
        Arc::make_mut(&mut self.contract_interface).recursion_binder = binder;
        self
    }

    pub fn with_recursion_peers(mut self, mut peers: Vec<String>) -> Self {
        peers.sort();
        peers.dedup();
        peers.retain(|peer| peer != &self.name);
        Arc::make_mut(&mut self.contract_interface).recursion_peers = peers;
        self
    }

    pub(crate) fn with_contract_requirement_sources(mut self, sources: Vec<Option<usize>>) -> Self {
        assert_eq!(
            sources.len(),
            self.contract_interface.contract_requires.len(),
            "contract requirement source map must match lowered requirements"
        );
        Arc::make_mut(&mut self.contract_interface).contract_requirement_sources =
            ContractRequirementSources(sources);
        self
    }

    #[cfg(test)]
    pub(crate) fn without_test_contract_requirement_sources(mut self) -> Self {
        Arc::make_mut(&mut self.contract_interface).contract_requirement_sources =
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
        Arc::make_mut(&mut self.contract_interface).contract_effect_claim_required = false;
        Arc::make_mut(&mut self.contract_interface).resource_derived_frame_mixed =
            !self.contract_interface.contract_mutable.is_empty();
        Arc::make_mut(&mut self.contract_interface).resource_derived_mutable_frame = true;
        self
    }

    pub fn with_composite_resource_definitions(
        mut self,
        mut definitions: Vec<CompositeResourceDefinition>,
    ) -> Self {
        definitions.sort_by(|left, right| left.name().cmp(right.name()));
        super::super::thread_confinement::propagate_thread_confinement(&mut definitions);
        super::super::owned_footprint_reach::propagate_owned_footprint_reach(&mut definitions);
        Arc::make_mut(&mut self.contract_interface).composite_resource_definitions = definitions;
        self
    }

    pub(crate) fn composite_resource_definition(
        &self,
        name: &str,
    ) -> Option<&CompositeResourceDefinition> {
        self.contract_interface.composite_resource_definition(name)
    }

    /// The definition a proof step may fold, unfold, or observe: none for a
    /// sealed family, whose instances only trusted contracts move.
    pub(crate) fn proof_composite_resource_definition(
        &self,
        name: &str,
    ) -> Option<&CompositeResourceDefinition> {
        self.composite_resource_definition(name)
            .filter(|definition| !definition.is_sealed())
    }

    /// Records the abstract families declared without `authorized`.
    pub fn with_ordinary_abstract_families(mut self, mut families: Vec<String>) -> Self {
        families.sort();
        families.dedup();
        Arc::make_mut(&mut self.contract_interface).ordinary_abstract_families = families;
        self
    }

    pub fn with_predicate_unfoldings(mut self, unfoldings: Vec<PredicateUnfolding>) -> Self {
        Arc::make_mut(&mut self.contract_interface).predicate_unfoldings = unfoldings;
        self
    }

    pub fn return_type(&self) -> ProgramType {
        self.contract_interface.return_type()
    }

    pub fn with_return_pointee_constant(mut self, constant: bool) -> Self {
        Arc::make_mut(&mut self.contract_interface).return_pointee_constant = constant;
        self
    }

    pub fn with_return_pointee_class(
        mut self,
        class: Option<crate::kernel::effective_type::CAccessClass>,
    ) -> Self {
        Arc::make_mut(&mut self.contract_interface).return_pointee_class = class;
        self
    }

    pub fn return_pointee_is_constant(&self) -> bool {
        self.contract_interface.return_pointee_is_constant()
    }

    pub fn return_aggregate_layout(&self) -> Option<&AggregateLayout> {
        self.contract_interface.return_aggregate_layout()
    }

    pub fn with_return_aggregate_layout(mut self, layout: AggregateLayout) -> Self {
        Arc::make_mut(&mut self.contract_interface).return_aggregate_layout = Some(layout);
        Arc::make_mut(&mut self.contract_interface).aggregate_return_mode =
            AggregateReturnMode::Copy;
        self
    }

    /// Selects completion into a separately supplied call destination. The
    /// contract must describe its actual storage authority and write effects.
    pub fn with_construction_return(mut self, layout: AggregateLayout) -> Self {
        Arc::make_mut(&mut self.contract_interface).return_aggregate_layout = Some(layout);
        Arc::make_mut(&mut self.contract_interface).aggregate_return_mode =
            AggregateReturnMode::Construction;
        self
    }

    /// Requires a nonthrowing void body to initialize the object named
    /// by this ordinary pointer parameter. Binding grants no storage or authority.
    /// Checked summaries retain the initialization established by the body.
    pub fn with_construction_parameter(mut self, index: usize, layout: AggregateLayout) -> Self {
        Arc::make_mut(&mut self.contract_interface).construction_parameter = Some((index, layout));
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

    pub fn parameters(&self) -> &[ProgramParameter] {
        self.contract_interface.parameters()
    }

    pub(crate) fn pop_parameter(&mut self) -> Option<ProgramParameter> {
        Arc::make_mut(&mut self.contract_interface).parameters.pop()
    }

    /// This function with its last `count` parameters as contract value
    /// parameters: values its contract names that are not C arguments. A
    /// call binds them per call; the body is proved for every value.
    pub(crate) fn with_trailing_value_parameters(mut self, count: usize) -> Option<Self> {
        if count == 0 {
            return Some(self);
        }
        self.contract_interface = Arc::new(
            Arc::unwrap_or_clone(self.contract_interface).with_trailing_value_parameters(count)?,
        );
        Some(self)
    }

    pub fn global_variables(&self) -> &[Global] {
        &self.global_variables
    }

    pub fn global_arrays(&self) -> &[GlobalArray] {
        &self.global_arrays
    }

    pub fn global_aggregates(&self) -> &[GlobalAggregate] {
        self.static_storage.global_aggregates.as_slice()
    }

    pub fn global_aggregate_arrays(&self) -> &[GlobalAggregateArray] {
        self.static_storage.global_aggregate_arrays.as_slice()
    }

    pub fn static_variables(&self) -> &[StaticLocal] {
        &self.static_variables
    }

    pub fn static_arrays(&self) -> &[StaticArray] {
        self.static_storage.static_arrays.as_slice()
    }

    pub fn static_aggregates(&self) -> &[StaticAggregate] {
        self.static_storage.static_aggregates.as_slice()
    }

    pub fn static_aggregate_arrays(&self) -> &[StaticAggregateArray] {
        self.static_storage.static_aggregate_arrays.as_slice()
    }

    pub fn string_literals(&self) -> &[StringLiteral] {
        &self.string_literals
    }

    pub(crate) fn function_pointer_type(&self) -> ProgramType {
        self.contract_interface.function_pointer_type()
    }

    pub(crate) fn exceptional_signature(&self) -> ExceptionalSignature {
        self.contract_interface.exceptional_signature()
    }

    pub fn body(&self) -> &ProgramStatement {
        &self.body
    }

    pub fn source_body(&self) -> &ProgramStatement {
        &self.source_body
    }

    pub fn resource_requires(&self) -> &[ResourceSpec] {
        self.contract_interface.resource_requires()
    }

    pub fn resource_ensures(&self) -> &[ResourceSpec] {
        self.contract_interface.resource_ensures()
    }

    pub fn resource_constructors(&self) -> &[ResourceSpec] {
        self.contract_interface.resource_constructors()
    }

    pub fn contract_requires(&self) -> &[SpecProposition] {
        self.contract_interface.contract_requires()
    }

    pub(crate) fn pop_contract_requirement(&mut self) -> Option<SpecProposition> {
        Arc::make_mut(&mut self.contract_interface)
            .contract_requires
            .pop()
    }

    pub fn contract_ensures(&self) -> &[SpecProposition] {
        self.contract_interface.contract_ensures()
    }

    pub(crate) fn exceptional_ensures(&self) -> &[SpecProposition] {
        self.contract_interface.exceptional_ensures()
    }

    pub fn contract_mutable(&self) -> &[MemorySegment] {
        self.contract_interface.contract_mutable()
    }

    pub(crate) fn contract_effect_claim_required(&self) -> bool {
        self.contract_interface.contract_effect_claim_required()
    }

    pub(crate) fn resource_derived_mutable_frame(&self) -> bool {
        self.contract_interface.resource_derived_mutable_frame()
    }

    pub fn contract_claims(&self) -> &[FunctionContractClaim] {
        self.contract_interface.contract_claims()
    }

    pub fn opaque_contract_supported(&self) -> bool {
        self.contract_interface.opaque_contract_supported()
            && !statement_contains_internal_throw(&self.body)
    }

    pub(crate) fn verified_direct_contract_supported(&self) -> bool {
        self.contract_interface.verified_direct_contract_supported()
            && (self.exceptional_signature().is_empty()
                || self.exceptional_signature() == ExceptionalSignature::Int32)
            && (!self.has_internal_exceptional_outcome()
                || !self.exceptional_signature().is_empty())
    }

    pub(crate) fn has_internal_exceptional_outcome(&self) -> bool {
        statement_contains_internal_throw(&self.body)
    }

    pub fn composite_resource_definitions(&self) -> &[CompositeResourceDefinition] {
        self.contract_interface.composite_resource_definitions()
    }

    pub fn predicate_unfoldings(&self) -> &[PredicateUnfolding] {
        self.contract_interface.predicate_unfoldings()
    }

    /// The body-independent contract carrier used by direct calls, callback
    /// applications, refinement, and certification.
    pub fn contract_interface(&self) -> &FunctionContractInterface {
        &self.contract_interface
    }
}

impl PredicateUnfolding {
    pub fn new(mut predicate: SpecProposition, body: SpecProposition) -> Self {
        if let SpecProposition::Predicate {
            resource_state_dependent,
            ..
        } = &mut predicate
        {
            // A client cannot erase a model dependency from a registered body.
            *resource_state_dependent |=
                super::super::spec::predicate_dependencies::observes_resource_state(&body);
        }
        Self { predicate, body }
    }

    pub fn predicate(&self) -> &SpecProposition {
        &self.predicate
    }

    pub fn body(&self) -> &SpecProposition {
        &self.body
    }
}

impl CompositeResourceDefinition {
    pub fn with_resource_parameters(mut self, parameters: Vec<ResourceSpec>) -> Self {
        self.resource_parameters = parameters;
        self
    }

    pub fn resource_parameters(&self) -> &[ResourceSpec] {
        &self.resource_parameters
    }

    pub(crate) fn with_instance_schema(mut self, schema: Option<ResourceFieldSchema>) -> Self {
        self.instance_schema = schema;
        self
    }

    pub(crate) fn instance_field_schema(&self) -> Option<&ResourceFieldSchema> {
        self.instance_schema.as_ref()
    }

    pub(crate) fn with_resource_match_body(mut self, body: Option<ResourceMatchBody>) -> Self {
        self.matched = body;
        self.thread_confined |= self.owns_population_authority();
        self
    }

    /// Named child instances of the unmatched body.
    pub(crate) fn with_children(mut self, children: Vec<ResourceChildSpec>) -> Self {
        self.children = children;
        self
    }
    pub fn new(
        name: impl Into<String>,
        parameters: Vec<ProgramParameter>,
        condition: Option<SpecProposition>,
        recursive: bool,
        contains: Vec<ResourceSpec>,
        facts: Vec<SpecProposition>,
    ) -> Self {
        let fact_source_indices = (0..facts.len()).collect();
        let mut definition = Self {
            resource_parameters: Vec::new(),
            instance_schema: None,
            matched: None,
            name: name.into(),
            parameters,
            witnesses: Vec::new(),
            condition,
            recursive,
            matched_recursive: false,
            facts_read_counts: false,
            thread_confined: false,
            contains_mutex_authority: false,
            authorized: false,
            reaches_population: false,
            owned_footprint_unnamed: false,
            facts_claim_liveness: false,
            contains,
            children: Vec::new(),
            facts,
            fact_source_indices,
            fact_source_spellings: Vec::new(),
            sealed: false,
        };
        // An authority control is confined to its creating thread
        // (`thread_confinement`); computing it here keeps every copy of the
        // definition, surface and kernel, in agreement.
        definition.thread_confined = definition.owns_population_authority();
        definition
    }

    pub fn with_witnesses(mut self, witnesses: Vec<ProgramParameter>) -> Self {
        self.witnesses = witnesses;
        self
    }

    pub(crate) fn with_fact_source_indices(mut self, indices: Vec<usize>) -> Self {
        self.fact_source_indices = indices;
        self
    }

    pub(crate) fn with_fact_source_spellings(mut self, spellings: Vec<String>) -> Self {
        self.fact_source_spellings = spellings;
        self
    }

    pub(crate) fn fact_source_spelling(&self, compiled_index: usize) -> Option<&str> {
        self.fact_source_index(compiled_index)
            .and_then(|index| self.fact_source_spellings.get(index))
            .map(String::as_str)
    }

    pub(crate) fn fact_source_index(&self, compiled_index: usize) -> Option<usize> {
        self.fact_source_indices.get(compiled_index).copied()
    }

    pub fn with_facts_read_counts(mut self, facts_read_counts: bool) -> Self {
        self.facts_read_counts = facts_read_counts;
        self
    }

    pub fn with_liveness_facts(mut self, facts_claim_liveness: bool) -> Self {
        self.facts_claim_liveness = facts_claim_liveness;
        self
    }

    /// Whether a stable loan of this composite may carry its body facts:
    /// recovery restores the exact escrowed head, so a fact is re-asserted
    /// precisely as folded, which is sound when everything the fact depends
    /// on is stable for the loan. The body's memory and tokens are; a
    /// population count the caller may change elsewhere and the liveness of
    /// storage the fact names are not (D12).
    pub fn facts_are_loan_stable(&self) -> bool {
        !self.facts_read_counts && !self.facts_claim_liveness
    }

    /// Equal arguments make every instance own the same positive cell range.
    /// This is a uniqueness consequence of exclusive memory ownership, not a
    /// declaration that families without memory are implicitly multiple.
    pub(in crate::kernel) fn has_fixed_exclusive_memory(&self) -> bool {
        self.witnesses.is_empty()
            && self.contains.iter().any(|child| {
                if child.access() != ResourceAccessMode::Own
                    || child.quantity() != &ResourceQuantity::One
                    || child.guard().is_some()
                {
                    return false;
                }
                let ResourceTerm::Memory(segment) = child.term() else {
                    return false;
                };
                let ProgramExpression::Variable(parameter) = &segment.base else {
                    return false;
                };
                let (ProgramExpression::Value(ProgramValue::Int32(start)), ProgramExpression::Value(ProgramValue::Int32(end))) =
                    (&segment.start, &segment.end) else { return false; };
                segment.guard.is_none()
                    && segment.element_width > 0
                    && self.parameters.iter().any(|p| p.name() == parameter)
                    && matches!((start.as_const(), end.as_const()), (Some(a), Some(b)) if (a as i32) < (b as i32))
            })
    }

    /// Whether the memory this body owns is a function of the composite's
    /// arguments alone: no condition, matched arm, witness, recursion,
    /// population authority or instance schema, and every clause an
    /// unguarded owned memory segment spelled from parameters and constants
    /// by casts, arithmetic and byte offsets, never by a load, with its base
    /// rooted at a pointer parameter. Opening such a body reads neither memory
    /// nor facts, so its ranges are the same wherever its fact is held, and a
    /// question about one address needs only the composites whose arguments
    /// spell its base (`memory_state::CallKeptRanges::range_holding`).
    pub(in crate::kernel) fn has_argument_direct_body(&self) -> bool {
        let parameter = |name: &str| self.parameters.iter().any(|p| p.name() == name);
        fn direct(expression: &ProgramExpression, parameter: &dyn Fn(&str) -> bool) -> bool {
            match expression {
                ProgramExpression::Variable(name) => parameter(name),
                ProgramExpression::Value(value) => !matches!(value, ProgramValue::Pointer(_)),
                ProgramExpression::Cast { expression, .. } => direct(expression, parameter),
                ProgramExpression::PointerOffsetBytes { pointer, .. } => direct(pointer, parameter),
                ProgramExpression::Add(left, right)
                | ProgramExpression::Subtract(left, right)
                | ProgramExpression::Multiply(left, right) => {
                    direct(left, parameter) && direct(right, parameter)
                }
                _ => false,
            }
        }
        fn rooted(expression: &ProgramExpression, parameter: &dyn Fn(&str) -> bool) -> bool {
            match expression {
                ProgramExpression::Variable(name) => parameter(name),
                ProgramExpression::Cast { expression, .. } => rooted(expression, parameter),
                ProgramExpression::PointerOffsetBytes { pointer, .. } => rooted(pointer, parameter),
                ProgramExpression::Add(left, _) | ProgramExpression::Subtract(left, _) => {
                    rooted(left, parameter)
                }
                _ => false,
            }
        }
        self.witnesses.is_empty()
            && self.condition.is_none()
            && self.matched.is_none()
            && self.instance_schema.is_none()
            && !self.recursive
            && !self.matched_recursive
            && !self.owns_population_authority()
            && !self.contains.is_empty()
            && self.contains.iter().all(|child| {
                let ResourceTerm::Memory(segment) = child.term() else {
                    return false;
                };
                child.access() == ResourceAccessMode::Own
                    && child.quantity() == &ResourceQuantity::One
                    && child.guard().is_none()
                    && child.resource_arguments().is_empty()
                    && segment.guard.is_none()
                    && rooted(&segment.base, &parameter)
                    && direct(&segment.base, &parameter)
                    && direct(&segment.start, &parameter)
                    && direct(&segment.end, &parameter)
            })
    }

    pub fn witnesses(&self) -> &[ProgramParameter] {
        &self.witnesses
    }

    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn parameters(&self) -> &[ProgramParameter] {
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

    /// Whether the body, unmatched or in an arm, owns a population
    /// authority: the definition is an authority control.
    pub fn owns_population_authority(&self) -> bool {
        self.contains
            .iter()
            .chain(
                self.matched
                    .iter()
                    .flat_map(|body| body.arms.iter())
                    .flat_map(|arm| arm.contains.iter()),
            )
            .any(|spec| matches!(spec.term(), ResourceTerm::PopulationAuthority { .. }))
    }

    /// Marks a field-bearing abstract family, which no proof step folds,
    /// unfolds, or observes.
    pub fn with_sealed(mut self, sealed: bool) -> Self {
        self.sealed = sealed;
        self
    }

    pub fn is_sealed(&self) -> bool {
        self.sealed
    }

    pub fn with_authorized(mut self, authorized: bool) -> Self {
        self.authorized = authorized;
        self
    }

    /// Whether the family was declared `authorized resource`.
    pub fn is_authorized(&self) -> bool {
        self.authorized
    }

    /// Whether folding, unfolding or moving this family can touch a
    /// population: see the `reaches_population` field.
    pub fn reaches_population(&self) -> bool {
        self.reaches_population
    }

    pub fn is_thread_confined(&self) -> bool {
        self.thread_confined
    }

    /// Whether this definition's owned footprint reaches memory no clause
    /// instance names (`owned_footprint_reach`).
    pub(crate) fn owned_footprint_reaches_unnamed_memory(&self) -> bool {
        self.owned_footprint_unnamed
    }

    /// Every family this definition contains or names as a child, in its
    /// unmatched body and in each arm.
    pub(crate) fn referenced_family_names(&self) -> impl Iterator<Item = &str> {
        let contained = self
            .contains
            .iter()
            .chain(
                self.matched
                    .iter()
                    .flat_map(|body| body.arms.iter())
                    .flat_map(|arm| arm.contains.iter()),
            )
            .filter_map(|spec| spec.contained_definition_name());
        let children = self
            .children
            .iter()
            .chain(
                self.matched
                    .iter()
                    .flat_map(|body| body.arms.iter())
                    .flat_map(|arm| arm.children.iter()),
            )
            .map(|child| child.resource.as_str());
        contained.chain(children)
    }

    pub fn needs_outcome_resource_transfer(&self) -> bool {
        self.recursive || self.owns_population_authority()
    }

    pub fn contains(&self) -> &[ResourceSpec] {
        &self.contains
    }

    pub fn facts(&self) -> &[SpecProposition] {
        &self.facts
    }
}

#[cfg(test)]
impl CompositeResourceDefinition {
    /// An authority control for kernel tests: the given body plus the owned
    /// authority over a bodyless `member` family, with facts that read counts.
    pub(crate) fn authority_control(
        name: impl Into<String>,
        parameters: Vec<ProgramParameter>,
        condition: Option<SpecProposition>,
        mut contains: Vec<ResourceSpec>,
        facts: Vec<SpecProposition>,
    ) -> Self {
        contains.push(
            ResourceSpec::new(
                ResourceTerm::PopulationAuthority {
                    population_arity: None,
                    protected: Box::new(ResourceTypeSpec {
                        resource: Box::new(ResourceSpec::composite(
                            ResourceAccessMode::Own,
                            "member".into(),
                            vec![],
                            vec![],
                        )),
                        schema: ResourceFieldSchema::new(vec![]).expect("empty schema"),
                    }),
                    snapshot: ResourceSnapshot::Current,
                },
                ResourceAccessMode::Own,
                ResourceQuantity::One,
                ResourceTransferRole::Consume,
                ResourceSnapshot::Current,
            )
            .expect("an owned authority is a valid resource clause"),
        );
        Self::new(name, parameters, condition, false, contains, facts).with_facts_read_counts(true)
    }
}

impl FunctionContractClaim {
    pub fn body_safety() -> Self {
        Self {
            key: FunctionContractClaimKey::BodySafety,
            target: FunctionContractClaimTarget::BodySafety,
        }
    }

    pub fn effect(index: usize) -> Self {
        Self {
            key: FunctionContractClaimKey::Effect(index),
            target: FunctionContractClaimTarget::Effect,
        }
    }

    pub fn ensure_proposition(source_index: usize, contract_index: usize) -> Self {
        Self {
            key: FunctionContractClaimKey::Ensure(source_index),
            target: FunctionContractClaimTarget::EnsureProposition(contract_index),
        }
    }

    pub fn ensure_resource(source_index: usize, resource_index: usize) -> Self {
        Self {
            key: FunctionContractClaimKey::Ensure(source_index),
            target: FunctionContractClaimTarget::EnsureResource(resource_index),
        }
    }
    pub(crate) fn exceptional_ensure_proposition(
        source_index: usize,
        contract_index: usize,
    ) -> Self {
        Self {
            key: FunctionContractClaimKey::ExceptionalEnsure(source_index),
            target: FunctionContractClaimTarget::ExceptionalEnsureProposition(contract_index),
        }
    }

    pub fn key(&self) -> &FunctionContractClaimKey {
        &self.key
    }

    pub fn target(&self) -> &FunctionContractClaimTarget {
        &self.target
    }
}

impl LoopInvariantCheck {
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

impl LoopEffectCheck {
    pub fn new(effect: LoopEffect, context: Option<String>) -> Self {
        Self {
            effect,
            span: LoopEffectSpan::Step,
            context,
            origin: LoopEffectOrigin::Unspecified,
            validated_ranges: None,
        }
    }

    pub fn new_with_origin(
        effect: LoopEffect,
        span: LoopEffectSpan,
        origin: LoopEffectOrigin,
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

    pub(crate) fn with_validated_ranges(mut self, ranges: Vec<MemoryRange>) -> Self {
        self.validated_ranges = Some(ranges);
        self
    }

    pub fn effect(&self) -> &LoopEffect {
        &self.effect
    }

    pub fn span(&self) -> LoopEffectSpan {
        self.span
    }

    pub fn context(&self) -> Option<&str> {
        self.context.as_deref()
    }

    pub fn origin(&self) -> LoopEffectOrigin {
        self.origin
    }

    pub(crate) fn validated_ranges(&self) -> Option<&[MemoryRange]> {
        self.validated_ranges.as_deref()
    }
}

impl MemorySegment {
    pub fn new(base: ProgramExpression, start: ProgramExpression, end: ProgramExpression) -> Self {
        Self {
            base,
            start,
            end,
            element_width: 4,
            guard: None,
            uninitialized: false,
            value_runs: super::SegmentValueRuns(None),
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

    pub fn with_uninitialized(mut self, uninitialized: bool) -> Self {
        self.uninitialized = uninitialized;
        self
    }

    pub fn is_uninitialized(&self) -> bool {
        self.uninitialized
    }

    pub fn with_value_runs(mut self, value_runs: Option<std::sync::Arc<[(u32, u32)]>>) -> Self {
        self.value_runs = super::SegmentValueRuns(value_runs);
        self
    }

    pub fn value_runs(&self) -> Option<&[(u32, u32)]> {
        self.value_runs.0.as_deref()
    }
}

impl MemoryRange {
    /// Physical identity for separation only. This does not carry permission
    /// to access the bytes and must not be used for ownership or containment.
    pub(crate) fn spatial_key(&self) -> Self {
        crate::instrumentation::record_deterministic_work(1);
        // Separation names physical bytes. A complete constant span, or a
        // single symbolic element, has one key across casts and element units.
        // This key carries no access/ownership authority.
        let (start, end) = self.bound_terms();
        let constant = if self.wide_bounds().is_some() {
            start
                .uint64_as_const()
                .zip(end.uint64_as_const())
                .and_then(|(start, end)| end.checked_sub(start).map(|count| (start, count)))
        } else {
            self.signed_constant_start()
                .zip(self.signed_constant_end())
                .filter(|(start, end)| 0 <= *start && *start <= *end)
                .map(|(start, end)| (start as u64, (end - start) as u64))
        };
        let both_constant = if self.wide_bounds().is_some() {
            start.uint64_as_const().is_some() && end.uint64_as_const().is_some()
        } else {
            start.as_const().is_some() && end.as_const().is_some()
        };
        let count = constant.map(|(_, count)| count).or_else(|| {
            if both_constant {
                return None;
            }
            let difference = if self.wide_bounds().is_some() {
                MachineTerm::uint64_subtract(end.clone(), start.clone()).uint64_as_const()
            } else {
                MachineTerm::subtract(end.clone(), start.clone())
                    .as_const()
                    .map(u64::from)
            };
            (difference == Some(1)).then_some(1)
        });
        if let Some(bytes) = count
            .and_then(|count| count.checked_mul(u64::from(self.element_width())))
            .and_then(|bytes| u32::try_from(bytes).ok())
        {
            return Self::new_with_element_width(
                self.start_pointer(),
                MachineTerm::constant(0),
                MachineTerm::constant(bytes),
                1,
            );
        }
        let constructor = if self.wide_bounds().is_some() {
            Self::new_wide
        } else {
            Self::new_with_element_width
        };
        constructor(
            self.base().clone(),
            start.clone(),
            end.clone(),
            self.element_width(),
        )
    }

    pub fn new(base: Pointer, start: MachineTerm, end: MachineTerm) -> Self {
        Self::new_with_element_width(base, start, end, 4)
    }

    /// Constructs a range with an explicit logical element width.
    ///
    /// `new` remains the compatibility constructor for the historical
    /// int32-only kernel callers. New ranges produced from typed C input
    /// should use this constructor instead.
    pub(crate) fn new_with_element_width(
        base: Pointer,
        start: MachineTerm,
        end: MachineTerm,
        element_width: u32,
    ) -> Self {
        assert!(element_width > 0, "memory element width must be positive");
        let carrier = PointerValue::new(base.clone(), ProgramType::VoidPointer);
        Self {
            opaque_extent: carrier.opaque_extent.clone(),
            carrier_extent_known: carrier.extent_is_known(),
            designation: std::sync::Arc::new(base.object_identity()),
            typed_carrier: false,
            base,
            start_bound: start,
            end_bound: end,
            element_width,
            kind: RangeIndexKind::Int32,
            formation_coverage: Default::default(),
        }
    }

    /// A typed clause carries the complete pointer's origin, independently of
    /// whichever address spelling the resource algebra subsequently selects.
    pub(crate) fn from_pointer_value(
        value: &PointerValue,
        start: MachineTerm,
        end: MachineTerm,
        element_width: u32,
    ) -> Self {
        Self::new_with_element_width(value.pointer().clone(), start, end, element_width)
            .with_pointer_carrier(value)
    }

    pub(crate) fn from_pointer_value_wide(
        value: &PointerValue,
        start: MachineTerm,
        end: MachineTerm,
        element_width: u32,
    ) -> Self {
        Self::new_wide(value.pointer().clone(), start, end, element_width)
            .with_pointer_carrier(value)
    }

    /// The origin and extent ancestry retained by this admitted footprint.
    /// Its own bounds describe the authorized bytes; this carrier is not a
    /// new pointer access and does not infer a selected subobject extent.
    pub(in crate::kernel) fn pointer_carrier(&self) -> PointerValue {
        PointerValue {
            pointer: self.base.clone(),
            designation: self.designation.clone(),
            opaque_extent: self.opaque_extent.clone(),
            program_type: ProgramType::VoidPointer,
            qualifiers: self.carrier_extent_known.then(|| {
                std::sync::Arc::new(PointerQualifiers {
                    extent_known: true,
                    ..Default::default()
                })
            }),
        }
    }

    pub(in crate::kernel) fn with_pointer_carrier(mut self, value: &PointerValue) -> Self {
        self.designation = value.designation.clone();
        self.opaque_extent = value.opaque_extent.clone();
        self.carrier_extent_known = value.extent_is_known();
        self.typed_carrier = true;
        self
    }

    pub(in crate::kernel) fn with_opaque_extent(
        mut self,
        origin: Option<std::sync::Arc<Pointer>>,
        known: bool,
    ) -> Self {
        self.opaque_extent = origin;
        self.carrier_extent_known = known;
        self
    }

    pub(in crate::kernel) fn with_designation(
        mut self,
        designation: std::sync::Arc<Pointer>,
    ) -> Self {
        self.designation = designation;
        self
    }

    pub(in crate::kernel) fn with_typed_carrier(mut self) -> Self {
        self.typed_carrier = true;
        self
    }

    pub(in crate::kernel) fn with_carrier_of(mut self, source: &Self) -> Self {
        self.designation = source.designation.clone();
        self.formation_coverage = source.formation_coverage.clone();
        self.typed_carrier = source.typed_carrier;
        self.opaque_extent = source.opaque_extent.clone();
        self.carrier_extent_known = source.carrier_extent_known;
        self
    }

    pub(in crate::kernel) fn access_designation(&self) -> (&Pointer, Option<&Pointer>) {
        (
            &self.designation,
            if self.carrier_extent_known {
                None
            } else {
                self.opaque_extent.as_deref()
            },
        )
    }

    /// Retained identity metadata for diagnostic rendering only. Reading this
    /// view performs no inference, normalization, or proof-state traversal.
    pub(crate) fn diagnostic_pointer_metadata(&self) -> (&Pointer, Option<&Pointer>, bool) {
        (
            &self.designation,
            self.opaque_extent.as_deref(),
            self.carrier_extent_known,
        )
    }

    pub fn kind(&self) -> RangeIndexKind {
        self.kind
    }

    /// A bound's bit pattern when it is a signed 32-bit constant. A wide
    /// range answers as a symbolic one does: not constant.
    pub(crate) fn constant_start(&self) -> Option<u32> {
        self.int32_bounds()?.0.as_const()
    }

    pub(crate) fn constant_end(&self) -> Option<u32> {
        self.int32_bounds()?.1.as_const()
    }

    /// A bound as the signed number it is, when it is a 32-bit constant.
    pub(crate) fn signed_constant_start(&self) -> Option<i64> {
        signed_bitvector_constant(self.int32_bounds()?.0)
    }

    pub(crate) fn signed_constant_end(&self) -> Option<i64> {
        signed_bitvector_constant(self.int32_bounds()?.1)
    }

    /// Whether either bound is not a constant.
    pub(crate) fn has_symbolic_bounds(&self) -> bool {
        match self.kind {
            RangeIndexKind::Int32 => {
                self.start_bound.as_const().is_none() || self.end_bound.as_const().is_none()
            }
            RangeIndexKind::UInt64 => {
                self.start_bound.uint64_as_const().is_none()
                    || self.end_bound.uint64_as_const().is_none()
            }
        }
    }

    /// The address of the range's first element, in its own index kind.
    pub(crate) fn start_pointer(&self) -> Pointer {
        match self.kind {
            RangeIndexKind::Int32 => self
                .base
                .offset_by_elements(self.start_bound.clone(), self.element_width),
            RangeIndexKind::UInt64 => self.base.offset_by_typed_elements(
                self.start_bound.clone(),
                self.element_width,
                true,
                true,
            ),
        }
    }

    /// The address one past the range's last element, in its own kind.
    pub(crate) fn end_pointer(&self) -> Pointer {
        match self.kind {
            RangeIndexKind::Int32 => self
                .base
                .offset_by_elements(self.end_bound.clone(), self.element_width),
            RangeIndexKind::UInt64 => self.base.offset_by_typed_elements(
                self.end_bound.clone(),
                self.element_width,
                true,
                true,
            ),
        }
    }

    /// The bounds as signed 32-bit indices, or nothing for a wide range: for
    /// a reader that answers "unknown" where it cannot read the bounds.
    pub(crate) fn int32_bounds(&self) -> Option<(&MachineTerm, &MachineTerm)> {
        (self.kind == RangeIndexKind::Int32).then_some((&self.start_bound, &self.end_bound))
    }

    /// That this range's memory is live in `memory`. An `Int32` range
    /// counts its bytes in 32 bits. A wide one states the wide fact: its
    /// count is the unsigned 64-bit `(end - start) * width`, written by
    /// [`wide_loadable_byte_count`] and read back by
    /// [`wide_loadable_element_count`].
    pub(crate) fn loadable_fact(&self, memory: &Memory) -> Proposition {
        match self.wide_bounds() {
            None => {
                let (base, bytes) = self.byte_footprint();
                Proposition::MemoryLoadable {
                    memory: memory.clone(),
                    base,
                    bytes,
                    wide: false,
                }
            }
            Some((start, end)) => Proposition::MemoryLoadable {
                memory: memory.clone(),
                base: self.start_pointer(),
                bytes: wide_loadable_byte_count(
                    MachineTerm::uint64_subtract(end.clone(), start.clone()),
                    self.element_width,
                ),
                wide: true,
            },
        }
    }

    /// The bound terms themselves, in either kind: for a traversal that
    /// reads their structure (the variables in them, a substitution into
    /// them) and never the numbers they denote.
    pub(crate) fn bound_terms(&self) -> (&MachineTerm, &MachineTerm) {
        (&self.start_bound, &self.end_bound)
    }

    /// The bounds of a wide range, which no signed 32-bit reader may take.
    pub(crate) fn wide_bounds(&self) -> Option<(&MachineTerm, &MachineTerm)> {
        (self.kind == RangeIndexKind::UInt64).then_some((&self.start_bound, &self.end_bound))
    }

    /// A reader of signed 32-bit bounds met a wide range. It was never
    /// taught the wide reading, and answering would misread the bounds, so
    /// it stops.
    #[track_caller]
    fn assert_int32(&self) {
        assert!(
            self.kind == RangeIndexKind::Int32,
            "a signed 32-bit reader was given a wide memory range"
        );
    }

    /// Returns this element-indexed range as a physical byte footprint.
    ///
    /// `MemoryRange` deliberately keeps its public bounds in element units:
    /// those are the units used by resource clauses such as `p[0..n]`.
    /// Callers that need to compare the actual memory occupied by a range can
    /// use this bounded, derived view without introducing a second resource
    /// representation. The returned pointer is the first byte of the range;
    /// the second value is its byte length.
    pub(crate) fn byte_footprint(&self) -> (Pointer, MachineTerm) {
        (
            self.start_pointer(),
            memory_range_byte_count(self.start().clone(), self.end().clone(), self.element_width),
        )
    }

    pub fn element_width(&self) -> u32 {
        self.element_width
    }

    /// Rebase a range without changing the domain of either endpoint.
    pub(crate) fn with_base(&self, base: Pointer) -> Self {
        Self {
            base,
            ..self.clone()
        }
    }

    /// Rebuilds a range with different bounds while preserving its element
    /// coordinate system.
    pub(crate) fn with_bounds(&self, base: Pointer, start: MachineTerm, end: MachineTerm) -> Self {
        Self {
            kind: self.kind,
            formation_coverage: self.formation_coverage.clone(),
            designation: self.designation.clone(),
            typed_carrier: self.typed_carrier,
            opaque_extent: self.opaque_extent.clone(),
            carrier_extent_known: self.carrier_extent_known,
            ..Self::new_with_element_width(base, start, end, self.element_width)
        }
    }

    /// The range of cells a guarded universal read can reach.
    ///
    /// `pointer` is a cell read inside `forall v { guard implies ... }`. When
    /// `pointer` is exactly element `v` of some `base`, in the addressing a
    /// range's own [`Self::start_pointer`] uses, and `guard` has conjuncts
    /// bounding `v` to `lo <= v < hi` in the comparison of that addressing's
    /// index kind, the answer is `base[lo..hi]` of that kind. Every value of
    /// `v` the guard admits is then an index of this range, so a view that
    /// covers the range covers every cell the read names. Other conjuncts
    /// only shrink the admitted set. An unsigned 64-bit index needs no lower
    /// conjunct, since `0` bounds it already; a signed one does.
    ///
    /// `base`, `lo` and `hi` must not mention `v`: the range is then one
    /// fixed set, rather than a description that varies with the binder.
    /// Any other shape answers nothing, and the caller keeps its per-cell
    /// check. The work is proportional to the guard and the pointer.
    pub(crate) fn guarded_quantified_cells(
        pointer: &Pointer,
        variable: Variable,
        guard: &Proposition,
        element_width: u32,
    ) -> Option<Self> {
        let is_variable = |term: &crate::kernel::SharedMachineIntegerTerm| {
            term.operand_view().variable() == Some(&variable)
        };
        let (base_offset, scaled) = match &pointer.offset {
            PointerOffsetTerm::Add(base, scaled) => (base.as_ref().clone(), scaled.as_ref()),
            scaled => (PointerOffsetTerm::Constant(0), scaled),
        };
        let kind = match scaled {
            PointerOffsetTerm::Int32Scaled { value, .. } if is_variable(value) => {
                RangeIndexKind::Int32
            }
            PointerOffsetTerm::Int64Scaled {
                value,
                unsigned: true,
                ..
            } if is_variable(value) => RangeIndexKind::UInt64,
            _ => return None,
        };
        let base = Pointer {
            block: pointer.block.clone(),
            offset: base_offset,
        };
        let index = MachineTerm::Variable(variable);
        let reconstructed = match kind {
            RangeIndexKind::Int32 => base.offset_by_elements(index, element_width),
            RangeIndexKind::UInt64 => {
                base.offset_by_typed_elements(index, element_width, true, true)
            }
        };
        if &reconstructed != pointer {
            return None;
        }
        let mut lower = (kind == RangeIndexKind::UInt64).then_some(MachineTerm::uint64_constant(0));
        let mut upper = None;
        let mut pending = vec![guard];
        while let Some(conjunct) = pending.pop() {
            match conjunct {
                Proposition::And(left, right) => {
                    pending.push(left);
                    pending.push(right);
                }
                Proposition::ConditionIs(condition, true) => match (kind, condition) {
                    (
                        RangeIndexKind::Int32,
                        ConditionTerm::Compare {
                            format: MachineIntegerType::Int32,
                            relation: CompareRelation::LessEqual,
                            left: lo,
                            right: v,
                        },
                    )
                    | (
                        RangeIndexKind::UInt64,
                        ConditionTerm::Compare {
                            format: MachineIntegerType::UInt64,
                            relation: CompareRelation::LessEqual,
                            left: lo,
                            right: v,
                        },
                    ) if matches!(v.as_ref(), MachineTerm::Variable(actual) if *actual == variable) => {
                        lower = Some(lo.as_ref().clone())
                    }
                    (
                        RangeIndexKind::Int32,
                        ConditionTerm::Compare {
                            format: MachineIntegerType::Int32,
                            relation: CompareRelation::LessThan,
                            left: v,
                            right: hi,
                        },
                    )
                    | (
                        RangeIndexKind::UInt64,
                        ConditionTerm::Compare {
                            format: MachineIntegerType::UInt64,
                            relation: CompareRelation::LessThan,
                            left: v,
                            right: hi,
                        },
                    ) if matches!(v.as_ref(), MachineTerm::Variable(actual) if *actual == variable) => {
                        upper = Some(hi.as_ref().clone())
                    }
                    _ => {}
                },
                _ => {}
            }
        }
        let (lower, upper) = (lower?, upper?);
        let mut mentioned = BTreeSet::new();
        for term in [
            Term::PointerOffset(base.offset.clone()),
            Term::Bitvector32(lower.clone()),
            Term::Bitvector32(upper.clone()),
        ] {
            crate::kernel::reasoning::collect_term_bitvector_variables(&term, &mut mentioned);
        }
        if mentioned.contains(&variable) {
            return None;
        }
        Some(match kind {
            RangeIndexKind::Int32 => {
                Self::new_with_element_width(base, lower, upper, element_width)
            }
            RangeIndexKind::UInt64 => Self::new_wide(base, lower, upper, element_width),
        })
    }

    /// A range whose bounds are unsigned 64-bit element indices.
    pub(crate) fn new_wide(
        base: Pointer,
        start: MachineTerm,
        end: MachineTerm,
        element_width: u32,
    ) -> Self {
        Self {
            kind: RangeIndexKind::UInt64,
            ..Self::new_with_element_width(base, start, end, element_width)
        }
    }

    pub fn base(&self) -> &Pointer {
        &self.base
    }

    #[track_caller]
    pub fn start(&self) -> &MachineTerm {
        self.assert_int32();
        &self.start_bound
    }

    #[track_caller]
    pub fn end(&self) -> &MachineTerm {
        self.assert_int32();
        &self.end_bound
    }

    /// The write set of memory no clause names: the largest valid extent at
    /// an unconstrained symbolic address.
    ///
    /// A resource footprint that reaches memory the kernel cannot spell -- a
    /// recursive body's nodes past the arguments, an existential witness's
    /// object -- covers every block reachable from its arguments, and those
    /// blocks are unknown. A symbolic block is never proven distinct from
    /// any block ([`super::PointerBlock::proven_distinct`]), no fact mentions
    /// this reserved identity, so nothing places its base, and the range is
    /// not empty, so no separation rule can place a cell outside it: every
    /// havoc, effect summary and transport that reads the write set treats
    /// it as covering all memory, except where a rule that does not consult
    /// the write set at all (the caller's residual ownership, the function's
    /// withheld ownership at a loop) keeps a cell. Consumers that ask the
    /// opposite, positive question -- does the write set *cover* an access --
    /// answer it through [`Self::is_unnamed_footprint`].
    pub(crate) fn unnamed_footprint() -> Self {
        Self::new_with_element_width(
            Pointer {
                block: super::PointerBlock::Symbolic(UNNAMED_FOOTPRINT_BLOCK),
                offset: super::PointerOffsetTerm::Constant(0),
            },
            MachineTerm::constant(0),
            // Endpoints are `int32` values: this is the largest extent whose
            // guards hold, so no consumer that assumes a held range's extent
            // guards can meet a false one here.
            MachineTerm::constant(i32::MAX as u32),
            1,
        )
    }

    /// Whether this is [`Self::unnamed_footprint`].
    pub(crate) fn is_unnamed_footprint(&self) -> bool {
        is_unnamed_footprint_base(&self.base)
    }
}

/// Whether a range or segment based at `base` is
/// [`MemoryRange::unnamed_footprint`]: the reserved block is spelled nowhere
/// else.
pub(crate) fn is_unnamed_footprint_base(base: &Pointer) -> bool {
    base.block == super::PointerBlock::Symbolic(UNNAMED_FOOTPRINT_BLOCK)
}

/// The reserved symbolic block of [`MemoryRange::unnamed_footprint`]. It is
/// never allocated to a program value, so no fact constrains it.
pub(crate) const UNNAMED_FOOTPRINT_BLOCK: super::Variable = super::Variable(u64::MAX - 0x666f_6f74);

/// Convert a logical element range to a physical byte count in the kernel's
/// 32-bit memory model. Callers must carry
/// [`memory_range_byte_count_guards`] whenever the range is supplied by a
/// contract or resource clause, since the arithmetic itself is modular.
pub(crate) fn memory_range_byte_count(
    start: MachineTerm,
    end: MachineTerm,
    element_width: u32,
) -> MachineTerm {
    assert!(element_width > 0, "memory element width must be positive");
    let element_count = canonical_subtract(end, start);
    canonical_multiply(element_count, MachineTerm::constant(element_width))
}

fn canonical_subtract(left: MachineTerm, right: MachineTerm) -> MachineTerm {
    match (&left, &right) {
        (bits32_constant!(left), bits32_constant!(right)) => {
            MachineTerm::constant(constant_u32(*left).wrapping_sub(constant_u32(*right)))
        }
        (_, bits32_constant!(0)) => left,
        _ if left == right => MachineTerm::constant(0),
        (
            binary_term!(Int32, Add, left_base, left_addend),
            binary_term!(Int32, Add, right_base, right_addend),
        ) if left_base == right_base => {
            canonical_subtract(left_addend.as_ref().clone(), right_addend.as_ref().clone())
        }
        _ => binary_node!(Int32, Subtract, Box::new(left), Box::new(right)),
    }
}

fn canonical_multiply(left: MachineTerm, right: MachineTerm) -> MachineTerm {
    match (&left, &right) {
        (bits32_constant!(left), bits32_constant!(right)) => {
            MachineTerm::constant(constant_u32(*left).wrapping_mul(constant_u32(*right)))
        }
        (_, bits32_constant!(1)) => left,
        (int32_constant!(1), _) => right,
        (_, bits32_constant!(0)) | (int32_constant!(0), _) => MachineTerm::constant(0),
        _ => binary_node!(Int32, Multiply, Box::new(left), Box::new(right)),
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
pub(crate) fn memory_range_element_count(range: &MemoryRange) -> MachineTerm {
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
    element_count: MachineTerm,
    element_width: u32,
) -> Vec<Proposition> {
    assert!(element_width > 0, "memory element width must be positive");
    let mut guards = vec![Proposition::ConditionIs(
        ConditionTerm::signed_less_equal(MachineTerm::constant(0), element_count.clone()),
        true,
    )];
    if element_count_limit_constrains_int32(element_width) {
        guards.push(Proposition::ConditionIs(
            ConditionTerm::signed_less_equal(
                element_count,
                MachineTerm::constant(memory_range_element_count_limit(element_width)),
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
    start: MachineTerm,
    end: MachineTerm,
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
    // The count is the `int32` difference of the endpoints; `fits` reads
    // its bits as a `uint32` count, which is σ of it. Given `start <= end`
    // the true difference lies in `[0, 2^32)`, and σ of the wrapped `int32`
    // difference is exactly it, so the unsigned comparison is the condition;
    // the count's own `int32` order is not (it wraps past `2^31 - 1`, which
    // the one-byte limit exceeds).
    let element_count = canonical_subtract(end, start);
    let fits = ConditionTerm::unsigned_less_equal(
        MachineTerm::sign_cast32(
            MachineIntegerType::Int32,
            MachineIntegerType::UInt32,
            element_count,
        ),
        MachineTerm::constant(memory_range_element_count_limit(element_width)),
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
pub(crate) fn scaled_extent_element_width(bytes: &MachineTerm) -> Option<u32> {
    let binary_term!(Int32, Multiply, left, right) = bytes else {
        return None;
    };
    match (left.as_ref(), right.as_ref()) {
        (bits32_constant!(width), _) | (_, bits32_constant!(width)) if constant_u32(*width) > 0 => {
            Some(constant_u32(*width))
        }
        _ => None,
    }
}

/// The element width a stated range's byte count was lowered with, when the
/// count reads as a range at all.
///
/// A range of `w`-byte elements lowers its extent to `(y - x) * w`, except
/// that a range of one-byte elements keeps it unscaled: `a[0..n]` over `uint8`
/// is `n` bytes itself. So a scaled count gives its factor, and a symbolic
/// unscaled one is a byte range. A constant count is neither: a cell's width
/// or a constant range's size is already a true count of bytes, and its
/// validity is decided where it was lowered.
pub(crate) fn stated_extent_element_width(bytes: &MachineTerm) -> Option<u32> {
    scaled_extent_element_width(bytes).or_else(|| bytes.as_const().is_none().then_some(1))
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
/// a fact about anything the surrounding scope can state. A byte range carries
/// its guards like a wider one, over its unscaled count; a constant byte count
/// carries nothing (see [`stated_extent_element_width`]).
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
        // A wide range's object-size guard, in the element form its contract
        // states. Only a citation asks for it: a 32-bit-free count has no
        // further guard a proof owes.
        Proposition::MemoryLoadable {
            bytes, wide: true, ..
        } => {
            if !every_spelling {
                return;
            }
            let (elements, width) = match bytes {
                MachineTerm::Binary {
                    format: MachineIntegerType::UInt64,
                    op: MachineBinaryOp::Multiply,
                    left: elements,
                    right: width,
                } => {
                    match width
                        .uint64_as_const()
                        .and_then(|width| u32::try_from(width).ok())
                    {
                        Some(width) if width > 1 => (elements.as_ref(), width),
                        _ => return,
                    }
                }
                _ => (bytes, 1),
            };
            let guard = Proposition::ConditionIs(
                ConditionTerm::uint64_less_equal(
                    elements.clone(),
                    MachineTerm::uint64_constant(i64::MAX as u64 / u64::from(width)),
                ),
                true,
            );
            if !guards.contains(&guard) {
                guards.push(guard);
            }
        }
        Proposition::MemoryLoadable { bytes, .. } => {
            let Some(element_width) = stated_extent_element_width(bytes) else {
                return;
            };
            let Some(element_count) =
                crate::kernel::reasoning::element_count_from_bytes(bytes, element_width)
            else {
                return;
            };
            let endpoints = if every_spelling {
                memory_range_byte_count_guards(
                    MachineTerm::constant(0),
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
pub(crate) fn memory_range_extent_guards(range: &MemoryRange) -> Vec<Proposition> {
    if let Some(guards) = wide_memory_range_extent_guards(range) {
        return guards;
    }
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

/// The bounds of a wide range written with `start` and `end`, when it is
/// one: a bound is a 64-bit integer, signed or unsigned. Every bound is read
/// as an unsigned 64-bit value, a signed one by its sign extension.
/// `bytes[0..length]`, `bytes[1..length]`, `bytes[a..b]`, `bytes[index..4]`,
/// `bytes[i..length]` with `int32 i`, `bytes[i..4u64]` and `bytes[0..n]`
/// with `int64 n` are wide. A range with two `int32` bounds is not, and
/// neither is one whose bounds are constants that fit an `int32`, unless
/// both are written `uint64`: `memcpy(dst, src, 16)` holds `dst[0..16]` as a
/// local array does (`design/typed-indices.md`, stage 2).
/// A range bound's value as an `int32` index, when it is a constant that
/// fits one: the only 64-bit bound a narrow range takes
/// ([`wide_range_bounds`]).
pub(crate) fn narrow_range_constant(value: &ProgramValue) -> Option<MachineTerm> {
    let value = value.numeric_value();
    let constant = match value {
        ProgramValue::Int32(bits32_constant!(bits)) => i64::from(constant_u32(*bits) as i32),
        ProgramValue::Int64(int64_constant!(value)) => constant_i64(*value),
        ProgramValue::UInt64(term) => i64::try_from(term.uint64_as_const()?).ok()?,
        _ => return None,
    };
    let constant = i32::try_from(constant).ok()?;
    Some(MachineTerm::constant(constant as u32))
}

pub(crate) fn wide_range_bounds(
    start: &ProgramValue,
    end: &ProgramValue,
) -> Option<(MachineTerm, MachineTerm)> {
    let start = start.numeric_value();
    let end = end.numeric_value();

    let widened = |value: &ProgramValue| match value {
        ProgramValue::UInt64(term) => Some(term.clone()),
        // A signed bound is read as its sign extension, the same bits as an
        // unsigned 64-bit value. A negative one becomes larger than any
        // extent the range's guards allow, so the range denotes memory only
        // when its bounds are nonnegative.
        ProgramValue::Int32(bits32_constant!(bits)) => Some(MachineTerm::uint64_constant(
            constant_u32(*bits) as i32 as i64 as u64,
        )),
        ProgramValue::Int32(term) => Some(MachineTerm::legacy_cast(
            MachineCastSpelling::UInt64FromInt32,
            Box::new(term.clone()),
        )),
        ProgramValue::Int64(int64_constant!(value)) => {
            Some(MachineTerm::uint64_constant(constant_i64(*value) as u64))
        }
        ProgramValue::Int64(term) => Some(MachineTerm::legacy_cast(
            MachineCastSpelling::UInt64FromInt64,
            Box::new(term.clone()),
        )),
        _ => None,
    };
    let wide_typed =
        |value: &ProgramValue| matches!(value, ProgramValue::UInt64(_) | ProgramValue::Int64(_));
    if narrow_range_constant(start).is_some()
        && narrow_range_constant(end).is_some()
        && !(matches!(start, ProgramValue::UInt64(_)) && matches!(end, ProgramValue::UInt64(_)))
    {
        return None;
    }
    if !wide_typed(start) && !wide_typed(end) {
        return None;
    }
    Some((widened(start)?, widened(end)?))
}

/// The byte count of a wide liveness fact over `elements` elements of
/// `width` bytes: the count itself at width one, and otherwise the product
/// with the width on the right, so the two parts can be read back.
pub(crate) fn wide_loadable_byte_count(elements: MachineTerm, width: u32) -> MachineTerm {
    if width == 1 {
        return elements;
    }
    MachineTerm::Binary {
        format: MachineIntegerType::UInt64,
        op: MachineBinaryOp::Multiply,
        left: Box::new(elements),
        right: Box::new(MachineTerm::uint64_constant(u64::from(width))),
    }
}

/// The element count of a wide liveness fact's byte count, for elements of
/// `width` bytes; nothing when the count was not written for that width.
pub(crate) fn wide_loadable_element_count(bytes: &MachineTerm, width: u32) -> Option<&MachineTerm> {
    if width == 1 {
        return Some(bytes);
    }
    match bytes {
        MachineTerm::Binary {
            format: MachineIntegerType::UInt64,
            op: MachineBinaryOp::Multiply,
            left: elements,
            right: by,
        } if by.uint64_as_const() == Some(u64::from(width)) => Some(elements),
        _ => None,
    }
}

/// What a wide range's bounds must satisfy to denote memory: they are in
/// order, and the range ends within the largest object there can be,
/// `isize::MAX` bytes. The second is what makes every element offset inside
/// the range an exact byte offset. A contract that holds the range on entry
/// is given both, as it is given the 32-bit guards of an `Int32` range; a
/// caller supplying the range proves them.
fn wide_memory_range_extent_guards(range: &MemoryRange) -> Option<Vec<Proposition>> {
    let (start, end) = range.wide_bounds()?;
    let limit = i64::MAX as u64 / u64::from(range.element_width());
    Some(vec![
        Proposition::ConditionIs(
            ConditionTerm::uint64_less_equal(start.clone(), end.clone()),
            true,
        ),
        Proposition::ConditionIs(
            ConditionTerm::uint64_less_equal(end.clone(), MachineTerm::uint64_constant(limit)),
            true,
        ),
    ])
}

/// Equivalent forms retained with an actual held range. The original endpoint
/// form serves memory reasoning; the signed form is available to proof text.
pub(crate) fn memory_range_extent_guard_spellings(range: &MemoryRange) -> Vec<Proposition> {
    if let Some(guards) = wide_memory_range_extent_guards(range) {
        return guards;
    }
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

/// Intrinsic bounds of a resource footprint whose admission was established.
/// A merely stated viewability/separation condition grants no domain evidence.
pub(crate) fn admitted_memory_range_extent_facts(range: &MemoryRange) -> Vec<Proposition> {
    let mut guards = memory_range_extent_guard_spellings(range);
    guards.extend(range.formation_coverage.iter().cloned());
    if range.typed_carrier
        && let Some(coverage) = range.pointer_carrier().opaque_coverage_fact(range)
    {
        guards.push(coverage);
    }
    guards
}

/// [`memory_range_byte_count_extent`] as a flat guard list: an invalid
/// constant range becomes the impossible guard, which refuses wherever the
/// caller discharges guards.
pub(crate) fn memory_range_byte_count_guards(
    start: MachineTerm,
    end: MachineTerm,
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

impl FunctionSpecification {
    pub fn new(
        state: ExecutionState,
        arguments: Vec<ProgramExpression>,
        requires: Vec<Proposition>,
        outcome: FunctionOutcome,
    ) -> Self {
        Self {
            state,
            arguments: arguments.into(),
            requires: requires.into(),
            outcome,
        }
    }

    pub fn state(&self) -> &ExecutionState {
        &self.state
    }

    pub fn arguments(&self) -> &[ProgramExpression] {
        &self.arguments
    }

    pub fn requires(&self) -> &[Proposition] {
        &self.requires
    }

    pub fn outcome(&self) -> &FunctionOutcome {
        &self.outcome
    }
}

impl FunctionContract {
    const PREDICATE_PREFIX: &'static str = "__click_function_contract::";

    pub(crate) fn with_proof_parameters(mut self, parameters: Vec<ResourceSpec>) -> Self {
        self.interface = self.interface.with_proof_parameters(parameters);
        self
    }

    pub fn new(name: impl Into<String>, function: ProgramFunction) -> Option<Self> {
        if !function.verified_direct_contract_supported() {
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
        interface: FunctionContractInterface,
    ) -> Option<Self> {
        // A throwing interface is supported when its exceptional channel is
        // the checked scalar one with pure clauses.
        (interface.verified_direct_contract_supported()
            && interface.aggregate_return_mode() == AggregateReturnMode::Copy
            && interface.construction_parameter().is_none()
            && interface.resource_constructors().is_empty()
            && !name.is_empty())
        .then_some(Self {
            name,
            callee_name,
            interface,
            value_arguments: Vec::new(),
        })
    }

    /// This contract with its last `count` parameters as value parameters.
    pub fn with_value_parameters(mut self, count: usize) -> Option<Self> {
        self.interface = self.interface.with_trailing_value_parameters(count)?;
        Some(self)
    }

    /// The contract of a function whose first `count` parameters are values
    /// fixed when its function value is made, as a closure's captures are.
    pub fn with_leading_value_parameters(mut self, count: usize) -> Option<Self> {
        self.interface = self.interface.with_leading_value_parameters(count)?;
        Some(self)
    }

    /// This contract as a fact attaching it to a function value found it:
    /// its value parameters fixed to `values`. `None` when the values do not
    /// have the parameters' number and types.
    pub(crate) fn instantiated(&self, values: &[ProgramValue]) -> Option<Self> {
        let parameters = self.interface.value_parameters();
        if values.len() != parameters.len()
            || !values
                .iter()
                .zip(parameters)
                .all(|(value, parameter)| value.program_type() == parameter.program_type())
        {
            return None;
        }
        let mut instantiated = self.clone();
        instantiated.value_arguments = values.to_vec();
        Some(instantiated)
    }

    pub(crate) fn value_arguments(&self) -> &[ProgramValue] {
        &self.value_arguments
    }

    pub fn name(&self) -> &str {
        &self.name
    }

    pub(crate) fn callee_name(&self) -> &str {
        &self.callee_name
    }

    pub fn function_pointer_type(&self) -> ProgramType {
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

    pub(crate) fn proof_parameters(&self) -> &[ResourceSpec] {
        self.interface.proof_parameters()
    }

    /// First-slice formation rule: a concrete target must expose exactly the
    /// same normalized interface. Behavioral refinement is intentionally a
    /// later rule; exact equality is restrictive but sound.
    pub(crate) fn exactly_matches(&self, function: &ProgramFunction) -> bool {
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
        function: &ProgramFunction,
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
        function: &ProgramFunction,
    ) -> bool {
        self.interface
            .has_compatible_signature_and_composite_vocabulary(function.contract_interface())
    }

    /// Opaque predicate identities may be compared definitionally only when
    /// an explicit refinement proof names the definitions it unfolds.
    pub(crate) fn has_same_predicate_unfoldings(&self, function: &ProgramFunction) -> bool {
        self.interface
            .has_same_predicate_unfoldings(function.contract_interface())
    }

    /// The body-independent interface selected by this nominal contract.
    pub fn interface(&self) -> &FunctionContractInterface {
        &self.interface
    }
}

fn statement_contains_internal_throw(statement: &ProgramStatement) -> bool {
    match statement {
        ProgramStatement::Throw(_) => true,
        ProgramStatement::ForStep { step, .. } => statement_contains_internal_throw(step),
        ProgramStatement::Seq(statements) => statements
            .iter()
            .any(|statement| statement_contains_internal_throw(statement)),
        ProgramStatement::TryCatchInt32 {
            try_body, handler, ..
        } => {
            statement_contains_internal_throw(try_body)
                || statement_contains_internal_throw(handler)
        }
        ProgramStatement::If {
            then_branch,
            else_branch,
            ..
        } => {
            statement_contains_internal_throw(then_branch)
                || statement_contains_internal_throw(else_branch)
        }
        ProgramStatement::While { body, .. } => statement_contains_internal_throw(body),
        ProgramStatement::Switch { cases, .. } => cases
            .iter()
            .any(|case| statement_contains_internal_throw(&case.body)),
        ProgramStatement::Skip
        | ProgramStatement::EndScalarReference(_)
        | ProgramStatement::ScalarReferenceScope(_)
        | ProgramStatement::EndAutomaticLifetimes { .. }
        | ProgramStatement::Break
        | ProgramStatement::Continue
        | ProgramStatement::Goto { .. }
        | ProgramStatement::Declare { .. }
        | ProgramStatement::DeclareAggregate { .. }
        | ProgramStatement::CopyAggregate { .. }
        | ProgramStatement::InitializeScalarArray { .. }
        | ProgramStatement::Assign { .. }
        | ProgramStatement::CallConstruct { .. }
        | ProgramStatement::Call { .. }
        | ProgramStatement::CallResult { .. }
        | ProgramStatement::HeapAllocate { .. }
        | ProgramStatement::HeapFree { .. }
        | ProgramStatement::Assert { .. }
        | ProgramStatement::StepValue { .. }
        | ProgramStatement::LoopTest { .. }
        | ProgramStatement::Return(_)
        | ProgramStatement::Store { .. }
        | ProgramStatement::TypedStore { .. }
        | ProgramStatement::Update { .. } => false,
    }
}

impl ExecutionEnvironment {
    pub(crate) fn with_modeled_pthread_binding(
        mut self,
        binding: Option<crate::languages::c::thread_runtime::ModeledPthreadBinding>,
    ) -> Self {
        self.modeled_pthread_binding = binding;
        self
    }

    pub(crate) fn with_modeled_mutex_definitions(
        mut self,
        definitions: BTreeMap<String, CompositeResourceDefinition>,
    ) -> Self {
        self.modeled_mutex_definition_list = definitions.values().cloned().collect();
        self.modeled_mutex_definitions = std::sync::Arc::new(definitions);
        self
    }

    /// Installs the selected target's byte order. The default is
    /// [`ByteOrder::Little`], the order of every selectable target.
    pub fn with_byte_order(mut self, byte_order: ByteOrder) -> Self {
        self.byte_order = byte_order;
        self
    }

    pub(crate) fn byte_order_fact(&self) -> Proposition {
        let fact = Proposition::Predicate {
            name: LITTLE_ENDIAN_PREDICATE_NAME.into(),
            arguments: vec![],
        };
        match self.byte_order {
            ByteOrder::Little => fact,
            ByteOrder::Big => Proposition::Not(Box::new(fact)),
        }
    }

    pub fn byte_order(&self) -> ByteOrder {
        self.byte_order
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

    /// Selects the values the proof's call map gives one ordinary C call to
    /// `function`, each for the contract value parameter it names.
    pub(crate) fn with_selected_call_values(
        mut self,
        function: &str,
        values: Vec<(String, ProgramValue)>,
    ) -> Self {
        self.selected_call_value_arguments =
            Some(std::sync::Arc::new((function.to_string(), values)));
        self
    }

    /// Selects the binder transport for one ordinary C call to `function`.
    /// The map is the only source of bindings for that call.
    pub(crate) fn with_selected_call_binders(
        self,
        function: &str,
        arity: usize,
        bindings: BTreeMap<Variable, Variable>,
    ) -> Self {
        self.with_selected_call_binders_and_types(function, arity, bindings, BTreeMap::new())
    }

    /// [`Self::with_selected_call_binders`] with runtime type binders.
    pub(crate) fn with_selected_call_binders_and_types(
        mut self,
        function: &str,
        arity: usize,
        bindings: BTreeMap<Variable, Variable>,
        type_arguments: BTreeMap<Variable, crate::kernel::ResourceDescription>,
    ) -> Self {
        self.selected_call_binders = Some(std::sync::Arc::new(CallBinderTransport {
            function: std::sync::Arc::from(function),
            arity,
            bindings: std::sync::Arc::new(bindings),
            type_arguments: std::sync::Arc::new(type_arguments),
        }));
        self
    }
    pub fn new() -> Self {
        Self::default()
    }

    pub fn with_function(mut self, function: ProgramFunction) -> Self {
        std::sync::Arc::make_mut(&mut self.functions).insert(function.name().to_string(), function);
        self.variable_index = ExecutionEnvironmentVariableIndex::default();
        self
    }

    pub fn with_function_contract(mut self, contract: FunctionContract) -> Self {
        std::sync::Arc::make_mut(&mut self.function_contracts)
            .insert(contract.name().to_string(), contract);
        self.variable_index = ExecutionEnvironmentVariableIndex::default();
        self
    }

    pub(crate) fn get_function_contract(&self, name: &str) -> Option<&FunctionContract> {
        self.function_contracts.get(name)
    }

    pub fn with_external_function_rule(mut self, rule: ExternalFunctionRule) -> Self {
        std::sync::Arc::make_mut(&mut self.external_function_rules)
            .insert(rule.function.name().to_string(), rule);
        self.variable_index = ExecutionEnvironmentVariableIndex::default();
        self
    }

    pub(crate) fn without_external_function_rule(mut self, name: &str) -> Self {
        std::sync::Arc::make_mut(&mut self.external_function_rules).remove(name);
        self.variable_index = ExecutionEnvironmentVariableIndex::default();
        self
    }

    pub fn get_function(&self, name: &str) -> Option<&ProgramFunction> {
        self.functions.get(name)
    }

    /// Every function body the project links. C termination reads a body with
    /// no verified rule as a call-graph node in two cases: a `static inline`
    /// helper a verified body calls, and a contract-less function whose
    /// address is taken, which a resolved function pointer executes in place.
    pub fn linked_functions(&self) -> Vec<&ProgramFunction> {
        self.functions.values().collect()
    }

    pub(in crate::kernel) fn get_external_function_rule(
        &self,
        name: &str,
    ) -> Option<&ExternalFunctionRule> {
        self.external_function_rules.get(name)
    }

    pub fn with_verified_function_rule(mut self, rule: VerifiedFunctionRule) -> Self {
        std::sync::Arc::make_mut(&mut self.verified_function_rules)
            .insert(rule.function.name().to_string(), rule);
        self.variable_index = ExecutionEnvironmentVariableIndex::default();
        self
    }

    pub fn with_verified_function_termination_rules(
        mut self,
        rules: impl IntoIterator<Item = VerifiedFunctionTerminationRule>,
    ) -> Self {
        for rule in rules {
            std::sync::Arc::make_mut(&mut self.verified_function_termination_rules)
                .insert(rule.function.name().to_string(), rule);
        }
        self.variable_index = ExecutionEnvironmentVariableIndex::default();
        self
    }

    pub fn has_verified_function_termination(&self, name: &str) -> bool {
        self.verified_function_termination_rules.contains_key(name)
    }

    pub fn without_verified_function_rule(mut self, name: &str) -> Self {
        std::sync::Arc::make_mut(&mut self.verified_function_rules).remove(name);
        self.variable_index = ExecutionEnvironmentVariableIndex::default();
        self
    }

    pub(in crate::kernel) fn get_verified_function_rule(
        &self,
        name: &str,
    ) -> Option<&VerifiedFunctionRule> {
        self.verified_function_rules.get(name)
    }

    pub(in crate::kernel) fn get_verified_function_termination_rule(
        &self,
        name: &str,
    ) -> Option<&VerifiedFunctionTerminationRule> {
        self.verified_function_termination_rules.get(name)
    }

    pub(crate) fn verified_function_rules(&self) -> Vec<VerifiedFunctionRule> {
        self.verified_function_rules.values().cloned().collect()
    }

    pub fn with_verified_loop_rules(
        mut self,
        rules: impl IntoIterator<Item = VerifiedLoopRule>,
    ) -> Self {
        // Loop rules keep their own variable indexes, so the environment's
        // index of its other parts stays valid.
        for rule in rules {
            self.verified_loop_rules.push(rule);
        }
        self
    }

    /// Installs the recursion anchor for the function being certified.
    ///
    /// There is no public constructor for [`RecursionAnchor`], so this is
    /// reached only through
    /// [`crate::kernel::program_execution_environment_with_recursion_anchor`],
    /// which derives the anchor from the function's own declared measure.
    pub(in crate::kernel) fn with_recursion_anchor(mut self, anchor: RecursionAnchor) -> Self {
        self.recursion_anchor = Some(std::sync::Arc::new(anchor));
        self.variable_index = ExecutionEnvironmentVariableIndex::default();
        self
    }

    /// Enables proof-only case splitting at verified conditional-resource
    /// call boundaries. The flag is part of the environment identity so a
    /// checked artifact produced with one call policy cannot be reused under
    /// another.
    pub(crate) fn with_conditional_resource_cases(mut self) -> Self {
        self.allow_conditional_resource_cases = true;
        self.variable_index = ExecutionEnvironmentVariableIndex::default();
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

    pub(in crate::kernel) fn recursion_anchor(&self) -> Option<&RecursionAnchor> {
        self.recursion_anchor.as_deref()
    }

    /// The shared anchor handle, for a certified artifact that has to record
    /// which anchor it was produced under.
    pub(in crate::kernel) fn recursion_anchor_handle(
        &self,
    ) -> Option<std::sync::Arc<RecursionAnchor>> {
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
            && self
                .verified_loop_rules
                .shares_storage_with(&other.verified_loop_rules)
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
    fn loop_rule_answers_for_recursion(&self, rule: &VerifiedLoopRule) -> bool {
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
        state: &ExecutionState,
        statement: &ProgramStatement,
        assumptions: &PureFactContext,
    ) -> Option<&VerifiedLoopRule> {
        self.verified_loop_rules.for_statement(statement).find(|rule| {
            // Every rule for this loop statement is a candidate, found through
            // the rules' statement index, in the order the rules were added.
            // The checks below read the rule's whole prerequisite context and
            // state.
            if rule.loop_statement != *statement || !self.loop_rule_answers_for_recursion(rule) {
                return false;
            }
            // A rule stepped under the very context it was certified under
            // finds each prerequisite exactly there: the two hold the same
            // fact sets by identity. Asking each still records reasoning
            // provenance, so a capture asks them all.
            let same_context = || {
                !crate::kernel::assumptions::implicit_reasoning_provenance_capturing()
                    && rule.required_assumptions.holds_the_facts_of(assumptions)
            };
            let assumptions_match = || same_context() || rule
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
                            Proposition::MemoryLoadable {
                                memory,
                                base,
                                bytes,
                                wide: false,
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
            state_matches && assumptions_match()
        })
    }
}

impl VerifiedLoopRule {
    pub(crate) fn loop_invariant_correspondence(
        &self,
        path_index: usize,
    ) -> &[(usize, Proposition)] {
        self.paths[path_index]
            .loop_invariant_correspondence
            .invariants
            .as_deref()
            .unwrap_or_default()
    }

    /// The loop head's pass count the path's facts state over.
    pub(crate) fn loop_iterations(&self, path_index: usize) -> Option<&IntegerTerm> {
        self.paths[path_index]
            .loop_invariant_correspondence
            .iterations
            .as_ref()
    }

    pub(crate) fn with_loop_index(mut self, loop_index: usize) -> Self {
        self.loop_index = Some(loop_index);
        self
    }

    pub fn with_composite_resource_definitions(
        mut self,
        definitions: impl IntoIterator<Item = CompositeResourceDefinition>,
    ) -> Self {
        self.composite_resource_definitions.extend(definitions);
        self
    }
}

impl TerminationError {
    pub fn message(&self) -> &str {
        &self.message
    }

    /// The function whose termination was being decided, when one was.
    pub fn function(&self) -> Option<&str> {
        self.function.as_deref()
    }

    /// Whether the check refused a function-level measure on a function
    /// with no recursive edge to rank.
    pub fn is_superfluous_recursive_measure(&self) -> bool {
        self.superfluous_recursive_measure
    }
}

impl std::fmt::Display for TerminationError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.message.fmt(formatter)
    }
}

impl std::error::Error for TerminationError {}

#[cfg(test)]
mod guarded_quantified_cell_tests {
    use super::*;

    fn index() -> Variable {
        Variable(2_000_000)
    }

    fn holds(condition: ConditionTerm) -> Proposition {
        Proposition::ConditionIs(condition, true)
    }

    fn variable(variable: Variable) -> Box<MachineTerm> {
        Box::new(MachineTerm::Variable(variable))
    }

    /// `p + v` for a byte array `p`, indexed by an unsigned 64-bit `v`.
    fn wide_cell(base: &Pointer) -> Pointer {
        base.offset_by_typed_elements(MachineTerm::Variable(index()), 1, true, true)
    }

    fn parameter() -> Pointer {
        Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::scale_int32(MachineTerm::Variable(Variable(7)), 1),
        }
    }

    #[test]
    fn an_unsigned_guard_names_the_range_from_zero() {
        let base = parameter();
        let length = MachineTerm::Variable(Variable(8));
        let guard = holds(ConditionTerm::Compare {
            format: MachineIntegerType::UInt64,
            relation: CompareRelation::LessThan,
            left: variable(index()),
            right: Box::new(length.clone()),
        });
        assert_eq!(
            MemoryRange::guarded_quantified_cells(&wide_cell(&base), index(), &guard, 1),
            Some(MemoryRange::new_wide(
                base,
                MachineTerm::uint64_constant(0),
                length,
                1
            ))
        );
    }

    #[test]
    fn a_guard_in_another_comparison_or_on_the_binder_names_nothing() {
        let base = parameter();
        let cell = wide_cell(&base);
        let length = Box::new(MachineTerm::Variable(Variable(8)));
        // A signed comparison does not bound an unsigned 64-bit index.
        let signed = holds(ConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::LessThan,
            left: variable(index()),
            right: length.clone(),
        });
        assert_eq!(
            MemoryRange::guarded_quantified_cells(&cell, index(), &signed, 1),
            None
        );
        // An upper bound that mentions the binder is not one fixed range.
        let circular = holds(ConditionTerm::Compare {
            format: MachineIntegerType::UInt64,
            relation: CompareRelation::LessThan,
            left: variable(index()),
            right: Box::new(MachineTerm::Binary {
                format: MachineIntegerType::UInt64,
                op: MachineBinaryOp::Add,
                left: variable(index()),
                right: length.clone(),
            }),
        });
        assert_eq!(
            MemoryRange::guarded_quantified_cells(&cell, index(), &circular, 1),
            None
        );
        // A stride other than the read's width is not that range's element.
        let bound = holds(ConditionTerm::Compare {
            format: MachineIntegerType::UInt64,
            relation: CompareRelation::LessThan,
            left: variable(index()),
            right: length,
        });
        assert_eq!(
            MemoryRange::guarded_quantified_cells(&cell, index(), &bound, 4),
            None
        );
        // A base that moves with the binder is not one fixed range.
        let moving = wide_cell(&Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::scale_int32(MachineTerm::Variable(index()), 1),
        });
        assert_eq!(
            MemoryRange::guarded_quantified_cells(&moving, index(), &bound, 1),
            None
        );
    }
}
