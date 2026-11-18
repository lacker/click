//! C syntax import for the executable C model.

use crate::kernel::{
    BindingDeclaration, BindingName, LocalBindingId, LocalFunctionId, StaticBindingId,
    StaticBindingMetadata, StaticBindingOwner,
};
use crate::languages::interface::pointer_array_element_type;
use crate::languages::interface::record_value_type;

pub use crate::languages::interface::{
    CallbackInterface, CallbackParameter, ImportedFunction, ImportedParameter, InterfaceType,
    RecordField, RecordLayout, RustIteratorKind, RustLoopIterator,
};

use crate::languages::interface::{RecordScalarField, RecordUnionField, RecordUnionLayout};
use std::collections::{BTreeMap, BTreeSet};

use crate::source::{SourcePosition, SourcePositionCursor};

use super::source::ExpandedLineMap;
use super::source_map::CSourceMap;
pub use super::target::{LongRank, PlainChar};

/// Stable documentation IDs for the accepted C surface. This registry
/// describes source forms rather than the lowered enum variants because some
/// forms are syntax sugar and several forms share a representation.
pub const C_PUBLIC_FORMS: &[&str] = &[
    "type.void",
    "type.int32",
    "type.uint8",
    "type.uint32",
    "type.standard-spellings",
    "type.typedef",
    "type.enum",
    "type.union",
    "type.pointer",
    "type.pointer-to-pointer",
    "type.array-parameter",
    "type.local-array",
    "type.struct-array-parameter",
    "type.struct-value",
    "type.local-integer-bit-field-record",
    "type.function-pointer",
    "type.struct-pointer",
    "type.typeof",
    "declaration.function",
    "declaration.struct",
    "declaration.struct-field-list",
    "declaration.enum",
    "declaration.union",
    "declaration.union-field-list",
    "declaration.static-local",
    "declaration.global-array",
    "declaration.local",
    "statement.struct-value-declaration",
    "statement.empty",
    "statement.block",
    "statement.assignment",
    "statement.initializer",
    "statement.declaration-list",
    "statement.call",
    "statement.call-assignment",
    "statement.return",
    "statement.if",
    "statement.else-if",
    "statement.unbraced-body",
    "statement.while",
    "statement.break",
    "statement.continue",
    "statement.switch",
    "statement.do-while",
    "statement.for",
    "statement.for-step-list",
    "statement.for-omitted-clause",
    "statement.for-init-list",
    "statement.for-declaration-list",
    "statement.store",
    "statement.sequential-kernel-store",
    "statement.malloc",
    "statement.calloc",
    "statement.realloc",
    "statement.free",
    "statement.increment",
    "statement.decrement",
    "statement.prefix-increment",
    "statement.prefix-decrement",
    "statement.add-assign",
    "statement.subtract-assign",
    "statement.multiply-assign",
    "statement.xor-assign",
    "statement.divide-assign",
    "statement.remainder-assign",
    "statement.shift-left-assign",
    "statement.shift-right-assign",
    "statement.bitwise-and-assign",
    "statement.bitwise-or-assign",
    "statement.memory-lvalue-update",
    "expression.variable",
    "expression.int-literal",
    "expression.hex-literal",
    "expression.octal-literal",
    "expression.integer-literal-suffix",
    "expression.char-literal",
    "expression.string-literal",
    "expression.null-pointer",
    "expression.address-of",
    "expression.cast",
    "expression.pointer-integer-cast",
    "expression.assignment",
    "expression.conditional",
    "expression.statement-expression",
    "expression.struct-compound-literal",
    "expression.builtin-expect",
    "expression.builtin-types-compatible",
    "expression.builtin-offsetof",
    "declaration.static-assert",
    "expression.sizeof-struct",
    "expression.sizeof-type",
    "expression.call",
    "expression.index",
    "expression.field",
    "expression.dereference",
    "expression.sequential-kernel-read",
    "expression.sequential-kernel-write",
    "expression.pointer-arithmetic",
    "operator.logical-not",
    "operator.unary-plus",
    "operator.logical-and",
    "operator.logical-or",
    "operator.equal",
    "operator.not-equal",
    "operator.less-than",
    "operator.less-equal",
    "operator.greater-than",
    "operator.greater-equal",
    "operator.add",
    "operator.subtract",
    "operator.multiply",
    "operator.divide",
    "operator.remainder",
    "operator.shift-left",
    "operator.shift-right",
    "operator.bitwise-and",
    "operator.bitwise-or",
    "operator.bitwise-xor",
    "operator.bitwise-not",
];

#[derive(Clone, Debug)]
struct StaticAddress {
    pointer: crate::kernel::Address,
    interface_type: InterfaceType,
    constant: bool,
    /// The member subobject the address selects, if any.
    bounds: Option<crate::kernel::SubobjectBounds>,
}

/// One string literal occurrence, with static storage and a source identity.
/// `bytes` includes the required terminating NUL byte.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CStringLiteral {
    identity: Option<crate::kernel::StringLiteralId>,
    bytes: Vec<u8>,
    /// The target's plain `char`, the literal's element type (C11 6.4.5p6).
    plain_char: PlainChar,
}

impl CStringLiteral {
    fn new(
        identity: Option<crate::kernel::StringLiteralId>,
        mut bytes: Vec<u8>,
        plain_char: PlainChar,
    ) -> Self {
        bytes.push(0);
        Self {
            identity,
            bytes,
            plain_char,
        }
    }

    pub fn plain_char(&self) -> PlainChar {
        self.plain_char
    }

    /// The kernel literal: its bytes stored as cells of the target's plain
    /// `char` representation.
    pub fn to_kernel(&self) -> crate::kernel::StringLiteral {
        crate::kernel::StringLiteral::new(
            self.identity
                .clone()
                .expect("literal metadata has a function owner"),
            self.bytes.clone(),
        )
        .with_element_type(self.plain_char.byte_type().to_kernel_type())
    }

    pub fn identity(&self) -> Option<&crate::kernel::StringLiteralId> {
        self.identity.as_ref()
    }

    pub fn bytes(&self) -> &[u8] {
        &self.bytes
    }
}

// The projected header's reserved binding denotes a value, with no C
// storage that a program can address or that a call can invalidate.
const HOSTED_STDOUT_BINDING: &str = "__click_c_stdio_stdout";

fn hosted_stdout_value() -> crate::kernel::ProgramValue {
    crate::kernel::ProgramValue::typed_pointer(
        crate::kernel::SymbolicMemory::global_pointer("__click_c_stdio_stdout_stream"),
        crate::kernel::ProgramType::Int32Pointer,
    )
}

/// A file-scope scalar declaration collected from one C translation unit.
/// `initializer` is absent for an `extern` declaration and present for the
/// definition that supplies storage (including an implicit zero initializer).
/// A definition without an initializer is marked tentative so repeated
/// declarations can be coalesced before a real initializer is selected.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CGlobal {
    name: String,
    kernel_name: BindingName,
    interface_type: InterfaceType,
    struct_name: Option<String>,
    initializer: Option<CExpression>,
    /// The address an externally linked pointer's initializer names,
    /// resolved in its defining translation unit. Another unit may not see
    /// the private object the initializer names, so it reads this value and
    /// never re-evaluates the initializer against its own names.
    resolved_address: Option<crate::kernel::ProgramValue>,
    hosted_stdout: bool,
    tentative: bool,
    file_static: bool,
    volatile: bool,
    pointee_volatile: bool,
    constant: bool,
    pointee_constant: bool,
}

impl CGlobal {
    fn declaration(
        name: String,
        interface_type: InterfaceType,
        struct_name: Option<String>,
    ) -> Self {
        Self {
            kernel_name: name.clone().into(),
            name,
            interface_type,
            struct_name,
            initializer: None,
            resolved_address: None,
            hosted_stdout: false,
            tentative: false,
            file_static: false,
            volatile: false,
            pointee_volatile: false,
            constant: false,
            pointee_constant: false,
        }
    }

    fn definition(
        name: String,
        interface_type: InterfaceType,
        struct_name: Option<String>,
        initializer: CExpression,
    ) -> Self {
        Self {
            kernel_name: name.clone().into(),
            name,
            interface_type,
            struct_name,
            initializer: Some(initializer),
            resolved_address: None,
            hosted_stdout: false,
            tentative: false,
            file_static: false,
            volatile: false,
            pointee_volatile: false,
            constant: false,
            pointee_constant: false,
        }
    }

    fn file_static_definition(
        name: String,
        kernel_name: BindingName,
        interface_type: InterfaceType,
        struct_name: Option<String>,
        initializer: CExpression,
    ) -> Self {
        Self {
            name,
            kernel_name,
            interface_type,
            struct_name,
            initializer: Some(initializer),
            resolved_address: None,
            hosted_stdout: false,
            tentative: false,
            file_static: true,
            volatile: false,
            pointee_volatile: false,
            constant: false,
            pointee_constant: false,
        }
    }

    pub fn name(&self) -> &str {
        &self.name
    }

    /// This global with its pointer initializer's address resolved by its
    /// defining translation unit.
    pub(crate) fn with_resolved_address(mut self, address: crate::kernel::ProgramValue) -> Self {
        self.resolved_address = Some(address);
        self
    }

    pub fn kernel_name(&self) -> &BindingName {
        &self.kernel_name
    }

    pub fn interface_type(&self) -> InterfaceType {
        self.interface_type
    }

    pub fn struct_name(&self) -> Option<&str> {
        self.struct_name.as_deref()
    }

    pub fn is_defined(&self) -> bool {
        self.initializer.is_some()
    }

    pub(crate) fn is_hosted_stdout(&self) -> bool {
        self.hosted_stdout
    }

    pub(crate) fn hosted_stdout(&self) -> Option<crate::kernel::ProgramValue> {
        self.is_hosted_stdout().then(hosted_stdout_value)
    }

    /// Returns whether this is a C tentative definition such as `int x;`.
    /// Tentative definitions have storage and are lowered with their implicit
    /// zero initializer, but may coalesce with other tentative declarations or
    /// with one initialized definition.
    pub fn is_tentative(&self) -> bool {
        self.tentative
    }

    pub(crate) fn is_initialized_definition(&self) -> bool {
        self.is_defined() && !self.is_tentative()
    }

    pub fn is_file_static(&self) -> bool {
        self.file_static
    }

    pub fn initializer(&self) -> Option<&CExpression> {
        self.initializer.as_ref()
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

    fn with_volatile(mut self, volatile: bool) -> Self {
        self.volatile = volatile;
        self
    }

    fn with_pointee_volatile(mut self, pointee_volatile: bool) -> Self {
        self.pointee_volatile = pointee_volatile;
        self
    }

    fn with_tentative(mut self, tentative: bool) -> Self {
        self.tentative = tentative;
        self
    }

    fn with_constant(mut self, constant: bool) -> Self {
        self.constant = constant;
        self
    }

    fn with_pointee_constant(mut self, pointee_constant: bool) -> Self {
        self.pointee_constant = pointee_constant;
        self
    }

    pub(crate) fn to_kernel_global(&self) -> Option<crate::kernel::Global> {
        let initializer = self.initializer.as_ref()?;
        let value = match self.interface_type {
            InterfaceType::Float32 => match initializer {
                CExpression::Float32Literal(bits) => {
                    crate::kernel::float32(crate::kernel::MachineTerm::constant(*bits))
                }
                _ => return None,
            },
            InterfaceType::Float64 => match initializer {
                CExpression::Float64Literal(bits) => {
                    crate::kernel::float64(crate::kernel::MachineTerm::uint64_constant(*bits))
                }
                _ => return None,
            },
            _ => kernel_integer_literal_value(self.interface_type, initializer)?,
        };
        Some(self.to_kernel_global_with_value(value))
    }

    fn to_kernel_global_with_value(
        &self,
        value: crate::kernel::ProgramValue,
    ) -> crate::kernel::Global {
        crate::kernel::Global::new_with_kernel_name(
            self.name.clone(),
            self.kernel_name.clone(),
            self.interface_type.to_kernel_type(),
            value,
        )
        .with_volatile(self.is_volatile())
        .with_pointee_volatile(self.pointee_is_volatile())
        .with_constant(self.is_constant())
        .with_pointee_constant(self.pointee_is_constant())
        .with_declared_class(self.declared_class())
    }

    /// The global's strict-aliasing class (`design/effective-types.md`). A
    /// struct pointer's class names its struct by tag, which is all a
    /// pointer class compares.
    fn declared_class(&self) -> Option<crate::kernel::effective_type::CAccessClass> {
        match self.struct_name.as_deref() {
            Some(name) => struct_pointer_class(
                self.interface_type,
                crate::kernel::effective_type::CPointeeBase::Struct(
                    crate::kernel::effective_type::CStructClass::opaque(name),
                ),
            ),
            None => self
                .interface_type
                .access_class()
                .or_else(|| int_pointer_class(self.interface_type)),
        }
    }
}

/// A file-scope scalar array collected from one C translation unit.
/// `initializer` is absent for an `extern` declaration or an incomplete
/// tentative definition, and present for the definition that supplies storage.
/// Missing elements in a complete definition are the zero initializer, held
/// implicitly by the [`CArrayInitializer`] rather than one by one. A
/// definition without an initializer is marked tentative so
/// repeated declarations can be coalesced before a real initializer is
/// selected.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CGlobalArray {
    name: String,
    kernel_name: BindingName,
    element_type: InterfaceType,
    length: Option<u32>,
    shape: Option<Vec<u32>>,
    incomplete_shape: Option<Vec<u32>>,
    initializer: Option<CArrayInitializer>,
    /// An externally linked pointer array lowered by its defining
    /// translation unit, whose element initializers may name objects private
    /// to that unit. Other units read this instead of re-evaluating them.
    resolved: Option<crate::kernel::GlobalArray>,
    tentative: bool,
    file_static: bool,
    constant: bool,
}

impl CGlobalArray {
    fn declaration(
        name: String,
        kernel_name: BindingName,
        element_type: InterfaceType,
        shape: Option<Vec<u32>>,
        incomplete_shape: Option<Vec<u32>>,
        file_static: bool,
    ) -> Self {
        let length = shape
            .as_deref()
            .map(|shape| array_shape_element_count(shape).expect("validated global array shape"));
        Self {
            name,
            kernel_name,
            element_type,
            length,
            shape,
            incomplete_shape,
            initializer: None,
            resolved: None,
            tentative: false,
            file_static,
            constant: false,
        }
    }

    fn definition(
        name: String,
        kernel_name: BindingName,
        element_type: InterfaceType,
        shape: Vec<u32>,
        initializer: CArrayInitializer,
        file_static: bool,
    ) -> Self {
        let length = array_shape_element_count(&shape).expect("validated global array shape");
        assert_eq!(
            initializer.length(),
            length,
            "a global array initializer covers its declared length"
        );
        Self {
            name,
            kernel_name,
            element_type,
            length: Some(length),
            shape: Some(shape),
            incomplete_shape: None,
            initializer: Some(initializer),
            resolved: None,
            tentative: false,
            file_static,
            constant: false,
        }
    }

    pub fn name(&self) -> &str {
        &self.name
    }

    /// This array as lowered by its defining translation unit.
    pub(crate) fn with_resolved(mut self, resolved: crate::kernel::GlobalArray) -> Self {
        self.resolved = Some(resolved);
        self
    }

    pub fn kernel_name(&self) -> &BindingName {
        &self.kernel_name
    }

    pub fn element_type(&self) -> InterfaceType {
        self.element_type
    }

    pub fn length(&self) -> u32 {
        self.length
            .expect("incomplete external array has no source-level length")
    }

    #[cfg(test)]
    pub(crate) fn array_length(&self) -> Option<u32> {
        self.length
    }

    pub fn shape(&self) -> Option<&[u32]> {
        self.shape.as_deref()
    }

    pub(crate) fn incomplete_shape(&self) -> Option<&[u32]> {
        self.incomplete_shape.as_deref()
    }

    /// Returns the dimensions needed to flatten an indexed source access.
    /// An incomplete outer dimension uses `1` as a placeholder because it
    /// affects no inner stride; the linked complete definition supplies the
    /// actual storage length later.
    pub(crate) fn index_shape(&self) -> Option<Vec<u32>> {
        if let Some(shape) = &self.shape {
            return Some(shape.clone());
        }
        self.incomplete_shape
            .as_ref()
            .filter(|shape| !shape.is_empty())
            .map(|shape| {
                let mut index_shape = Vec::with_capacity(shape.len() + 1);
                index_shape.push(1);
                index_shape.extend(shape.iter().copied());
                index_shape
            })
    }

    pub fn is_incomplete(&self) -> bool {
        self.length.is_none()
    }

    pub(crate) fn complete_c_type(&self) -> Option<InterfaceType> {
        array_type_for_element(self.element_type, self.length?)
    }

    pub fn is_defined(&self) -> bool {
        self.initializer.is_some()
    }

    /// Returns whether this is a C tentative definition such as `int x[3];`.
    /// Tentative definitions have storage and are lowered with implicit zero
    /// initializers, but may coalesce with other tentative declarations or
    /// with one initialized definition.
    pub fn is_tentative(&self) -> bool {
        self.tentative
    }

    pub(crate) fn is_initialized_definition(&self) -> bool {
        self.is_defined() && !self.is_tentative()
    }

    pub fn is_file_static(&self) -> bool {
        self.file_static
    }

    pub fn is_constant(&self) -> bool {
        self.constant
    }

    fn with_constant(mut self, constant: bool) -> Self {
        self.constant = constant;
        self
    }

    fn with_tentative(mut self, tentative: bool) -> Self {
        self.tentative = tentative;
        self
    }

    pub fn initializer(&self) -> Option<&CArrayInitializer> {
        self.initializer.as_ref()
    }

    fn to_kernel_global_array_with_values(
        &self,
        values: crate::kernel::ArrayContents,
    ) -> crate::kernel::GlobalArray {
        crate::kernel::GlobalArray::new_with_kernel_name(
            self.name.clone(),
            self.kernel_name.clone(),
            self.element_type.to_kernel_type(),
            self.length(),
            values,
        )
        .with_constant(self.is_constant())
        .with_declared_class(self.element_type.access_class())
    }
}

/// A file-scope object with a supported struct layout. Aggregate values are
/// represented by their stable address-backed layout rather than a scalar
/// initializer value. `initializer` contains only explicitly initialized
/// scalar leaves; omitted leaves are zero-initialized by the kernel. A
/// definition without an initializer is marked tentative so repeated
/// declarations can be coalesced before a real initializer is selected.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CGlobalAggregate {
    name: String,
    kernel_name: BindingName,
    struct_name: String,
    layout: RecordLayout,
    initializer: Option<Vec<CAggregateInitializer>>,
    defined: bool,
    tentative: bool,
    file_static: bool,
    constant: bool,
}

/// A fixed-size one-dimensional file-scope array of supported struct
/// aggregates. The initializer offsets are relative to the beginning of the
/// complete array block; omitted elements and fields are zero-initialized by
/// the kernel.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CGlobalAggregateArray {
    name: String,
    kernel_name: BindingName,
    struct_name: String,
    layout: RecordLayout,
    length: Option<u32>,
    initializer: Option<Vec<CAggregateInitializer>>,
    tentative: bool,
    file_static: bool,
    constant: bool,
}

impl CGlobalAggregateArray {
    fn declaration(
        name: String,
        kernel_name: BindingName,
        struct_name: String,
        layout: RecordLayout,
        length: Option<u32>,
        file_static: bool,
    ) -> Self {
        Self {
            name,
            kernel_name,
            struct_name,
            layout,
            length,
            initializer: None,
            tentative: false,
            file_static,
            constant: false,
        }
    }

    fn definition(
        name: String,
        kernel_name: BindingName,
        struct_name: String,
        layout: RecordLayout,
        length: u32,
        initializer: Vec<CAggregateInitializer>,
        file_static: bool,
    ) -> Self {
        Self {
            name,
            kernel_name,
            struct_name,
            layout,
            length: Some(length),
            initializer: Some(initializer),
            tentative: false,
            file_static,
            constant: false,
        }
    }

    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn kernel_name(&self) -> &BindingName {
        &self.kernel_name
    }

    pub fn struct_name(&self) -> &str {
        &self.struct_name
    }

    pub fn layout(&self) -> &RecordLayout {
        &self.layout
    }

    pub fn length(&self) -> u32 {
        self.length
            .expect("incomplete external aggregate array has no source-level length")
    }

    pub(crate) fn array_length(&self) -> Option<u32> {
        self.length
    }

    pub fn is_incomplete(&self) -> bool {
        self.length.is_none()
    }

    pub fn interface_type(&self) -> InterfaceType {
        self.complete_c_type()
            .expect("incomplete external aggregate array has no C type")
    }

    pub(crate) fn complete_c_type(&self) -> Option<InterfaceType> {
        Some(InterfaceType::UInt8Array(
            self.length?
                .checked_mul(self.layout.size_bytes())
                .expect("validated aggregate array size"),
        ))
    }

    pub fn is_defined(&self) -> bool {
        self.initializer.is_some()
    }

    /// Returns whether this is a C tentative definition such as
    /// `struct state x[2];`.
    /// Tentative definitions have storage and are lowered with implicit zero
    /// initialization, but may coalesce with other tentative declarations or
    /// with one initialized definition.
    pub fn is_tentative(&self) -> bool {
        self.tentative
    }

    pub(crate) fn is_initialized_definition(&self) -> bool {
        self.is_defined() && !self.is_tentative()
    }

    pub fn is_file_static(&self) -> bool {
        self.file_static
    }

    pub fn is_constant(&self) -> bool {
        self.constant
    }

    fn with_constant(mut self, constant: bool) -> Self {
        self.constant = constant;
        self
    }

    fn with_tentative(mut self, tentative: bool) -> Self {
        self.tentative = tentative;
        self
    }

    pub fn initializer(&self) -> Option<&[CAggregateInitializer]> {
        self.initializer.as_deref()
    }

    pub(crate) fn to_kernel_global_aggregate_array(
        &self,
    ) -> Option<crate::kernel::GlobalAggregateArray> {
        let initializer = self.initializer.as_ref()?;
        let initializers = initializer
            .iter()
            .map(CAggregateInitializer::to_kernel)
            .collect::<Option<Vec<_>>>()?;
        Some(
            crate::kernel::GlobalAggregateArray::new(
                self.name.clone(),
                self.kernel_name.clone(),
                self.layout.to_kernel_aggregate_layout(),
                self.length(),
                initializers,
            )
            .with_constant(self.is_constant())
            .with_declared_class(
                self.layout
                    .class
                    .clone()
                    .map(crate::kernel::effective_type::CAccessClass::Struct),
            ),
        )
    }
}

impl CGlobalAggregate {
    fn declaration(
        name: String,
        kernel_name: BindingName,
        struct_name: String,
        layout: RecordLayout,
        file_static: bool,
    ) -> Self {
        Self {
            name,
            kernel_name,
            struct_name,
            layout,
            initializer: None,
            defined: false,
            tentative: false,
            file_static,
            constant: false,
        }
    }

    fn definition(
        name: String,
        kernel_name: BindingName,
        struct_name: String,
        layout: RecordLayout,
        initializer: Vec<CAggregateInitializer>,
        file_static: bool,
    ) -> Self {
        Self {
            name,
            kernel_name,
            struct_name,
            layout,
            initializer: Some(initializer),
            defined: true,
            tentative: false,
            file_static,
            constant: false,
        }
    }

    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn kernel_name(&self) -> &BindingName {
        &self.kernel_name
    }

    pub fn struct_name(&self) -> &str {
        &self.struct_name
    }

    pub fn layout(&self) -> &RecordLayout {
        &self.layout
    }

    pub fn is_defined(&self) -> bool {
        self.defined
    }

    /// Returns whether this is a C tentative definition such as
    /// `struct state x;`.
    /// Tentative definitions have storage and are lowered with implicit zero
    /// initialization, but may coalesce with other tentative declarations or
    /// with one initialized definition.
    pub fn is_tentative(&self) -> bool {
        self.tentative
    }

    pub(crate) fn is_initialized_definition(&self) -> bool {
        self.is_defined() && !self.is_tentative()
    }

    pub fn is_file_static(&self) -> bool {
        self.file_static
    }

    pub fn is_constant(&self) -> bool {
        self.constant
    }

    fn with_constant(mut self, constant: bool) -> Self {
        self.constant = constant;
        self
    }

    fn with_tentative(mut self, tentative: bool) -> Self {
        self.tentative = tentative;
        self
    }

    pub fn initializer(&self) -> Option<&[CAggregateInitializer]> {
        self.initializer.as_deref()
    }

    pub(crate) fn to_kernel_global_aggregate(&self) -> Option<crate::kernel::GlobalAggregate> {
        let initializer = self.initializer.as_ref()?;
        let initializers = initializer
            .iter()
            .map(CAggregateInitializer::to_kernel)
            .collect::<Option<Vec<_>>>()?;
        self.defined.then(|| {
            crate::kernel::GlobalAggregate::new(
                self.name.clone(),
                self.kernel_name.clone(),
                self.layout.to_kernel_aggregate_layout(),
                initializers,
            )
            .with_constant(self.is_constant())
            .with_declared_class(
                self.layout
                    .class
                    .clone()
                    .map(crate::kernel::effective_type::CAccessClass::Struct),
            )
        })
    }
}

fn supports_local_array_initializer(interface_type: InterfaceType) -> bool {
    matches!(
        interface_type,
        InterfaceType::Int32Array(_)
            | InterfaceType::UInt32Array(_)
            | InterfaceType::CharArray(_, _)
            | InterfaceType::UInt8Array(_)
            | InterfaceType::Float32Array(_)
            | InterfaceType::Float64Array(_)
            | InterfaceType::PointerArray(_, _, _)
    )
}

fn array_type_for_element(element_type: InterfaceType, length: u32) -> Option<InterfaceType> {
    if let Some(pointer_element) = pointer_array_element(element_type) {
        return Some(InterfaceType::PointerArray(
            pointer_element,
            element_type.long_rank().unwrap_or(LongRank::Long),
            length,
        ));
    }
    Some(match element_type {
        InterfaceType::Int8 => InterfaceType::Int8Array(length),
        InterfaceType::Int16 => InterfaceType::Int16Array(length),
        InterfaceType::Int32 => InterfaceType::Int32Array(length),
        InterfaceType::Char(plain) => InterfaceType::CharArray(plain, length),
        InterfaceType::UInt8 => InterfaceType::UInt8Array(length),
        InterfaceType::UInt16 => InterfaceType::UInt16Array(length),
        InterfaceType::UInt32 => InterfaceType::UInt32Array(length),
        InterfaceType::Int64(rank) => InterfaceType::Int64Array(rank, length),
        InterfaceType::Int128 => InterfaceType::Int128Array(length),
        InterfaceType::UInt64(rank) => InterfaceType::UInt64Array(rank, length),
        InterfaceType::UInt128 => InterfaceType::UInt128Array(length),
        InterfaceType::Float32 => InterfaceType::Float32Array(length),
        InterfaceType::Float64 => InterfaceType::Float64Array(length),
        _ => return None,
    })
}

fn pointer_array_element(
    interface_type: InterfaceType,
) -> Option<crate::kernel::PointerArrayElement> {
    use crate::kernel::PointerArrayElement as Element;
    Some(match interface_type {
        InterfaceType::VoidPointer => Element::Void,
        InterfaceType::CharPointer(PlainChar::Unsigned) => Element::UnsignedPlainChar,
        InterfaceType::CharPointer(PlainChar::Signed) => Element::SignedPlainChar,
        InterfaceType::CharPointerPointer(PlainChar::Unsigned) => Element::UnsignedPlainCharPointer,
        InterfaceType::CharPointerPointer(PlainChar::Signed) => Element::SignedPlainCharPointer,
        InterfaceType::Int8Pointer => Element::Int8,
        InterfaceType::Int16Pointer => Element::Int16,
        InterfaceType::Int32Pointer => Element::Int32,
        InterfaceType::UInt8Pointer => Element::UInt8,
        InterfaceType::UInt16Pointer => Element::UInt16,
        InterfaceType::UInt32Pointer => Element::UInt32,
        InterfaceType::Int64Pointer(_) => Element::Int64,
        InterfaceType::Int128Pointer => Element::Int128,
        InterfaceType::UInt64Pointer(_) => Element::UInt64,
        InterfaceType::UInt128Pointer => Element::UInt128,
        InterfaceType::Float32Pointer => Element::Float32,
        InterfaceType::Float64Pointer => Element::Float64,
        _ => return None,
    })
}

/// A literal initializer's kernel value at its declared interface type.
fn kernel_integer_literal_value(
    interface_type: InterfaceType,
    initializer: &CExpression,
) -> Option<crate::kernel::ProgramValue> {
    Some(match interface_type {
        InterfaceType::Bool => {
            crate::kernel::ProgramValue::bool_constant(initializer_integer_bits(initializer)? != 0)
        }
        InterfaceType::Float32 => match initializer {
            CExpression::Float32Literal(bits) => {
                crate::kernel::float32(crate::kernel::MachineTerm::constant(*bits))
            }
            _ => return None,
        },
        InterfaceType::Float64 => match initializer {
            CExpression::Float64Literal(bits) => {
                crate::kernel::float64(crate::kernel::MachineTerm::uint64_constant(*bits))
            }
            _ => return None,
        },
        InterfaceType::Int8 => crate::kernel::int8(initializer_integer_bits(initializer)?),
        InterfaceType::Int16 => crate::kernel::int16(initializer_integer_bits(initializer)?),
        InterfaceType::Int32 => crate::kernel::int32(initializer_integer_bits(initializer)?),
        InterfaceType::Char(plain) => kernel_integer_literal_value(plain.byte_type(), initializer)?,
        InterfaceType::UInt8 => crate::kernel::uint8(initializer_integer_bits(initializer)?),
        InterfaceType::UInt16 => crate::kernel::uint16(initializer_integer_bits(initializer)?),
        InterfaceType::UInt32 => crate::kernel::uint32(initializer_integer_bits(initializer)?),
        InterfaceType::Int64(_) => match initializer {
            CExpression::Int64Literal(value) => {
                crate::kernel::int64(crate::kernel::MachineTerm::int64_constant(*value))
            }
            CExpression::Int32Literal(value) => {
                crate::kernel::int64(crate::kernel::MachineTerm::int64_from_32(
                    crate::kernel::MachineTerm::constant(*value),
                ))
            }
            CExpression::UInt8Literal(value) => {
                crate::kernel::int64(crate::kernel::MachineTerm::int64_from_uint32(
                    crate::kernel::MachineTerm::constant(u32::from(*value)),
                ))
            }
            CExpression::UInt32Literal(value) => {
                crate::kernel::int64(crate::kernel::MachineTerm::int64_from_uint32(
                    crate::kernel::MachineTerm::constant(*value),
                ))
            }
            _ => return None,
        },
        InterfaceType::UInt64(_) => match initializer {
            CExpression::UInt64Literal(value) => {
                crate::kernel::uint64(crate::kernel::MachineTerm::uint64_constant(*value))
            }
            CExpression::Int64Literal(value) if *value >= 0 => {
                crate::kernel::uint64(crate::kernel::MachineTerm::uint64_constant(*value as u64))
            }
            CExpression::Int32Literal(value) => {
                crate::kernel::uint64(crate::kernel::MachineTerm::uint64_from_int32(
                    crate::kernel::MachineTerm::constant(*value),
                ))
            }
            CExpression::UInt8Literal(value) => {
                crate::kernel::uint64(crate::kernel::MachineTerm::uint64_from_32(
                    crate::kernel::MachineTerm::constant(u32::from(*value)),
                ))
            }
            CExpression::UInt32Literal(value) => {
                crate::kernel::uint64(crate::kernel::MachineTerm::uint64_from_32(
                    crate::kernel::MachineTerm::constant(*value),
                ))
            }
            _ => return None,
        },
        InterfaceType::VoidPointer
        | InterfaceType::VoidPointerPointer
        | InterfaceType::Int8Pointer
        | InterfaceType::Int8PointerPointer
            if matches!(initializer, CExpression::Int32Literal(0)) =>
        {
            crate::kernel::ProgramValue::typed_pointer(
                crate::kernel::Address::null(),
                interface_type.to_kernel_type(),
            )
        }
        InterfaceType::Int16Pointer
        | InterfaceType::UInt16Pointer
        | InterfaceType::Int32Pointer
        | InterfaceType::CharPointer(_)
        | InterfaceType::UInt8Pointer
        | InterfaceType::UInt32Pointer
        | InterfaceType::Int128Pointer
        | InterfaceType::Int64Pointer(_)
        | InterfaceType::UInt128Pointer
        | InterfaceType::UInt64Pointer(_)
        | InterfaceType::Float32Pointer
        | InterfaceType::Float64Pointer
        | InterfaceType::Int16PointerPointer
        | InterfaceType::UInt16PointerPointer
        | InterfaceType::Int32PointerPointer
        | InterfaceType::CharPointerPointer(_)
        | InterfaceType::UInt8PointerPointer
        | InterfaceType::UInt32PointerPointer
        | InterfaceType::Int128PointerPointer
        | InterfaceType::Int64PointerPointer(_)
        | InterfaceType::UInt128PointerPointer
        | InterfaceType::UInt64PointerPointer(_)
        | InterfaceType::Float32PointerPointer
        | InterfaceType::Float64PointerPointer
            if matches!(initializer, CExpression::Int32Literal(0)) =>
        {
            crate::kernel::ProgramValue::typed_pointer(
                crate::kernel::Address::null(),
                interface_type.to_kernel_type(),
            )
        }
        _ => return None,
    })
}

fn kernel_aggregate_initializer_value(
    interface_type: InterfaceType,
    initializer: &CExpression,
) -> Option<crate::kernel::ProgramValue> {
    match interface_type {
        InterfaceType::Int32Pointer
        | InterfaceType::CharPointer(_)
        | InterfaceType::UInt8Pointer
        | InterfaceType::Float32Pointer
        | InterfaceType::Float64Pointer
        | InterfaceType::Int32PointerPointer
        | InterfaceType::CharPointerPointer(_)
        | InterfaceType::UInt8PointerPointer
        | InterfaceType::Float32PointerPointer
        | InterfaceType::Float64PointerPointer
            if matches!(initializer, CExpression::Int32Literal(0)) =>
        {
            Some(crate::kernel::ProgramValue::typed_pointer(
                crate::kernel::Address::null(),
                interface_type.to_kernel_type(),
            ))
        }
        // A callback field holds a function address or the null pointer. The
        // address is stored already retagged with the field's declared
        // signature, exactly as a store through a pointer coerces `&f` before
        // writing the cell, so a later load dispatches to the concrete target.
        InterfaceType::FunctionPointer(_) => match initializer {
            CExpression::Int32Literal(0) => Some(crate::kernel::ProgramValue::typed_pointer(
                crate::kernel::Address::null(),
                interface_type.to_kernel_type(),
            )),
            CExpression::FunctionAddress(name) => Some(crate::kernel::ProgramValue::typed_pointer(
                crate::kernel::Address::function(name.clone()),
                interface_type.to_kernel_type(),
            )),
            _ => None,
        },
        InterfaceType::Int8 => kernel_integer_literal_value(interface_type, initializer),
        InterfaceType::Int16
        | InterfaceType::Bool
        | InterfaceType::Int32
        | InterfaceType::Char(_)
        | InterfaceType::UInt8
        | InterfaceType::UInt16
        | InterfaceType::UInt32
        | InterfaceType::Int64(_)
        | InterfaceType::UInt64(_)
        | InterfaceType::Float32
        | InterfaceType::Float64 => kernel_integer_literal_value(interface_type, initializer),
        _ => None,
    }
}

/// A function-local scalar with static storage duration. The source name is
/// what C fragments use; `kernel_name` keeps distinct block scopes distinct
/// in the lowered C expression tree.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CStaticLocal {
    source_name: String,
    kernel_name: BindingName,
    interface_type: InterfaceType,
    initializer: CExpression,
    volatile: bool,
    pointee_volatile: bool,
    constant: bool,
    pointee_constant: bool,
}

/// A function-local fixed-size scalar array with static storage duration.
/// The source name is what C fragments use; `kernel_name` keeps distinct
/// block scopes distinct in the lowered C expression tree.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CStaticArray {
    source_name: String,
    kernel_name: BindingName,
    element_type: InterfaceType,
    length: u32,
    shape: Vec<u32>,
    initializer: CArrayInitializer,
    constant: bool,
    /// Whether a pointer element's pointee is const-qualified.
    pointee_constant: bool,
}

impl CStaticArray {
    fn new(
        source_name: String,
        kernel_name: BindingName,
        element_type: InterfaceType,
        length: u32,
        initializer: CArrayInitializer,
    ) -> Self {
        assert_eq!(
            initializer.length(),
            length,
            "a static array initializer covers its declared length"
        );
        Self {
            source_name,
            kernel_name,
            element_type,
            length,
            shape: vec![length],
            initializer,
            constant: false,
            pointee_constant: false,
        }
    }

    pub fn name(&self) -> &str {
        &self.source_name
    }

    pub fn shape(&self) -> &[u32] {
        &self.shape
    }

    fn with_shape(mut self, shape: Vec<u32>) -> Self {
        self.shape = shape;
        self
    }

    pub fn kernel_name(&self) -> &BindingName {
        &self.kernel_name
    }

    pub fn element_type(&self) -> InterfaceType {
        self.element_type
    }

    pub fn length(&self) -> u32 {
        self.length
    }

    pub fn interface_type(&self) -> InterfaceType {
        array_type_for_element(self.element_type, self.length)
            .expect("validated static array element type")
    }

    pub fn initializer(&self) -> &CArrayInitializer {
        &self.initializer
    }

    pub fn is_constant(&self) -> bool {
        self.constant
    }

    fn with_constant(mut self, constant: bool) -> Self {
        self.constant = constant;
        self
    }

    pub fn pointee_is_constant(&self) -> bool {
        self.pointee_constant
    }

    fn with_pointee_constant(mut self, pointee_constant: bool) -> Self {
        self.pointee_constant = pointee_constant;
        self
    }

    fn to_kernel_static_array_with_values(
        &self,
        values: crate::kernel::ArrayContents,
    ) -> crate::kernel::StaticArray {
        crate::kernel::StaticArray::new(
            self.source_name.clone(),
            self.kernel_name.clone(),
            self.element_type.to_kernel_type(),
            self.length,
            values,
        )
        .with_constant(self.is_constant())
    }
}

impl CStaticLocal {
    fn new(
        source_name: String,
        kernel_name: BindingName,
        interface_type: InterfaceType,
        initializer: CExpression,
    ) -> Self {
        Self {
            source_name,
            kernel_name,
            interface_type,
            initializer,
            volatile: false,
            pointee_volatile: false,
            constant: false,
            pointee_constant: false,
        }
    }

    pub fn name(&self) -> &str {
        &self.source_name
    }

    pub fn kernel_name(&self) -> &BindingName {
        &self.kernel_name
    }

    pub fn interface_type(&self) -> InterfaceType {
        self.interface_type
    }

    pub fn initializer(&self) -> &CExpression {
        &self.initializer
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

    fn with_volatile(mut self, volatile: bool) -> Self {
        self.volatile = volatile;
        self
    }

    fn with_pointee_volatile(mut self, pointee_volatile: bool) -> Self {
        self.pointee_volatile = pointee_volatile;
        self
    }

    fn with_constant(mut self, constant: bool) -> Self {
        self.constant = constant;
        self
    }

    fn with_pointee_constant(mut self, pointee_constant: bool) -> Self {
        self.pointee_constant = pointee_constant;
        self
    }

    pub(crate) fn to_kernel_static(&self) -> Option<crate::kernel::StaticLocal> {
        let value = match self.interface_type {
            InterfaceType::Float32 => match &self.initializer {
                CExpression::Float32Literal(bits) => {
                    crate::kernel::float32(crate::kernel::MachineTerm::constant(*bits))
                }
                _ => return None,
            },
            InterfaceType::Float64 => match &self.initializer {
                CExpression::Float64Literal(bits) => {
                    crate::kernel::float64(crate::kernel::MachineTerm::uint64_constant(*bits))
                }
                _ => return None,
            },
            InterfaceType::Bool => crate::kernel::ProgramValue::bool_constant(
                initializer_integer_bits(&self.initializer)? != 0,
            ),
            InterfaceType::Int8 => {
                crate::kernel::int8(initializer_integer_bits(&self.initializer)?)
            }
            InterfaceType::Int16 => {
                crate::kernel::int16(initializer_integer_bits(&self.initializer)?)
            }
            InterfaceType::Int32 => {
                crate::kernel::int32(initializer_integer_bits(&self.initializer)?)
            }
            InterfaceType::Char(PlainChar::Signed) => {
                crate::kernel::int8(initializer_integer_bits(&self.initializer)?)
            }
            InterfaceType::Char(PlainChar::Unsigned) => {
                crate::kernel::uint8(initializer_integer_bits(&self.initializer)?)
            }
            InterfaceType::UInt8 => {
                crate::kernel::uint8(initializer_integer_bits(&self.initializer)?)
            }
            InterfaceType::UInt16 => {
                crate::kernel::uint16(initializer_integer_bits(&self.initializer)?)
            }
            InterfaceType::UInt32 => {
                crate::kernel::uint32(initializer_integer_bits(&self.initializer)?)
            }
            _ => return None,
        };
        Some(self.to_kernel_static_with_value(value))
    }

    fn to_kernel_static_with_value(
        &self,
        value: crate::kernel::ProgramValue,
    ) -> crate::kernel::StaticLocal {
        crate::kernel::StaticLocal::new(
            self.source_name.clone(),
            self.kernel_name.clone(),
            self.interface_type.to_kernel_type(),
            value,
        )
        .with_volatile(self.is_volatile())
        .with_pointee_volatile(self.pointee_is_volatile())
        .with_constant(self.is_constant())
        .with_pointee_constant(self.pointee_is_constant())
    }
}

fn initializer_integer_bits(initializer: &CExpression) -> Option<u32> {
    match initializer {
        CExpression::Int32Literal(value) => Some(*value),
        CExpression::UInt8Literal(value) => Some(u32::from(*value)),
        CExpression::UInt32Literal(value) => Some(*value),
        _ => None,
    }
}

/// A static-storage scalar array's initializer as written: the elements it
/// names, by flattened index, ascending, over the element type's zero
/// initializer for every other of the array's `length` elements.
///
/// Held once and shared, so `int32 buf[1000000];` or `int32 t[1000] = {1};`
/// costs what its initializer wrote, not its declared length, however often
/// the declaration is copied, compared or lowered. An element whose written
/// value is exactly the zero initializer is not listed, so two initializers
/// are equal exactly when every element is spelled the same.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CArrayInitializer {
    length: u32,
    zero: CExpression,
    elements: std::sync::Arc<[(u32, CExpression)]>,
}

impl CArrayInitializer {
    /// `length` elements of `element_type`, each the zero initializer except
    /// the listed ones, whose indices are ascending, distinct and in bounds.
    fn new(
        length: u32,
        element_type: InterfaceType,
        elements: impl IntoIterator<Item = (u32, CExpression)>,
    ) -> Self {
        let zero = zero_initializer(element_type);
        let elements = elements
            .into_iter()
            .filter(|(_, value)| *value != zero)
            .collect::<std::sync::Arc<[_]>>();
        assert!(
            elements.windows(2).all(|pair| pair[0].0 < pair[1].0)
                && elements.last().is_none_or(|(index, _)| *index < length),
            "an array initializer lists distinct in-bounds elements in ascending order"
        );
        Self {
            length,
            zero,
            elements,
        }
    }

    /// Every element the zero initializer.
    fn zeroed(length: u32, element_type: InterfaceType) -> Self {
        Self::new(length, element_type, [])
    }

    pub fn length(&self) -> u32 {
        self.length
    }

    /// The listed elements, ascending by index.
    pub fn elements(&self) -> &[(u32, CExpression)] {
        &self.elements
    }

    /// Whether some element is the zero initializer.
    pub fn has_zero_elements(&self) -> bool {
        self.elements.len() < self.length as usize
    }

    /// Every distinct spelling of an element: the zero initializer when
    /// some element is it, then each listed value.
    pub fn values(&self) -> impl Iterator<Item = &CExpression> + '_ {
        self.has_zero_elements()
            .then_some(&self.zero)
            .into_iter()
            .chain(self.elements.iter().map(|(_, value)| value))
    }

    /// Every element in index order, one per element.
    #[cfg(test)]
    pub(crate) fn dense_values(&self) -> Vec<CExpression> {
        let mut values = vec![self.zero.clone(); self.length as usize];
        for (index, value) in self.elements.iter() {
            values[*index as usize] = value.clone();
        }
        values
    }

    /// The kernel's contents: each element lowered by `lower`, which is
    /// asked once for the zero initializer when some element is it and once
    /// per listed element, or `None` when one does not lower. When every
    /// element is listed, the first one's value stands as the default.
    fn to_kernel_contents(
        &self,
        mut lower: impl FnMut(&CExpression) -> Option<crate::kernel::ProgramValue>,
    ) -> Option<crate::kernel::ArrayContents> {
        let default = match (self.has_zero_elements(), self.elements.first()) {
            (false, Some((_, first))) => lower(first)?,
            _ => lower(&self.zero)?,
        };
        let elements = self
            .elements
            .iter()
            .map(|(index, value)| {
                crate::instrumentation::record_deterministic_work(1);
                Some((*index, lower(value)?))
            })
            .collect::<Option<Vec<_>>>()?;
        Some(crate::kernel::ArrayContents::new(
            self.length,
            default,
            elements,
        ))
    }
}

/// The zero stores an automatic array's initializer makes into every one of
/// its elements before the elements it writes: `count` elements `stride`
/// bytes apart, each receiving the typed stores `cells` spell for element 0,
/// as `(offset, value type, pointee qualification, zero initializer)`,
/// ascending by offset. The declaration carries this instead of one store
/// per element, so `int32 buf[1000000] = {0};` costs its element's cells.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CZeroFill {
    stride: u32,
    count: u32,
    cells: std::sync::Arc<[(u32, InterfaceType, bool, CExpression)]>,
    pub(crate) written_elements: std::sync::Arc<[(u32, CExpression)]>,
}

impl CZeroFill {
    /// The zero stores of element 0 of a `count`-element array, recovered
    /// from `stores`, which the caller spelled into the element at
    /// `CExpression::Variable(base)`. `None` unless every store is a typed
    /// store of a literal at a constant byte offset from that base, so the
    /// fill stands for exactly the stores the caller would otherwise emit.
    fn from_element_stores(
        base: impl Into<BindingName>,
        stride: u32,
        count: u32,
        stores: &[CStatement],
    ) -> Option<Self> {
        let base = base.into();
        let mut cells = stores
            .iter()
            .map(|store| {
                let (offset, value_type, pointee_constant, value) = typed_store_at(&base, store)?;
                (offset < stride
                    && matches!(
                        value.to_kernel_expression(),
                        crate::kernel::ProgramExpression::Value(_)
                    ))
                .then(|| (offset, value_type, pointee_constant, value.clone()))
            })
            .collect::<Option<Vec<_>>>()?;
        cells.sort_by_key(|(offset, ..)| *offset);
        Some(Self {
            stride,
            count,
            cells: cells.into(),
            written_elements: Default::default(),
        })
    }

    /// `stores` without each one this fill already makes: a typed store at
    /// a constant offset from `base` spelled exactly as the fill's zero store
    /// at that offset within its element, which would leave the cell the
    /// fill left. A store at an offset another of `stores` also writes is
    /// kept, so the order of the two is kept too.
    fn without_its_own_stores(
        &self,
        base: impl Into<BindingName>,
        stores: Vec<CStatement>,
    ) -> Vec<CStatement> {
        let base = base.into();
        let mut writes = BTreeMap::<u32, usize>::new();
        for store in &stores {
            if let Some((offset, ..)) = typed_store_at(&base, store) {
                *writes.entry(offset).or_default() += 1;
            }
        }
        stores
            .into_iter()
            .filter(|store| {
                let Some((offset, value_type, pointee_constant, value)) =
                    typed_store_at(&base, store)
                else {
                    return true;
                };
                let within = offset % self.stride;
                !(writes[&offset] == 1
                    && offset / self.stride < self.count
                    && self
                        .cells
                        .binary_search_by_key(&within, |(offset, ..)| *offset)
                        .is_ok_and(|position| {
                            let (_, cell_type, cell_constant, zero) = &self.cells[position];
                            *cell_type == value_type
                                && *cell_constant == pointee_constant
                                && zero == value
                        }))
            })
            .collect()
    }

    fn to_kernel(&self) -> crate::kernel::ZeroFill {
        crate::kernel::ZeroFill::new(
            self.stride,
            self.count,
            self.cells
                .iter()
                .map(|(offset, value_type, pointee_constant, zero)| {
                    let crate::kernel::ProgramExpression::Value(zero) = zero.to_kernel_expression()
                    else {
                        unreachable!("a zero fill holds only literal zero initializers")
                    };
                    crate::kernel::ZeroCell::new(
                        *offset,
                        value_type.to_kernel_type(),
                        *pointee_constant,
                        zero,
                    )
                })
                .collect(),
        )
        .with_written_elements(
            self.written_elements
                .iter()
                .map(|(index, value)| (*index, value.to_kernel_expression()))
                .collect(),
        )
    }
}

/// A typed store into the object named `base` at a constant byte offset
/// from it: the offset, the stored type, its pointee qualification and the
/// stored expression. `None` for any other statement.
fn typed_store_at(
    base: impl Into<BindingName>,
    store: &CStatement,
) -> Option<(u32, InterfaceType, bool, &CExpression)> {
    let base = base.into();
    let CStatement::Store {
        pointer,
        value,
        value_type: Some(value_type),
        pointee_constant,
        ..
    } = store
    else {
        return None;
    };
    let mut offset = 0u32;
    let mut pointer = pointer;
    loop {
        match pointer {
            CExpression::Variable(name) if name == &base => break,
            CExpression::PointerOffsetBytes {
                pointer: inner,
                bytes,
            } => {
                offset = offset.checked_add(*bytes)?;
                pointer = inner;
            }
            CExpression::Subobject { pointer: inner, .. } => pointer = inner,
            // Only the element store `base + index` of a scalar array, whose
            // index scales by the stored element type.
            CExpression::Add(inner, index) if matches!(inner.as_ref(), CExpression::Variable(name) if name == &base) =>
            {
                let CExpression::Int32Literal(index) = index.as_ref() else {
                    return None;
                };
                offset = offset.checked_add(index.checked_mul(value_type.abi_size_bytes())?)?;
                pointer = inner;
            }
            _ => return None,
        }
    }
    Some((offset, *value_type, *pointee_constant, value))
}

/// Whether no initializer expression in `stores` names the object `base`
/// being initialized, so none can observe whether an element it does not
/// write is zero yet. The declaration's zero fill then stands for the zero
/// stores whatever order they are made in.
fn stores_do_not_read_the_object(base: impl Into<BindingName>, stores: &[CStatement]) -> bool {
    let base = base.into();
    stores.iter().all(|store| {
        let CStatement::Store { value, .. } = store else {
            return false;
        };
        let mut names = BTreeSet::new();
        super::address_taken::mentioned_names(value, &mut names);
        !names.contains(&base)
    })
}

fn zero_initializer(interface_type: InterfaceType) -> CExpression {
    match interface_type {
        InterfaceType::Float32 => CExpression::Float32Literal(0),
        InterfaceType::Float64 => CExpression::Float64Literal(0),
        _ => CExpression::Int32Literal(0),
    }
}

/// A function-local aggregate with stable storage shared by every invocation
/// of its owning function.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CStaticAggregate {
    source_name: String,
    kernel_name: BindingName,
    struct_name: String,
    layout: RecordLayout,
    initializer: Vec<CAggregateInitializer>,
    constant: bool,
}

/// A fixed-size one-dimensional function-local static array of supported
/// struct aggregates. Its storage is qualified by the owning function and is
/// initialized once for the whole symbolic execution.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CStaticAggregateArray {
    source_name: String,
    kernel_name: BindingName,
    struct_name: String,
    layout: RecordLayout,
    length: u32,
    initializer: Vec<CAggregateInitializer>,
    constant: bool,
}

impl CStaticAggregateArray {
    fn new(
        source_name: String,
        kernel_name: BindingName,
        struct_name: String,
        layout: RecordLayout,
        length: u32,
        initializer: Vec<CAggregateInitializer>,
    ) -> Self {
        Self {
            source_name,
            kernel_name,
            struct_name,
            layout,
            length,
            initializer,
            constant: false,
        }
    }

    pub fn name(&self) -> &str {
        &self.source_name
    }

    pub fn kernel_name(&self) -> &BindingName {
        &self.kernel_name
    }

    pub fn struct_name(&self) -> &str {
        &self.struct_name
    }

    pub fn length(&self) -> u32 {
        self.length
    }

    pub fn interface_type(&self) -> InterfaceType {
        InterfaceType::UInt8Array(
            self.length
                .checked_mul(self.layout.size_bytes())
                .expect("validated static aggregate array size"),
        )
    }

    pub fn initializer(&self) -> &[CAggregateInitializer] {
        &self.initializer
    }

    pub fn is_constant(&self) -> bool {
        self.constant
    }

    fn with_constant(mut self, constant: bool) -> Self {
        self.constant = constant;
        self
    }

    pub(crate) fn to_kernel_static_aggregate_array(&self) -> crate::kernel::StaticAggregateArray {
        crate::kernel::StaticAggregateArray::new(
            self.source_name.clone(),
            self.kernel_name.clone(),
            self.layout.to_kernel_aggregate_layout(),
            self.length,
            self.initializer
                .iter()
                .map(CAggregateInitializer::to_kernel)
                .collect::<Option<Vec<_>>>()
                .expect("validated static aggregate array initializer"),
        )
        .with_constant(self.is_constant())
    }
}

impl CStaticAggregate {
    fn new(
        source_name: String,
        kernel_name: BindingName,
        struct_name: String,
        layout: RecordLayout,
        initializer: Vec<CAggregateInitializer>,
    ) -> Self {
        Self {
            source_name,
            kernel_name,
            struct_name,
            layout,
            initializer,
            constant: false,
        }
    }

    pub fn name(&self) -> &str {
        &self.source_name
    }

    pub fn kernel_name(&self) -> &BindingName {
        &self.kernel_name
    }

    pub fn struct_name(&self) -> &str {
        &self.struct_name
    }

    pub fn layout(&self) -> &RecordLayout {
        &self.layout
    }

    pub fn initializer(&self) -> &[CAggregateInitializer] {
        &self.initializer
    }

    pub fn is_constant(&self) -> bool {
        self.constant
    }

    fn with_constant(mut self, constant: bool) -> Self {
        self.constant = constant;
        self
    }

    pub(crate) fn to_kernel_static_aggregate(&self) -> crate::kernel::StaticAggregate {
        crate::kernel::StaticAggregate::new(
            self.source_name.clone(),
            self.kernel_name.clone(),
            self.layout.to_kernel_aggregate_layout(),
            self.initializer
                .iter()
                .map(CAggregateInitializer::to_kernel)
                .collect::<Option<Vec<_>>>()
                .expect("validated static aggregate initializer"),
        )
        .with_constant(self.is_constant())
    }
}

impl CallbackInterface {
    /// The function-pointer type of this signature.
    pub(crate) fn pointer_type(&self) -> InterfaceType {
        function_pointer_type(self)
    }
}

// The C type keeps integer rank (`long` and `long long` are distinct), but
// some typeof metadata is erased. Keep enough source identity for
// compile-time compatibility, or refuse the query.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum CompatibilityIdentity {
    Direct,
    TypeofStruct,
    Unavailable,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct ParsedType {
    compatibility_identity: CompatibilityIdentity,
    interface_type: InterfaceType,
    /// A distinct x86-64 extended-precision object. The current kernel
    /// transports its 16-byte storage as opaque bytes; it is never a binary64.
    long_double: bool,
    /// A GNU `aligned` typedef changes the alignment of values of this alias.
    /// Pointer uses are safe to import; value storage is refused until that
    /// alignment is represented in allocations and aggregate layouts.
    aligned_typedef: bool,
    /// Declaration-only compiler type. No layout, value or call ABI is granted.
    /// Kept only in typedef aliases and signatures of unusable prototypes.
    opaque_builtin: bool,
    /// Full callback ABI, including nominal pointee tags, retained by aliases.
    function_pointer_signature: Option<CallbackInterface>,
    struct_name: Option<String>,
    enum_name: Option<String>,
    union_name: Option<String>,
    is_volatile: bool,
    /// Volatile qualifiers indexed from the outermost object type. Bit 0 is
    /// the declared object, bit 1 its immediate pointee, and deeper bits are
    /// retained long enough to reject unsupported qualifier depth precisely.
    volatile_levels: u8,
    is_constant: bool,
    pointee_constant: bool,
    /// Pointer `*` tokens written in this type specifier itself, so a
    /// declaration list can tell `struct rb_node *parent, *tmp;` — where every
    /// declarator repeats the same depth — from a list that would give two
    /// declarators different types.
    pointer_depth: u8,
}

impl ParsedType {
    fn object_is_volatile(&self) -> bool {
        self.volatile_levels & 1 != 0
    }

    fn pointee_is_volatile(&self) -> bool {
        self.volatile_levels & 2 != 0
    }

    fn has_deeper_volatile(&self) -> bool {
        self.volatile_levels & !3 != 0
    }
}

/// One explicitly initialized scalar leaf in a static-storage aggregate.
/// Offsets are relative to the aggregate's base address; omitted leaves are
/// supplied by static zero initialization.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CAggregateInitializer {
    offset_bytes: u32,
    interface_type: InterfaceType,
    value: CExpression,
}

impl CAggregateInitializer {
    fn new(offset_bytes: u32, interface_type: InterfaceType, value: CExpression) -> Self {
        Self {
            offset_bytes,
            interface_type,
            value,
        }
    }

    pub fn offset_bytes(&self) -> u32 {
        self.offset_bytes
    }

    pub fn interface_type(&self) -> InterfaceType {
        self.interface_type
    }

    pub fn value(&self) -> &CExpression {
        &self.value
    }

    fn to_kernel(&self) -> Option<crate::kernel::AggregateInitializer> {
        Some(crate::kernel::AggregateInitializer::new(
            self.offset_bytes,
            kernel_aggregate_initializer_value(self.interface_type, &self.value)?,
        ))
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CEnumDefinition {
    values: BTreeMap<String, i64>,
    /// The integer type an object of the enumeration has: `uint32` when no
    /// value is negative, otherwise `int32`.
    compatible_type: InterfaceType,
}

/// The literal of enumeration constant `value` at `interface_type`, `int32` or
/// `uint32`, when the type holds it.
fn enum_constant_literal(value: i64, interface_type: InterfaceType) -> Option<CExpression> {
    match interface_type {
        InterfaceType::Int32 => i32::try_from(value)
            .ok()
            .map(|value| CExpression::Int32Literal(value as u32)),
        InterfaceType::UInt32 => u32::try_from(value).ok().map(CExpression::UInt32Literal),
        _ => None,
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CUnionLayout {
    fields: BTreeMap<String, CUnionField>,
    size_bytes: u32,
    alignment_bytes: u32,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CUnionField {
    interface_type: InterfaceType,
    long_double: bool,
    pointee_constant: bool,
    enum_name: Option<String>,
    struct_name: Option<String>,
    union_name: Option<String>,
    array_element_width: Option<u32>,
    array_shape: Option<Vec<u32>>,
    offset_bytes: u32,
    byte_width: u32,
}

/// The parser-owned identity of one source-level struct-field access.
///
/// This metadata is deliberately retained only on the C syntax tree.  The
/// kernel expression produced by [`CExpression::to_kernel_expression`] does
/// not include it in its semantic identity or certificate representation.
/// `occurrence` is allocated in source traversal order within one function;
/// the source position and field spelling make the identity useful to later
/// source-plan consumers without reconstructing a walk from kernel terms.
#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub struct CFieldSourceId {
    source_identity: Option<String>,
    function_name: String,
    occurrence: u32,
}

/// Source validation data attached to a parsed field access.  The identity is
/// separate so later execution events can carry only the canonical token and
/// validate the spelling/location against the selected source plan.
#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub struct CFieldSource {
    id: CFieldSourceId,
    position: SourcePosition,
    field_name: String,
}

impl CFieldSourceId {
    pub fn source_identity(&self) -> Option<&str> {
        self.source_identity.as_deref()
    }

    pub fn function_name(&self) -> &str {
        &self.function_name
    }

    pub fn occurrence(&self) -> u32 {
        self.occurrence
    }
}

impl CFieldSource {
    pub fn id(&self) -> &CFieldSourceId {
        &self.id
    }

    pub fn field_name(&self) -> &str {
        &self.field_name
    }
}

/// A translation unit's declarations of one kind, by name. Every parsed
/// function keeps the declarations visible at its definition; a persistent
/// map shares them, so that state is O(1) and a later declaration costs
/// O(log n), however declarations and definitions interleave.
pub type DeclarationMap<V> = imbl::OrdMap<String, V>;

/// Struct layouts by name, whichever map holds them.
pub trait StructLayouts {
    fn struct_layout(&self, name: &str) -> Option<&RecordLayout>;
}

impl StructLayouts for BTreeMap<String, RecordLayout> {
    fn struct_layout(&self, name: &str) -> Option<&RecordLayout> {
        self.get(name)
    }
}

impl StructLayouts for DeclarationMap<RecordLayout> {
    fn struct_layout(&self, name: &str) -> Option<&RecordLayout> {
        self.get(name)
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum CAbi {
    Lp64,
}

impl CAbi {
    pub const SUPPORTED: Self = super::target::CTarget::SUPPORTED.abi();

    pub(in crate::languages) fn size_and_alignment(
        self,
        interface_type: InterfaceType,
    ) -> (u32, u32) {
        match (self, interface_type) {
            (_, InterfaceType::Parameter(_)) => unreachable!("an abstract type has no layout"),
            (Self::Lp64, InterfaceType::ParameterPointer(_)) => (8, 8),
            (Self::Lp64, InterfaceType::Int128 | InterfaceType::UInt128) => (16, 16),
            (
                Self::Lp64,
                InterfaceType::Int128Array(length) | InterfaceType::UInt128Array(length),
            ) => (length.saturating_mul(16), 16),

            (Self::Lp64, InterfaceType::Void) => (0, 1),
            (Self::Lp64, InterfaceType::Bool) => (1, 1),
            (Self::Lp64, InterfaceType::VoidPointer | InterfaceType::VoidPointerPointer) => (8, 8),
            (Self::Lp64, InterfaceType::Int8) => (1, 1),
            (Self::Lp64, InterfaceType::Int16) => (2, 2),
            (Self::Lp64, InterfaceType::Int32) => (4, 4),
            (Self::Lp64, InterfaceType::Char(_) | InterfaceType::UInt8) => (1, 1),
            (Self::Lp64, InterfaceType::UInt16) => (2, 2),
            (Self::Lp64, InterfaceType::UInt32) => (4, 4),
            (Self::Lp64, InterfaceType::Int64(_) | InterfaceType::UInt64(_)) => (8, 8),
            (Self::Lp64, InterfaceType::Float32) => (4, 4),
            (Self::Lp64, InterfaceType::Float64) => (8, 8),
            (
                Self::Lp64,
                InterfaceType::Int32Pointer
                | InterfaceType::Int8Pointer
                | InterfaceType::Int16Pointer
                | InterfaceType::UInt16Pointer
                | InterfaceType::CharPointer(_)
                | InterfaceType::UInt8Pointer
                | InterfaceType::UInt32Pointer
                | InterfaceType::Int128Pointer
                | InterfaceType::Int64Pointer(_)
                | InterfaceType::UInt128Pointer
                | InterfaceType::UInt64Pointer(_)
                | InterfaceType::Float32Pointer
                | InterfaceType::Float64Pointer
                | InterfaceType::Int8PointerPointer
                | InterfaceType::Int16PointerPointer
                | InterfaceType::UInt16PointerPointer
                | InterfaceType::Int32PointerPointer
                | InterfaceType::CharPointerPointer(_)
                | InterfaceType::UInt8PointerPointer
                | InterfaceType::UInt32PointerPointer
                | InterfaceType::Int128PointerPointer
                | InterfaceType::Int64PointerPointer(_)
                | InterfaceType::UInt128PointerPointer
                | InterfaceType::UInt64PointerPointer(_)
                | InterfaceType::Float32PointerPointer
                | InterfaceType::Float64PointerPointer,
            ) => (8, 8),
            (Self::Lp64, InterfaceType::FunctionPointer(_)) => (8, 8),
            (Self::Lp64, InterfaceType::Int32Array(length)) => (length.saturating_mul(4), 4),
            (
                Self::Lp64,
                InterfaceType::Int8Array(length)
                | InterfaceType::CharArray(_, length)
                | InterfaceType::UInt8Array(length),
            ) => (length, 1),
            (
                Self::Lp64,
                InterfaceType::Int16Array(length) | InterfaceType::UInt16Array(length),
            ) => (length.saturating_mul(2), 2),
            (Self::Lp64, InterfaceType::UInt32Array(length)) => (length.saturating_mul(4), 4),
            (
                Self::Lp64,
                InterfaceType::Int64Array(_, length) | InterfaceType::UInt64Array(_, length),
            ) => (length.saturating_mul(8), 8),
            (Self::Lp64, InterfaceType::Float32Array(length)) => (length.saturating_mul(4), 4),
            (Self::Lp64, InterfaceType::Float64Array(length)) => (length.saturating_mul(8), 8),
            (Self::Lp64, InterfaceType::PointerArray(_, _, length)) => {
                (length.saturating_mul(8), 8)
            }
        }
    }
}

pub(crate) fn is_integer_type(interface_type: InterfaceType) -> bool {
    matches!(
        interface_type,
        InterfaceType::Bool
            | InterfaceType::Int8
            | InterfaceType::Int16
            | InterfaceType::Int32
            | InterfaceType::UInt8
            | InterfaceType::UInt16
            | InterfaceType::UInt32
            | InterfaceType::Int64(_)
            | InterfaceType::UInt64(_)
            | InterfaceType::Char(_)
    )
}

fn is_arithmetic_type(interface_type: InterfaceType) -> bool {
    is_integer_type(interface_type)
        || matches!(
            interface_type,
            InterfaceType::Float32 | InterfaceType::Float64
        )
}

fn is_unsupported_concurrency_builtin(name: &str) -> bool {
    name.starts_with("__atomic_")
        || name.starts_with("__sync_")
        || name == "smp_load_acquire"
        || name == "smp_store_release"
        || name == "smp_mb"
        || name == "smp_rmb"
        || name == "smp_wmb"
}

fn integer_promotion_type(interface_type: InterfaceType) -> Option<InterfaceType> {
    match interface_type {
        InterfaceType::Int8 => Some(InterfaceType::Int32),
        InterfaceType::Bool
        | InterfaceType::Int16
        | InterfaceType::Char(_)
        | InterfaceType::UInt8
        | InterfaceType::UInt16 => Some(InterfaceType::Int32),
        InterfaceType::Int32
        | InterfaceType::UInt32
        | InterfaceType::Int64(_)
        | InterfaceType::UInt64(_) => Some(interface_type),
        _ => None,
    }
}

/// Returns the type selected by C11's usual arithmetic conversions for the
/// modeled LP64 scalar types. Integer promotions happen before rank and
/// signedness are compared, so all of the small integer types become int32.
fn usual_arithmetic_conversion_type(
    left: InterfaceType,
    right: InterfaceType,
) -> Option<InterfaceType> {
    if !is_arithmetic_type(left) || !is_arithmetic_type(right) {
        return None;
    }
    if left == InterfaceType::Float64 || right == InterfaceType::Float64 {
        return Some(InterfaceType::Float64);
    }
    if left == InterfaceType::Float32 || right == InterfaceType::Float32 {
        return Some(InterfaceType::Float32);
    }

    let left = integer_promotion_type(left)?;
    let right = integer_promotion_type(right)?;
    // `long` and `long long` share a representation; the common type of a
    // 64-bit pair has the greater rank (C11 6.3.1.8).
    let rank = match (left.long_rank(), right.long_rank()) {
        (Some(left), Some(right)) => left.max(right),
        (Some(rank), None) | (None, Some(rank)) => rank,
        (None, None) => LongRank::Long,
    };
    let with_rank = |interface_type: InterfaceType| match interface_type {
        InterfaceType::Int64(_) => InterfaceType::Int64(rank),
        InterfaceType::UInt64(_) => InterfaceType::UInt64(rank),
        other => other,
    };
    let left_unsigned = matches!(left, InterfaceType::UInt32 | InterfaceType::UInt64(_));
    let right_unsigned = matches!(right, InterfaceType::UInt32 | InterfaceType::UInt64(_));
    if left_unsigned == right_unsigned {
        return Some(match (left, right) {
            (InterfaceType::Int64(_), _) | (_, InterfaceType::Int64(_)) if !left_unsigned => {
                InterfaceType::Int64(rank)
            }
            (InterfaceType::UInt64(_), _) | (_, InterfaceType::UInt64(_)) => {
                InterfaceType::UInt64(rank)
            }
            (InterfaceType::UInt32, _) | (_, InterfaceType::UInt32) => InterfaceType::UInt32,
            _ => InterfaceType::Int32,
        });
    }

    let (signed, unsigned) = if left_unsigned {
        (right, left)
    } else {
        (left, right)
    };
    let signed_bits = integer_type_bits(signed)?;
    let unsigned_bits = integer_type_bits(unsigned)?;
    if signed_bits > unsigned_bits {
        Some(with_rank(signed))
    } else {
        Some(with_rank(unsigned))
    }
}

fn integer_type_bits(interface_type: InterfaceType) -> Option<u32> {
    match interface_type {
        InterfaceType::Int32 | InterfaceType::UInt32 => Some(32),
        InterfaceType::Int64(_) | InterfaceType::UInt64(_) => Some(64),
        _ => None,
    }
}

/// The standard-library function a `__builtin_constant_p` call lowers to.
/// Its contract leaves the result an unknown 0 or 1.
pub(crate) const CONSTANT_P_UNKNOWN: &str = "__click_constant_p_unknown";

/// C's null pointer constant: the integer constant `0`, or that constant
/// cast to `void *`.
fn is_null_pointer_constant(expression: &CExpression) -> bool {
    match expression {
        CExpression::Int32Literal(0) => true,
        CExpression::Cast {
            expression,
            interface_type: InterfaceType::VoidPointer,
            pointee_constant: false,
            pointee_volatile: false,
            ..
        } => matches!(**expression, CExpression::Int32Literal(0)),
        _ => false,
    }
}

fn ternary_expression_type(
    then_type: Option<InterfaceType>,
    else_type: Option<InterfaceType>,
    then_branch: &CExpression,
    else_branch: &CExpression,
) -> Option<InterfaceType> {
    let (Some(then_type), Some(else_type)) = (then_type, else_type) else {
        return None;
    };
    // An array operand, such as a string literal, is converted to a pointer
    // to its first element (C11 6.3.2.1p3), so `c ? "" : " "` has type
    // `char *` although its operands are `char[1]` and `char[2]`.
    let (then_type, else_type) = (decay_to_pointer(then_type), decay_to_pointer(else_type));
    usual_arithmetic_conversion_type(then_type, else_type).or_else(|| {
        if then_type == else_type
            || (then_type.is_object_pointer() && is_null_pointer_constant(else_branch))
        {
            Some(then_type)
        } else if else_type.is_object_pointer() && is_null_pointer_constant(then_branch) {
            Some(else_type)
        } else {
            None
        }
    })
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CSwitchCase {
    value: Option<u32>,
    body: Box<CStatement>,
}

impl CSwitchCase {
    pub fn value(&self) -> Option<u32> {
        self.value
    }

    pub fn body(&self) -> &CStatement {
        &self.body
    }
}

/// Where a source statement was written, for diagnostics only.
///
/// A site never takes part in what a statement means. Every site compares
/// equal to every other, so the same C parsed at another line, in another
/// file, or with its statements written differently yields equal C trees,
/// and nothing that compares, interns, or caches statements can depend on a
/// site. Lowering to kernel statements drops it: the source execution layout
/// keeps each statement's site in a side table keyed by its statement index,
/// which a refusal reads to name the line it refused.
#[derive(Clone, Default)]
pub struct CSite(Option<std::sync::Arc<CStatementSite>>);

/// The first source line of a statement and its position.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CStatementSite {
    position: SourcePosition,
    text: Box<str>,
    /// Where this statement sits among the statements as written: its index
    /// among the block items of the function body, then among its parent
    /// statement's children, and so on. Proof paths such as
    /// `statement(2).statement(0)` resolve through it. Statements a
    /// statement's lowering moved ahead of it carry the same path.
    source_path: Option<std::sync::Arc<[u32]>>,
    source_bindings: Option<std::sync::Arc<CSourceBindings>>,
}

/// Persistent lexical declaration index captured at a C loop head.
pub(crate) type CSourceBindings = imbl::OrdMap<String, (usize, BindingName)>;

/// The longest statement excerpt a site keeps, in characters.
const SITE_TEXT_LIMIT: usize = 100;

impl CSite {
    pub const NONE: Self = Self(None);

    pub fn get(&self) -> Option<&std::sync::Arc<CStatementSite>> {
        self.0.as_ref()
    }

    pub fn is_none(&self) -> bool {
        self.0.is_none()
    }

    /// This site, recording that its statement is the one at `path`.
    fn with_source_path(self, path: Option<std::sync::Arc<[u32]>>) -> Self {
        match (self.0, path) {
            (Some(site), Some(path)) => Self(Some(std::sync::Arc::new(CStatementSite {
                position: site.position.clone(),
                text: site.text.clone(),
                source_path: Some(path),
                source_bindings: site.source_bindings.clone(),
            }))),
            (site, _) => Self(site),
        }
    }
}

impl PartialEq for CSite {
    fn eq(&self, _: &Self) -> bool {
        true
    }
}

impl Eq for CSite {}

impl std::fmt::Debug for CSite {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // Debug output of a statement must not change with its line either.
        formatter.write_str("CSite")
    }
}

impl CStatementSite {
    pub(crate) fn source_bindings(&self) -> Option<&CSourceBindings> {
        self.source_bindings.as_deref()
    }

    /// The statement's place among the statements as written; see the field.
    pub fn source_path(&self) -> Option<&[u32]> {
        self.source_path.as_deref()
    }

    /// The statement as written, from its first token to its end on its
    /// first line, with `…` marking a statement that continues past it.
    pub fn text(&self) -> &str {
        &self.text
    }

    /// `file:line:column`, or `line L, column C` for a source with no file.
    pub fn location(&self) -> String {
        match &self.position.origin {
            Some(origin) => format!(
                "{}:{}:{}",
                origin.filename, origin.line, self.position.column
            ),
            None => self.position.to_string(),
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum CStatement {
    FillArrayTail {
        name: BindingName,
        element_type: InterfaceType,
        start: u32,
        count: u32,
    },
    EndAggregateLifetimes {
        names: Vec<BindingName>,
        steps: Vec<u32>,
        site: CSite,
    },
    Skip,
    Break,
    Continue,
    Goto {
        target: String,
        position: Option<SourcePosition>,
        direct_function_body: bool,
    },
    Label {
        name: String,
        statement: Box<CStatement>,
        position: Option<SourcePosition>,
        direct_function_body: bool,
    },
    Declare {
        initializer: Option<CExpression>,
        interface_type: InterfaceType,
        name: BindingDeclaration,
        volatile: bool,
        pointee_volatile: bool,
        constant: bool,
        pointee_constant: bool,
        /// The zero stores an initializer makes into every element of an
        /// automatic array before the elements it writes; absent for an
        /// object declared without one, which stays uninitialized.
        zero_fill: Option<CZeroFill>,
        /// The object's strict-aliasing class when the parser knows more
        /// than `interface_type` says: an `int *` versus a struct pointer, or a byte
        /// array versus an array of structs (`design/effective-types.md`).
        declared_class: Option<crate::kernel::effective_type::CAccessClass>,
        /// Where the source statement was written; see [`CSite`].
        site: CSite,
    },
    DeclareStructValue {
        name: BindingDeclaration,
        layout: RecordLayout,
        /// Where the source statement was written; see [`CSite`].
        site: CSite,
    },
    Assign {
        name: BindingName,
        expression: CExpression,
        /// Leaves the target's value from before this assignment as the
        /// result of step N: the value of a postfix `p++`.
        prior_result: Option<u32>,
        /// Where the source statement was written; see [`CSite`].
        site: CSite,
    },
    /// A call inside an expression of the statement that follows it. Its
    /// result is that statement's `CExpression::StepResult { step, .. }`,
    /// never a variable.
    CallResult {
        aggregate_layout: Option<RecordLayout>,
        call: u32,
        function_name: String,
        arguments: Vec<CExpression>,
        /// The callee's declared result type, when it is declared here.
        result_type: Option<InterfaceType>,
        result_aggregate_layout: Option<RecordLayout>,
        result_pointee_constant: bool,
        /// The function pointer the call goes through, when it is not a call
        /// of a named function; `function_name` then describes it as written.
        callee: Option<CCallee>,
        /// Where the source statement was written; see [`CSite`].
        site: CSite,
    },
    Call {
        function_name: String,
        arguments: Vec<CExpression>,
        /// The function pointer the call goes through, when it is not a call
        /// of a named function; `function_name` then describes it as written.
        callee: Option<CCallee>,
        /// Where the source statement was written; see [`CSite`].
        site: CSite,
    },
    /// A statement-form call through a modeled function-pointer expression.
    /// Parsing expands this to a typed callback local before kernel lowering.
    IndirectCall {
        function: CExpression,
        signature: CallbackInterface,
        arguments: Vec<CExpression>,
        position: Option<SourcePosition>,
        /// Where the source statement was written; see [`CSite`].
        site: CSite,
    },
    HeapAllocate {
        target: BindingName,
        bytes: CExpression,
        zeroed: bool,
        object_type: Option<(crate::kernel::effective_type::CAccessClass, u32, u32)>,
        /// Where the source statement was written; see [`CSite`].
        site: CSite,
    },
    HeapFree {
        pointer: CExpression,
        /// Where the source statement was written; see [`CSite`].
        site: CSite,
    },
    /// A generated proof check for an index into a declared array dimension.
    /// This is not source-level `assert`; it is inserted while flattening
    /// multidimensional and inline array accesses so C's subobject bounds are
    /// checked before the enclosing allocation is accessed.
    Assert {
        condition: CExpression,
        label: String,
        /// Where the source statement was written; see [`CSite`].
        site: CSite,
    },
    Seq(Box<CStatement>, Box<CStatement>),
    /// The returned expression and where the `return` was written.
    Return(CExpression, CSite),
    Store {
        pointer: CExpression,
        value: CExpression,
        value_type: Option<InterfaceType>,
        /// The access class of the stored lvalue when `value_type` does not
        /// give it: a member store names its struct, and an `int *` store
        /// is told from a struct pointer's.
        lvalue_class: Option<crate::kernel::effective_type::CAccessClass>,
        pointee_constant: bool,
        /// Where the source statement was written; see [`CSite`].
        site: CSite,
    },
    /// A checked sequential access primitive imported from the Linux-style
    /// READ_ONCE/WRITE_ONCE/RCU macro family. The kernel records the access as
    /// observable and ordered, but this node does not assert atomicity,
    /// inter-thread visibility, release/acquire ordering, or grace periods.
    SequentialStore {
        target: CExpression,
        value: CExpression,
        value_type: InterfaceType,
        pointee_constant: bool,
        /// Where the source statement was written; see [`CSite`].
        site: CSite,
    },
    /// Copy an address-backed aggregate whose layout includes overlapping
    /// union storage. Ordinary scalar stores cannot represent this copy
    /// without losing the member views, so the kernel receives the complete
    /// aggregate metadata.
    AggregateCopy {
        target: CExpression,
        source: CExpression,
        layout: RecordLayout,
        /// Where the source statement was written; see [`CSite`].
        site: CSite,
    },
    Update {
        target: CExpression,
        operator: CUpdateOperator,
        operand: CExpression,
        /// Where the source statement was written; see [`CSite`].
        site: CSite,
    },
    /// A loop's own test inside its pass, after the calls its condition
    /// makes: true continues, false leaves the loop. It is a position of the
    /// loop as written (`loop(i).test`), not a statement of the source.
    LoopTest {
        aggregate_steps: Vec<u32>,
        condition: CExpression,
        /// The loop's site: the test is the loop's own region.
        site: CSite,
    },
    If {
        condition: CExpression,
        then_branch: Box<CStatement>,
        else_branch: Box<CStatement>,
        /// The operator inside an expression this `if` decides, when it is
        /// one (`&&`, `||` or the ternary operator), rather than an `if` of
        /// the source.
        operator: Option<COperator>,
        /// Where the source statement was written; see [`CSite`].
        site: CSite,
    },
    /// A value the rest of its statement reads, the result of each of
    /// `steps` (one per reader); see `ProgramStatement::StepValue`. With no
    /// steps the value is evaluated and discarded.
    StepValue {
        aggregate_layout: Option<RecordLayout>,
        steps: Vec<u32>,
        expression: CExpression,
        interface_type: Option<InterfaceType>,
        pointee_constant: bool,
        /// Where the source statement was written; see [`CSite`].
        site: CSite,
    },
    While {
        test: Option<Box<CStatement>>,
        condition: CExpression,
        body: Box<CStatement>,
        /// Where the source statement was written; see [`CSite`].
        site: CSite,
    },
    DoWhile {
        test: Option<Box<CStatement>>,
        condition: CExpression,
        body: Box<CStatement>,
        /// Where the source statement was written; see [`CSite`].
        site: CSite,
    },
    For {
        test: Option<Box<CStatement>>,
        initializer: Box<CStatement>,
        condition: CExpression,
        step: Box<CStatement>,
        body: Box<CStatement>,
        /// Where the source statement was written; see [`CSite`].
        site: CSite,
    },
    Switch {
        expression: CExpression,
        cases: Vec<CSwitchCase>,
        /// Where the source statement was written; see [`CSite`].
        site: CSite,
    },
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum CUpdateOperator {
    Add,
    Subtract,
    Multiply,
    Divide,
    Remainder,
    ShiftLeft,
    ShiftRight,
    BitwiseAnd,
    BitwiseOr,
    BitwiseXor,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
pub enum CFloatClassification {
    Finite,
    Infinite,
    Zero,
    Subnormal,
    Nan,
}

/// Scale an index for pointer arithmetic in a type wide enough for a C int
/// index and a stride that can span the modeled storage extent.
fn widened_stride(index: CExpression, width: u32) -> CExpression {
    CExpression::Multiply(
        Box::new(CExpression::Cast {
            expression: Box::new(index),
            interface_type: InterfaceType::Int64(LongRank::Long),
            struct_name: None,
            pointee_volatile: false,
            pointee_constant: false,
            explicit_qualification: false,
        }),
        Box::new(CExpression::Int64Literal(i64::from(width))),
    )
}

/// A loaded type with the access class its kernel type cannot give
/// (`design/effective-types.md`).
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CClassedType {
    pub interface_type: InterfaceType,
    pub class: crate::kernel::effective_type::CAccessClass,
}

/// The function pointer a call goes through, and its signature.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CCallee {
    pub pointer: CExpression,
    pub signature: CallbackInterface,
}

impl CCallee {
    fn to_kernel(&self) -> crate::kernel::Callee {
        crate::kernel::Callee {
            pointer: self.pointer.to_kernel_expression(),
            pointer_type: function_pointer_type(&self.signature).to_kernel_type(),
        }
    }
}

/// A function pointer expression as the source writes it, which names a call
/// through it: `fp`, `s->cb`, `s.cb` or `*fp`.
fn callee_source_text(expression: &CExpression) -> String {
    match expression {
        CExpression::Variable(name) => name.source_name().to_owned(),
        CExpression::Field {
            pointer,
            source: Some(source),
            ..
        } => {
            // Member lowering narrows the field after adding its offset;
            // neither belongs in the field's spelling.
            let mut base = pointer.as_ref();
            while let CExpression::Subobject { pointer, .. } = base {
                base = pointer;
            }
            if let CExpression::PointerOffsetBytes { pointer, .. } = base {
                base = pointer;
            }
            match base {
                CExpression::AddressOf(object) => {
                    format!("{}.{}", callee_source_text(object), source.field_name())
                }
                pointer => format!("{}->{}", callee_source_text(pointer), source.field_name()),
            }
        }
        CExpression::Load(pointer, _) => format!("*{}", callee_source_text(pointer)),
        _ => "the function pointer".to_string(),
    }
}

/// The operator an operator `if` decides, and the step whose result is the
/// operator's value.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct COperator {
    pub kind: crate::kernel::OperatorKind,
    pub step: u32,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum CExpression {
    StringLiteral(std::sync::Arc<CStringLiteral>),
    Void,
    Variable(BindingName),
    /// The result of a step this expression's statement made: the term a
    /// call step (`CStatement::CallResult`) returned, or the value an
    /// assignment step with `prior_result` replaced, with its C type.
    StepResult {
        step: u32,
        origin: crate::kernel::StepOrigin,
        /// The result's C type; `None` for a call whose callee is declared
        /// only later in the translation unit, or not at all.
        interface_type: Option<InterfaceType>,
        pointee_constant: bool,
        struct_name: Option<String>,
    },
    /// A C function call that is still embedded in an expression. The
    /// parser lowers it to a call step before the AST reaches the kernel,
    /// so the kernel executes calls only as checked statement transitions.
    /// The position identifies the source call site for diagnostics emitted
    /// while performing that lowering.
    Call {
        function_name: String,
        arguments: Vec<CExpression>,
        position: Option<SourcePosition>,
    },
    /// A call through a modeled function-pointer expression. The parser keeps
    /// the expression until lowering can materialize it in a typed callback
    /// local, then reuses the kernel's existing indirect-call statement path.
    IndirectCall {
        function: Box<CExpression>,
        signature: CallbackInterface,
        arguments: Vec<CExpression>,
        position: Option<SourcePosition>,
    },
    /// A simple scalar assignment before expression lowering materializes
    /// its converted result and write as ordinary checked statements. C
    /// deliberately keeps the lvalue boundary narrow: only a named scalar
    /// object is accepted here, not memory lvalues or update operators.
    Assignment {
        name: BindingName,
        value: Box<CExpression>,
        interface_type: InterfaceType,
        struct_name: Option<String>,
        pointee_constant: bool,
        position: Option<SourcePosition>,
    },
    /// A named scalar's pre/post increment or decrement. Lowering reads it
    /// once, preserves the expression value, and emits an ordinary checked
    /// typed assignment before the enclosing expression proceeds.
    ScalarUpdate {
        name: BindingName,
        increment: bool,
        prefix: bool,
        interface_type: InterfaceType,
        struct_name: Option<String>,
        pointee_constant: bool,
        position: Option<SourcePosition>,
    },
    FunctionAddress(String),
    Cast {
        expression: Box<CExpression>,
        interface_type: InterfaceType,
        /// The struct tag of a pointer cast target, so field access through
        /// the cast result resolves the same layout as a declared pointer.
        struct_name: Option<String>,
        /// Volatility of the pointer-valued cell reached by this pointer.
        /// This is the qualifier in `T * volatile *`, not volatility of the
        /// storage designated by `T *`.
        pointee_volatile: bool,
        /// Const qualification of the storage reached by this pointer. A
        /// qualified destination adds a read-only view without changing
        /// pointer identity.
        pointee_constant: bool,
        /// A cast written in the source: its result has exactly the
        /// destination's pointee qualification, so it may drop `const`. A
        /// cast inserted by the parser keeps the source view instead.
        explicit_qualification: bool,
    },
    Ternary {
        condition: Box<CExpression>,
        then_branch: Box<CExpression>,
        else_branch: Box<CExpression>,
    },
    /// A sequenced body and value before lowering to ordinary C statements.
    /// GNU statement expressions yield a scalar after their inner block;
    /// compound literals initialize an aggregate place in the enclosing block.
    /// Keeping the body attached preserves conditional evaluation and effects.
    StatementExpression {
        /// True for the place produced by a block-scope compound literal.
        aggregate_lvalue: bool,
        /// Effects of a literal initializer, retained for enclosing C order checks.
        initializer_call: Option<SourcePosition>,
        initializer_assignment: Option<SourcePosition>,
        /// Objects owned by a GNU expression's inner block, retired after its value.
        scope_lifetimes: Vec<BindingName>,
        body: Box<CStatement>,
        value: Box<CExpression>,
        interface_type: InterfaceType,
        struct_name: Option<String>,
        function_pointer_signature: Option<CallbackInterface>,
        pointee_constant: bool,
    },
    FloatNegate(Box<CExpression>),
    FloatClassification {
        expression: Box<CExpression>,
        classification: CFloatClassification,
    },
    AddressOf(Box<CExpression>),
    PointerOffsetBytes {
        pointer: Box<CExpression>,
        bytes: u32,
    },
    Int32Literal(u32),
    UInt8Literal(u8),
    UInt32Literal(u32),
    Int64Literal(i64),
    UInt64Literal(u64),
    /// The IEEE-754 binary32 representation used by the typed float model.
    Float32Literal(u32),
    /// The IEEE-754 binary64 representation used by the typed double model.
    Float64Literal(u64),
    SizeOfStruct {
        name: String,
        bytes: u32,
    },
    SizeOfUnion {
        name: String,
        bytes: u32,
    },
    SizeOfType {
        interface_type: InterfaceType,
        struct_name: Option<String>,
        bytes: u32,
    },
    LessThan(Box<CExpression>, Box<CExpression>),
    LessEqual(Box<CExpression>, Box<CExpression>),
    GreaterThan(Box<CExpression>, Box<CExpression>),
    GreaterEqual(Box<CExpression>, Box<CExpression>),
    Equal(Box<CExpression>, Box<CExpression>),
    NotEqual(Box<CExpression>, Box<CExpression>),
    Not(Box<CExpression>),
    And(Box<CExpression>, Box<CExpression>),
    Or(Box<CExpression>, Box<CExpression>),
    Add(Box<CExpression>, Box<CExpression>),
    Subtract(Box<CExpression>, Box<CExpression>),
    Multiply(Box<CExpression>, Box<CExpression>),
    Divide(Box<CExpression>, Box<CExpression>),
    Remainder(Box<CExpression>, Box<CExpression>),
    ShiftLeft(Box<CExpression>, Box<CExpression>),
    ShiftRight(Box<CExpression>, Box<CExpression>),
    BitwiseAnd(Box<CExpression>, Box<CExpression>),
    BitwiseOr(Box<CExpression>, Box<CExpression>),
    BitwiseXor(Box<CExpression>, Box<CExpression>),
    BitwiseNot(Box<CExpression>),
    /// `*pointer`, with the lvalue's type when the kernel type of the loaded
    /// value cannot give its access class (`design/effective-types.md`).
    Load(Box<CExpression>, Option<CClassedType>),
    /// One observable sequential read of the source lvalue. `struct_name`
    /// carries nominal pointer provenance through the lowering boundary.
    SequentialRead {
        pointee_constant: bool,
        target: Box<CExpression>,
        interface_type: InterfaceType,
        struct_name: Option<String>,
    },
    /// Expression form of a sequential write. Lowering materializes its
    /// result after the ordered store so the target and value are evaluated
    /// once, as required by the checked primitive contract.
    SequentialWrite {
        target: Box<CExpression>,
        value: Box<CExpression>,
        interface_type: InterfaceType,
        struct_name: Option<String>,
    },
    /// Address of an embedded struct field. Aggregate objects have no
    /// runtime `ProgramValue`; this node carries the aggregate place through nested
    /// member selection until a scalar field is selected.
    AggregateAddress {
        pointer: Box<CExpression>,
        struct_name: String,
    },
    /// A struct member's address narrowed to the member's `width` bytes
    /// (`design/pointer-subobject-bounds.md`); lowers to the kernel's
    /// `ProgramExpression::Subobject`.
    Subobject {
        pointer: Box<CExpression>,
        width: u32,
    },
    Field {
        pointer: Box<CExpression>,
        field_type: InterfaceType,
        pointee_constant: bool,
        field_struct_name: Option<String>,
        function_pointer_signature: Option<CallbackInterface>,
        array_shape: Option<Vec<u32>>,
        /// Source origin minted by the C parser.  This is absent on
        /// parser-synthesized field loads used by aggregate copies.
        source: Option<CFieldSource>,
        /// The member access through the containing struct, for the
        /// strict-aliasing check (`design/effective-types.md`).
        access_class: Option<crate::kernel::effective_type::CAccessClass>,
    },
    UnionField {
        pointer: Box<CExpression>,
        field_type: InterfaceType,
        union_name: String,
        pointee_constant: bool,
    },
    /// Address of an embedded union. Union members overlap at offset zero and
    /// are selected as typed scalar loads; the union itself has no runtime
    /// aggregate value.
    UnionAddress {
        pointer: Box<CExpression>,
        union_name: String,
    },
    /// `base[index]`, with the element type when the kernel type of the
    /// loaded value cannot give its access class (`design/effective-types.md`).
    Index(Box<CExpression>, Box<CExpression>, Option<CClassedType>),
    /// An array index whose declared subobject bound must be established
    /// before the enclosing flattened offset is used.
    CheckedArrayIndex {
        index: Box<CExpression>,
        length: u32,
    },
}

/// Matches every binary operator [`CExpression`]: arithmetic, bitwise, comparison and logical,
/// binding the operands to `$left` and `$right`.
macro_rules! binary_c_operation {
    ($left:pat, $right:pat) => {
        $crate::languages::c::syntax::CExpression::Add($left, $right)
            | $crate::languages::c::syntax::CExpression::Subtract($left, $right)
            | $crate::languages::c::syntax::CExpression::Multiply($left, $right)
            | $crate::languages::c::syntax::CExpression::Divide($left, $right)
            | $crate::languages::c::syntax::CExpression::Remainder($left, $right)
            | $crate::languages::c::syntax::CExpression::BitwiseAnd($left, $right)
            | $crate::languages::c::syntax::CExpression::BitwiseOr($left, $right)
            | $crate::languages::c::syntax::CExpression::BitwiseXor($left, $right)
            | $crate::languages::c::syntax::CExpression::ShiftLeft($left, $right)
            | $crate::languages::c::syntax::CExpression::ShiftRight($left, $right)
            | $crate::languages::c::syntax::CExpression::Equal($left, $right)
            | $crate::languages::c::syntax::CExpression::NotEqual($left, $right)
            | $crate::languages::c::syntax::CExpression::LessThan($left, $right)
            | $crate::languages::c::syntax::CExpression::LessEqual($left, $right)
            | $crate::languages::c::syntax::CExpression::GreaterThan($left, $right)
            | $crate::languages::c::syntax::CExpression::GreaterEqual($left, $right)
            | $crate::languages::c::syntax::CExpression::And($left, $right)
            | $crate::languages::c::syntax::CExpression::Or($left, $right)
    };
}
pub(crate) use binary_c_operation;

/// Matches every two-operand [`CExpression`]: the binary operators and indexing, binding the
/// operands to `$left` and `$right`.
macro_rules! binary_c_expression {
    ($left:pat, $right:pat) => {
        $crate::languages::c::syntax::binary_c_operation!($left, $right)
            | $crate::languages::c::syntax::CExpression::Index($left, $right, _)
    };
}
pub(crate) use binary_c_expression;

/// Matches every [`CExpression`] comparison, binding the operands to `$left` and `$right`.
macro_rules! c_comparison {
    ($left:pat, $right:pat) => {
        $crate::languages::c::syntax::CExpression::Equal($left, $right)
            | $crate::languages::c::syntax::CExpression::NotEqual($left, $right)
            | $crate::languages::c::syntax::CExpression::LessThan($left, $right)
            | $crate::languages::c::syntax::CExpression::LessEqual($left, $right)
            | $crate::languages::c::syntax::CExpression::GreaterThan($left, $right)
            | $crate::languages::c::syntax::CExpression::GreaterEqual($left, $right)
    };
}
pub(crate) use c_comparison;

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CSyntaxError {
    limit_exceeded: bool,
    message: String,
    position: Option<SourcePosition>,
}

impl ImportedFunction {
    pub fn static_locals(&self) -> &BTreeMap<BindingName, CStaticLocal> {
        &self.static_locals
    }

    pub fn static_arrays(&self) -> &BTreeMap<BindingName, CStaticArray> {
        &self.static_arrays
    }

    pub fn static_aggregates(&self) -> &BTreeMap<BindingName, CStaticAggregate> {
        &self.static_aggregates
    }

    pub fn static_aggregate_arrays(&self) -> &BTreeMap<BindingName, CStaticAggregateArray> {
        &self.static_aggregate_arrays
    }

    fn static_object_address(&self, name: &BindingName) -> Option<StaticAddress> {
        if let Some(global) = self
            .globals
            .values()
            .find(|global| name.is_named(global.name()) || global.kernel_name() == name)
        {
            return Some(StaticAddress {
                bounds: None,
                pointer: crate::kernel::SymbolicMemory::global_pointer(global.kernel_name()),
                interface_type: global.interface_type(),
                constant: global.is_constant(),
            });
        }
        if let Some(global_array) = self
            .global_arrays
            .values()
            .find(|global| name.is_named(global.name()) || global.kernel_name() == name)
        {
            let interface_type = global_array.complete_c_type()?;
            return Some(StaticAddress {
                bounds: None,
                pointer: crate::kernel::SymbolicMemory::global_pointer(global_array.kernel_name()),
                interface_type,
                constant: global_array.is_constant(),
            });
        }
        if let Some(global_aggregate) = self
            .global_aggregates
            .values()
            .find(|global| name.is_named(global.name()) || global.kernel_name() == name)
        {
            return Some(StaticAddress {
                bounds: None,
                pointer: crate::kernel::SymbolicMemory::global_pointer(
                    global_aggregate.kernel_name(),
                ),
                interface_type: record_value_type(global_aggregate.layout()),
                constant: global_aggregate.is_constant(),
            });
        }
        if let Some(global_aggregate_array) = self
            .global_aggregate_arrays
            .values()
            .find(|global| name.is_named(global.name()) || global.kernel_name() == name)
        {
            let interface_type = global_aggregate_array.complete_c_type()?;
            return Some(StaticAddress {
                bounds: None,
                pointer: crate::kernel::SymbolicMemory::global_pointer(
                    global_aggregate_array.kernel_name(),
                ),
                interface_type,
                constant: global_aggregate_array.is_constant(),
            });
        }
        if let Some(static_local) = self.static_locals.values().find(|static_local| {
            name.is_named(static_local.name()) || static_local.kernel_name() == name
        }) {
            return Some(StaticAddress {
                bounds: None,
                pointer: crate::kernel::SymbolicMemory::static_pointer(
                    &self.name,
                    static_local.kernel_name(),
                ),
                interface_type: static_local.interface_type(),
                constant: static_local.is_constant(),
            });
        }
        if let Some(static_array) = self.static_arrays.values().find(|static_array| {
            name.is_named(static_array.name()) || static_array.kernel_name() == name
        }) {
            return Some(StaticAddress {
                bounds: None,
                pointer: crate::kernel::SymbolicMemory::static_pointer(
                    &self.name,
                    static_array.kernel_name(),
                ),
                interface_type: static_array.interface_type(),
                constant: static_array.is_constant(),
            });
        }
        if let Some(static_aggregate) = self.static_aggregates.values().find(|static_aggregate| {
            name.is_named(static_aggregate.name()) || static_aggregate.kernel_name() == name
        }) {
            return Some(StaticAddress {
                bounds: None,
                pointer: crate::kernel::SymbolicMemory::static_pointer(
                    &self.name,
                    static_aggregate.kernel_name(),
                ),
                interface_type: record_value_type(static_aggregate.layout()),
                constant: static_aggregate.is_constant(),
            });
        }
        self.static_aggregate_arrays
            .values()
            .find(|static_aggregate_array| {
                name.is_named(static_aggregate_array.name())
                    || static_aggregate_array.kernel_name() == name
            })
            .map(|static_aggregate_array| StaticAddress {
                bounds: None,
                pointer: crate::kernel::SymbolicMemory::static_pointer(
                    &self.name,
                    static_aggregate_array.kernel_name(),
                ),
                interface_type: static_aggregate_array.interface_type(),
                constant: static_aggregate_array.is_constant(),
            })
    }

    fn static_address_expression(&self, expression: &CExpression) -> Option<StaticAddress> {
        match expression {
            CExpression::StringLiteral(literal) => Some(StaticAddress {
                pointer: crate::kernel::SymbolicMemory::string_literal_pointer(
                    literal.identity()?,
                    literal.bytes(),
                ),
                interface_type: InterfaceType::CharArray(
                    literal.plain_char(),
                    u32::try_from(literal.bytes().len()).expect("literal length fits u32"),
                ),
                constant: false,
                bounds: None,
            }),
            CExpression::Variable(name) => self.static_object_address(name),
            CExpression::Field {
                pointer,
                field_type,
                ..
            }
            | CExpression::UnionField {
                pointer,
                field_type,
                ..
            } => {
                let mut address = self.static_address_expression(pointer)?;
                address.interface_type = *field_type;
                Some(address)
            }
            CExpression::Index(base, index, _) => {
                let mut address = self.static_address_expression(base)?;
                let element_type = address.interface_type.pointee_type()?;
                let index = static_integer_value(index)?;
                let bytes = index.checked_mul(element_type.abi_size_bytes())?;
                address.pointer = address.pointer.offset_by_bytes(bytes);
                address.interface_type = element_type;
                Some(address)
            }
            CExpression::PointerOffsetBytes { pointer, bytes } => {
                let mut address = self.static_address_expression(pointer)?;
                address.pointer = address.pointer.offset_by_bytes(*bytes);
                Some(address)
            }
            CExpression::Subobject { pointer, width } => {
                let mut address = self.static_address_expression(pointer)?;
                address.bounds = Some(crate::kernel::SubobjectBounds::constant(
                    address.pointer.clone(),
                    *width,
                ));
                Some(address)
            }
            CExpression::Add(pointer, offset) => {
                let mut address = self.static_address_expression(pointer)?;
                address.pointer = address
                    .pointer
                    .offset_by_bytes(static_integer_value(offset)?);
                Some(address)
            }
            CExpression::AggregateAddress {
                pointer,
                struct_name,
            } => {
                let mut address = self.static_address_expression(pointer)?;
                address.interface_type = record_value_type(self.structs.get(struct_name)?);
                Some(address)
            }
            CExpression::UnionAddress {
                pointer,
                union_name,
            } => {
                let mut address = self.static_address_expression(pointer)?;
                address.interface_type =
                    InterfaceType::UInt8Array(self.unions.get(union_name)?.size_bytes);
                Some(address)
            }
            CExpression::Cast {
                expression,
                interface_type,
                ..
            } => {
                let mut address = self.static_address_expression(expression)?;
                address.interface_type = *interface_type;
                Some(address)
            }
            _ => None,
        }
    }

    fn static_address_initializer_value(
        &self,
        declared_type: InterfaceType,
        declared_pointee_constant: bool,
        initializer: &CExpression,
    ) -> Option<crate::kernel::ProgramValue> {
        let CExpression::AddressOf(target) = initializer else {
            return None;
        };
        let address = self.static_address_expression(target)?;
        if address.interface_type.pointer_type()? != declared_type {
            return None;
        }
        Some(crate::kernel::ProgramValue::Pointer(
            crate::kernel::Pointer::new(address.pointer, declared_type.to_kernel_type())
                .with_pointee_constant(declared_pointee_constant)
                .with_bounds(address.bounds),
        ))
    }

    fn validate_static_pointer_initializer(
        &self,
        declared_type: InterfaceType,
        declared_pointee_constant: bool,
        initializer: &CExpression,
    ) -> Result<(), CSyntaxError> {
        if matches!(initializer, CExpression::Int32Literal(0)) {
            return Ok(());
        }
        let CExpression::AddressOf(target) = initializer else {
            return Err(CSyntaxError::new(
                "static pointer initializers currently support only null or the address of a declared object or subobject",
            ));
        };
        let Some(address) = self.static_address_expression(target) else {
            return Err(CSyntaxError::new(
                "static pointer initializers currently support only null or the address of a declared object or subobject",
            ));
        };
        let Some(expected_type) = address.interface_type.pointer_type() else {
            return Err(CSyntaxError::new(
                "static pointer initializers currently support only addresses of scalar objects or scalar subobjects",
            ));
        };
        if expected_type != declared_type {
            return Err(CSyntaxError::new(format!(
                "address initializer has type `{expected_type:?}`, but `{declared_type:?}` is required"
            )));
        }
        if address.constant && !declared_pointee_constant {
            return Err(CSyntaxError::new(
                "cannot discard const qualification from a pointer initializer",
            ));
        }
        Ok(())
    }

    /// Revalidates address-valued static initializers after global linkage has
    /// replaced translation-unit declarations with their selected
    /// definitions. Parsing checks the declarations visible at each use;
    /// this final pass checks the linked object graph that lowering will use.
    /// The address an externally linked pointer global's initializer names,
    /// resolved against this translation unit's own names, where any private
    /// object it names is visible. Validates the initializer first.
    pub(crate) fn resolve_linked_pointer_initializer(
        &self,
        global: &CGlobal,
    ) -> Result<Option<crate::kernel::ProgramValue>, CSyntaxError> {
        let Some(initializer) = global.initializer() else {
            return Ok(None);
        };
        if !global.interface_type().is_pointer() {
            return Ok(None);
        }
        self.validate_static_pointer_initializer(
            global.interface_type(),
            global.pointee_is_constant(),
            initializer,
        )?;
        Ok(self.static_address_initializer_value(
            global.interface_type(),
            global.pointee_is_constant(),
            initializer,
        ))
    }

    /// An externally linked pointer array lowered against this translation
    /// unit's own names, as [`Self::resolve_linked_pointer_initializer`] does
    /// for a scalar. Validates the element initializers first.
    pub(crate) fn resolve_linked_pointer_array(
        &self,
        array: &CGlobalArray,
    ) -> Result<Option<crate::kernel::GlobalArray>, CSyntaxError> {
        let Some(initializer) = array.initializer() else {
            return Ok(None);
        };
        if !array.element_type().is_pointer() {
            return Ok(None);
        }
        for value in initializer.values() {
            self.validate_static_pointer_initializer(array.element_type(), false, value)?;
        }
        Ok(self.to_kernel_global_array(array))
    }

    pub(crate) fn validate_static_initializers(&self) -> Result<(), CSyntaxError> {
        for global in self.globals.values() {
            if global.interface_type().is_pointer()
                && global.resolved_address.is_none()
                && let Some(initializer) = global.initializer()
            {
                self.validate_static_pointer_initializer(
                    global.interface_type(),
                    global.pointee_is_constant(),
                    initializer,
                )?;
            }
        }
        for array in self
            .global_arrays
            .values()
            .filter(|array| array.element_type().is_pointer() && array.resolved.is_none())
        {
            if let Some(initializer) = array.initializer() {
                for value in initializer.values() {
                    self.validate_static_pointer_initializer(array.element_type(), false, value)?;
                }
            }
        }
        for static_local in self.static_locals.values() {
            if static_local.interface_type().is_pointer() {
                self.validate_static_pointer_initializer(
                    static_local.interface_type(),
                    static_local.pointee_is_constant(),
                    static_local.initializer(),
                )?;
            }
        }
        for array in self
            .static_arrays
            .values()
            .filter(|array| array.element_type().is_pointer())
        {
            for value in array.initializer().values() {
                self.validate_static_pointer_initializer(
                    array.element_type(),
                    array.pointee_is_constant(),
                    value,
                )?;
            }
        }
        Ok(())
    }

    fn to_kernel_global(&self, global: &CGlobal) -> Option<crate::kernel::Global> {
        if let Some(value) = &global.resolved_address {
            return Some(global.to_kernel_global_with_value(value.clone()));
        }
        let initializer = global.initializer()?;
        if let Some(value) = self.static_address_initializer_value(
            global.interface_type(),
            global.pointee_is_constant(),
            initializer,
        ) {
            return Some(global.to_kernel_global_with_value(value));
        }
        global.to_kernel_global()
    }

    fn to_kernel_global_array(&self, array: &CGlobalArray) -> Option<crate::kernel::GlobalArray> {
        if let Some(resolved) = &array.resolved {
            return Some(resolved.clone());
        }
        let values = array.initializer()?.to_kernel_contents(|initializer| {
            self.static_address_initializer_value(array.element_type(), false, initializer)
                .or_else(|| kernel_integer_literal_value(array.element_type(), initializer))
        })?;
        Some(array.to_kernel_global_array_with_values(values))
    }

    fn to_kernel_static_array(&self, array: &CStaticArray) -> Option<crate::kernel::StaticArray> {
        let values = array.initializer().to_kernel_contents(|initializer| {
            self.static_address_initializer_value(
                array.element_type(),
                array.pointee_is_constant(),
                initializer,
            )
            .or_else(|| kernel_integer_literal_value(array.element_type(), initializer))
        })?;
        Some(array.to_kernel_static_array_with_values(values))
    }

    fn to_kernel_static(&self, static_local: &CStaticLocal) -> Option<crate::kernel::StaticLocal> {
        let initializer = static_local.initializer();
        if let Some(value) = self.static_address_initializer_value(
            static_local.interface_type(),
            static_local.pointee_is_constant(),
            initializer,
        ) {
            return Some(static_local.to_kernel_static_with_value(value));
        }
        static_local.to_kernel_static()
    }

    pub fn to_kernel_function(&self) -> crate::kernel::ProgramFunction {
        if let Some(function) = &self.prelowered_kernel_function {
            return function.clone();
        }
        let kernel_body = self
            .body
            .to_kernel_statement_with_control_targets(&self.control_targets);
        let mut suffix: Option<std::sync::Arc<crate::kernel::ProgramStatement>> = None;
        let mut control_targets = BTreeMap::new();
        if !self.control_targets.is_empty() {
            let mut statements = Vec::new();
            flatten_direct_c_statements(&self.body, &mut statements);
            for statement in statements.into_iter().rev() {
                let lowered =
                    statement.to_kernel_statement_with_control_targets(&self.control_targets);
                let remaining = match suffix {
                    Some(tail) => {
                        std::sync::Arc::new(crate::kernel::program_seq(lowered, (*tail).clone()))
                    }
                    None => std::sync::Arc::new(lowered),
                };
                if let CStatement::Label { name, .. } = statement {
                    let (target, statement_index) = self
                        .control_targets
                        .get(name)
                        .expect("validated label has a target record");
                    control_targets.insert(
                        *target,
                        crate::kernel::ControlTarget {
                            statement_index: *statement_index,
                            remaining: remaining.clone(),
                        },
                    );
                }
                suffix = Some(remaining);
            }
        }
        let mut function = crate::kernel::program_function(
            if self.return_struct_name.is_some() {
                crate::kernel::ProgramType::UInt8Pointer
            } else {
                self.return_type.to_kernel_type()
            },
            self.name.clone(),
            self.parameters
                .iter()
                .map(ImportedParameter::to_kernel_parameter)
                .collect(),
            kernel_body,
        )
        .with_control_targets(control_targets);
        function = function.with_return_pointee_constant(self.return_pointee_constant);
        if self.program_entry_state.is_some() {
            function = function.with_program_entry();
        }
        if self.inline_body {
            function = function.with_inline_body();
        }
        if let Some(name) = &self.return_struct_name {
            let layout = self
                .structs
                .get(name)
                .expect("struct return has a parsed layout")
                .to_kernel_aggregate_layout();
            function = match self.aggregate_return_mode {
                crate::kernel::AggregateReturnMode::Copy => {
                    function.with_return_aggregate_layout(layout)
                }
                crate::kernel::AggregateReturnMode::Construction => {
                    function.with_construction_return(layout)
                }
            };
        }
        self.with_kernel_static_storage(function, true)
    }

    /// Startup needs storage declarations, not another copy of each body
    /// or each function's complete visible global environment.
    pub(crate) fn to_kernel_static_storage(
        &self,
        include_globals: bool,
    ) -> crate::kernel::ProgramFunction {
        self.with_kernel_static_storage(
            crate::kernel::ProgramFunction::new(
                crate::kernel::ProgramType::Void,
                self.name.clone(),
                vec![],
                crate::kernel::ProgramStatement::Skip,
            ),
            include_globals,
        )
    }

    fn with_kernel_static_storage(
        &self,
        mut function: crate::kernel::ProgramFunction,
        include_globals: bool,
    ) -> crate::kernel::ProgramFunction {
        if include_globals {
            function = function
                .with_global_variables(
                    self.globals
                        .values()
                        .filter_map(|global| self.to_kernel_global(global))
                        .collect(),
                )
                .with_global_arrays(
                    self.global_arrays
                        .values()
                        .filter_map(|array| self.to_kernel_global_array(array))
                        .collect(),
                )
                .with_global_aggregates(
                    self.global_aggregates
                        .values()
                        .filter_map(CGlobalAggregate::to_kernel_global_aggregate)
                        .collect(),
                )
                .with_global_aggregate_arrays(
                    self.global_aggregate_arrays
                        .values()
                        .filter_map(CGlobalAggregateArray::to_kernel_global_aggregate_array)
                        .collect(),
                );
        }
        function
            .with_static_variables(
                self.static_locals
                    .values()
                    .filter_map(|static_local| self.to_kernel_static(static_local))
                    .collect(),
            )
            .with_static_arrays(
                self.static_arrays
                    .values()
                    .filter_map(|array| self.to_kernel_static_array(array))
                    .collect(),
            )
            .with_static_aggregates(
                self.static_aggregates
                    .values()
                    .map(CStaticAggregate::to_kernel_static_aggregate)
                    .collect(),
            )
            .with_static_aggregate_arrays(
                self.static_aggregate_arrays
                    .values()
                    .map(CStaticAggregateArray::to_kernel_static_aggregate_array)
                    .collect(),
            )
            .with_string_literals(
                self.string_literals
                    .iter()
                    .map(CStringLiteral::to_kernel)
                    .collect(),
            )
    }
}

fn natural_cycle_statement_supported(statement: &CStatement) -> bool {
    match statement {
        CStatement::Seq(first, second) => {
            natural_cycle_statement_supported(first) && natural_cycle_statement_supported(second)
        }
        CStatement::If {
            then_branch,
            else_branch,
            ..
        } => {
            natural_cycle_statement_supported(then_branch)
                && natural_cycle_statement_supported(else_branch)
        }
        CStatement::While { .. }
        | CStatement::DoWhile { .. }
        | CStatement::For { .. }
        | CStatement::Switch { .. }
        | CStatement::Label { .. }
        | CStatement::Break
        | CStatement::Continue
        | CStatement::Declare { .. }
        | CStatement::DeclareStructValue { .. } => false,
        _ => true,
    }
}

fn natural_cycle_statement_contains_goto(statement: &CStatement) -> bool {
    match statement {
        CStatement::Goto { .. } => true,
        CStatement::Seq(first, second) => {
            natural_cycle_statement_contains_goto(first)
                || natural_cycle_statement_contains_goto(second)
        }
        CStatement::If {
            then_branch,
            else_branch,
            ..
        } => {
            natural_cycle_statement_contains_goto(then_branch)
                || natural_cycle_statement_contains_goto(else_branch)
        }
        _ => false,
    }
}

fn collect_natural_cycle_goto_targets<'a>(statement: &'a CStatement, targets: &mut Vec<&'a str>) {
    match statement {
        CStatement::Goto { target, .. } => targets.push(target),
        CStatement::Seq(first, second) => {
            collect_natural_cycle_goto_targets(first, targets);
            collect_natural_cycle_goto_targets(second, targets);
        }
        CStatement::If {
            then_branch,
            else_branch,
            ..
        } => {
            collect_natural_cycle_goto_targets(then_branch, targets);
            collect_natural_cycle_goto_targets(else_branch, targets);
        }
        _ => {}
    }
}

impl CExpression {
    /// Returns parser-minted source origin for a source-level scalar field load.
    /// Synthesized aggregate-copy loads and all non-field expressions return
    /// `None`.
    pub fn field_source(&self) -> Option<&CFieldSource> {
        match self {
            Self::Field { source, .. } => source.as_ref(),
            _ => None,
        }
    }

    pub fn field_source_id(&self) -> Option<&CFieldSourceId> {
        self.field_source().map(|source| source.id())
    }
}

impl CEnumDefinition {
    pub fn values(&self) -> &BTreeMap<String, i64> {
        &self.values
    }

    pub fn value(&self, name: &str) -> Option<i64> {
        self.values.get(name).copied()
    }
}

impl CUnionLayout {
    pub fn fields(&self) -> &BTreeMap<String, CUnionField> {
        &self.fields
    }

    pub fn field(&self, name: &str) -> Option<&CUnionField> {
        self.fields.get(name)
    }

    pub fn size_bytes(&self) -> u32 {
        self.size_bytes
    }

    pub fn alignment_bytes(&self) -> u32 {
        self.alignment_bytes
    }
}

impl CUnionField {
    pub fn interface_type(&self) -> InterfaceType {
        self.interface_type
    }

    pub fn is_long_double(&self) -> bool {
        self.long_double
    }

    pub fn pointee_is_constant(&self) -> bool {
        self.pointee_constant
    }

    pub fn offset_bytes(&self) -> u32 {
        self.offset_bytes
    }

    pub fn byte_width(&self) -> u32 {
        self.byte_width
    }

    pub fn struct_name(&self) -> Option<&str> {
        self.struct_name.as_deref()
    }

    pub fn array_shape(&self) -> Option<&[u32]> {
        self.array_shape.as_deref()
    }

    fn kernel_copyable(&self) -> bool {
        self.struct_name.is_none()
            && self.union_name.is_none()
            && self.array_element_width.is_none()
            && matches!(
                self.interface_type,
                InterfaceType::Int32
                    | InterfaceType::UInt8
                    | InterfaceType::Int32Pointer
                    | InterfaceType::UInt8Pointer
                    | InterfaceType::Int32PointerPointer
                    | InterfaceType::UInt8PointerPointer
            )
    }
}

impl InterfaceType {
    /// The access class of an object or lvalue of this type, or of an
    /// array's elements (`design/effective-types.md`). `int *` and `int **`
    /// give none, because a struct pointer shares their spelling here and its
    /// struct is recorded beside the type; function pointers and pointer
    /// arrays give none either.
    pub fn access_class(self) -> Option<crate::kernel::effective_type::CAccessClass> {
        use crate::kernel::effective_type::{CAccessClass, CPointeeBase, CScalarClass};
        use crate::languages::c::target::LongRank;
        let rank = |rank: LongRank| match rank {
            LongRank::Long => CScalarClass::Long,
            LongRank::LongLong => CScalarClass::LongLong,
        };
        let integer = |class, signed| CPointeeBase::Integer { class, signed };
        let pointer = |base, depth| Some(CAccessClass::Pointer { base, depth });
        let scalar = |class| Some(CAccessClass::Scalar(class));
        match self {
            Self::Parameter(_) | Self::ParameterPointer(_) => None,
            Self::Char(_) | Self::CharArray(..) | Self::Int8 | Self::UInt8 => {
                scalar(CScalarClass::Char)
            }
            Self::Int8Array(_) | Self::UInt8Array(_) => scalar(CScalarClass::Char),
            Self::Bool => scalar(CScalarClass::Bool),
            Self::Int16 | Self::UInt16 | Self::Int16Array(_) | Self::UInt16Array(_) => {
                scalar(CScalarClass::Short)
            }
            Self::Int32 | Self::UInt32 | Self::Int32Array(_) | Self::UInt32Array(_) => {
                scalar(CScalarClass::Int)
            }
            Self::Int64(long) | Self::UInt64(long) => scalar(rank(long)),
            Self::Int64Array(long, _) | Self::UInt64Array(long, _) => scalar(rank(long)),
            Self::Int128 | Self::UInt128 | Self::Int128Array(_) | Self::UInt128Array(_) => {
                scalar(CScalarClass::Int128)
            }
            Self::Float32 | Self::Float32Array(_) => scalar(CScalarClass::Float),
            Self::Float64 | Self::Float64Array(_) => scalar(CScalarClass::Double),
            Self::VoidPointer => pointer(CPointeeBase::Void, 1),
            Self::VoidPointerPointer => pointer(CPointeeBase::Void, 2),
            Self::CharPointer(_) => pointer(CPointeeBase::PlainChar, 1),
            Self::CharPointerPointer(_) => pointer(CPointeeBase::PlainChar, 2),
            Self::Int8Pointer => pointer(CPointeeBase::SignedChar, 1),
            Self::UInt8Pointer => pointer(CPointeeBase::UnsignedChar, 1),
            Self::Int8PointerPointer => pointer(CPointeeBase::SignedChar, 2),
            Self::UInt8PointerPointer => pointer(CPointeeBase::UnsignedChar, 2),
            Self::Int16Pointer => pointer(integer(CScalarClass::Short, true), 1),
            Self::UInt16Pointer => pointer(integer(CScalarClass::Short, false), 1),
            Self::Int16PointerPointer => pointer(integer(CScalarClass::Short, true), 2),
            Self::UInt16PointerPointer => pointer(integer(CScalarClass::Short, false), 2),
            Self::UInt32Pointer => pointer(integer(CScalarClass::Int, false), 1),
            Self::UInt32PointerPointer => pointer(integer(CScalarClass::Int, false), 2),
            Self::Int64Pointer(long) => pointer(integer(rank(long), true), 1),
            Self::UInt64Pointer(long) => pointer(integer(rank(long), false), 1),
            Self::Int64PointerPointer(long) => pointer(integer(rank(long), true), 2),
            Self::UInt64PointerPointer(long) => pointer(integer(rank(long), false), 2),
            Self::Int128Pointer => pointer(integer(CScalarClass::Int128, true), 1),
            Self::UInt128Pointer => pointer(integer(CScalarClass::Int128, false), 1),
            Self::Int128PointerPointer => pointer(integer(CScalarClass::Int128, true), 2),
            Self::UInt128PointerPointer => pointer(integer(CScalarClass::Int128, false), 2),
            Self::Float32Pointer => pointer(CPointeeBase::Float, 1),
            Self::Float64Pointer => pointer(CPointeeBase::Double, 1),
            Self::Float32PointerPointer => pointer(CPointeeBase::Float, 2),
            Self::Float64PointerPointer => pointer(CPointeeBase::Double, 2),
            Self::Void
            | Self::Int32Pointer
            | Self::Int32PointerPointer
            | Self::FunctionPointer(_)
            | Self::PointerArray(..) => None,
        }
    }

    /// The class a declared object of this type records, when the kernel
    /// type cannot give it: a `long` or `long long`, a pointer whose pointee
    /// the kernel type erases, or a scalar array, whose kernel block is
    /// otherwise untyped.
    pub fn declared_class(self) -> Option<crate::kernel::effective_type::CAccessClass> {
        // `int8` and `uint8` arrays record nothing: the frontend also
        // declares a local array of structs as one, and its members are not
        // bytes.
        if matches!(self, Self::Int8Array(_) | Self::UInt8Array(_)) {
            return None;
        }
        let class = self.access_class()?;
        let derived =
            crate::kernel::effective_type::CAccessClass::of_kernel_type(self.to_kernel_type());
        (self.array_length().is_some() || derived.as_ref() != Some(&class)).then_some(class)
    }

    pub(in crate::languages) fn is_supported_static_scalar(self) -> bool {
        matches!(
            self,
            Self::Bool
                | Self::VoidPointer
                | Self::VoidPointerPointer
                | Self::Int8
                | Self::Int16
                | Self::Int32
                | Self::Char(_)
                | Self::UInt8
                | Self::UInt16
                | Self::UInt32
                | Self::Int64(_)
                | Self::UInt64(_)
                | Self::Float32
                | Self::Float64
                | Self::Int8Pointer
                | Self::Int16Pointer
                | Self::UInt16Pointer
                | Self::Int32Pointer
                | Self::CharPointer(_)
                | Self::UInt8Pointer
                | Self::UInt32Pointer
                | Self::Int128Pointer
                | Self::Int64Pointer(_)
                | Self::UInt128Pointer
                | Self::UInt64Pointer(_)
                | Self::Float32Pointer
                | Self::Float64Pointer
                | Self::Int8PointerPointer
                | Self::Int16PointerPointer
                | Self::UInt16PointerPointer
                | Self::Int32PointerPointer
                | Self::CharPointerPointer(_)
                | Self::UInt8PointerPointer
                | Self::UInt32PointerPointer
                | Self::Int128PointerPointer
                | Self::Int64PointerPointer(_)
                | Self::UInt128PointerPointer
                | Self::UInt64PointerPointer(_)
                | Self::Float32PointerPointer
                | Self::Float64PointerPointer
        )
    }
}

impl CStatement {
    /// Where this statement was written, for a statement kind that records
    /// it; see [`CSite`].
    pub fn site(&self) -> Option<&CSite> {
        match self {
            Self::EndAggregateLifetimes { site, .. }
            | Self::Declare { site, .. }
            | Self::StepValue { site, .. }
            | Self::DeclareStructValue { site, .. }
            | Self::Assign { site, .. }
            | Self::Call { site, .. }
            | Self::CallResult { site, .. }
            | Self::IndirectCall { site, .. }
            | Self::HeapAllocate { site, .. }
            | Self::HeapFree { site, .. }
            | Self::Assert { site, .. }
            | Self::LoopTest { site, .. }
            | Self::Return(_, site)
            | Self::Store { site, .. }
            | Self::SequentialStore { site, .. }
            | Self::AggregateCopy { site, .. }
            | Self::Update { site, .. }
            | Self::If { site, .. }
            | Self::While { site, .. }
            | Self::DoWhile { site, .. }
            | Self::For { site, .. }
            | Self::Switch { site, .. } => Some(site),
            Self::FillArrayTail { .. }
            | Self::Skip
            | Self::Break
            | Self::Continue
            | Self::Goto { .. }
            | Self::Label { .. }
            | Self::Seq(_, _) => None,
        }
    }

    fn site_mut(&mut self) -> Option<&mut CSite> {
        match self {
            Self::EndAggregateLifetimes { site, .. } => Some(site),
            Self::Declare { site, .. }
            | Self::StepValue { site, .. }
            | Self::DeclareStructValue { site, .. }
            | Self::Assign { site, .. }
            | Self::Call { site, .. }
            | Self::CallResult { site, .. }
            | Self::IndirectCall { site, .. }
            | Self::HeapAllocate { site, .. }
            | Self::HeapFree { site, .. }
            | Self::Assert { site, .. }
            | Self::LoopTest { site, .. }
            | Self::Return(_, site)
            | Self::Store { site, .. }
            | Self::SequentialStore { site, .. }
            | Self::AggregateCopy { site, .. }
            | Self::Update { site, .. }
            | Self::If { site, .. }
            | Self::While { site, .. }
            | Self::DoWhile { site, .. }
            | Self::For { site, .. }
            | Self::Switch { site, .. } => Some(site),
            Self::FillArrayTail { .. }
            | Self::Skip
            | Self::Break
            | Self::Continue
            | Self::Goto { .. }
            | Self::Label { .. }
            | Self::Seq(_, _) => None,
        }
    }

    pub(crate) fn to_kernel_statement_with_control_targets(
        &self,
        targets: &BTreeMap<String, (crate::kernel::ControlTargetId, usize)>,
    ) -> crate::kernel::ProgramStatement {
        enum Task<'a> {
            Visit(&'a CStatement),
            Seq,
            If(&'a CExpression),
        }
        let mut tasks = vec![Task::Visit(self)];
        let mut results = Vec::new();
        while let Some(task) = tasks.pop() {
            crate::instrumentation::record_deterministic_work(1);
            match task {
                Task::Visit(Self::Seq(first, second)) => {
                    tasks.push(Task::Seq);
                    tasks.push(Task::Visit(second));
                    tasks.push(Task::Visit(first));
                }
                Task::Visit(Self::If {
                    condition,
                    then_branch,
                    else_branch,
                    ..
                }) => {
                    tasks.push(Task::If(condition));
                    tasks.push(Task::Visit(else_branch));
                    tasks.push(Task::Visit(then_branch));
                }
                Task::Visit(Self::Label { statement, .. }) => tasks.push(Task::Visit(statement)),
                Task::Visit(statement) => results.push(statement.to_kernel_statement_leaf(targets)),
                Task::Seq => {
                    let second = results.pop().expect("second statement");
                    let first = results.pop().expect("first statement");
                    results.push(crate::kernel::program_seq(first, second));
                }
                Task::If(condition) => {
                    let else_branch = results.pop().expect("else statement");
                    let then_branch = results.pop().expect("then statement");
                    results.push(crate::kernel::program_if(
                        condition.to_kernel_expression(),
                        then_branch,
                        else_branch,
                    ));
                }
            }
        }
        debug_assert_eq!(results.len(), 1);
        results.pop().expect("root statement")
    }

    fn to_kernel_statement_leaf(
        &self,
        targets: &BTreeMap<String, (crate::kernel::ControlTargetId, usize)>,
    ) -> crate::kernel::ProgramStatement {
        match self {
            Self::StepValue {
                aggregate_layout,
                steps,
                expression,
                interface_type,
                pointee_constant,
                ..
            } => crate::kernel::ProgramStatement::StepValue {
                aggregate_layout: aggregate_layout.as_ref().map(|record| {
                    crate::kernel::AggregateResultLayout {
                        layout: record.to_kernel_aggregate_layout(),
                        declared_class: record
                            .class
                            .clone()
                            .map(crate::kernel::effective_type::CAccessClass::Struct),
                    }
                }),
                steps: steps.clone(),
                expression: expression.to_kernel_expression(),
                value_type: interface_type.map(|interface_type| interface_type.to_kernel_type()),
                pointee_constant: *pointee_constant,
            },
            Self::FillArrayTail {
                name,
                element_type,
                start,
                count,
            } => {
                let pointer = CExpression::Add(
                    Box::new(CExpression::Variable(name.clone())),
                    Box::new(CExpression::UInt32Literal(*start)),
                );
                crate::kernel::program_write_scalar_array_region(
                    pointer.to_kernel_expression(),
                    zero_initializer(*element_type).to_kernel_expression(),
                    element_type.to_kernel_type(),
                    *count,
                    false,
                )
            }
            Self::EndAggregateLifetimes { names, steps, .. } => {
                crate::kernel::ProgramStatement::EndAutomaticLifetimes {
                    names: names.clone(),
                    steps: steps.clone(),
                }
            }
            Self::Skip => crate::kernel::program_skip(),
            Self::Break => crate::kernel::program_break(),
            Self::Continue => crate::kernel::program_continue(),
            Self::Goto { target, .. } => crate::kernel::program_goto(
                targets
                    .get(target)
                    .expect("validated C goto target has a kernel identity")
                    .0,
            ),
            Self::Label { .. } | Self::Seq(..) | Self::If { .. } => {
                unreachable!("structured statement handled by the iterative visitor")
            }
            Self::Declare {
                interface_type,
                name,
                volatile,
                pointee_volatile,
                constant,
                pointee_constant,
                zero_fill,
                initializer,
                declared_class: parsed_class,
                ..
            } => {
                let mut statement = crate::kernel::program_declare_with_zero_fill(
                    name.clone(),
                    interface_type.to_kernel_type(),
                    *volatile,
                    *pointee_volatile,
                    *constant,
                    *pointee_constant,
                    zero_fill.as_ref().map(CZeroFill::to_kernel),
                );
                if let crate::kernel::ProgramStatement::Declare {
                    initializer: value,
                    declared_class,
                    ..
                } = &mut statement
                {
                    *value = initializer.as_ref().map(CExpression::to_kernel_expression);
                    *declared_class = parsed_class
                        .clone()
                        .or_else(|| interface_type.declared_class());
                }
                statement
            }
            Self::DeclareStructValue { name, layout, .. } => {
                crate::kernel::program_declare_classed_aggregate(
                    name.clone(),
                    layout.to_kernel_aggregate_layout(),
                    layout
                        .class
                        .clone()
                        .map(crate::kernel::effective_type::CAccessClass::Struct),
                )
            }
            Self::Assign {
                name,
                expression,
                prior_result,
                ..
            } => crate::kernel::ProgramStatement::Assign {
                name: name.clone(),
                expression: expression.to_kernel_expression(),
                source: Default::default(),
                prior_result: *prior_result,
            },
            Self::CallResult {
                aggregate_layout,
                call,
                function_name,
                arguments,
                result_type,
                result_aggregate_layout,
                result_pointee_constant,
                callee,
                ..
            } => crate::kernel::ProgramStatement::CallResult {
                aggregate_layout: aggregate_layout.as_ref().map(|record| {
                    crate::kernel::AggregateResultLayout {
                        layout: record.to_kernel_aggregate_layout(),
                        declared_class: record
                            .class
                            .clone()
                            .map(crate::kernel::effective_type::CAccessClass::Struct),
                    }
                }),
                call: *call,
                function_name: function_name.clone(),
                arguments: arguments
                    .iter()
                    .map(CExpression::to_kernel_expression)
                    .collect(),
                result_type: result_type.map(|interface_type| interface_type.to_kernel_type()),
                result_aggregate_layout: result_aggregate_layout
                    .as_ref()
                    .map(RecordLayout::to_kernel_aggregate_layout),
                result_pointee_constant: *result_pointee_constant,
                callee: callee.as_ref().map(CCallee::to_kernel),
            },
            Self::Call {
                function_name,
                arguments,
                callee,
                ..
            } => crate::kernel::ProgramStatement::Call {
                function_name: function_name.clone(),
                arguments: arguments
                    .iter()
                    .map(CExpression::to_kernel_expression)
                    .collect(),
                callee: callee.as_ref().map(CCallee::to_kernel),
            },
            Self::IndirectCall { .. } => {
                unreachable!("indirect call statements must be lowered before kernel conversion")
            }
            Self::HeapAllocate {
                target,
                bytes,
                zeroed,
                object_type,
                ..
            } => crate::kernel::ProgramStatement::HeapAllocate {
                target: target.clone(),
                bytes: bytes.to_kernel_expression(),
                zeroed: *zeroed,
                object_type: object_type.clone(),
                ends_program_on_failure: false,
            },
            Self::HeapFree { pointer, .. } => {
                crate::kernel::program_heap_free(pointer.to_kernel_expression())
            }
            Self::Assert {
                condition, label, ..
            } => crate::kernel::program_labeled_assert(
                condition.to_kernel_expression(),
                label.clone(),
            ),
            Self::LoopTest {
                aggregate_steps,
                condition,
                ..
            } => crate::kernel::ProgramStatement::LoopTest {
                aggregate_steps: aggregate_steps.clone(),
                condition: condition.to_kernel_expression(),
            },
            Self::Return(expression, _) => {
                crate::kernel::program_return(expression.to_kernel_expression())
            }
            Self::Store {
                pointer,
                value,
                value_type,
                lvalue_class,
                pointee_constant,
                ..
            } => match value_type {
                Some(value_type) => crate::kernel::program_qualified_typed_store(
                    pointer.to_kernel_expression(),
                    value.to_kernel_expression(),
                    value_type.to_kernel_type(),
                    lvalue_class.clone().or_else(|| value_type.access_class()),
                    *pointee_constant,
                    false,
                ),
                None => crate::kernel::program_store(
                    pointer.to_kernel_expression(),
                    value.to_kernel_expression(),
                ),
            },
            Self::SequentialStore {
                target,
                value,
                value_type,
                pointee_constant,
                ..
            } => crate::kernel::program_qualified_typed_store(
                CExpression::AddressOf(Box::new(target.clone())).to_kernel_expression(),
                value.to_kernel_expression(),
                value_type.to_kernel_type(),
                value_type.access_class(),
                *pointee_constant,
                true,
            ),
            Self::AggregateCopy {
                target,
                source,
                layout,
                ..
            } => crate::kernel::program_copy_aggregate(
                target.to_kernel_expression(),
                source.to_kernel_expression(),
                layout.to_kernel_aggregate_layout(),
            ),
            Self::Update {
                target,
                operator,
                operand,
                ..
            } => crate::kernel::program_update(
                target.to_kernel_expression(),
                match operator {
                    CUpdateOperator::Add => crate::kernel::UpdateOperator::Add,
                    CUpdateOperator::Subtract => crate::kernel::UpdateOperator::Subtract,
                    CUpdateOperator::Multiply => crate::kernel::UpdateOperator::Multiply,
                    CUpdateOperator::Divide => crate::kernel::UpdateOperator::Divide,
                    CUpdateOperator::Remainder => crate::kernel::UpdateOperator::Remainder,
                    CUpdateOperator::ShiftLeft => crate::kernel::UpdateOperator::ShiftLeft,
                    CUpdateOperator::ShiftRight => crate::kernel::UpdateOperator::ShiftRight,
                    CUpdateOperator::BitwiseAnd => crate::kernel::UpdateOperator::BitwiseAnd,
                    CUpdateOperator::BitwiseOr => crate::kernel::UpdateOperator::BitwiseOr,
                    CUpdateOperator::BitwiseXor => crate::kernel::UpdateOperator::BitwiseXor,
                },
                operand.to_kernel_expression(),
            ),
            Self::While {
                test,
                condition,
                body,
                ..
            } => crate::kernel::program_while(
                condition.to_kernel_expression(),
                Vec::new(),
                body.to_kernel_statement_with_control_targets(targets),
            )
            .with_optional_loop_test(
                test.as_ref()
                    .map(|test| test.to_kernel_statement_with_control_targets(targets)),
                crate::kernel::LoopTestPosition::BeforeBody,
            ),
            Self::DoWhile {
                test,
                condition,
                body,
                ..
            } => crate::kernel::program_do_while(
                condition.to_kernel_expression(),
                body.to_kernel_statement_with_control_targets(targets),
            )
            .with_optional_loop_test(
                test.as_ref()
                    .map(|test| test.to_kernel_statement_with_control_targets(targets)),
                crate::kernel::LoopTestPosition::AfterBody,
            ),
            Self::For {
                test,
                initializer,
                condition,
                step,
                body,
                ..
            } => {
                let step = step.to_kernel_statement_with_control_targets(targets);
                crate::kernel::program_seq(
                    initializer.to_kernel_statement_with_control_targets(targets),
                    crate::kernel::program_while(
                        condition.to_kernel_expression(),
                        Vec::new(),
                        body.to_kernel_statement_with_control_targets(targets),
                    )
                    .with_loop_update(step)
                    .with_optional_loop_test(
                        test.as_ref()
                            .map(|test| test.to_kernel_statement_with_control_targets(targets)),
                        crate::kernel::LoopTestPosition::BeforeBody,
                    ),
                )
            }
            Self::Switch {
                expression, cases, ..
            } => crate::kernel::program_switch(
                expression.to_kernel_expression(),
                cases
                    .iter()
                    .map(|case| crate::kernel::SwitchCase {
                        value: case.value,
                        body: Box::new(case.body.to_kernel_statement_with_control_targets(targets)),
                    })
                    .collect(),
            ),
        }
    }
}

impl CExpression {
    /// Lowers an expression a Click specification wrote in C syntax. Its
    /// integer casts convert modulo 2^N, as the same cast in C source does;
    /// a specification states a checked conversion with `to_T(...)`.
    pub fn to_kernel_specification_expression(&self) -> crate::kernel::ProgramExpression {
        self.lower_expression()
    }

    pub fn to_kernel_expression(&self) -> crate::kernel::ProgramExpression {
        self.lower_expression()
    }

    fn lower_expression(&self) -> crate::kernel::ProgramExpression {
        match self {
            Self::StringLiteral(literal) => crate::kernel::ProgramExpression::StringLiteral(
                literal
                    .identity
                    .clone()
                    .expect("runtime string literal belongs to a function"),
            ),
            Self::StepResult { step, origin, .. } => crate::kernel::ProgramExpression::StepResult {
                step: *step,
                origin: origin.clone(),
                ends: true,
            },
            Self::Void => crate::kernel::program_void_value(),
            Self::Variable(name) if name.is_named(HOSTED_STDOUT_BINDING) => {
                crate::kernel::ProgramExpression::Value(hosted_stdout_value())
            }
            Self::Variable(name) => crate::kernel::program_expression::variable(name.clone()),
            Self::Call { .. } => {
                unreachable!("call expressions must be lowered before kernel conversion")
            }
            Self::IndirectCall { .. } => {
                unreachable!("indirect call expressions must be lowered before kernel conversion")
            }
            Self::Assignment { .. } | Self::ScalarUpdate { .. } => {
                unreachable!("assignment expressions must be lowered before kernel conversion")
            }
            Self::StatementExpression { .. } => {
                unreachable!("statement expressions must be lowered before kernel conversion")
            }
            Self::FunctionAddress(name) => {
                crate::kernel::program_expression::function_address(name.clone())
            }
            Self::Cast {
                expression,
                interface_type,
                struct_name,
                pointee_volatile,
                pointee_constant,
                explicit_qualification,
            } => {
                let cast = if *explicit_qualification {
                    crate::kernel::program_expression::c_source_cast_with_pointee_qualifiers_and_struct
                } else {
                    crate::kernel::program_expression::cast_with_pointee_qualifiers_and_struct
                };
                let lowered = cast(
                    expression.lower_expression(),
                    interface_type.to_kernel_type(),
                    *pointee_volatile,
                    *pointee_constant,
                    struct_name.clone(),
                );
                // A C cast converts modulo 2^N wherever it is written,
                // in C source or in a specification.
                crate::kernel::program_expression::c_source_integer_conversion(lowered)
            }
            Self::Ternary {
                condition,
                then_branch,
                else_branch,
            } => crate::kernel::program_expression::conditional(
                condition.lower_expression(),
                then_branch.lower_expression(),
                else_branch.lower_expression(),
            ),
            Self::FloatNegate(expression) => {
                crate::kernel::program_expression::float_negate(expression.lower_expression())
            }
            Self::FloatClassification {
                expression,
                classification,
            } => crate::kernel::program_expression::float_classification(
                expression.lower_expression(),
                match classification {
                    CFloatClassification::Finite => crate::kernel::FloatClassification::Finite,
                    CFloatClassification::Infinite => crate::kernel::FloatClassification::Infinite,
                    CFloatClassification::Zero => crate::kernel::FloatClassification::Zero,
                    CFloatClassification::Subnormal => {
                        crate::kernel::FloatClassification::Subnormal
                    }
                    CFloatClassification::Nan => crate::kernel::FloatClassification::Nan,
                },
            ),
            Self::AddressOf(target) => match target.as_ref() {
                Self::AggregateAddress { pointer, .. } | Self::UnionAddress { pointer, .. } => {
                    pointer.lower_expression()
                }
                target => {
                    crate::kernel::ProgramExpression::AddressOf(Box::new(target.lower_expression()))
                }
            },
            Self::AggregateAddress { pointer, .. } => pointer.lower_expression(),
            Self::UnionAddress { pointer, .. } => pointer.lower_expression(),
            Self::PointerOffsetBytes { pointer, bytes } => {
                crate::kernel::program_expression::pointer_offset_bytes(
                    pointer.lower_expression(),
                    *bytes,
                )
            }
            Self::Subobject { pointer, width } => crate::kernel::ProgramExpression::Subobject {
                pointer: Box::new(pointer.lower_expression()),
                width: *width,
            },
            Self::Int32Literal(value) => crate::kernel::program_expression::int32_literal(*value),
            Self::UInt8Literal(value) => crate::kernel::program_expression::uint8_literal(*value),
            Self::UInt32Literal(value) => crate::kernel::program_expression::uint32_literal(*value),
            Self::Int64Literal(value) => crate::kernel::program_expression::int64_literal(*value),
            Self::UInt64Literal(value) => crate::kernel::program_expression::uint64_literal(*value),
            Self::Float32Literal(bits) => crate::kernel::program_expression::float32_literal(*bits),
            Self::Float64Literal(bits) => crate::kernel::program_expression::float64_literal(*bits),
            Self::SizeOfStruct { bytes, .. } | Self::SizeOfType { bytes, .. } => {
                crate::kernel::program_expression::uint64_literal(u64::from(*bytes))
            }
            Self::SizeOfUnion { bytes, .. } => {
                crate::kernel::program_expression::uint64_literal(u64::from(*bytes))
            }
            Self::LessThan(left, right) => crate::kernel::program_expression::less_than(
                left.lower_expression(),
                right.lower_expression(),
            ),
            Self::LessEqual(left, right) => crate::kernel::program_expression::less_equal(
                left.lower_expression(),
                right.lower_expression(),
            ),
            Self::GreaterThan(left, right) => crate::kernel::program_expression::greater_than(
                left.lower_expression(),
                right.lower_expression(),
            ),
            Self::GreaterEqual(left, right) => crate::kernel::program_expression::greater_equal(
                left.lower_expression(),
                right.lower_expression(),
            ),
            Self::Equal(left, right) => crate::kernel::program_expression::equal(
                left.lower_expression(),
                right.lower_expression(),
            ),
            Self::NotEqual(left, right) => crate::kernel::program_expression::not_equal(
                left.lower_expression(),
                right.lower_expression(),
            ),
            Self::Not(expression) => {
                crate::kernel::program_expression::not(expression.lower_expression())
            }
            Self::And(left, right) => crate::kernel::program_expression::and(
                left.lower_expression(),
                right.lower_expression(),
            ),
            Self::Or(left, right) => crate::kernel::program_expression::or(
                left.lower_expression(),
                right.lower_expression(),
            ),
            Self::Add(left, right) => crate::kernel::program_expression::add(
                left.lower_expression(),
                right.lower_expression(),
            ),
            Self::Subtract(left, right) => crate::kernel::program_expression::subtract(
                left.lower_expression(),
                right.lower_expression(),
            ),
            Self::Multiply(left, right) => crate::kernel::program_expression::multiply(
                left.lower_expression(),
                right.lower_expression(),
            ),
            Self::Divide(left, right) => crate::kernel::program_expression::divide(
                left.lower_expression(),
                right.lower_expression(),
            ),
            Self::Remainder(left, right) => crate::kernel::program_expression::remainder(
                left.lower_expression(),
                right.lower_expression(),
            ),
            Self::ShiftLeft(left, right) => crate::kernel::program_expression::shift_left(
                left.lower_expression(),
                right.lower_expression(),
            ),
            Self::ShiftRight(left, right) => crate::kernel::program_expression::shift_right(
                left.lower_expression(),
                right.lower_expression(),
            ),
            Self::BitwiseAnd(left, right) => crate::kernel::program_expression::bitwise_and(
                left.lower_expression(),
                right.lower_expression(),
            ),
            Self::BitwiseOr(left, right) => crate::kernel::program_expression::bitwise_or(
                left.lower_expression(),
                right.lower_expression(),
            ),
            Self::BitwiseXor(left, right) => crate::kernel::program_expression::bitwise_xor(
                left.lower_expression(),
                right.lower_expression(),
            ),
            Self::BitwiseNot(expression) => {
                crate::kernel::program_expression::bitwise_not(expression.lower_expression())
            }
            Self::Load(pointer, None) => {
                crate::kernel::program_expression::load(pointer.lower_expression())
            }
            Self::Load(pointer, Some(loaded_type)) => {
                crate::kernel::program_expression::classed_load(
                    pointer.lower_expression(),
                    loaded_type.interface_type.to_kernel_type(),
                    Some(loaded_type.class.clone()),
                )
            }
            Self::SequentialRead {
                target,
                interface_type,
                pointee_constant,
                ..
            } => crate::kernel::program_expression::qualified_volatile_typed_load(
                CExpression::AddressOf(Box::new(target.as_ref().clone())).lower_expression(),
                interface_type.to_kernel_type(),
                *pointee_constant,
            ),
            Self::SequentialWrite { .. } => {
                unreachable!(
                    "sequential write expressions must be lowered before kernel conversion"
                )
            }
            Self::Field {
                pointer,
                field_type,
                pointee_constant,
                source,
                access_class,
                ..
            } => crate::kernel::program_expression::qualified_typed_load_with_source(
                pointer.lower_expression(),
                field_type.to_kernel_type(),
                *pointee_constant,
                access_class.clone(),
                source.as_ref().and_then(|source| {
                    source.id().source_identity().map(|source_identity| {
                        crate::kernel::LoadSourceId {
                            owner: crate::kernel::LoadSourceOwnerId {
                                source_unit: std::sync::Arc::from(source_identity),
                                function: std::sync::Arc::from(source.id().function_name()),
                            },
                            occurrence: source.id().occurrence(),
                            reference_access: None,
                        }
                    })
                }),
            ),
            Self::UnionField {
                pointer,
                field_type,
                ..
            } => crate::kernel::program_expression::typed_load(
                pointer.lower_expression(),
                field_type.to_kernel_type(),
            ),
            Self::Index(base, index, None) => crate::kernel::program_expression::index(
                base.lower_expression(),
                index.lower_expression(),
            ),
            // The kernel evaluates `base[index]` as the lvalue at
            // `base + index`; a typed load of that address is the same access
            // with the class the kernel type cannot give.
            Self::Index(base, index, Some(element_type)) => {
                crate::kernel::program_expression::classed_load(
                    crate::kernel::program_expression::add(
                        base.lower_expression(),
                        index.lower_expression(),
                    ),
                    element_type.interface_type.to_kernel_type(),
                    Some(element_type.class.clone()),
                )
            }
            Self::CheckedArrayIndex { index, .. } => index.lower_expression(),
        }
    }
}

impl CSyntaxError {
    fn new(message: impl Into<String>) -> Self {
        Self {
            limit_exceeded: false,
            message: message.into(),
            position: None,
        }
    }

    fn at(position: SourcePosition, message: impl Into<String>) -> Self {
        Self {
            limit_exceeded: false,
            message: message.into(),
            position: Some(position),
        }
    }

    /// Attaches `position` if the error does not already carry one.
    fn with_position(mut self, position: SourcePosition) -> Self {
        self.position.get_or_insert(position);
        self
    }

    /// The parser stopped at a run limit rather than rejecting C syntax.
    pub(crate) fn limit_exceeded(&self) -> bool {
        self.limit_exceeded
    }

    pub fn message(&self) -> &str {
        &self.message
    }

    pub fn position(&self) -> Option<SourcePosition> {
        self.position.clone()
    }
}

impl std::fmt::Display for CSyntaxError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self.position {
            Some(position) => write!(f, "{position}: {}", self.message),
            None => write!(f, "{}", self.message),
        }
    }
}

pub fn parse_function(source: &str) -> Result<ImportedFunction, CSyntaxError> {
    parse_function_for_abi(source, CAbi::SUPPORTED)
}

pub fn parse_function_for_abi(source: &str, abi: CAbi) -> Result<ImportedFunction, CSyntaxError> {
    Parser::new(source, abi)?.parse_function()
}

/// Parses every function definition in one C source. Prototypes are accepted
/// as declarations and are used to validate later definitions, but are not
/// returned as executable functions.
pub fn parse_functions(source: &str) -> Result<Vec<ImportedFunction>, CSyntaxError> {
    parse_functions_for_abi(source, CAbi::SUPPORTED)
}

#[derive(Clone)]
pub(crate) struct CTranslationUnit {
    pub functions: Vec<ImportedFunction>,
    pub function_declarations: BTreeMap<String, CFunctionHeader>,
    pub function_declaration_lines: BTreeMap<String, Vec<usize>>,
    pub builtin_pthread_declarations: BTreeSet<String>,
    pub shadowed_pthread_names: BTreeSet<String>,
    pub structs: DeclarationMap<RecordLayout>,
    pub unions: DeclarationMap<CUnionLayout>,
    pub globals: DeclarationMap<CGlobal>,
    pub global_arrays: DeclarationMap<CGlobalArray>,
    pub global_aggregates: DeclarationMap<CGlobalAggregate>,
    pub global_aggregate_arrays: DeclarationMap<CGlobalAggregateArray>,
    /// External objects named in value or address positions by this unit.
    pub referenced_external_objects: BTreeSet<String>,
    /// The typedef names a function head may write for their types.
    pub head_typedefs: BTreeMap<String, CHeadTypedef>,
}

/// The type a typedef name stands for where a function head writes it:
/// `typedef unsigned int u32;`, `typedef const char *name_t;`,
/// `typedef struct node node_t;` or `typedef struct node *node_ptr;`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum CHeadTypedef {
    /// A scalar type, or a pointer to one.
    Scalar {
        interface_type: InterfaceType,
        constant: bool,
        pointee_constant: bool,
    },
    /// A struct type, `Int32`, or a pointer to one, `Int32Pointer` or
    /// `Int32PointerPointer`.
    Struct {
        name: String,
        interface_type: InterfaceType,
        constant: bool,
        pointee_constant: bool,
    },
    /// A function pointer, `typedef int (*unary)(int);`, with its signature.
    FunctionPointer {
        interface_type: InterfaceType,
        signature: CallbackInterface,
    },
    /// A scalar array, `typedef int triple[3];`: its element type, possibly
    /// `const`, and length.
    Array {
        element: InterfaceType,
        length: u32,
        constant: bool,
    },
    /// An alias of a union, or a volatile, aligned or extended-precision
    /// type, which a head writes as its type, or one that two verified
    /// sources give different types.
    Other,
}

impl CHeadTypedef {
    fn of(parsed: &ParsedType) -> Self {
        Self::restated(parsed).unwrap_or(Self::Other)
    }

    fn restated(parsed: &ParsedType) -> Option<Self> {
        if let (InterfaceType::FunctionPointer(_), Some(signature)) =
            (parsed.interface_type, &parsed.function_pointer_signature)
            && !parsed.is_volatile
            && parsed.volatile_levels == 0
            && !parsed.is_constant
        {
            return Some(Self::FunctionPointer {
                interface_type: parsed.interface_type,
                signature: signature.clone(),
            });
        }
        if let Some(length) = parsed.interface_type.array_length()
            && let Some(element) = parsed.interface_type.pointee_type()
            && !parsed.is_volatile
            && parsed.volatile_levels == 0
            && !parsed.long_double
            && !parsed.aligned_typedef
            && !parsed.opaque_builtin
            && parsed.struct_name.is_none()
            && parsed.union_name.is_none()
        {
            return Some(Self::Array {
                element,
                length,
                constant: parsed.is_constant,
            });
        }
        if parsed.long_double
            || parsed.aligned_typedef
            || parsed.opaque_builtin
            || parsed.function_pointer_signature.is_some()
            || parsed.union_name.is_some()
            || parsed.volatile_levels != 0
            || parsed.is_volatile
            || matches!(parsed.interface_type, InterfaceType::FunctionPointer(_))
            // An array has an element type but is not a pointer.
            || (!parsed.interface_type.is_pointer() && parsed.interface_type.pointee_type().is_some())
        {
            return None;
        }
        Some(match &parsed.struct_name {
            Some(name) => Self::Struct {
                name: name.clone(),
                interface_type: parsed.interface_type,
                constant: parsed.is_constant,
                pointee_constant: parsed.pointee_constant,
            },
            None => Self::Scalar {
                interface_type: parsed.interface_type,
                constant: parsed.is_constant,
                pointee_constant: parsed.pointee_constant,
            },
        })
    }
}

/// [`parse_translation_unit_for_target`] under the default target.
#[cfg(test)]
pub(crate) fn parse_translation_unit_for_source(
    source: &str,
    source_identity: &str,
    line_map: &ExpandedLineMap,
) -> Result<CTranslationUnit, CSyntaxError> {
    parse_translation_unit_for_target(
        source,
        source_identity,
        line_map,
        super::target::CTarget::SUPPORTED,
    )
}

/// Parses one expanded source-bundle translation unit under `target`, whose
/// ABI and plain `char` signedness its types take.
pub(crate) fn parse_translation_unit_for_target(
    source: &str,
    source_identity: &str,
    line_map: &ExpandedLineMap,
    target: super::target::CTarget,
) -> Result<CTranslationUnit, CSyntaxError> {
    let mut unit = Parser::new_with_source_identity_and_line_map(
        source,
        target.abi(),
        Some(source_identity),
        line_map,
    )?
    .with_target(target)
    .parse_translation_unit()?;
    unit.builtin_pthread_declarations = unit
        .function_declaration_lines
        .iter()
        .filter(|(_, lines)| {
            lines
                .iter()
                .any(|line| line_map.is_builtin_pthread_line(*line))
        })
        .map(|(name, _)| name.clone())
        .collect();
    Ok(unit)
}

/// Parses compiler-preprocessed C while retaining original file/line
/// locations from validated line markers. `source_identity` remains the
/// translation-unit linkage identity and is deliberately independent of the
/// diagnostic origin filename.
#[cfg(test)]
pub(crate) fn parse_translation_unit_for_import(
    source: &str,
    source_identity: &str,
    map: &CSourceMap,
    promises: PromiseAttributes,
) -> Result<CTranslationUnit, CSyntaxError> {
    parse_translation_unit_for_import_target(
        source,
        source_identity,
        map,
        promises,
        super::target::CTarget::SUPPORTED,
    )
}

/// Parses compiler-preprocessed C under the import's target, retaining
/// original file/line locations from validated line markers.
pub(crate) fn parse_translation_unit_for_import_target(
    source: &str,
    source_identity: &str,
    map: &CSourceMap,
    promises: PromiseAttributes,
    target: super::target::CTarget,
) -> Result<CTranslationUnit, CSyntaxError> {
    let mut parser =
        Parser::new_with_source_identity_and_map(source, target.abi(), Some(source_identity), map)?
            .with_target(target);
    parser.refuse_promises = promises == PromiseAttributes::Refuse;
    parser.parse_translation_unit()
}

/// Whether a compiler import accepts the function attributes and qualifiers
/// that GCC's optimizer trusts as programmer promises. Click checks none of
/// those promises. Without optimization GCC does not act on them, so they
/// are accepted and ignored; under an option profile that accepts `-O2` they
/// are refused. The GCC 13 measurements behind the list are in
/// `docs/reference/cli/import.md`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PromiseAttributes {
    Accept,
    Refuse,
}

/// Why an otherwise accepted function attribute is refused when GCC
/// optimizes. Attributes the frontend refuses in every mode (`pure`,
/// `malloc`, `returns_nonnull`, `alloc_size`, `assume_aligned`, ...) are not
/// listed.
fn optimizer_promise(attribute: &str) -> Option<&'static str> {
    Some(match attribute {
        "nonnull" | "__nonnull__" => {
            "GCC at -O2 deletes the parameter's null checks even with -fno-delete-null-pointer-checks, and Click does not check the promise"
        }
        "const" | "__const__" => {
            "GCC at -O2 merges calls and assumes the function touches no memory, and Click does not check the promise"
        }
        "leaf" | "__leaf__" => {
            "GCC at -O2 assumes the call leaves this unit's unescaped static data unchanged, and Click does not check the promise"
        }
        "access" | "__access__" => {
            "it promises how the function accesses the pointed-to object, and Click does not check the promise"
        }
        "noreturn" | "__noreturn__" => {
            "GCC emits nothing after a call to it, and Click proves calls unreachable only for `compiletime_assert`'s error declarations"
        }
        "returns_twice" | "__returns_twice__" => {
            "a second return from a call needs a control-flow model that Click does not have"
        }
        _ => return None,
    })
}

#[cfg(test)]
pub(crate) fn parse_functions_for_source(
    source: &str,
    source_identity: &str,
) -> Result<Vec<ImportedFunction>, CSyntaxError> {
    Parser::new_with_source_identity(source, CAbi::SUPPORTED, Some(source_identity))?
        .parse_functions()
}

/// [`parse_functions`] under `target`, whose plain `char` signedness its
/// types take.
#[cfg(test)]
pub(crate) fn parse_functions_for_target(
    source: &str,
    target: super::target::CTarget,
) -> Result<Vec<ImportedFunction>, CSyntaxError> {
    Parser::new(source, target.abi())?
        .with_target(target)
        .parse_functions()
}

pub fn parse_functions_for_abi(
    source: &str,
    abi: CAbi,
) -> Result<Vec<ImportedFunction>, CSyntaxError> {
    Parser::new(source, abi)?.parse_functions()
}

/// Validates a C header after its includes have been expanded. Headers may
/// contain type declarations, prototypes, and supported `static inline` or
/// `static __always_inline` bodies; other function definitions are rejected.
/// `line_map` attributes diagnostics to the bundle header lines behind the
/// expanded text.
pub fn validate_header(source: &str, line_map: &ExpandedLineMap) -> Result<(), CSyntaxError> {
    validate_header_for_target(source, line_map, super::target::CTarget::SUPPORTED)
}

/// [`validate_header`] under `target`.
pub fn validate_header_for_target(
    source: &str,
    line_map: &ExpandedLineMap,
    target: super::target::CTarget,
) -> Result<(), CSyntaxError> {
    Parser::new_with_source_identity_and_line_map(source, target.abi(), None, line_map)?
        .with_target(target)
        .parse_header()
}

fn validate_function_returns(
    statement: &CStatement,
    return_type: InterfaceType,
) -> Result<(), CSyntaxError> {
    match statement {
        CStatement::Return(CExpression::Void, _) if return_type != InterfaceType::Void => {
            Err(CSyntaxError::new("non-void functions must return a value"))
        }
        CStatement::Return(CExpression::Void, _) => Ok(()),
        CStatement::Return(_, _) if return_type == InterfaceType::Void => {
            Err(CSyntaxError::new("void functions cannot return a value"))
        }
        CStatement::Seq(first, second) => {
            validate_function_returns(first, return_type)?;
            validate_function_returns(second, return_type)
        }
        CStatement::If {
            then_branch,
            else_branch,
            ..
        } => {
            validate_function_returns(then_branch, return_type)?;
            validate_function_returns(else_branch, return_type)
        }
        CStatement::While { test, body, .. }
        | CStatement::DoWhile { test, body, .. }
        | CStatement::For { test, body, .. } => {
            if let Some(test) = test {
                validate_function_returns(test, return_type)?;
            }
            validate_function_returns(body, return_type)
        }
        CStatement::Switch { cases, .. } => cases
            .iter()
            .try_for_each(|case| validate_function_returns(&case.body, return_type)),
        CStatement::Label { statement, .. } => validate_function_returns(statement, return_type),
        CStatement::EndAggregateLifetimes { .. }
        | CStatement::FillArrayTail { .. }
        | CStatement::Skip
        | CStatement::Break
        | CStatement::Continue
        | CStatement::Goto { .. }
        | CStatement::Declare { .. }
        | CStatement::DeclareStructValue { .. }
        | CStatement::Assign { .. }
        | CStatement::Call { .. }
        | CStatement::CallResult { .. }
        | CStatement::IndirectCall { .. }
        | CStatement::HeapAllocate { .. }
        | CStatement::HeapFree { .. }
        | CStatement::Return(_, _)
        | CStatement::Store { .. }
        | CStatement::SequentialStore { .. }
        | CStatement::AggregateCopy { .. }
        | CStatement::Update { .. }
        | CStatement::Assert { .. }
        | CStatement::StepValue { .. }
        | CStatement::LoopTest { .. } => Ok(()),
    }
}

pub(crate) fn flatten_direct_c_statements<'a>(
    statement: &'a CStatement,
    statements: &mut Vec<&'a CStatement>,
) {
    match statement {
        CStatement::Seq(first, second) => {
            flatten_direct_c_statements(first, statements);
            flatten_direct_c_statements(second, statements);
        }
        statement => statements.push(statement),
    }
}

/// Counts source statement regions using the same preorder as Surface
/// execution. A control target needs this index rather than its ordinal among
/// direct function-body statements: an `if` contributes regions for the
/// condition and both arms before its continuation.
fn c_source_statement_width(statement: &CStatement) -> usize {
    match statement {
        CStatement::Seq(first, second) => {
            c_source_statement_width(first) + c_source_statement_width(second)
        }
        CStatement::If {
            then_branch,
            else_branch,
            ..
        } => 1 + c_source_statement_width(then_branch) + c_source_statement_width(else_branch),
        CStatement::While { test, body, .. } | CStatement::DoWhile { test, body, .. } => {
            1 + c_source_statement_width(body)
                + test
                    .as_ref()
                    .map_or(0, |test| c_source_statement_width(test))
        }
        CStatement::For {
            test,
            initializer,
            step,
            body,
            ..
        } => {
            c_source_statement_width(initializer)
                + 1
                + c_source_statement_width(body)
                + c_source_statement_width(step)
                + test
                    .as_ref()
                    .map_or(0, |test| c_source_statement_width(test))
        }
        // Switch is one source region in the current Surface layout. Goto
        // functions reject it below, but keeping the count aligned avoids a
        // second definition of source indexing.
        _ => 1,
    }
}

fn control_statement_error(
    position: &Option<SourcePosition>,
    message: impl Into<String>,
) -> CSyntaxError {
    match position {
        Some(position) => CSyntaxError::at(position.clone(), message),
        None => CSyntaxError::new(message),
    }
}

/// Resolves the deliberately narrow goto slice after the complete function
/// body is available. Targets remain direct function-body labels; jumps may
/// also originate in `if` arms. Ordinary accepted edges point forward, with
/// one reducible natural-cycle exception checked below.
fn validate_direct_forward_gotos(
    body: &CStatement,
) -> Result<BTreeMap<String, (crate::kernel::ControlTargetId, usize)>, CSyntaxError> {
    fn first_control_position(statement: &CStatement) -> Option<Option<SourcePosition>> {
        let mut pending = vec![statement];
        while let Some(statement) = pending.pop() {
            match statement {
                CStatement::Goto { position, .. } | CStatement::Label { position, .. } => {
                    return Some(position.clone());
                }
                CStatement::Seq(first, second)
                | CStatement::If {
                    then_branch: first,
                    else_branch: second,
                    ..
                } => {
                    pending.push(second);
                    pending.push(first);
                }
                CStatement::While { test, body, .. } | CStatement::DoWhile { test, body, .. } => {
                    pending.push(body);
                    if let Some(test) = test {
                        pending.push(test);
                    }
                }
                CStatement::For {
                    test,
                    initializer,
                    step,
                    body,
                    ..
                } => {
                    pending.push(step);
                    pending.push(body);
                    pending.push(initializer);
                    if let Some(test) = test {
                        pending.push(test);
                    }
                }
                CStatement::Switch { cases, .. } => {
                    pending.extend(cases.iter().rev().map(|case| case.body()));
                }
                _ => {}
            }
        }
        None
    }

    let Some(control_position) = first_control_position(body) else {
        return Ok(BTreeMap::new());
    };

    let mut statements = Vec::new();
    flatten_direct_c_statements(body, &mut statements);
    // A loop or switch may precede every label, as when `goto out;` skips
    // the loops that do a function's work. It is then either run in full
    // or jumped over, so a jump never enters, leaves, or re-enters it.
    let first_label = statements
        .iter()
        .position(|statement| matches!(statement, CStatement::Label { .. }))
        .unwrap_or(statements.len());
    for (index, statement) in statements.iter().enumerate() {
        if !matches!(
            statement,
            CStatement::While { .. }
                | CStatement::DoWhile { .. }
                | CStatement::For { .. }
                | CStatement::Switch { .. }
        ) {
            continue;
        }
        if index > first_label {
            return Err(control_statement_error(
                &control_position,
                "the goto slice supports loops and switches only before every label",
            ));
        }
        if let Some(position) = first_control_position(statement) {
            return Err(control_statement_error(
                &position,
                "the goto slice does not support labels or jumps inside loops or switches",
            ));
        }
    }

    #[derive(Clone)]
    struct PendingGoto {
        target: String,
        position: Option<SourcePosition>,
        direct_statement_index: usize,
    }

    fn collect_if_arm_gotos(
        statement: &CStatement,
        direct_statement_index: usize,
        gotos: &mut Vec<PendingGoto>,
    ) -> Result<(), CSyntaxError> {
        match statement {
            CStatement::Goto {
                target, position, ..
            } => gotos.push(PendingGoto {
                target: target.clone(),
                position: position.clone(),
                direct_statement_index,
            }),
            CStatement::Label { position, .. } => {
                return Err(control_statement_error(
                    position,
                    "goto labels must be direct function-body statements",
                ));
            }
            CStatement::Seq(first, second) => {
                collect_if_arm_gotos(first, direct_statement_index, gotos)?;
                collect_if_arm_gotos(second, direct_statement_index, gotos)?;
            }
            CStatement::If {
                then_branch,
                else_branch,
                ..
            } => {
                collect_if_arm_gotos(then_branch, direct_statement_index, gotos)?;
                collect_if_arm_gotos(else_branch, direct_statement_index, gotos)?;
            }
            CStatement::While { .. }
            | CStatement::DoWhile { .. }
            | CStatement::For { .. }
            | CStatement::Switch { .. } => {
                return Err(control_statement_error(
                    &first_control_position(statement).flatten(),
                    "the conditional goto slice does not support jumps inside loops or switches",
                ));
            }
            _ => {}
        }
        Ok(())
    }

    let natural_cycle_shape = matches!(
        statements.first(),
        Some(CStatement::Label {
            direct_function_body: true,
            ..
        })
    ) && (matches!(
        statements.last(),
        Some(CStatement::Goto {
            direct_function_body: true,
            ..
        })
    ) || matches!(
        statements.first(),
        Some(CStatement::Label { statement, .. })
            if natural_cycle_statement_contains_goto(statement)
    ) || (matches!(
        statements.last(),
        Some(CStatement::Label {
            direct_function_body: true,
            ..
        })
    ) && statements.len() > 2
        && matches!(
            statements.first(),
            Some(CStatement::Label { statement, .. })
                if natural_cycle_statement_contains_goto(statement)
        )));
    let mut labels = BTreeMap::new();
    let mut gotos = Vec::new();
    let mut source_statement_index = 0;
    for (index, statement) in statements.iter().enumerate() {
        match statement {
            CStatement::Goto {
                target,
                position,
                direct_function_body,
            } => {
                if !direct_function_body {
                    return Err(control_statement_error(
                        position,
                        "goto statements must be direct function-body statements or occur inside an `if` arm",
                    ));
                }
                gotos.push(PendingGoto {
                    target: target.clone(),
                    position: position.clone(),
                    direct_statement_index: index,
                });
            }
            CStatement::Label {
                name,
                statement,
                position,
                direct_function_body,
            } => {
                if !direct_function_body {
                    return Err(control_statement_error(
                        position,
                        "goto labels must be direct function-body statements",
                    ));
                }
                // Outside a natural cycle, a label may also govern an `if`
                // without control statements of its own, as in Linux's
                // `out: if (...) unit = "UNK"; else ...`.
                let forward_if = !natural_cycle_shape
                    && matches!(statement.as_ref(), CStatement::If { .. })
                    && natural_cycle_statement_supported(statement)
                    && !natural_cycle_statement_contains_goto(statement);
                if matches!(
                    statement.as_ref(),
                    CStatement::Seq(..)
                        | CStatement::If { .. }
                        | CStatement::While { .. }
                        | CStatement::DoWhile { .. }
                        | CStatement::For { .. }
                        | CStatement::Switch { .. }
                        | CStatement::Goto { .. }
                        | CStatement::Label { .. }
                ) && !forward_if
                    && !(natural_cycle_shape
                        && ((index == 0 && natural_cycle_statement_supported(statement))
                            || (index + 1 == statements.len()
                                && matches!(statements.last(), Some(CStatement::Label { .. }))
                                && natural_cycle_statement_supported(statement)
                                && !natural_cycle_statement_contains_goto(statement))))
                {
                    return Err(control_statement_error(
                        position,
                        "the goto slice requires a label to govern one ordinary statement",
                    ));
                }
                if natural_cycle_shape && index == 0 {
                    collect_if_arm_gotos(statement, index, &mut gotos)?;
                }
                if labels
                    .insert(
                        name.clone(),
                        (index, source_statement_index, position.clone()),
                    )
                    .is_some()
                {
                    return Err(control_statement_error(
                        position,
                        format!("duplicate label `{name}`"),
                    ));
                }
            }
            CStatement::If {
                then_branch,
                else_branch,
                ..
            } => {
                collect_if_arm_gotos(then_branch, index, &mut gotos)?;
                collect_if_arm_gotos(else_branch, index, &mut gotos)?;
            }
            _ => {}
        }
        // A labeled statement has its body's source regions; the natural
        // cycle layout instead gives its entry label one region.
        source_statement_index += match statement {
            CStatement::Label { statement, .. } if !natural_cycle_shape => {
                c_source_statement_width(statement)
            }
            statement => c_source_statement_width(statement),
        };
    }

    let mut targets = BTreeMap::new();
    for (ordinal, (name, (_, source_index, _))) in labels.iter().enumerate() {
        let identity = u32::try_from(ordinal)
            .map(crate::kernel::ControlTargetId)
            .map_err(|_| CSyntaxError::new("too many control-flow labels"))?;
        targets.insert(name.clone(), (identity, *source_index));
    }
    let goto_count = gotos.len();
    let mut backward_gotos = Vec::new();
    let mut forward_gotos = Vec::new();
    for pending in gotos {
        let Some((target_index, _, _)) = labels.get(&pending.target) else {
            return Err(control_statement_error(
                &pending.position,
                format!("unknown goto label `{}`", pending.target),
            ));
        };
        if *target_index <= pending.direct_statement_index {
            backward_gotos.push((pending, *target_index));
            continue;
        }
        forward_gotos.push((pending.clone(), *target_index));
        if statements[pending.direct_statement_index + 1..*target_index]
            .iter()
            .any(|statement| {
                matches!(
                    statement,
                    CStatement::Declare { .. } | CStatement::DeclareStructValue { .. }
                )
            })
        {
            return Err(control_statement_error(
                &pending.position,
                format!(
                    "goto to `{}` would bypass a local declaration",
                    pending.target
                ),
            ));
        }
    }
    let natural_label_contains_goto = matches!(
        statements.first(),
        Some(CStatement::Label { statement, .. })
            if natural_cycle_statement_contains_goto(statement)
    );
    if natural_label_contains_goto || !backward_gotos.is_empty() {
        let explicit_exit_shape = natural_cycle_shape
            && statements.len() > 2
            && matches!(statements.last(), Some(CStatement::Label { .. }))
            && !backward_gotos.is_empty()
            && !forward_gotos.is_empty()
            && goto_count == backward_gotos.len() + forward_gotos.len()
            && labels.len() == 2
            && backward_gotos
                .iter()
                .all(|(_, target_index)| *target_index == 0)
            && forward_gotos
                .iter()
                .all(|(_, target_index)| *target_index + 1 == statements.len())
            && matches!(
                statements.first(),
                Some(CStatement::Label { statement, .. })
                    if natural_cycle_statement_supported(statement)
            )
            && statements[1..statements.len() - 1]
                .iter()
                .all(|statement| natural_cycle_statement_supported(statement))
            && matches!(
                statements.last(),
                Some(CStatement::Label { statement, .. })
                    if natural_cycle_statement_supported(statement)
                        && !natural_cycle_statement_contains_goto(statement)
            );
        let supported = natural_cycle_shape
            && ((!backward_gotos.is_empty()
                && forward_gotos.is_empty()
                && goto_count == backward_gotos.len()
                && labels.len() == 1
                && backward_gotos
                    .iter()
                    .all(|(_, target_index)| *target_index == 0)
                && matches!(
                    statements.first(),
                    Some(CStatement::Label { statement, .. })
                        if natural_cycle_statement_supported(statement)
                )
                && statements[1..]
                    .iter()
                    .all(|statement| natural_cycle_statement_supported(statement)))
                || explicit_exit_shape);
        if !supported {
            let position = backward_gotos
                .first()
                .map(|(pending, _)| pending.position.clone())
                .unwrap_or_else(|| control_position.clone());
            let message = backward_gotos
                .first()
                .map(|(pending, _)| {
                    format!(
                        "backward goto to `{}` is not a supported natural cycle",
                        pending.target
                    )
                })
                .unwrap_or_else(|| "nested goto is not a supported natural cycle".into());
            return Err(control_statement_error(&position, message));
        }
    }
    Ok(targets)
}

fn statement_contains_control_transfer(statement: &CStatement) -> bool {
    match statement {
        CStatement::Break
        | CStatement::LoopTest { .. }
        | CStatement::Continue
        | CStatement::Goto { .. }
        | CStatement::Return(_, _) => true,
        CStatement::Label { statement, .. } => statement_contains_control_transfer(statement),
        CStatement::Seq(first, second) => {
            statement_contains_control_transfer(first)
                || statement_contains_control_transfer(second)
        }
        CStatement::If {
            then_branch,
            else_branch,
            ..
        } => {
            statement_contains_control_transfer(then_branch)
                || statement_contains_control_transfer(else_branch)
        }
        CStatement::While { test, body, .. }
        | CStatement::DoWhile { test, body, .. }
        | CStatement::For { test, body, .. } => {
            statement_contains_control_transfer(body)
                || test
                    .as_ref()
                    .is_some_and(|test| statement_contains_control_transfer(test))
        }
        CStatement::Switch { cases, .. } => cases
            .iter()
            .any(|case| statement_contains_control_transfer(&case.body)),
        CStatement::EndAggregateLifetimes { .. }
        | CStatement::FillArrayTail { .. }
        | CStatement::Skip
        | CStatement::Declare { .. }
        | CStatement::DeclareStructValue { .. }
        | CStatement::Assign { .. }
        | CStatement::Call { .. }
        | CStatement::CallResult { .. }
        | CStatement::IndirectCall { .. }
        | CStatement::HeapAllocate { .. }
        | CStatement::HeapFree { .. }
        | CStatement::Assert { .. }
        | CStatement::StepValue { .. }
        | CStatement::Store { .. }
        | CStatement::SequentialStore { .. }
        | CStatement::AggregateCopy { .. }
        | CStatement::Update { .. } => false,
    }
}

fn validate_global_initializer(
    parser: &Parser,
    interface_type: InterfaceType,
    pointee_constant: bool,
    initializer: &CExpression,
) -> Result<(), CSyntaxError> {
    if matches!(
        interface_type,
        InterfaceType::Float32 | InterfaceType::Float64
    ) {
        let matches_type = matches!(
            (interface_type, initializer),
            (InterfaceType::Float32, CExpression::Float32Literal(_))
                | (InterfaceType::Float64, CExpression::Float64Literal(_))
        );
        return if matches_type {
            Ok(())
        } else {
            Err(parser.error_here("floating-point global initializer has the wrong type"))
        };
    }
    if interface_type.is_pointer() {
        return parser.validate_static_pointer_initializer(
            interface_type,
            pointee_constant,
            initializer,
        );
    }
    let bits = match initializer {
        CExpression::Int32Literal(value) => u64::from(*value),
        CExpression::UInt8Literal(value) => u64::from(*value),
        CExpression::UInt32Literal(value) => u64::from(*value),
        _ => {
            return Err(
                parser.error_here("global initializers currently support only integer literals")
            );
        }
    };
    let valid = match interface_type {
        InterfaceType::Bool => true,
        InterfaceType::Int8 => bits <= i8::MAX as u64,
        InterfaceType::Int16 => bits <= i16::MAX as u64,
        InterfaceType::Int32 => bits <= i32::MAX as u64,
        InterfaceType::Char(PlainChar::Signed) => bits <= i8::MAX as u64,
        InterfaceType::Char(PlainChar::Unsigned) => bits <= u8::MAX as u64,
        InterfaceType::UInt8 => bits <= u8::MAX as u64,
        InterfaceType::UInt16 => bits <= u16::MAX as u64,
        InterfaceType::UInt32 => true,
        _ => false,
    };
    if valid {
        Ok(())
    } else {
        Err(parser.error_here(format!(
            "integer literal is out of range for global type {}",
            interface_type.diagnostic_name()
        )))
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum StaticIntegerValue {
    Signed { value: i128, bits: u32 },
    Unsigned { value: u128, bits: u32 },
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum StaticIntegerEvaluationError {
    NotConstant,
    Overflow,
    DivisionByZero,
    InvalidShift,
    OutOfRange,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum StaticIntegerKind {
    Signed,
    Unsigned,
}

fn is_static_integer_type(interface_type: InterfaceType) -> bool {
    matches!(
        interface_type,
        InterfaceType::Int8
            | InterfaceType::Int16
            | InterfaceType::Int32
            | InterfaceType::Char(_)
            | InterfaceType::UInt8
            | InterfaceType::UInt16
            | InterfaceType::UInt32
            | InterfaceType::Int64(_)
            | InterfaceType::UInt64(_)
    )
}

fn static_integer_type_info(interface_type: InterfaceType) -> Option<(StaticIntegerKind, u32)> {
    match interface_type {
        InterfaceType::Int8 => Some((StaticIntegerKind::Signed, 8)),
        InterfaceType::Int16 => Some((StaticIntegerKind::Signed, 16)),
        InterfaceType::Int32 => Some((StaticIntegerKind::Signed, 32)),
        InterfaceType::Char(PlainChar::Signed) => Some((StaticIntegerKind::Signed, 8)),
        InterfaceType::Char(PlainChar::Unsigned) => Some((StaticIntegerKind::Unsigned, 8)),
        InterfaceType::UInt8 => Some((StaticIntegerKind::Unsigned, 8)),
        InterfaceType::UInt16 => Some((StaticIntegerKind::Unsigned, 16)),
        InterfaceType::UInt32 => Some((StaticIntegerKind::Unsigned, 32)),
        InterfaceType::Int64(_) => Some((StaticIntegerKind::Signed, 64)),
        InterfaceType::UInt64(_) => Some((StaticIntegerKind::Unsigned, 64)),
        _ => None,
    }
}

fn static_integer_value_kind(value: StaticIntegerValue) -> StaticIntegerKind {
    match value {
        StaticIntegerValue::Signed { .. } => StaticIntegerKind::Signed,
        StaticIntegerValue::Unsigned { .. } => StaticIntegerKind::Unsigned,
    }
}

fn static_integer_value_bits(value: StaticIntegerValue) -> u32 {
    match value {
        StaticIntegerValue::Signed { bits, .. } | StaticIntegerValue::Unsigned { bits, .. } => bits,
    }
}

fn signed_bounds(bits: u32) -> Option<(i128, i128)> {
    if bits == 0 || bits >= 128 {
        return None;
    }
    let upper = (1i128 << (bits - 1)) - 1;
    Some((-1i128 - upper, upper))
}

fn unsigned_max(bits: u32) -> Option<u128> {
    if bits == 0 || bits >= 128 {
        return None;
    }
    Some((1u128 << bits) - 1)
}

fn checked_static_signed(
    value: i128,
    bits: u32,
) -> Result<StaticIntegerValue, StaticIntegerEvaluationError> {
    let (_, maximum) = signed_bounds(bits).ok_or(StaticIntegerEvaluationError::Overflow)?;
    let minimum = -1i128 - maximum;
    if (minimum..=maximum).contains(&value) {
        Ok(StaticIntegerValue::Signed { value, bits })
    } else {
        Err(StaticIntegerEvaluationError::Overflow)
    }
}

fn checked_static_unsigned(
    value: u128,
    bits: u32,
) -> Result<StaticIntegerValue, StaticIntegerEvaluationError> {
    let maximum = unsigned_max(bits).ok_or(StaticIntegerEvaluationError::Overflow)?;
    if value <= maximum {
        Ok(StaticIntegerValue::Unsigned { value, bits })
    } else {
        Err(StaticIntegerEvaluationError::Overflow)
    }
}

fn static_integer_common_kind(
    left: StaticIntegerValue,
    right: StaticIntegerValue,
) -> (StaticIntegerKind, u32) {
    let left_bits = static_integer_value_bits(left);
    let right_bits = static_integer_value_bits(right);
    match (
        static_integer_value_kind(left),
        static_integer_value_kind(right),
    ) {
        (StaticIntegerKind::Signed, StaticIntegerKind::Signed) => {
            (StaticIntegerKind::Signed, left_bits.max(right_bits))
        }
        (StaticIntegerKind::Unsigned, StaticIntegerKind::Unsigned) => {
            (StaticIntegerKind::Unsigned, left_bits.max(right_bits))
        }
        (StaticIntegerKind::Signed, StaticIntegerKind::Unsigned) => {
            if right_bits >= left_bits {
                (StaticIntegerKind::Unsigned, right_bits)
            } else {
                (StaticIntegerKind::Signed, left_bits)
            }
        }
        (StaticIntegerKind::Unsigned, StaticIntegerKind::Signed) => {
            if left_bits >= right_bits {
                (StaticIntegerKind::Unsigned, left_bits)
            } else {
                (StaticIntegerKind::Signed, right_bits)
            }
        }
    }
}

fn convert_static_integer(
    value: StaticIntegerValue,
    kind: StaticIntegerKind,
    bits: u32,
) -> Result<StaticIntegerValue, StaticIntegerEvaluationError> {
    match (kind, value) {
        (StaticIntegerKind::Signed, StaticIntegerValue::Signed { value, .. }) => {
            checked_static_signed(value, bits)
        }
        (StaticIntegerKind::Signed, StaticIntegerValue::Unsigned { value, .. }) => {
            let value =
                i128::try_from(value).map_err(|_| StaticIntegerEvaluationError::Overflow)?;
            checked_static_signed(value, bits)
        }
        (StaticIntegerKind::Unsigned, StaticIntegerValue::Unsigned { value, .. }) => {
            checked_static_unsigned(value, bits)
        }
        (StaticIntegerKind::Unsigned, StaticIntegerValue::Signed { value, .. }) => {
            let value = if value < 0 {
                let modulus = 1i128
                    .checked_shl(bits)
                    .ok_or(StaticIntegerEvaluationError::Overflow)?;
                value.rem_euclid(modulus) as u128
            } else {
                u128::try_from(value).map_err(|_| StaticIntegerEvaluationError::Overflow)?
            };
            checked_static_unsigned(value, bits)
        }
    }
}

fn evaluate_static_integer_binary(
    left: StaticIntegerValue,
    right: StaticIntegerValue,
    operation: fn(i128, i128) -> Option<i128>,
    unsigned_operation: fn(u128, u128) -> Option<u128>,
) -> Result<StaticIntegerValue, StaticIntegerEvaluationError> {
    let (kind, bits) = static_integer_common_kind(left, right);
    let left = convert_static_integer(left, kind, bits)?;
    let right = convert_static_integer(right, kind, bits)?;
    match (kind, left, right) {
        (
            StaticIntegerKind::Signed,
            StaticIntegerValue::Signed { value: left, .. },
            StaticIntegerValue::Signed { value: right, .. },
        ) => checked_static_signed(
            operation(left, right).ok_or(StaticIntegerEvaluationError::Overflow)?,
            bits,
        ),
        (
            StaticIntegerKind::Unsigned,
            StaticIntegerValue::Unsigned { value: left, .. },
            StaticIntegerValue::Unsigned { value: right, .. },
        ) => checked_static_unsigned(
            unsigned_operation(left, right).ok_or(StaticIntegerEvaluationError::Overflow)?
                & unsigned_max(bits).expect("static unsigned operations use a valid width"),
            bits,
        ),
        _ => unreachable!("static integer conversion preserves the common kind"),
    }
}

fn evaluate_static_integer_comparison(
    left: StaticIntegerValue,
    right: StaticIntegerValue,
    signed_operation: fn(i128, i128) -> bool,
    unsigned_operation: fn(u128, u128) -> bool,
) -> Result<StaticIntegerValue, StaticIntegerEvaluationError> {
    let (kind, bits) = static_integer_common_kind(left, right);
    let left = convert_static_integer_for_comparison(left, kind, bits)?;
    let right = convert_static_integer_for_comparison(right, kind, bits)?;
    let result = match (kind, left, right) {
        (
            StaticIntegerKind::Signed,
            StaticIntegerValue::Signed { value: left, .. },
            StaticIntegerValue::Signed { value: right, .. },
        ) => signed_operation(left, right),
        (
            StaticIntegerKind::Unsigned,
            StaticIntegerValue::Unsigned { value: left, .. },
            StaticIntegerValue::Unsigned { value: right, .. },
        ) => unsigned_operation(left, right),
        _ => unreachable!("static integer conversion preserves the common kind"),
    };
    checked_static_signed(i128::from(result), 32)
}

fn convert_static_integer_for_comparison(
    value: StaticIntegerValue,
    kind: StaticIntegerKind,
    bits: u32,
) -> Result<StaticIntegerValue, StaticIntegerEvaluationError> {
    match (kind, value) {
        (StaticIntegerKind::Unsigned, StaticIntegerValue::Signed { value, .. }) if value < 0 => {
            let modulus = 1i128
                .checked_shl(bits)
                .ok_or(StaticIntegerEvaluationError::Overflow)?;
            checked_static_unsigned(value.rem_euclid(modulus) as u128, bits)
        }
        _ => convert_static_integer(value, kind, bits),
    }
}

fn static_integer_is_true(value: StaticIntegerValue) -> bool {
    match value {
        StaticIntegerValue::Signed { value, .. } => value != 0,
        StaticIntegerValue::Unsigned { value, .. } => value != 0,
    }
}

fn static_integer_boolean(value: bool) -> Result<StaticIntegerValue, StaticIntegerEvaluationError> {
    checked_static_signed(i128::from(value), 32)
}

fn cast_static_integer(
    value: StaticIntegerValue,
    interface_type: InterfaceType,
) -> Result<StaticIntegerValue, StaticIntegerEvaluationError> {
    let (kind, bits) = static_integer_type_info(interface_type)
        .ok_or(StaticIntegerEvaluationError::NotConstant)?;
    let value = convert_static_integer_modulo(value, kind == StaticIntegerKind::Signed, bits);
    Ok(match kind {
        StaticIntegerKind::Signed => StaticIntegerValue::Signed { value, bits },
        StaticIntegerKind::Unsigned => StaticIntegerValue::Unsigned {
            value: value as u128,
            bits,
        },
    })
}

/// A static integer converted to an integer type of `bits` bits, as GCC and
/// Clang convert it: the value reduced modulo 2^`bits` into the type's range.
/// C11 6.3.1.3p2 defines this for an unsigned type, and GCC defines the
/// implementation-defined conversion to a signed type the same way ("the
/// value is reduced modulo 2^N to be within range of the type").
fn convert_static_integer_modulo(value: StaticIntegerValue, signed: bool, bits: u32) -> i128 {
    let value = match value {
        StaticIntegerValue::Signed { value, .. } => value,
        StaticIntegerValue::Unsigned { value, .. } => value as i128,
    };
    let modulus = 1i128 << bits;
    let reduced = value.rem_euclid(modulus);
    if signed && reduced >= modulus / 2 {
        reduced - modulus
    } else {
        reduced
    }
}

fn evaluate_static_integer_expression(
    expression: &CExpression,
) -> Result<StaticIntegerValue, StaticIntegerEvaluationError> {
    match expression {
        CExpression::Int32Literal(value) => {
            checked_static_signed(i128::from(i32::from_ne_bytes(value.to_ne_bytes())), 32)
        }
        CExpression::UInt8Literal(value) => checked_static_signed(i128::from(*value), 32),
        CExpression::UInt32Literal(value) => checked_static_unsigned(u128::from(*value), 32),
        CExpression::Int64Literal(value) => checked_static_signed(i128::from(*value), 64),
        CExpression::UInt64Literal(value) => checked_static_unsigned(u128::from(*value), 64),
        CExpression::SizeOfStruct { bytes, .. }
        | CExpression::SizeOfUnion { bytes, .. }
        | CExpression::SizeOfType { bytes, .. } => checked_static_unsigned(u128::from(*bytes), 64),
        CExpression::Not(expression) => {
            let value = evaluate_static_integer_expression(expression)?;
            static_integer_boolean(!static_integer_is_true(value))
        }
        CExpression::BitwiseNot(expression) => {
            let value = evaluate_static_integer_expression(expression)?;
            match value {
                StaticIntegerValue::Signed { value, bits } => checked_static_signed(!value, bits),
                StaticIntegerValue::Unsigned { value, bits } => {
                    checked_static_unsigned(!value & unsigned_max(bits).unwrap(), bits)
                }
            }
        }
        CExpression::Add(left, right) => evaluate_static_integer_binary(
            evaluate_static_integer_expression(left)?,
            evaluate_static_integer_expression(right)?,
            i128::checked_add,
            |left, right| Some(left.wrapping_add(right)),
        ),
        CExpression::Subtract(left, right) => evaluate_static_integer_binary(
            evaluate_static_integer_expression(left)?,
            evaluate_static_integer_expression(right)?,
            i128::checked_sub,
            |left, right| Some(left.wrapping_sub(right)),
        ),
        CExpression::Multiply(left, right) => evaluate_static_integer_binary(
            evaluate_static_integer_expression(left)?,
            evaluate_static_integer_expression(right)?,
            i128::checked_mul,
            |left, right| Some(left.wrapping_mul(right)),
        ),
        CExpression::Divide(left, right) => {
            let left = evaluate_static_integer_expression(left)?;
            let right = evaluate_static_integer_expression(right)?;
            if matches!(right, StaticIntegerValue::Signed { value: 0, .. })
                || matches!(right, StaticIntegerValue::Unsigned { value: 0, .. })
            {
                return Err(StaticIntegerEvaluationError::DivisionByZero);
            }
            evaluate_static_integer_binary(left, right, i128::checked_div, u128::checked_div)
        }
        CExpression::Remainder(left, right) => {
            let left = evaluate_static_integer_expression(left)?;
            let right = evaluate_static_integer_expression(right)?;
            if matches!(right, StaticIntegerValue::Signed { value: 0, .. })
                || matches!(right, StaticIntegerValue::Unsigned { value: 0, .. })
            {
                return Err(StaticIntegerEvaluationError::DivisionByZero);
            }
            evaluate_static_integer_binary(left, right, i128::checked_rem, u128::checked_rem)
        }
        CExpression::ShiftLeft(left, right) => {
            let left = evaluate_static_integer_expression(left)?;
            let right = evaluate_static_integer_expression(right)?;
            let shift =
                match right {
                    StaticIntegerValue::Signed { value, .. } => u32::try_from(value)
                        .map_err(|_| StaticIntegerEvaluationError::InvalidShift)?,
                    StaticIntegerValue::Unsigned { value, .. } => u32::try_from(value)
                        .map_err(|_| StaticIntegerEvaluationError::InvalidShift)?,
                };
            let bits = static_integer_value_bits(left);
            if shift >= bits {
                return Err(StaticIntegerEvaluationError::InvalidShift);
            }
            match left {
                StaticIntegerValue::Signed { value, .. } => {
                    if value < 0 {
                        return Err(StaticIntegerEvaluationError::InvalidShift);
                    }
                    checked_static_signed(
                        value
                            .checked_shl(shift)
                            .ok_or(StaticIntegerEvaluationError::Overflow)?,
                        bits,
                    )
                }
                StaticIntegerValue::Unsigned { value, .. } => checked_static_unsigned(
                    value
                        .checked_shl(shift)
                        .ok_or(StaticIntegerEvaluationError::Overflow)?
                        & unsigned_max(bits).expect("static unsigned shifts use a valid width"),
                    bits,
                ),
            }
        }
        CExpression::ShiftRight(left, right) => {
            let left = evaluate_static_integer_expression(left)?;
            let right = evaluate_static_integer_expression(right)?;
            let shift =
                match right {
                    StaticIntegerValue::Signed { value, .. } => u32::try_from(value)
                        .map_err(|_| StaticIntegerEvaluationError::InvalidShift)?,
                    StaticIntegerValue::Unsigned { value, .. } => u32::try_from(value)
                        .map_err(|_| StaticIntegerEvaluationError::InvalidShift)?,
                };
            let bits = static_integer_value_bits(left);
            if shift >= bits {
                return Err(StaticIntegerEvaluationError::InvalidShift);
            }
            match left {
                StaticIntegerValue::Signed { value, .. } => {
                    checked_static_signed(value >> shift, bits)
                }
                StaticIntegerValue::Unsigned { value, .. } => {
                    checked_static_unsigned(value >> shift, bits)
                }
            }
        }
        CExpression::BitwiseAnd(left, right) => evaluate_static_integer_binary(
            evaluate_static_integer_expression(left)?,
            evaluate_static_integer_expression(right)?,
            |left, right| Some(left & right),
            |left, right| Some(left & right),
        ),
        CExpression::BitwiseOr(left, right) => evaluate_static_integer_binary(
            evaluate_static_integer_expression(left)?,
            evaluate_static_integer_expression(right)?,
            |left, right| Some(left | right),
            |left, right| Some(left | right),
        ),
        CExpression::BitwiseXor(left, right) => evaluate_static_integer_binary(
            evaluate_static_integer_expression(left)?,
            evaluate_static_integer_expression(right)?,
            |left, right| Some(left ^ right),
            |left, right| Some(left ^ right),
        ),
        CExpression::LessThan(left, right) => evaluate_static_integer_comparison(
            evaluate_static_integer_expression(left)?,
            evaluate_static_integer_expression(right)?,
            |left, right| left < right,
            |left, right| left < right,
        ),
        CExpression::LessEqual(left, right) => evaluate_static_integer_comparison(
            evaluate_static_integer_expression(left)?,
            evaluate_static_integer_expression(right)?,
            |left, right| left <= right,
            |left, right| left <= right,
        ),
        CExpression::GreaterThan(left, right) => evaluate_static_integer_comparison(
            evaluate_static_integer_expression(left)?,
            evaluate_static_integer_expression(right)?,
            |left, right| left > right,
            |left, right| left > right,
        ),
        CExpression::GreaterEqual(left, right) => evaluate_static_integer_comparison(
            evaluate_static_integer_expression(left)?,
            evaluate_static_integer_expression(right)?,
            |left, right| left >= right,
            |left, right| left >= right,
        ),
        CExpression::Equal(left, right) => evaluate_static_integer_comparison(
            evaluate_static_integer_expression(left)?,
            evaluate_static_integer_expression(right)?,
            |left, right| left == right,
            |left, right| left == right,
        ),
        CExpression::NotEqual(left, right) => evaluate_static_integer_comparison(
            evaluate_static_integer_expression(left)?,
            evaluate_static_integer_expression(right)?,
            |left, right| left != right,
            |left, right| left != right,
        ),
        CExpression::And(left, right) => {
            let left = evaluate_static_integer_expression(left)?;
            if !static_integer_is_true(left) {
                return static_integer_boolean(false);
            }
            static_integer_boolean(static_integer_is_true(evaluate_static_integer_expression(
                right,
            )?))
        }
        CExpression::Or(left, right) => {
            let left = evaluate_static_integer_expression(left)?;
            if static_integer_is_true(left) {
                return static_integer_boolean(true);
            }
            static_integer_boolean(static_integer_is_true(evaluate_static_integer_expression(
                right,
            )?))
        }
        CExpression::Ternary {
            condition,
            then_branch,
            else_branch,
        } => {
            if static_integer_is_true(evaluate_static_integer_expression(condition)?) {
                evaluate_static_integer_expression(then_branch)
            } else {
                evaluate_static_integer_expression(else_branch)
            }
        }
        CExpression::Cast {
            expression,
            interface_type,
            ..
        } => cast_static_integer(
            evaluate_static_integer_expression(expression)?,
            *interface_type,
        ),
        CExpression::CheckedArrayIndex { index, .. } => evaluate_static_integer_expression(index),
        CExpression::StringLiteral(_)
        | CExpression::Void
        | CExpression::Variable(_)
        | CExpression::StepResult { .. }
        | CExpression::Call { .. }
        | CExpression::IndirectCall { .. }
        | CExpression::Assignment { .. }
        | CExpression::ScalarUpdate { .. }
        | CExpression::FunctionAddress(_)
        | CExpression::FloatNegate(_)
        | CExpression::FloatClassification { .. }
        | CExpression::AddressOf(_)
        | CExpression::PointerOffsetBytes { .. }
        | CExpression::Subobject { .. }
        | CExpression::Float32Literal(_)
        | CExpression::Float64Literal(_)
        | CExpression::Load(_, _)
        | CExpression::SequentialRead { .. }
        | CExpression::SequentialWrite { .. }
        | CExpression::AggregateAddress { .. }
        | CExpression::Field { .. }
        | CExpression::UnionAddress { .. }
        | CExpression::UnionField { .. }
        | CExpression::StatementExpression { .. }
        | CExpression::Index(_, _, _) => Err(StaticIntegerEvaluationError::NotConstant),
    }
}

fn evaluate_static_switch_case_value(
    expression: &CExpression,
) -> Result<u32, StaticIntegerEvaluationError> {
    let value = evaluate_static_integer_expression(expression)?;
    match value {
        StaticIntegerValue::Signed { value, .. } => {
            let value =
                i32::try_from(value).map_err(|_| StaticIntegerEvaluationError::OutOfRange)?;
            Ok(value as u32)
        }
        StaticIntegerValue::Unsigned { value, .. } => {
            u32::try_from(value).map_err(|_| StaticIntegerEvaluationError::OutOfRange)
        }
    }
}

/// The literal a static integer initializes an object of `interface_type` with: the
/// value converted to `interface_type` as GCC and Clang convert it, out-of-range
/// values included ([`convert_static_integer_modulo`]).
fn static_integer_literal_for_type(
    interface_type: InterfaceType,
    value: StaticIntegerValue,
) -> Result<CExpression, StaticIntegerEvaluationError> {
    let (kind, bits) = static_integer_type_info(interface_type)
        .ok_or(StaticIntegerEvaluationError::NotConstant)?;
    let value = convert_static_integer_modulo(value, kind == StaticIntegerKind::Signed, bits);
    Ok(match (kind, bits) {
        (StaticIntegerKind::Signed, 64) => CExpression::Int64Literal(value as i64),
        (StaticIntegerKind::Unsigned, 64) => CExpression::UInt64Literal(value as u64),
        (StaticIntegerKind::Signed, _) => CExpression::Int32Literal((value as i32) as u32),
        (StaticIntegerKind::Unsigned, _) => CExpression::UInt32Literal(value as u32),
    })
}

/// Converts an integer constant expression that `interface_type` cannot represent to
/// the literal GCC and Clang give it, at an assignment, initialization,
/// return, argument, or cast to the integer type `interface_type`: `unsigned char c =
/// -56` stores 200, and `signed char c = 200` stores -56. Both compilers
/// accept these, at most with a `-Woverflow` or `-Wconstant-conversion`
/// warning, and define the value modulo 2^N. A representable constant, or an
/// expression that is not a constant, is left for the checked conversion.
fn convert_integer_constant(interface_type: InterfaceType, expression: &mut CExpression) {
    if static_integer_type_info(interface_type).is_none() {
        return;
    }
    let Ok(value) = evaluate_static_integer_expression(expression) else {
        return;
    };
    if static_integer_fits(interface_type, value) {
        return;
    }
    if let Ok(literal) = static_integer_literal_for_type(interface_type, value) {
        *expression = literal;
    }
}

/// Whether `value` is representable in `interface_type` unchanged.
fn static_integer_fits(interface_type: InterfaceType, value: StaticIntegerValue) -> bool {
    let Some((kind, bits)) = static_integer_type_info(interface_type) else {
        return false;
    };
    let converted = convert_static_integer_modulo(value, kind == StaticIntegerKind::Signed, bits);
    match value {
        StaticIntegerValue::Signed { value, .. } => value == converted,
        StaticIntegerValue::Unsigned { value, .. } => {
            i128::try_from(value).is_ok_and(|value| value == converted)
        }
    }
}

fn normalize_static_initializer(
    parser: &Parser,
    interface_type: InterfaceType,
    pointee_constant: bool,
    initializer: &CExpression,
    storage: &str,
    static_local: bool,
) -> Result<CExpression, CSyntaxError> {
    if !is_static_integer_type(interface_type) {
        let initializer = if interface_type.is_pointer() {
            parser.decayed_static_pointer_initializer(initializer)
        } else {
            initializer.clone()
        };
        if static_local {
            validate_static_initializer(parser, interface_type, pointee_constant, &initializer)?;
        } else {
            validate_global_initializer(parser, interface_type, pointee_constant, &initializer)?;
        }
        return Ok(initializer);
    }
    let value = evaluate_static_integer_expression(initializer).map_err(|error| {
        let message = match error {
            StaticIntegerEvaluationError::NotConstant => {
                format!(
                    "{storage} initializers currently support only integer constant expressions"
                )
            }
            StaticIntegerEvaluationError::Overflow => {
                format!("integer constant expression overflows in {storage} initializer")
            }
            StaticIntegerEvaluationError::DivisionByZero => {
                format!("integer constant expression divides by zero in {storage} initializer")
            }
            StaticIntegerEvaluationError::InvalidShift => {
                format!("integer constant expression has an invalid shift in {storage} initializer")
            }
            StaticIntegerEvaluationError::OutOfRange => {
                format!(
                    "integer constant expression is out of range for {storage} type {}",
                    interface_type.diagnostic_name()
                )
            }
        };
        parser.error_here(message)
    })?;
    static_integer_literal_for_type(interface_type, value).map_err(|error| {
        let message = match error {
            StaticIntegerEvaluationError::OutOfRange => {
                format!(
                    "integer constant expression is out of range for {storage} type {}",
                    interface_type.diagnostic_name()
                )
            }
            _ => format!("{storage} initializer is not a supported integer constant expression"),
        };
        parser.error_here(message)
    })
}

fn validate_static_initializer(
    parser: &Parser,
    interface_type: InterfaceType,
    pointee_constant: bool,
    initializer: &CExpression,
) -> Result<(), CSyntaxError> {
    if matches!(
        interface_type,
        InterfaceType::Float32 | InterfaceType::Float64
    ) {
        let matches_type = matches!(
            (interface_type, initializer),
            (InterfaceType::Float32, CExpression::Float32Literal(_))
                | (InterfaceType::Float64, CExpression::Float64Literal(_))
        );
        return if matches_type {
            Ok(())
        } else {
            Err(parser.error_here("floating-point static initializer has the wrong type"))
        };
    }
    if interface_type.is_pointer() {
        return parser.validate_static_pointer_initializer(
            interface_type,
            pointee_constant,
            initializer,
        );
    }
    let bits = match initializer {
        CExpression::Int32Literal(value) => u64::from(*value),
        CExpression::UInt8Literal(value) => u64::from(*value),
        CExpression::UInt32Literal(value) => u64::from(*value),
        _ => {
            return Err(parser
                .error_here("static local initializers currently support only integer literals"));
        }
    };
    let valid = match interface_type {
        InterfaceType::Bool => true,
        InterfaceType::Int8 => bits <= i8::MAX as u64,
        InterfaceType::Int16 => bits <= i16::MAX as u64,
        InterfaceType::Int32 => bits <= i32::MAX as u64,
        InterfaceType::Char(PlainChar::Signed) => bits <= i8::MAX as u64,
        InterfaceType::Char(PlainChar::Unsigned) => bits <= u8::MAX as u64,
        InterfaceType::UInt8 => bits <= u8::MAX as u64,
        InterfaceType::UInt16 => bits <= u16::MAX as u64,
        InterfaceType::UInt32 => true,
        _ => false,
    };
    if valid {
        Ok(())
    } else {
        Err(parser.error_here(format!(
            "integer literal is out of range for static local type {}",
            interface_type.diagnostic_name()
        )))
    }
}

fn validate_aggregate_initializer(
    parser: &Parser,
    interface_type: InterfaceType,
    initializer: &CExpression,
) -> Result<(), CSyntaxError> {
    match interface_type {
        InterfaceType::Int64(_) => {
            if matches!(
                initializer,
                CExpression::Int32Literal(_)
                    | CExpression::UInt8Literal(_)
                    | CExpression::UInt32Literal(_)
                    | CExpression::Int64Literal(_)
            ) {
                Ok(())
            } else {
                Err(parser.error_here(
                    "aggregate initializers currently support only integer, floating-point, or null-pointer literals",
                ))
            }
        }
        InterfaceType::UInt64(_) => {
            let valid = match initializer {
                CExpression::Int32Literal(_)
                | CExpression::UInt8Literal(_)
                | CExpression::UInt32Literal(_)
                | CExpression::UInt64Literal(_) => true,
                CExpression::Int64Literal(value) => *value >= 0,
                _ => false,
            };
            if valid {
                Ok(())
            } else {
                Err(parser.error_here(
                    "aggregate initializers currently support only integer, floating-point, or null-pointer literals",
                ))
            }
        }
        InterfaceType::Int32Pointer
        | InterfaceType::CharPointer(_)
        | InterfaceType::UInt8Pointer
        | InterfaceType::Float32Pointer
        | InterfaceType::Float64Pointer
        | InterfaceType::Int32PointerPointer
        | InterfaceType::CharPointerPointer(_)
        | InterfaceType::UInt8PointerPointer
        | InterfaceType::Float32PointerPointer
        | InterfaceType::Float64PointerPointer => {
            if matches!(initializer, CExpression::Int32Literal(0)) {
                Ok(())
            } else {
                Err(parser.error_here(
                    "aggregate pointer initializers currently support only the null pointer literal",
                ))
            }
        }
        _ => validate_global_initializer(parser, interface_type, false, initializer).map_err(|error| {
            if error.message().contains("out of range") {
                error
            } else {
                parser.error_here(
                    "aggregate initializers currently support only integer, floating-point, or null-pointer literals",
                )
            }
        }),
    }
}

fn align_up(offset: u32, alignment: u32) -> Option<u32> {
    debug_assert!(alignment.is_power_of_two());
    offset
        .checked_add(alignment - 1)
        .map(|value| value & !(alignment - 1))
}

/// The address of `field` within the struct at `base`. The member is its own
/// subobject (`design/pointer-subobject-bounds.md`): arithmetic from its
/// address stays inside it, and an access through it may not reach a sibling
/// at an adjacent address. A union member is not narrowed; union members
/// overlap by design.
fn member_pointer(base: CExpression, field: &RecordField) -> CExpression {
    let member = offset_field_pointer(base, field.offset_bytes);
    if field.union_name.is_some() || field.byte_width == 0 {
        return member;
    }
    CExpression::Subobject {
        pointer: Box::new(member),
        width: field.byte_width,
    }
}

fn offset_field_pointer(base: CExpression, offset_bytes: u32) -> CExpression {
    if offset_bytes == 0 {
        return base;
    }
    CExpression::PointerOffsetBytes {
        pointer: Box::new(base),
        bytes: offset_bytes,
    }
}

/// See [`Parser::struct_class`]. A struct-pointer member's pointee is
/// identified by tag alone, which keeps a self-referential struct finite.
fn struct_class_in(
    name: &str,
    structs: &DeclarationMap<RecordLayout>,
    unions: &DeclarationMap<CUnionLayout>,
) -> crate::kernel::effective_type::CStructClass {
    use crate::kernel::effective_type::CStructClass;
    match structs.get(name) {
        Some(RecordLayout {
            class: Some(class), ..
        }) => class.clone(),
        Some(layout) => struct_class_of_fields(name, &layout.fields, structs, unions),
        None => CStructClass::opaque(name),
    }
}

/// The class of struct `name` with `fields`; see [`Parser::struct_class`].
pub(super) fn struct_class_of_fields(
    name: &str,
    fields: &BTreeMap<String, RecordField>,
    structs: &DeclarationMap<RecordLayout>,
    unions: &DeclarationMap<CUnionLayout>,
) -> crate::kernel::effective_type::CStructClass {
    let mut contents = crate::kernel::effective_type::CStructContentsBuilder::default();
    for field in fields.values() {
        add_member_class(
            &mut contents,
            field.interface_type,
            field.struct_name.as_deref(),
            field.union_name.as_deref(),
            field.array_element_width.is_some(),
            structs,
            unions,
        );
    }
    contents.build(name)
}

/// Adds what a member of type `interface_type` contributes to its struct's
/// contents. `struct_array` marks an inline array of embedded structs.
fn add_member_class(
    contents: &mut crate::kernel::effective_type::CStructContentsBuilder,
    interface_type: InterfaceType,
    struct_name: Option<&str>,
    union_name: Option<&str>,
    struct_array: bool,
    structs: &DeclarationMap<RecordLayout>,
    unions: &DeclarationMap<CUnionLayout>,
) {
    use crate::kernel::effective_type::{CPointeeBase, CStructClass};
    match (struct_name, union_name) {
        (Some(name), _) if interface_type == InterfaceType::Int32 || struct_array => {
            contents.embed(struct_class_in(name, structs, unions))
        }
        (Some(name), _) => contents.member(struct_pointer_class(
            interface_type,
            CPointeeBase::Struct(CStructClass::opaque(name)),
        )),
        (None, Some(name)) if !interface_type.is_pointer() => match unions.get(name) {
            Some(layout) => {
                for field in layout.fields.values() {
                    add_member_class(
                        contents,
                        field.interface_type,
                        field.struct_name.as_deref(),
                        field.union_name.as_deref(),
                        field.array_element_width.is_some(),
                        structs,
                        unions,
                    );
                }
            }
            None => contents.member(None),
        },
        _ => contents.member(
            interface_type
                .access_class()
                .or_else(|| int_pointer_class(interface_type)),
        ),
    }
}

/// The class of the object a pointer of declared type `interface_type` designates
/// (`design/effective-types.md`), as a pointer parameter's declaration gives
/// it: through `struct_name` for a struct pointer, otherwise the pointee
/// type's class, with `int *` and `int **` told apart from struct pointers
/// by the absence of a struct. A struct whose layout `structs` does not hold
/// is identified by its tag alone. Click declarations of model fields use it
/// so a pointer read from a model designates what its declaration promises.
pub fn declared_pointee_class(
    interface_type: InterfaceType,
    struct_name: Option<&str>,
    structs: &BTreeMap<String, RecordLayout>,
) -> Option<crate::kernel::effective_type::CAccessClass> {
    use crate::kernel::effective_type::{CPointeeBase, CStructClass};
    match struct_name {
        Some(name) => {
            let class = structs
                .get(name)
                .and_then(|layout| layout.class.clone())
                .unwrap_or_else(|| CStructClass::opaque(name));
            struct_pointer_class(interface_type, CPointeeBase::Struct(class))?.pointee()
        }
        None => {
            let pointee = interface_type.pointee_type()?;
            pointee
                .access_class()
                .or_else(|| int_pointer_class(pointee))
        }
    }
}

/// The class of an `int *` or `int **` of type `interface_type`, which the frontend
/// spells as it spells struct pointers; callers know there is no struct.
fn int_pointer_class(
    interface_type: InterfaceType,
) -> Option<crate::kernel::effective_type::CAccessClass> {
    use crate::kernel::effective_type::{CAccessClass, CPointeeBase, CScalarClass};
    let depth = match interface_type {
        InterfaceType::Int32Pointer => 1,
        InterfaceType::Int32PointerPointer => 2,
        _ => return None,
    };
    Some(CAccessClass::Pointer {
        base: CPointeeBase::Integer {
            class: CScalarClass::Int,
            signed: true,
        },
        depth,
    })
}

/// The class of a struct pointer of type `interface_type`, a pointer or an array
/// of pointers, to `base`; `None` for a function pointer.
fn struct_pointer_class(
    interface_type: InterfaceType,
    base: crate::kernel::effective_type::CPointeeBase,
) -> Option<crate::kernel::effective_type::CAccessClass> {
    let depth = match interface_type {
        InterfaceType::PointerArray(..) => 1,
        _ if !interface_type.is_object_pointer() => return None,
        _ if interface_type
            .pointee_type()
            .is_some_and(InterfaceType::is_pointer) =>
        {
            2
        }
        _ => 1,
    };
    Some(crate::kernel::effective_type::CAccessClass::Pointer { base, depth })
}

fn is_plain_struct_type(parsed_type: &ParsedType) -> bool {
    parsed_type.struct_name.is_some() && parsed_type.interface_type == InterfaceType::Int32
}

fn struct_scalar_array_shape(field: &RecordField) -> Option<(InterfaceType, Vec<u32>)> {
    let (element_type, length) = match field.interface_type {
        InterfaceType::Int32Array(length) => (InterfaceType::Int32, length),
        InterfaceType::UInt32Array(length) => (InterfaceType::UInt32, length),
        InterfaceType::Int64Array(rank, length) => (InterfaceType::Int64(rank), length),
        InterfaceType::Int128Array(length) => (InterfaceType::Int128, length),
        InterfaceType::UInt64Array(rank, length) => (InterfaceType::UInt64(rank), length),
        InterfaceType::UInt128Array(length) => (InterfaceType::UInt128, length),
        InterfaceType::CharArray(plain, length) => (InterfaceType::Char(plain), length),
        InterfaceType::UInt8Array(length) => (InterfaceType::UInt8, length),
        InterfaceType::PointerArray(element, rank, length) => {
            (pointer_array_element_type(element, rank), length)
        }
        _ => return None,
    };
    if field.struct_name.is_some()
        && !matches!(field.interface_type, InterfaceType::PointerArray(_, _, _))
    {
        return None;
    }
    Some((
        element_type,
        field.array_shape.clone().unwrap_or_else(|| vec![length]),
    ))
}

fn zero_initializer_value(interface_type: InterfaceType) -> CExpression {
    match interface_type {
        InterfaceType::Float32 => CExpression::Float32Literal(0),
        InterfaceType::Float64 => CExpression::Float64Literal(0),
        InterfaceType::Char(PlainChar::Unsigned) => CExpression::UInt8Literal(0),
        InterfaceType::Char(PlainChar::Signed) => CExpression::Int32Literal(0),
        InterfaceType::UInt8 => CExpression::UInt8Literal(0),
        InterfaceType::UInt32 => CExpression::UInt32Literal(0),
        InterfaceType::Int64(_) => CExpression::Int64Literal(0),
        InterfaceType::UInt64(_) => CExpression::UInt64Literal(0),
        InterfaceType::Int8 | InterfaceType::Int8Pointer | InterfaceType::Int8PointerPointer => {
            CExpression::Int32Literal(0)
        }
        InterfaceType::Bool
        | InterfaceType::Int16
        | InterfaceType::Int32
        | InterfaceType::UInt16
        | InterfaceType::Int16Pointer
        | InterfaceType::UInt16Pointer
        | InterfaceType::Int32Pointer
        | InterfaceType::CharPointer(_)
        | InterfaceType::UInt8Pointer
        | InterfaceType::UInt32Pointer
        | InterfaceType::Int128Pointer
        | InterfaceType::Int64Pointer(_)
        | InterfaceType::UInt128Pointer
        | InterfaceType::UInt64Pointer(_)
        | InterfaceType::Int16PointerPointer
        | InterfaceType::UInt16PointerPointer
        | InterfaceType::Int32PointerPointer
        | InterfaceType::CharPointerPointer(_)
        | InterfaceType::UInt8PointerPointer
        | InterfaceType::UInt32PointerPointer
        | InterfaceType::Int128PointerPointer
        | InterfaceType::Int64PointerPointer(_)
        | InterfaceType::UInt128PointerPointer
        | InterfaceType::UInt64PointerPointer(_) => CExpression::Int32Literal(0),
        _ => unreachable!("zero initializer called for non-scalar field type"),
    }
}

fn flatten_aggregate_layout(
    fields: &BTreeMap<String, RecordField>,
    structs: &DeclarationMap<RecordLayout>,
    unions: &DeclarationMap<CUnionLayout>,
) -> (Vec<RecordScalarField>, Vec<RecordUnionLayout>) {
    fn row_major_index_path(flat_index: u32, shape: &[u32]) -> String {
        let mut remaining = flat_index;
        let mut indexes = vec![0; shape.len()];
        for (dimension, length) in shape.iter().enumerate().rev() {
            indexes[dimension] = remaining % *length;
            remaining /= *length;
        }
        indexes
            .into_iter()
            .map(|index| format!("[{index}]"))
            .collect()
    }

    fn append_nested_fields(
        aggregate_fields: &mut Vec<RecordScalarField>,
        prefix: &str,
        base_offset: u32,
        nested_layout: &RecordLayout,
    ) {
        for nested_field in nested_layout.aggregate_fields() {
            aggregate_fields.push(RecordScalarField {
                pointee_constant: nested_field.pointee_constant,
                name: format!("{prefix}.{}", nested_field.name),
                offset_bytes: base_offset
                    .checked_add(nested_field.offset_bytes)
                    .expect("validated embedded struct field offset"),
                interface_type: nested_field.interface_type,
            });
        }
    }

    fn append_nested_unions(
        aggregate_unions: &mut Vec<RecordUnionLayout>,
        prefix: &str,
        base_offset: u32,
        nested_layout: &RecordLayout,
    ) {
        for nested_union in &nested_layout.aggregate_unions {
            aggregate_unions.push(RecordUnionLayout {
                name: format!("{prefix}.{}", nested_union.name),
                offset_bytes: base_offset
                    .checked_add(nested_union.offset_bytes)
                    .expect("validated embedded union offset"),
                size_bytes: nested_union.size_bytes,
                fields: nested_union.fields.clone(),
            });
        }
    }

    let mut aggregate_fields = Vec::new();
    let mut aggregate_unions = Vec::new();
    for (field_name, field) in fields {
        if field.interface_type == InterfaceType::Int32
            && let Some(nested_name) = field.struct_name.as_ref()
            && field.array_element_width.is_none()
        {
            let nested_layout = structs
                .get(nested_name)
                .expect("embedded struct field has a parsed layout");
            append_nested_fields(
                &mut aggregate_fields,
                field_name,
                field.offset_bytes,
                nested_layout,
            );
            append_nested_unions(
                &mut aggregate_unions,
                field_name,
                field.offset_bytes,
                nested_layout,
            );
        } else if let (Some(nested_name), Some(element_width), Some(shape)) = (
            field.struct_name.as_ref(),
            field.array_element_width,
            field.array_shape.as_deref(),
        ) {
            let nested_layout = structs
                .get(nested_name)
                .expect("embedded struct array field has a parsed layout");
            let element_count = shape
                .iter()
                .try_fold(1u32, |count, length| count.checked_mul(*length))
                .expect("validated embedded struct array field element count");
            for flat_index in 0..element_count {
                let element_offset = field
                    .offset_bytes
                    .checked_add(
                        flat_index
                            .checked_mul(element_width)
                            .expect("validated embedded struct array field offset"),
                    )
                    .expect("validated embedded struct array field offset");
                let index_path = row_major_index_path(flat_index, shape);
                append_nested_fields(
                    &mut aggregate_fields,
                    &format!("{field_name}{index_path}"),
                    element_offset,
                    nested_layout,
                );
                append_nested_unions(
                    &mut aggregate_unions,
                    &format!("{field_name}{index_path}"),
                    element_offset,
                    nested_layout,
                );
            }
        } else if let Some(union_name) = &field.union_name {
            let union_layout = unions
                .get(union_name)
                .expect("embedded union field has a parsed layout");
            aggregate_unions.push(RecordUnionLayout {
                name: field_name.clone(),
                offset_bytes: field.offset_bytes,
                size_bytes: union_layout.size_bytes,
                fields: union_layout
                    .fields
                    .iter()
                    .map(|(name, union_field)| RecordUnionField {
                        name: name.clone(),
                        offset_bytes: union_field.offset_bytes,
                        interface_type: union_field.interface_type,
                    })
                    .collect(),
            });
        } else {
            aggregate_fields.push(RecordScalarField {
                pointee_constant: field.pointee_constant,
                name: field_name.clone(),
                offset_bytes: field.offset_bytes,
                interface_type: field.interface_type,
            });
        }
    }
    (aggregate_fields, aggregate_unions)
}

fn field_expression(
    pointer: CExpression,
    field_type: InterfaceType,
    field_struct_name: Option<String>,
    field_union_name: Option<String>,
    function_pointer_signature: Option<CallbackInterface>,
    array_shape: Option<Vec<u32>>,
    source: Option<CFieldSource>,
    pointee_constant: bool,
    access_class: Option<crate::kernel::effective_type::CAccessClass>,
) -> CExpression {
    if let Some(union_name) = field_union_name {
        return CExpression::UnionAddress {
            pointer: Box::new(pointer),
            union_name,
        };
    }
    if field_type == InterfaceType::Int32
        && let Some(struct_name) = field_struct_name
    {
        return CExpression::AggregateAddress {
            pointer: Box::new(pointer),
            struct_name,
        };
    }
    CExpression::Field {
        pointer: Box::new(pointer),
        field_type,
        pointee_constant,
        field_struct_name,
        function_pointer_signature,
        array_shape,
        source,
        access_class,
    }
}

fn contains_aggregate_value(expression: &CExpression) -> bool {
    match expression {
        CExpression::ScalarUpdate { .. } => false,
        CExpression::AggregateAddress { .. } | CExpression::UnionAddress { .. } => true,
        CExpression::Field {
            field_type,
            field_struct_name,
            ..
        } => *field_type == InterfaceType::Int32 && field_struct_name.is_some(),
        CExpression::UnionField { .. } => false,
        // Call arguments are checked against the callee's parameter shape
        // while they are parsed. In particular, a direct aggregate lvalue is
        // valid when the corresponding parameter is a copyable struct, so it
        // must not be rejected again by the enclosing expression check.
        CExpression::Call { .. } | CExpression::IndirectCall { .. } => false,
        CExpression::AddressOf(_) => false,
        CExpression::Cast { expression, .. }
        | CExpression::FloatNegate(expression)
        | CExpression::FloatClassification { expression, .. }
        | CExpression::PointerOffsetBytes {
            pointer: expression,
            ..
        }
        | CExpression::Subobject {
            pointer: expression,
            ..
        }
        | CExpression::Not(expression)
        | CExpression::BitwiseNot(expression)
        | CExpression::Load(expression, _)
        | CExpression::CheckedArrayIndex {
            index: expression, ..
        } => contains_aggregate_value(expression),
        CExpression::SequentialRead { target, .. } => contains_aggregate_value(target),
        CExpression::SequentialWrite { target, value, .. } => {
            contains_aggregate_value(target) || contains_aggregate_value(value)
        }
        CExpression::Ternary {
            condition,
            then_branch,
            else_branch,
        } => {
            contains_aggregate_value(condition)
                || contains_aggregate_value(then_branch)
                || contains_aggregate_value(else_branch)
        }
        CExpression::StatementExpression { value, .. } | CExpression::Assignment { value, .. } => {
            contains_aggregate_value(value)
        }
        crate::languages::c::syntax::binary_c_expression!(left, right) => {
            contains_aggregate_value(left) || contains_aggregate_value(right)
        }
        CExpression::StringLiteral(_)
        | CExpression::Void
        | CExpression::Variable(_)
        | CExpression::StepResult { .. }
        | CExpression::FunctionAddress(_)
        | CExpression::Int32Literal(_)
        | CExpression::UInt8Literal(_)
        | CExpression::UInt32Literal(_)
        | CExpression::Int64Literal(_)
        | CExpression::UInt64Literal(_)
        | CExpression::Float32Literal(_)
        | CExpression::Float64Literal(_)
        | CExpression::SizeOfStruct { .. }
        | CExpression::SizeOfUnion { .. }
        | CExpression::SizeOfType { .. } => false,
    }
}

fn is_builtin_type_start(name: &str) -> bool {
    matches!(
        name,
        "void"
            | "_Bool"
            | "bool"
            | "struct"
            | "union"
            | "enum"
            | "int8"
            | "int16"
            | "int32"
            | "int"
            | "int32_t"
            | "uint8"
            | "uint8_t"
            | "uint16"
            | "uint32"
            | "uint32_t"
            | "int64"
            | "uint64"
            | "unsigned"
            | "signed"
            | "char"
            | "short"
            | "long"
            | "size_t"
            | "ssize_t"
            | "int8_t"
            | "int16_t"
            | "int64_t"
            | "uint16_t"
            | "uint64_t"
            | "float"
            | "double"
            | "volatile"
            | "typeof"
            | "__typeof__"
    )
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum Token {
    Ident(String),
    Number(String),
    CharLiteral(u8),
    StringLiteral(Vec<u8>),
    LParen,
    RParen,
    LBracket,
    RBracket,
    LBrace,
    RBrace,
    Comma,
    Semicolon,
    Plus,
    PlusPlus,
    PlusEqual,
    Minus,
    Arrow,
    Dot,
    Ellipsis,
    MinusMinus,
    MinusEqual,
    LessThan,
    LessEqual,
    ShiftLeft,
    ShiftLeftEqual,
    GreaterThan,
    GreaterEqual,
    ShiftRight,
    ShiftRightEqual,
    EqualEqual,
    BangEqual,
    Bang,
    AmpAmp,
    PipePipe,
    Star,
    StarEqual,
    CaretEqual,
    Slash,
    SlashEqual,
    Percent,
    PercentEqual,
    Amp,
    AmpEqual,
    Pipe,
    PipeEqual,
    Caret,
    Tilde,
    Equal,
    Question,
    Colon,
}

impl Token {
    /// A human-readable rendering for diagnostics, such as `` identifier `x` ``
    /// or `` `;` ``.
    fn describe(&self) -> String {
        match self {
            Self::Ident(name) => format!("identifier `{name}`"),
            Self::Number(number) => format!("number `{number}`"),
            Self::CharLiteral(value) => {
                format!("character literal `{}`", (*value as char).escape_default())
            }
            Self::StringLiteral(value) => {
                format!("string literal with {} bytes", value.len())
            }
            other => format!("`{}`", other.form()),
        }
    }

    fn form(&self) -> &'static str {
        match self {
            Self::Ident(_) | Self::Number(_) | Self::CharLiteral(_) | Self::StringLiteral(_) => "",
            Self::LParen => "(",
            Self::RParen => ")",
            Self::LBracket => "[",
            Self::RBracket => "]",
            Self::LBrace => "{",
            Self::RBrace => "}",
            Self::Comma => ",",
            Self::Semicolon => ";",
            Self::Plus => "+",
            Self::PlusPlus => "++",
            Self::PlusEqual => "+=",
            Self::Minus => "-",
            Self::Arrow => "->",
            Self::Dot => ".",
            Self::Ellipsis => "...",
            Self::MinusMinus => "--",
            Self::MinusEqual => "-=",
            Self::LessThan => "<",
            Self::LessEqual => "<=",
            Self::ShiftLeft => "<<",
            Self::ShiftLeftEqual => "<<=",
            Self::GreaterThan => ">",
            Self::GreaterEqual => ">=",
            Self::ShiftRight => ">>",
            Self::ShiftRightEqual => ">>=",
            Self::EqualEqual => "==",
            Self::BangEqual => "!=",
            Self::Bang => "!",
            Self::AmpAmp => "&&",
            Self::PipePipe => "||",
            Self::Star => "*",
            Self::StarEqual => "*=",
            Self::CaretEqual => "^=",
            Self::Slash => "/",
            Self::SlashEqual => "/=",
            Self::Percent => "%",
            Self::PercentEqual => "%=",
            Self::Amp => "&",
            Self::AmpEqual => "&=",
            Self::Pipe => "|",
            Self::PipeEqual => "|=",
            Self::Caret => "^",
            Self::Tilde => "~",
            Self::Equal => "=",
            Self::Question => "?",
            Self::Colon => ":",
        }
    }

    fn is_scalar_update(&self) -> bool {
        matches!(
            self,
            Self::Equal
                | Self::PlusPlus
                | Self::MinusMinus
                | Self::PlusEqual
                | Self::MinusEqual
                | Self::StarEqual
                | Self::CaretEqual
                | Self::SlashEqual
                | Self::PercentEqual
                | Self::ShiftLeftEqual
                | Self::ShiftRightEqual
                | Self::AmpEqual
                | Self::PipeEqual
        )
    }
}

/// A captured error position; see [`Parser::error_context`].
struct ErrorContext {
    position: Option<SourcePosition>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum GlobalArrayLength {
    Complete(Vec<u32>),
    /// The outer bound is omitted; the vector contains any known inner bounds.
    Incomplete(Vec<u32>),
}

fn array_shape_element_count(shape: &[u32]) -> Option<u32> {
    shape.iter().copied().try_fold(1u32, u32::checked_mul)
}

pub(crate) fn array_lengths_compatible(left: Option<u32>, right: Option<u32>) -> bool {
    match (left, right) {
        (Some(left), Some(right)) => left == right,
        _ => true,
    }
}

pub(crate) fn array_shapes_compatible(left: &CGlobalArray, right: &CGlobalArray) -> bool {
    match (
        left.shape(),
        left.incomplete_shape(),
        right.shape(),
        right.incomplete_shape(),
    ) {
        (Some(left), _, Some(right), _) => left == right,
        (Some(complete), _, None, Some(incomplete))
        | (None, Some(incomplete), Some(complete), _) => {
            complete.len() == incomplete.len() + 1 && complete[1..] == incomplete[..]
        }
        (None, Some(left), None, Some(right)) => left == right,
        _ => true,
    }
}

pub(crate) fn merge_global_array_declarations(
    previous: Option<&CGlobalArray>,
    declaration: CGlobalArray,
) -> CGlobalArray {
    match previous {
        Some(previous) if previous.is_initialized_definition() => previous.clone(),
        Some(_) if declaration.is_initialized_definition() => declaration,
        Some(previous)
            if previous.is_tentative()
                && previous.is_incomplete()
                && declaration.is_tentative()
                && !declaration.is_incomplete() =>
        {
            declaration
        }
        Some(previous) if previous.is_tentative() => previous.clone(),
        _ => declaration,
    }
}

impl ErrorContext {
    fn error(&self, message: impl Into<String>) -> CSyntaxError {
        match &self.position {
            Some(position) => CSyntaxError::at(position.clone(), message),
            None => CSyntaxError::new(message),
        }
    }
}

#[derive(Clone, Debug, Default)]
struct CVariableTypes(BTreeMap<BindingName, InterfaceType>);
impl std::ops::Deref for CVariableTypes {
    type Target = BTreeMap<BindingName, InterfaceType>;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}
impl std::ops::DerefMut for CVariableTypes {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}
impl CVariableTypes {
    fn insert(&mut self, name: BindingName, ty: InterfaceType) -> Option<InterfaceType> {
        if let Some(id) = name.local_id() {
            id.initialize_program_type(ty.to_kernel_type());
        }
        self.0.insert(name, ty)
    }
}

#[derive(Clone, Debug, Default)]
struct CVariableArrayShapes(BTreeMap<BindingName, Vec<u32>>);
impl std::ops::Deref for CVariableArrayShapes {
    type Target = BTreeMap<BindingName, Vec<u32>>;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}
impl std::ops::DerefMut for CVariableArrayShapes {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}
impl CVariableArrayShapes {
    fn insert(&mut self, name: BindingName, value: Vec<u32>) -> Option<Vec<u32>> {
        if let Some(id) = name.local_id() {
            id.initialize_array_shape(&value);
        }
        self.0.insert(name, value)
    }
}

#[derive(Clone, Debug, Default)]
struct CVariableStructs(BTreeMap<BindingName, String>);
impl std::ops::Deref for CVariableStructs {
    type Target = BTreeMap<BindingName, String>;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}
impl std::ops::DerefMut for CVariableStructs {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}
impl CVariableStructs {
    fn insert(&mut self, name: BindingName, value: String) -> Option<String> {
        if let Some(id) = name.local_id() {
            id.initialize_struct_name(&value);
        }
        if let Some(id) = name.static_id() {
            id.initialize_struct_name(&value);
        }
        self.0.insert(name, value)
    }
}

#[derive(Clone)]
struct Parser {
    tokens: Vec<Token>,
    positions: Vec<SourcePosition>,
    /// The parsed text by line, so a statement's site can quote the line it
    /// was written on. Positions index it by their parsed (not origin) line.
    source_lines: std::sync::Arc<[Box<str>]>,
    /// The line as written for each parsed line a macro expansion rewrote,
    /// so a site quotes the expansion site rather than the replacement.
    written_lines: std::sync::Arc<BTreeMap<usize, std::sync::Arc<str>>>,
    position: usize,
    // Bit-field records are admitted only through their private local lowering.
    bit_field_records: BTreeMap<String, std::sync::Arc<bit_fields::BitFieldRecord>>,
    local_bit_fields: BTreeMap<BindingName, bit_fields::LocalBitFields>,
    bit_field_forbidden_operand: bool,
    unevaluated_operand: bool,
    function_has_bit_fields: bool,
    structs: DeclarationMap<RecordLayout>,
    enums: DeclarationMap<CEnumDefinition>,
    enum_constants: BTreeMap<String, CExpression>,
    typedefs: BTreeMap<String, ParsedType>,
    parsing_function_header: bool,
    opaque_function_signature: bool,
    opaque_signature_types: Vec<(bool, bool)>,
    variable_structs: CVariableStructs,
    /// The struct name of each automatic struct-pointer local declared in the
    /// function currently being parsed, keyed by its C spelling. `None` marks
    /// a spelling declared twice with different struct types, which is
    /// dropped rather than guessed.
    local_struct_pointers: BTreeMap<BindingName, Option<String>>,
    local_struct_values: BTreeMap<BindingName, Option<String>>,
    /// Whether each automatic local spelling declared in the function being
    /// parsed has pointer type in every declaration.
    local_pointers: BTreeMap<BindingName, bool>,
    variable_struct_values: BTreeMap<BindingName, String>,
    variable_array_shapes: CVariableArrayShapes,
    local_row_pointers: imbl::OrdMap<BindingName, row_pointers::LocalRowPointer>,
    incomplete_array_names: BTreeSet<BindingName>,
    variable_types: CVariableTypes,
    variable_function_pointers: BTreeMap<BindingName, CallbackInterface>,
    variable_constants: BTreeSet<BindingName>,
    variable_pointee_constants: BTreeSet<BindingName>,
    unions: DeclarationMap<CUnionLayout>,
    /// The names declared in each open lexical scope, innermost last. The
    /// source name is retained for lookup, while `kernel_name` is the
    /// identity emitted into the C AST. Click's kernel keys a local by its
    /// name alone, so a shadowing declaration receives a fresh internal name
    /// instead of silently overwriting the outer object. Sibling scopes may
    /// reuse a name because the earlier object is dead.
    scopes: Vec<Vec<ScopeBinding>>,
    /// Storage introduced by literal occurrences in each open scope. The
    /// initializer stays in its expression; only allocation is at block entry.
    compound_literal_declarations: Vec<Vec<CStatement>>,
    repeatable_compound_literal_scope: Option<usize>,
    function_has_compound_literals: bool,
    function_has_goto: bool,
    visible_bindings: CSourceBindings,
    loop_source_bindings: BTreeMap<usize, std::sync::Arc<CSourceBindings>>,
    binding_function: Option<LocalFunctionId>,
    parsing_binding_parameters: bool,
    next_parameter_binding: u32,
    next_local_binding: u32,
    /// Names declared in a `for` initializer whose loop scope has closed.
    /// C-source parsing intentionally permits unresolved cross-file calls and
    /// object names for later validation, so this records only the specific
    /// out-of-scope declarations that must not be treated as such names.
    out_of_scope_names: BTreeSet<String>,
    /// Mutable scalar locals whose address is formed anywhere in the current
    /// function. A call can only change an automatic scalar through such an
    /// escaped address; static-storage scalars are handled separately.
    address_taken_variables: BTreeSet<BindingName>,
    next_static_binding: u32,
    file_static_bindings: BTreeMap<String, StaticBindingId>,
    /// The number the next call inside an expression gets: its result is
    /// `CExpression::StepResult` with that number.
    next_call_result: u32,
    aggregate_expression_steps: Vec<u32>,
    callback_statement_sources: imbl::OrdMap<BindingName, CExpression>,
    next_field_source_ordinal: u32,
    loop_contexts: Vec<CLoopContext>,
    function_declarations: BTreeMap<String, CFunctionHeader>,
    /// The most recent attribute that is valid only on `static inline`.
    static_inline_attribute: &'static str,
    /// Unnamed parameters seen by `parse_parameters`; a function header
    /// records how many belong to it.
    unnamed_parameters: usize,
    /// Set while parsing a block-scope function declaration, the only place
    /// the GNU `error` attribute is accepted; records whether it was seen.
    error_attribute: Option<bool>,
    /// Set for a compiler import whose option profile accepts optimization:
    /// the attributes and qualifiers GCC's optimizer trusts as unchecked
    /// programmer promises are refused. See `PromiseAttributes`.
    refuse_promises: bool,
    /// Under `refuse_promises`, the refusal of a `noreturn` seen in a
    /// block-scope declaration, kept until the declaration shows whether it
    /// is a `compiletime_assert` error declaration, the one place it is
    /// allowed.
    pending_noreturn: Option<CSyntaxError>,
    /// Function names declared in a block, with the scope depth they leave
    /// with.
    block_function_declarations: Vec<(usize, String)>,
    /// Set while parsing a discarded call statement, the only position in
    /// which a call to an `error` function is accepted.
    statement_call: bool,
    /// The fixed-arity function the formatted-output call whose arguments
    /// were just parsed calls; see [`Parser::call_target`].
    formatted_output_call: std::cell::RefCell<Option<String>>,
    function_declaration_lines: BTreeMap<String, Vec<usize>>,
    shadowed_pthread_names: BTreeSet<String>,
    function_source_names: BTreeMap<String, String>,
    defined_functions: BTreeSet<String>,
    globals: DeclarationMap<CGlobal>,
    global_arrays: DeclarationMap<CGlobalArray>,
    global_aggregates: DeclarationMap<CGlobalAggregate>,
    global_aggregate_arrays: DeclarationMap<CGlobalAggregateArray>,
    referenced_external_objects: BTreeSet<String>,
    static_locals: BTreeMap<BindingName, CStaticLocal>,
    static_arrays: BTreeMap<BindingName, CStaticArray>,
    static_aggregates: BTreeMap<BindingName, CStaticAggregate>,
    static_aggregate_arrays: BTreeMap<BindingName, CStaticAggregateArray>,
    string_literals: Vec<CStringLiteral>,
    header_mode: bool,
    source_identity: Option<String>,
    current_function_source_name: Option<String>,
    import_mode: bool,
    abi: CAbi,
    /// The signedness the selected C target gives plain `char`.
    plain_char: PlainChar,
    /// The rank the selected C target gives `int64_t` and `uint64_t`.
    int64_t_rank: LongRank,
    current_return_struct_name: Option<String>,
    current_return_pointer_struct_name: Option<String>,
    current_return_type: InterfaceType,
    current_return_pointee_constant: bool,
    /// Lexical compound-statement depth inside the function currently being
    /// parsed. Forward-goto labels remain direct children of the function
    /// body; the validator separately admits jumps nested in `if` arms.
    function_block_depth: usize,
    /// Non-compound statement nesting under `if`, loops, or a label.
    controlled_statement_depth: usize,
    /// The statements as written that are open while parsing, innermost
    /// last: each one's path and how many children it has so far. The
    /// function body is the empty path. `None` marks a region whose
    /// statements get no path, such as a statement expression's body.
    source_regions: Vec<Option<(std::sync::Arc<[u32]>, u32)>>,
    /// The next statement parsed is a label's body: it is the label's own
    /// statement as written, not a child of it.
    source_label_body: bool,
}

#[derive(Clone, Debug)]
struct ScopeBinding {
    source_name: Option<String>,
    kernel_name: BindingName,
    shadowed: Option<VariableMetadata>,
    previous_visible: Option<(usize, BindingName)>,
}

#[derive(Clone, Debug)]
struct VariableMetadata {
    interface_type: InterfaceType,
    struct_name: Option<String>,
    struct_value: Option<String>,
    array_shape: Option<Vec<u32>>,
    function_pointer: Option<CallbackInterface>,
    constant: bool,
    pointee_constant: bool,
    incomplete_array: bool,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct CFunctionHeader {
    declaration_line: usize,
    /// Where the declarator names the function, for a diagnostic about the
    /// declaration as a whole.
    name_position: Option<SourcePosition>,
    return_type: InterfaceType,
    return_pointee_constant: bool,
    return_struct_name: Option<String>,
    return_pointer_struct_name: Option<String>,
    /// The C spelling used to resolve declarations and calls in this
    /// translation unit.
    source_name: String,
    /// The kernel identity. Internal-linkage inline definitions are qualified
    /// by the including translation unit so separate TUs get separate
    /// instances of a shared header helper.
    name: String,
    internal_linkage: bool,
    weak_linkage: bool,
    returns_twice: bool,
    /// The prototype ends in `, ...`. Only body-less declarations carry
    /// this; calls and address uses are refused because the variable
    /// arguments have no model.
    variadic: bool,
    /// A parameter has no name, which only a body-less prototype may do.
    has_unnamed_parameter: bool,
    /// The declarator's parameter list is empty, `f()`, which before C23
    /// declares the function without a prototype. Click otherwise reads it
    /// as `f(void)`.
    empty_parameter_list: bool,
    /// No callable ABI exists for a retained declaration-only builtin type.
    opaque_signature: bool,
    /// Per-position builtin/extended-precision identities, including the return.
    opaque_signature_types: Vec<(bool, bool)>,
    /// Unmodeled compiler promises: prototype only, never callable/addressable.
    opaque_attributes: bool,
    /// Declared with GNU `error`: the compiler rejects the program unless
    /// it removes every call, so a call must be unreachable.
    compile_time_error: bool,
    parameters: Vec<ImportedParameter>,
}

impl CFunctionHeader {
    #[cfg(test)]
    pub(crate) fn return_type(&self) -> InterfaceType {
        self.return_type
    }

    #[cfg(test)]
    pub(crate) fn parameters(&self) -> &[ImportedParameter] {
        &self.parameters
    }

    pub(crate) fn linkage_name(&self) -> &str {
        &self.name
    }

    pub(crate) fn compatible_with(&self, other: &Self) -> bool {
        function_headers_compatible(self, other)
    }
}

/// A type in the C prototype of a standard-library function Click specifies.
/// Every target is LP64, so `size_t` is `unsigned long`, Click's `uint64`.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum LibraryType {
    Void,
    Int,
    SizeT,
    VoidPointer,
    ConstVoidPointer,
    ConstCharPointer,
}

impl LibraryType {
    /// Whether a declared type is this one. Plain `char` is distinct from
    /// `signed char` and `unsigned char`, and a pointee's qualifiers are part
    /// of a pointer's type; a parameter's own top-level qualifiers are not
    /// (C11 6.7.6.3p15).
    fn matches(
        self,
        interface_type: InterfaceType,
        pointee_constant: bool,
        pointee_volatile: bool,
        nominal: bool,
    ) -> bool {
        if nominal || pointee_volatile {
            return false;
        }
        match self {
            Self::Void => interface_type == InterfaceType::Void,
            Self::Int => interface_type == InterfaceType::Int32,
            // `size_t` is `unsigned long`, never `unsigned long long`.
            Self::SizeT => interface_type == InterfaceType::UInt64(LongRank::Long),
            Self::VoidPointer => interface_type == InterfaceType::VoidPointer && !pointee_constant,
            Self::ConstVoidPointer => {
                interface_type == InterfaceType::VoidPointer && pointee_constant
            }
            Self::ConstCharPointer => {
                matches!(interface_type, InterfaceType::CharPointer(_)) && pointee_constant
            }
        }
    }
}

/// The standard C prototype of each library function Click specifies: the
/// `<string.h>` functions with a contract in `library/c/string.click` and the
/// `<stdlib.h>` functions of the allocation model. A call binds to Click's
/// specification by the function's name, so a declaration of one of these
/// names must have the library's type.
const LIBRARY_PROTOTYPES: &[(&str, &str, LibraryType, &[LibraryType])] = {
    use LibraryType::*;
    &[
        (
            "memcpy",
            "void *memcpy(void *dest, const void *src, size_t n)",
            VoidPointer,
            &[VoidPointer, ConstVoidPointer, SizeT],
        ),
        (
            "memcmp",
            "int memcmp(const void *s1, const void *s2, size_t n)",
            Int,
            &[ConstVoidPointer, ConstVoidPointer, SizeT],
        ),
        (
            "memset",
            "void *memset(void *s, int c, size_t n)",
            VoidPointer,
            &[VoidPointer, Int, SizeT],
        ),
        (
            "strlen",
            "size_t strlen(const char *s)",
            SizeT,
            &[ConstCharPointer],
        ),
        ("malloc", "void *malloc(size_t size)", VoidPointer, &[SizeT]),
        (
            "calloc",
            "void *calloc(size_t count, size_t size)",
            VoidPointer,
            &[SizeT, SizeT],
        ),
        (
            "realloc",
            "void *realloc(void *pointer, size_t size)",
            VoidPointer,
            &[VoidPointer, SizeT],
        ),
        ("free", "void free(void *pointer)", Void, &[VoidPointer]),
    ]
};

/// The Click library module whose contract a C declaration of `header`
/// brings: `click::c::string` for the `<string.h>` functions Click
/// specifies. The allocator family is part of the kernel's allocation model
/// and brings no module.
pub(crate) fn library_contract_module(header: &CFunctionHeader) -> Option<&'static str> {
    let (name, ..) = library_function_prototype(header)?;
    library_contract_module_named(name)
}

/// The Click library module whose contract a call to the library function
/// `name` uses; see [`library_contract_module`].
pub(crate) fn library_contract_module_named(name: &str) -> Option<&'static str> {
    matches!(name, "memcpy" | "memcmp" | "memset" | "strlen").then_some("library/c/string.click")
}

/// Whether `header` declares the C library's `snprintf`,
/// `int snprintf(char *s, size_t n, const char *format, ...)`, whose calls
/// with a string-literal format Click models.
fn formatted_output_prototype(header: &CFunctionHeader) -> bool {
    header.source_name == "snprintf"
        && !header.internal_linkage
        && header.variadic
        && header.return_type == InterfaceType::Int32
        && matches!(
            header.parameters.as_slice(),
            [buffer, size, format]
                if matches!(buffer.interface_type, InterfaceType::CharPointer(_))
                    && !buffer.pointee_constant
                    && size.interface_type == InterfaceType::UInt64(LongRank::Long)
                    && matches!(format.interface_type, InterfaceType::CharPointer(_))
                    && format.pointee_constant
        )
}

/// The library function Click specifies that `header` declares with
/// external linkage, by its C name or its linked symbol: the function's
/// name, its standard prototype, and whether the declared type is
/// compatible with that prototype.
fn library_function_prototype(
    header: &CFunctionHeader,
) -> Option<(&'static str, &'static str, bool)> {
    if header.internal_linkage {
        return None;
    }
    let (name, prototype, return_type, parameters) = LIBRARY_PROTOTYPES
        .iter()
        .find(|(name, ..)| *name == header.name.as_str() || *name == header.source_name.as_str())?;
    let compatible = !header.variadic
        && !header.opaque_signature
        && return_type.matches(
            header.return_type,
            header.return_pointee_constant,
            false,
            header.return_struct_name.is_some() || header.return_pointer_struct_name.is_some(),
        )
        // A declaration without a prototype is compatible with a prototype
        // whose parameter types are unchanged by the default argument
        // promotions, as each library prototype's are (C11 6.7.6.3p15).
        && (header.empty_parameter_list
            || header.parameters.len() == parameters.len()
                && header
                    .parameters
            .iter()
            .zip(parameters.iter())
            .all(|(parameter, expected)| {
                !parameter.reference
                    && expected.matches(
                        parameter.interface_type,
                        parameter.pointee_constant,
                        parameter.pointee_volatile,
                        parameter.struct_name.is_some()
                            || parameter.union_name.is_some()
                            || parameter.function_pointer_signature.is_some(),
                    )
            }));
    Some((*name, *prototype, compatible))
}

/// A `long long` scalar, pointer, or array type spelled in C: Click's
/// `int64`/`uint64` names would not tell it from `long`.
fn describe_long_long_type(interface_type: InterfaceType) -> String {
    let (base, suffix) = match interface_type {
        InterfaceType::Int64(_) => ("long long", String::new()),
        InterfaceType::UInt64(_) => ("unsigned long long", String::new()),
        InterfaceType::Int64Pointer(_) => ("long long", " *".to_string()),
        InterfaceType::UInt64Pointer(_) => ("unsigned long long", " *".to_string()),
        InterfaceType::Int64PointerPointer(_) => ("long long", " **".to_string()),
        InterfaceType::UInt64PointerPointer(_) => ("unsigned long long", " **".to_string()),
        InterfaceType::Int64Array(_, length) => ("long long", format!("[{length}]")),
        InterfaceType::UInt64Array(_, length) => ("unsigned long long", format!("[{length}]")),
        other => return format!("{other:?}"),
    };
    format!("{base}{suffix}")
}

/// The declared type of a function, spelled with Click's C type names, for a
/// diagnostic that compares it with another.
fn describe_function_header_type(header: &CFunctionHeader) -> String {
    let describe = |interface_type: InterfaceType,
                    struct_name: Option<&str>,
                    pointee_constant: bool,
                    pointee_volatile: bool| {
        let base = match (interface_type, struct_name) {
            (InterfaceType::FunctionPointer(_), _) => "function pointer".to_string(),
            (_, Some(name)) if interface_type.is_pointer() => format!("struct {name} *"),
            (_, Some(name)) => format!("struct {name}"),
            (InterfaceType::Char(_), None) => "char".to_string(),
            (InterfaceType::CharPointer(_), None) => "char *".to_string(),
            (InterfaceType::CharPointerPointer(_), None) => "char **".to_string(),
            (_, None) if interface_type.long_rank() == Some(LongRank::LongLong) => {
                describe_long_long_type(interface_type)
            }
            _ => {
                let spelling =
                    crate::kernel::program_type_spelling(interface_type.to_kernel_type());
                let pointee = spelling.trim_end_matches('*');
                if pointee.len() == spelling.len() {
                    spelling.to_string()
                } else {
                    format!("{pointee} {}", &spelling[pointee.len()..])
                }
            }
        };
        let mut qualifiers = String::new();
        if pointee_constant {
            qualifiers.push_str("const ");
        }
        if pointee_volatile {
            qualifiers.push_str("volatile ");
        }
        format!("{qualifiers}{base}")
    };
    let return_type = describe(
        header.return_type,
        header
            .return_struct_name
            .as_deref()
            .or(header.return_pointer_struct_name.as_deref()),
        header.return_pointee_constant,
        false,
    );
    let mut parameters = header
        .parameters
        .iter()
        .map(|parameter| {
            describe(
                parameter.interface_type,
                parameter
                    .struct_name
                    .as_deref()
                    .or(parameter.union_name.as_deref()),
                parameter.pointee_constant,
                parameter.pointee_volatile,
            )
        })
        .collect::<Vec<_>>();
    if header.variadic {
        parameters.push("...".to_string());
    }
    if parameters.is_empty() && !header.empty_parameter_list {
        parameters.push("void".to_string());
    }
    format!("{return_type} ({})", parameters.join(", "))
}

fn function_headers_compatible(left: &CFunctionHeader, right: &CFunctionHeader) -> bool {
    left.return_type == right.return_type
        && left.return_pointee_constant == right.return_pointee_constant
        && left.return_struct_name == right.return_struct_name
        && left.return_pointer_struct_name == right.return_pointer_struct_name
        && left.internal_linkage == right.internal_linkage
        && left.weak_linkage == right.weak_linkage
        && left.returns_twice == right.returns_twice
        && left.variadic == right.variadic
        && left.opaque_signature == right.opaque_signature
        && (!left.opaque_signature || left.opaque_signature_types == right.opaque_signature_types)
        && left.opaque_attributes == right.opaque_attributes
        && left.compile_time_error == right.compile_time_error
        && left.name == right.name
        && left.parameters.len() == right.parameters.len()
        && left
            .parameters
            .iter()
            .zip(&right.parameters)
            .all(|(left, right)| {
                left.interface_type == right.interface_type
                    && left.pointee_is_constant() == right.pointee_is_constant()
                    && left.struct_name == right.struct_name
                    && left.union_name == right.union_name
                    && left.function_pointer_signature == right.function_pointer_signature
                    && left.array_element_width == right.array_element_width
            })
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum CLoopContext {
    While,
    For,
    DoWhile,
    Switch,
}

impl Parser {
    fn new(source: &str, abi: CAbi) -> Result<Self, CSyntaxError> {
        Self::new_with_source_identity(source, abi, None)
    }

    /// The value of the character constant whose byte is `byte`. C11
    /// 6.4.4.4p10 gives it the `int` value of a plain `char` holding the
    /// byte, so under a signed plain `char` a byte of 0x80 or more is
    /// negative. A byte below 0x80 has the same value under either target
    /// and keeps its unsigned-byte literal.
    fn character_constant(&self, byte: u8) -> CExpression {
        match self.plain_char.character_value(byte) {
            value if value < 0 => CExpression::Int32Literal(value as i32 as u32),
            _ => CExpression::UInt8Literal(byte),
        }
    }

    /// A character constant written as an array designator index.
    fn character_designator_index(&self, byte: u8) -> Result<u32, CSyntaxError> {
        u32::try_from(self.plain_char.character_value(byte)).map_err(|_| {
            self.error_at_previous(format!(
                "character constant designator index `{}` is negative under this target's signed plain `char`",
                (byte as char).escape_default()
            ))
        })
    }

    /// Selects the target's plain `char` signedness. Every parser starts
    /// with the default target's, which the test-only entry points keep.
    fn with_target(mut self, target: super::target::CTarget) -> Self {
        self.plain_char = target.plain_char();
        self.int64_t_rank = target.int64_t_rank();
        self
    }

    fn new_with_source_identity(
        source: &str,
        abi: CAbi,
        source_identity: Option<&str>,
    ) -> Result<Self, CSyntaxError> {
        let (tokens, positions) = tokenize(source)?;
        Self::from_tokens(source, tokens, positions, abi, source_identity, false)
    }

    fn new_with_source_identity_and_map(
        source: &str,
        abi: CAbi,
        source_identity: Option<&str>,
        map: &CSourceMap,
    ) -> Result<Self, CSyntaxError> {
        let (tokens, positions) = tokenize(source).map_err(|error| {
            let position = error.position().map(|position| map.lookup(position));
            match position {
                Some(position) => CSyntaxError::at(position, error.message()),
                None => error,
            }
        })?;
        let positions = positions
            .into_iter()
            .map(|position| map.lookup(position))
            .collect();
        Self::from_tokens(source, tokens, positions, abi, source_identity, true)
    }

    /// Parses source-bundle C while attributing diagnostics to the bundle
    /// file and line behind each expanded line. `source_identity` remains the
    /// translation-unit linkage identity and is deliberately independent of
    /// the diagnostic origin filename.
    fn new_with_source_identity_and_line_map(
        source: &str,
        abi: CAbi,
        source_identity: Option<&str>,
        line_map: &ExpandedLineMap,
    ) -> Result<Self, CSyntaxError> {
        let (tokens, positions) = tokenize(source).map_err(|error| {
            let position = error.position().map(|position| line_map.lookup(position));
            match position {
                Some(position) => CSyntaxError::at(position, error.message()),
                None => error,
            }
        })?;
        let positions = positions
            .into_iter()
            .map(|position| line_map.lookup(position))
            .collect();
        let mut parser = Self::from_tokens(source, tokens, positions, abi, source_identity, false)?;
        parser.written_lines = std::sync::Arc::new(line_map.written_lines().clone());
        Ok(parser)
    }

    fn from_tokens(
        source: &str,
        mut tokens: Vec<Token>,
        positions: Vec<SourcePosition>,
        abi: CAbi,
        source_identity: Option<&str>,
        import_mode: bool,
    ) -> Result<Self, CSyntaxError> {
        // The modeled <stdio.h> projects the stdout macro through a reserved
        // identifier. Keep the source name in both C and sidecar bindings.
        for token in &mut tokens {
            if let Token::Ident(name) = token
                && name == HOSTED_STDOUT_BINDING
            {
                *name = "stdout".into();
            }
        }
        Ok(Self {
            tokens,
            positions,
            source_lines: source.split('\n').map(Box::from).collect(),
            written_lines: std::sync::Arc::default(),
            position: 0,
            structs: DeclarationMap::new(),
            bit_field_records: BTreeMap::new(),
            local_bit_fields: BTreeMap::new(),
            bit_field_forbidden_operand: false,
            unevaluated_operand: false,
            function_has_bit_fields: false,
            enums: DeclarationMap::new(),
            enum_constants: BTreeMap::new(),
            typedefs: BTreeMap::new(),
            parsing_function_header: false,
            opaque_function_signature: false,
            opaque_signature_types: Vec::new(),
            variable_structs: Default::default(),
            local_struct_pointers: BTreeMap::new(),
            local_struct_values: BTreeMap::new(),
            local_pointers: BTreeMap::new(),
            variable_struct_values: BTreeMap::new(),
            variable_array_shapes: Default::default(),
            local_row_pointers: Default::default(),
            incomplete_array_names: BTreeSet::new(),
            variable_types: CVariableTypes::default(),
            variable_function_pointers: BTreeMap::new(),
            variable_constants: BTreeSet::new(),
            variable_pointee_constants: BTreeSet::new(),
            unions: DeclarationMap::new(),
            scopes: Vec::new(),
            compound_literal_declarations: Vec::new(),
            repeatable_compound_literal_scope: None,
            function_has_compound_literals: false,
            function_has_goto: false,
            visible_bindings: CSourceBindings::new(),
            loop_source_bindings: BTreeMap::new(),
            binding_function: None,
            parsing_binding_parameters: false,
            next_parameter_binding: 0,
            next_local_binding: 0,
            out_of_scope_names: BTreeSet::new(),
            address_taken_variables: BTreeSet::new(),
            next_static_binding: 0,
            file_static_bindings: BTreeMap::new(),
            next_call_result: 0,
            aggregate_expression_steps: Vec::new(),
            callback_statement_sources: imbl::OrdMap::new(),
            next_field_source_ordinal: 0,
            loop_contexts: Vec::new(),
            function_declarations: BTreeMap::new(),
            static_inline_attribute: "always-inline",
            unnamed_parameters: 0,
            error_attribute: None,
            refuse_promises: false,
            pending_noreturn: None,
            block_function_declarations: Vec::new(),
            statement_call: false,
            formatted_output_call: std::cell::RefCell::new(None),
            function_declaration_lines: BTreeMap::new(),
            shadowed_pthread_names: BTreeSet::new(),
            function_source_names: BTreeMap::new(),
            defined_functions: BTreeSet::new(),
            globals: DeclarationMap::new(),
            global_arrays: DeclarationMap::new(),
            global_aggregates: DeclarationMap::new(),
            global_aggregate_arrays: DeclarationMap::new(),
            referenced_external_objects: BTreeSet::new(),
            static_locals: BTreeMap::new(),
            static_arrays: BTreeMap::new(),
            static_aggregates: BTreeMap::new(),
            static_aggregate_arrays: BTreeMap::new(),
            string_literals: Vec::new(),
            header_mode: false,
            source_identity: source_identity.map(str::to_string),
            current_function_source_name: None,
            import_mode,
            abi,
            plain_char: super::target::CTarget::SUPPORTED.plain_char(),
            int64_t_rank: super::target::CTarget::SUPPORTED.int64_t_rank(),
            current_return_struct_name: None,
            current_return_pointer_struct_name: None,
            current_return_type: InterfaceType::Void,
            current_return_pointee_constant: false,
            function_block_depth: 0,
            controlled_statement_depth: 0,
            source_regions: Vec::new(),
            source_label_body: false,
        })
    }

    fn push_scope(&mut self) {
        self.scopes.push(Vec::new());
        self.compound_literal_declarations.push(Vec::new());
    }

    /// Closes the innermost scope; its names, and any struct layouts they
    /// carried, are no longer visible.
    fn pop_scope(&mut self) {
        self.compound_literal_declarations.pop();
        let depth = self.scopes.len();
        while let Some((declared_depth, _)) = self.block_function_declarations.last()
            && *declared_depth >= depth
        {
            let (_, source_name) = self
                .block_function_declarations
                .pop()
                .expect("the last entry was just inspected");
            if let Some(header) = self.function_declarations.remove(&source_name) {
                self.function_source_names.remove(&header.name);
            }
        }
        for binding in self.scopes.pop().unwrap_or_default().into_iter().rev() {
            if let Some(source_name) = &binding.source_name {
                if let Some(previous) = &binding.previous_visible {
                    self.visible_bindings
                        .insert(source_name.clone(), previous.clone());
                } else {
                    self.visible_bindings.remove(source_name);
                }
            }
            self.local_bit_fields.remove(&binding.kernel_name);
            self.variable_structs.remove(&binding.kernel_name);
            self.variable_struct_values.remove(&binding.kernel_name);
            self.variable_array_shapes.remove(&binding.kernel_name);
            if let Some(row) = self.local_row_pointers.remove(&binding.kernel_name) {
                self.variable_types.remove(&row.storage);
            }
            self.variable_types.remove(&binding.kernel_name);
            self.variable_function_pointers.remove(&binding.kernel_name);
            self.variable_constants.remove(&binding.kernel_name);
            self.variable_pointee_constants.remove(&binding.kernel_name);
            self.incomplete_array_names.remove(&binding.kernel_name);
            if let Some(metadata) = binding.shadowed {
                let name = binding.kernel_name;
                self.variable_types
                    .insert(name.clone(), metadata.interface_type);
                if let Some(value) = metadata.struct_name {
                    self.variable_structs.insert(name.clone(), value);
                }
                if let Some(value) = metadata.struct_value {
                    self.variable_struct_values.insert(name.clone(), value);
                }
                if let Some(value) = metadata.array_shape {
                    self.variable_array_shapes.insert(name.clone(), value);
                }
                if let Some(value) = metadata.function_pointer {
                    self.variable_function_pointers.insert(name.clone(), value);
                }
                if metadata.constant {
                    self.variable_constants.insert(name.clone());
                }
                if metadata.pointee_constant {
                    self.variable_pointee_constants.insert(name.clone());
                }
                if metadata.incomplete_array {
                    self.incomplete_array_names.insert(name);
                }
            }
        }
    }

    fn pop_for_scope(&mut self) {
        let names = self
            .scopes
            .last()
            .into_iter()
            .flat_map(|scope| scope.iter())
            .filter_map(|binding| binding.source_name.clone())
            .collect::<Vec<_>>();
        self.pop_scope();
        for name in names {
            let remains_visible = self.visible_bindings.contains_key(&name)
                || self.globals.contains_key(&name)
                || self.global_arrays.contains_key(&name)
                || self.global_aggregates.contains_key(&name)
                || self.global_aggregate_arrays.contains_key(&name);
            if remains_visible {
                self.out_of_scope_names.remove(&name);
            } else {
                self.out_of_scope_names.insert(name);
            }
        }
    }

    fn resolve_name(&self, source_name: &str) -> BindingName {
        self.visible_bindings
            .get(source_name)
            .map(|(_, binding)| binding.clone())
            .or_else(|| {
                self.globals
                    .get(source_name)
                    .map(|global| global.kernel_name().into())
            })
            .or_else(|| {
                self.global_arrays
                    .get(source_name)
                    .map(|global| global.kernel_name().into())
            })
            .or_else(|| {
                self.global_aggregates
                    .get(source_name)
                    .map(|global| global.kernel_name().into())
            })
            .or_else(|| {
                self.global_aggregate_arrays
                    .get(source_name)
                    .map(|global| global.kernel_name().into())
            })
            .unwrap_or_else(|| source_name.into())
    }

    /// Whether `name`, already resolved by [`Self::resolve_name`], is an
    /// object this translation unit declares. `resolve_name` falls back to the
    /// source spelling for a name it does not know, so the only way to tell a
    /// declared object from an undeclared identifier is to look the resolved
    /// name back up. This walks every declaration, so call it only on a path
    /// that is already reporting an error.
    fn declares_resolved_object(&self, name: &BindingName) -> bool {
        self.variable_types.contains_key(name)
            || self
                .scopes
                .iter()
                .flat_map(|scope| scope.iter())
                .any(|binding| binding.kernel_name == (name).into())
            || self
                .globals
                .values()
                .any(|global| name == global.kernel_name())
            || self
                .global_arrays
                .values()
                .any(|global| name == global.kernel_name())
            || self
                .global_aggregates
                .values()
                .any(|global| name == global.kernel_name())
            || self
                .global_aggregate_arrays
                .values()
                .any(|global| name == global.kernel_name())
    }

    /// Whether `source_name`, as spelled in the source, names an object this
    /// translation unit currently declares. The source-keyed lookups answer
    /// every visible name on their own; the resolved-name walk runs only when
    /// they all miss, which is the path that is about to report an error.
    fn declares_source_object(&self, source_name: &str) -> bool {
        self.visible_bindings.contains_key(source_name)
            || self.globals.contains_key(source_name)
            || self.global_arrays.contains_key(source_name)
            || self.global_aggregates.contains_key(source_name)
            || self.global_aggregate_arrays.contains_key(source_name)
            || self.declares_resolved_object(&self.resolve_name(source_name))
    }

    /// Resolves a name used in a value position. A name this translation unit
    /// never declared, and a name whose declaration has gone out of scope,
    /// are both rejected here rather than lowered to a variable the kernel
    /// would later report as unbound.
    fn resolve_object_name(
        &mut self,
        source_name: &str,
        position: Option<SourcePosition>,
    ) -> Result<BindingName, CSyntaxError> {
        let name = self.resolve_name(source_name);
        if !self.out_of_scope_names.contains(source_name)
            && self.declares_source_object(source_name)
        {
            if self
                .globals
                .get(source_name)
                .is_some_and(|object| !object.is_file_static())
                || self
                    .global_arrays
                    .get(source_name)
                    .is_some_and(|object| !object.is_file_static())
                || self
                    .global_aggregates
                    .get(source_name)
                    .is_some_and(|object| !object.is_file_static())
                || self
                    .global_aggregate_arrays
                    .get(source_name)
                    .is_some_and(|object| !object.is_file_static())
            {
                self.referenced_external_objects
                    .insert(source_name.to_owned());
            }
            Ok(name)
        } else {
            Err(self.error_at_position(
                position,
                format!("use of undeclared identifier `{source_name}`"),
            ))
        }
    }

    fn variable_is_constant(&self, name: &BindingName) -> bool {
        self.variable_constants.contains(name)
            || name
                .named()
                .and_then(|name| self.globals.get(name))
                .is_some_and(CGlobal::is_constant)
            || self
                .globals
                .values()
                .find(|global| name == global.kernel_name())
                .is_some_and(CGlobal::is_constant)
            || name
                .named()
                .and_then(|name| self.global_arrays.get(name))
                .is_some_and(CGlobalArray::is_constant)
            || self
                .global_arrays
                .values()
                .find(|global| name == global.kernel_name())
                .is_some_and(CGlobalArray::is_constant)
            || name
                .named()
                .and_then(|name| self.global_aggregates.get(name))
                .is_some_and(CGlobalAggregate::is_constant)
            || self
                .global_aggregates
                .values()
                .find(|global| name == global.kernel_name())
                .is_some_and(CGlobalAggregate::is_constant)
            || name
                .named()
                .and_then(|name| self.global_aggregate_arrays.get(name))
                .is_some_and(CGlobalAggregateArray::is_constant)
            || self
                .global_aggregate_arrays
                .values()
                .find(|global| name == global.kernel_name())
                .is_some_and(CGlobalAggregateArray::is_constant)
    }

    fn variable_pointee_is_constant(&self, name: &BindingName) -> bool {
        self.variable_pointee_constants.contains(name)
    }

    fn expression_is_constant_lvalue(&self, expression: &CExpression) -> bool {
        match expression {
            CExpression::Variable(name) => self.variable_is_constant(name),
            CExpression::Load(pointer, _) => self.expression_pointee_is_constant(pointer),
            CExpression::Index(base, _, _) => self.expression_pointee_is_constant(base),
            CExpression::Field { pointer, .. } | CExpression::UnionField { pointer, .. } => {
                self.expression_is_constant_lvalue(pointer)
                    || self.expression_pointee_is_constant(pointer)
            }
            CExpression::AggregateAddress { pointer, .. }
            | CExpression::UnionAddress { pointer, .. } => {
                self.expression_is_constant_lvalue(pointer)
            }
            CExpression::StatementExpression {
                aggregate_lvalue: true,
                pointee_constant,
                ..
            } => *pointee_constant,
            _ => false,
        }
    }

    fn expression_pointee_is_constant(&self, expression: &CExpression) -> bool {
        match expression {
            CExpression::Field {
                pointee_constant, ..
            }
            | CExpression::UnionField {
                pointee_constant, ..
            } => *pointee_constant,
            CExpression::Assignment {
                pointee_constant, ..
            }
            | CExpression::ScalarUpdate {
                pointee_constant, ..
            } => *pointee_constant,
            CExpression::SequentialRead { target, .. }
            | CExpression::SequentialWrite { target, .. } => {
                self.expression_pointee_is_constant(target)
            }
            CExpression::Call { function_name, .. } => {
                self.call_return_pointee_is_constant(function_name)
            }
            CExpression::IndirectCall { signature, .. } => signature.return_pointee_constant,
            CExpression::Variable(name) => {
                self.variable_pointee_is_constant(name)
                    || (self.variable_is_constant(name)
                        && (self.incomplete_array_names.contains(name)
                            || self.variable_types.get(name).is_some_and(|interface_type| {
                                matches!(
                                    interface_type,
                                    InterfaceType::Int8Array(_)
                                        | InterfaceType::Int16Array(_)
                                        | InterfaceType::CharArray(_, _)
                                        | InterfaceType::UInt8Array(_)
                                        | InterfaceType::UInt16Array(_)
                                        | InterfaceType::UInt32Array(_)
                                        | InterfaceType::Int32Array(_)
                                        | InterfaceType::Int128Array(_)
                                        | InterfaceType::Int64Array(_, _)
                                        | InterfaceType::UInt128Array(_)
                                        | InterfaceType::UInt64Array(_, _)
                                        | InterfaceType::Float32Array(_)
                                        | InterfaceType::Float64Array(_)
                                )
                            })))
            }
            CExpression::AddressOf(target) => self.expression_is_constant_lvalue(target),
            CExpression::PointerOffsetBytes { pointer, .. }
            | CExpression::Subobject { pointer, .. }
            | CExpression::Subtract(pointer, _) => self.expression_pointee_is_constant(pointer),
            CExpression::Add(left, right) => {
                self.expression_pointee_is_constant(left)
                    || self.expression_pointee_is_constant(right)
            }
            CExpression::Cast {
                expression,
                pointee_constant,
                explicit_qualification,
                ..
            } => {
                *pointee_constant
                    || (!*explicit_qualification && self.expression_pointee_is_constant(expression))
            }
            CExpression::Ternary {
                then_branch,
                else_branch,
                ..
            } => {
                self.expression_pointee_is_constant(then_branch)
                    || self.expression_pointee_is_constant(else_branch)
            }
            CExpression::StatementExpression {
                pointee_constant, ..
            } => *pointee_constant,
            // An element of a static pointer table, such as `units_10[i]` of
            // `static const char *const units_10[]`.
            CExpression::Index(base, _, _) => matches!(
                base.as_ref(),
                CExpression::Variable(name)
                    if self.static_arrays.get(name)
                        .is_some_and(CStaticArray::pointee_is_constant)
            ),
            _ => false,
        }
    }

    fn is_aggregate_result_member(&self, expression: &CExpression) -> bool {
        let CExpression::Field { pointer, .. } = expression else {
            return false;
        };
        let mut base = pointer.as_ref();
        loop {
            match base {
                CExpression::Subobject { pointer, .. }
                | CExpression::PointerOffsetBytes { pointer, .. }
                | CExpression::Cast {
                    expression: pointer,
                    ..
                } => base = pointer,
                CExpression::Call { .. }
                | CExpression::IndirectCall { .. }
                | CExpression::Ternary { .. }
                | CExpression::StepResult { .. } => {
                    return self.aggregate_struct_name(base).is_some();
                }
                _ => return false,
            }
        }
    }

    fn reject_constant_lvalue_write(&self, expression: &CExpression) -> Result<(), CSyntaxError> {
        if self.is_aggregate_result_member(expression) {
            return Err(
                self.error_here("a member of an aggregate expression result is not an lvalue")
            );
        }
        if self.expression_is_constant_lvalue(expression) {
            Err(self.error_here("cannot modify a const-qualified lvalue"))
        } else {
            Ok(())
        }
    }

    fn reject_discarded_const_pointer(
        &self,
        declared_type: InterfaceType,
        declared_pointee_constant: bool,
        expression: &mut CExpression,
    ) -> Result<(), CSyntaxError> {
        self.validate_char_pointer_assignment(declared_type, expression)?;
        convert_integer_constant(declared_type, expression);
        if declared_type.is_pointer()
            && !declared_pointee_constant
            && self.expression_pointee_is_constant(expression)
        {
            return Err(
                self.error_here("cannot discard const qualification from a pointer initializer")
            );
        }
        Ok(())
    }

    fn static_object_type(&self, name: &BindingName) -> Option<(InterfaceType, bool)> {
        if let Some(global) = self
            .globals
            .values()
            .find(|global| name.is_named(global.name()) || global.kernel_name() == name)
        {
            return Some((global.interface_type(), global.is_constant()));
        }
        if let Some(global_array) = self
            .global_arrays
            .values()
            .find(|global| name.is_named(global.name()) || global.kernel_name() == name)
        {
            return Some((global_array.complete_c_type()?, global_array.is_constant()));
        }
        if let Some(global_aggregate) = self
            .global_aggregates
            .values()
            .find(|global| name.is_named(global.name()) || global.kernel_name() == name)
        {
            return Some((
                record_value_type(global_aggregate.layout()),
                global_aggregate.is_constant(),
            ));
        }
        if let Some(global_aggregate_array) = self
            .global_aggregate_arrays
            .values()
            .find(|global| name.is_named(global.name()) || global.kernel_name() == name)
        {
            return Some((
                global_aggregate_array.complete_c_type()?,
                global_aggregate_array.is_constant(),
            ));
        }
        if let Some(static_local) = self.static_locals.values().find(|static_local| {
            name.is_named(static_local.name()) || static_local.kernel_name() == name
        }) {
            return Some((static_local.interface_type(), static_local.is_constant()));
        }
        if let Some(static_array) = self.static_arrays.values().find(|static_array| {
            name.is_named(static_array.name()) || static_array.kernel_name() == name
        }) {
            return Some((static_array.interface_type(), static_array.is_constant()));
        }
        if let Some(static_aggregate) = self.static_aggregates.values().find(|static_aggregate| {
            name.is_named(static_aggregate.name()) || static_aggregate.kernel_name() == name
        }) {
            return Some((
                record_value_type(static_aggregate.layout()),
                static_aggregate.is_constant(),
            ));
        }
        self.static_aggregate_arrays
            .values()
            .find(|static_aggregate_array| {
                name.is_named(static_aggregate_array.name())
                    || static_aggregate_array.kernel_name() == name
            })
            .map(|static_aggregate_array| {
                (
                    static_aggregate_array.interface_type(),
                    static_aggregate_array.is_constant(),
                )
            })
    }

    fn static_address_expression(&self, expression: &CExpression) -> Option<(InterfaceType, bool)> {
        match expression {
            CExpression::StringLiteral(literal) if literal.identity.is_some() => Some((
                InterfaceType::CharArray(
                    literal.plain_char(),
                    u32::try_from(literal.bytes().len()).expect("literal length fits u32"),
                ),
                false,
            )),
            CExpression::Variable(name) => self.static_object_type(name),
            CExpression::Field {
                pointer,
                field_type,
                ..
            }
            | CExpression::UnionField {
                pointer,
                field_type,
                ..
            } => {
                let (_, constant) = self.static_address_expression(pointer)?;
                Some((*field_type, constant))
            }
            CExpression::Index(base, index, _) => {
                let (base_type, constant) = self.static_address_expression(base)?;
                static_integer_value(index)?;
                Some((base_type.pointee_type()?, constant))
            }
            CExpression::PointerOffsetBytes { pointer, .. }
            | CExpression::Subobject { pointer, .. } => self.static_address_expression(pointer),
            CExpression::Add(pointer, offset) => {
                static_integer_value(offset)?;
                self.static_address_expression(pointer)
            }
            CExpression::AggregateAddress {
                pointer,
                struct_name,
            } => {
                let (_, constant) = self.static_address_expression(pointer)?;
                Some((record_value_type(self.structs.get(struct_name)?), constant))
            }
            CExpression::UnionAddress {
                pointer,
                union_name,
            } => {
                let (_, constant) = self.static_address_expression(pointer)?;
                Some((
                    InterfaceType::UInt8Array(self.unions.get(union_name)?.size_bytes),
                    constant,
                ))
            }
            CExpression::Cast {
                expression,
                interface_type,
                ..
            } => {
                let (_, constant) = self.static_address_expression(expression)?;
                Some((*interface_type, constant))
            }
            _ => None,
        }
    }

    /// A pointer initializer naming an array object, such as a string
    /// literal or another static table, as the address of its first element
    /// (C11 6.3.2.1p3); any other initializer unchanged.
    fn decayed_static_pointer_initializer(&self, initializer: &CExpression) -> CExpression {
        if self
            .static_address_expression(initializer)
            .is_some_and(|(ty, _)| ty.array_length().is_some())
        {
            return CExpression::AddressOf(Box::new(CExpression::Index(
                Box::new(initializer.clone()),
                Box::new(CExpression::Int32Literal(0)),
                None,
            )));
        }
        initializer.clone()
    }

    fn static_address_target(&self, expression: &CExpression) -> Option<(InterfaceType, bool)> {
        let CExpression::AddressOf(target) = expression else {
            return None;
        };
        self.static_address_expression(target)
    }

    fn validate_static_pointer_initializer(
        &self,
        declared_type: InterfaceType,
        declared_pointee_constant: bool,
        initializer: &CExpression,
    ) -> Result<(), CSyntaxError> {
        if matches!(initializer, CExpression::Int32Literal(0)) {
            return Ok(());
        }
        let Some((target_type, target_is_constant)) = self.static_address_target(initializer)
        else {
            if matches!(initializer, CExpression::StringLiteral(_)) {
                return Err(self.error_here(
                    "file-scope pointer initializers do not support string literals yet",
                ));
            }
            return Err(self.error_here(
                "static pointer initializers currently support only null or the address of a declared object or subobject",
            ));
        };
        let Some(expected_type) = target_type.pointer_type() else {
            return Err(self.error_here(
                "static pointer initializers currently support only addresses of scalar objects or scalar subobjects",
            ));
        };
        if expected_type != declared_type {
            return Err(self.error_here(format!(
                "address initializer has type `{expected_type:?}`, but `{declared_type:?}` is required"
            )));
        }
        if target_is_constant && !declared_pointee_constant {
            return Err(
                self.error_here("cannot discard const qualification from a pointer initializer")
            );
        }
        Ok(())
    }

    /// Whether the `static` declaration at the cursor declares a function:
    /// its first parenthesis outside an attribute directly follows the
    /// declared name. `static int (*callback)(int);` declares an object, and
    /// so does anything that reaches `=`, `[`, `;`, or `{` first.
    fn static_function_declarator_ahead(&self) -> bool {
        let mut offset = 1;
        loop {
            match self.peek_n(offset) {
                Some(Token::Ident(name)) if name == "__attribute__" => {
                    offset += 1;
                    let mut depth = 0usize;
                    loop {
                        match self.peek_n(offset) {
                            Some(Token::LParen) => depth += 1,
                            Some(Token::RParen) => {
                                depth = depth.saturating_sub(1);
                                if depth == 0 {
                                    break;
                                }
                            }
                            None => return false,
                            _ => {}
                        }
                        offset += 1;
                    }
                }
                Some(Token::LParen) => {
                    return matches!(self.peek_n(offset - 1), Some(Token::Ident(_)))
                        && !self.is_type_start_at(offset - 1)
                        && self.peek_n(offset + 1) != Some(&Token::Star);
                }
                Some(Token::Ident(_) | Token::Star) => {}
                _ => return false,
            }
            offset += 1;
        }
    }

    fn file_static_kernel_name(&mut self, source_name: &str) -> BindingName {
        let next = self.file_static_bindings.len() as u32;
        self.file_static_bindings
            .entry(source_name.to_owned())
            .or_insert_with(|| {
                StaticBindingId::new(
                    StaticBindingOwner::File(self.source_identity.clone()),
                    next,
                    source_name.to_owned(),
                )
            })
            .clone()
            .into()
    }

    fn inline_function_kernel_name(&self, source_name: &str) -> String {
        format!(
            "{source_name}#inline:{}",
            self.source_identity.as_deref().unwrap_or("source")
        )
    }

    /// The declaration behind a call target. Calls carry the kernel name,
    /// which for a `static inline` header function is the mangled
    /// internal-linkage name rather than the declaration's source name.
    fn function_declaration_for_call(&self, function_name: &str) -> Option<&CFunctionHeader> {
        self.function_declarations.get(function_name).or_else(|| {
            self.function_source_names
                .get(function_name)
                .and_then(|name| self.function_declarations.get(name))
        })
    }

    fn resolve_function_name(&self, source_name: &str) -> String {
        self.function_declarations
            .get(source_name)
            .map(|function| function.name.clone())
            .unwrap_or_else(|| source_name.to_string())
    }

    fn function_declaration(&self, name: &str) -> Option<&CFunctionHeader> {
        self.function_declaration_for_call(name)
    }

    /// C decays a bare function designator to a pointer to that function in
    /// every position where a value is expected, so `f` and `&f` denote the
    /// same address. Only a name this translation unit declares as a function
    /// decays; a name it knows as an object, a name whose declaration has gone
    /// out of scope, and a name it does not know at all stay object references
    /// so they keep their ordinary diagnostics. Call positions never reach
    /// here, so `f(x)` remains a call.
    fn bare_function_designator(
        &self,
        source_name: &str,
    ) -> Result<Option<CExpression>, CSyntaxError> {
        if self.out_of_scope_names.contains(source_name)
            || self
                .variable_types
                .contains_key(&self.resolve_name(source_name))
            || !self.function_declarations.contains_key(source_name)
        {
            return Ok(None);
        }
        if self
            .function_declarations
            .get(source_name)
            .is_some_and(|header| header.opaque_attributes)
        {
            return Err(self.error_here(format!("function `{source_name}` uses declaration-only compiler attributes; function-address uses require modeled semantics")));
        }
        if self
            .function_declarations
            .get(source_name)
            .is_some_and(|header| header.opaque_signature)
        {
            return Err(self.error_here(format!(
                "function `{source_name}` uses declaration-only signature (__builtin_va_list or long double); function-address uses require a modeled ABI"
            )));
        }
        if self
            .function_declarations
            .get(source_name)
            .is_some_and(|header| header.weak_linkage)
        {
            return Err(self.error_here(format!(
                "weak function `{source_name}` may be absent; function-address uses need an availability model"
            )));
        }
        if self
            .function_declarations
            .get(source_name)
            .is_some_and(|header| header.compile_time_error)
        {
            return Err(self.error_here(format!(
                "function `{source_name}` is declared with the GNU `error` attribute; its address cannot be used"
            )));
        }
        if self
            .function_declarations
            .get(source_name)
            .is_some_and(|header| header.variadic)
        {
            return Err(self.error_here(format!(
                "variadic function `{source_name}` has no modeled variable-argument signature; function-address uses are not supported"
            )));
        }
        if self
            .function_declarations
            .get(source_name)
            .is_some_and(|header| header.returns_twice)
        {
            return Err(self.error_here(format!(
                "returns-twice function `{source_name}` needs a checked control-flow model"
            )));
        }
        Ok(Some(CExpression::FunctionAddress(
            self.resolve_function_name(source_name),
        )))
    }

    fn new_automatic_binding(&mut self, spelling: Option<String>) -> BindingName {
        let Some(function) = self.binding_function.clone() else {
            return BindingName::Named(spelling.expect("a standalone binding has a source name"));
        };
        let counter = if self.parsing_binding_parameters {
            &mut self.next_parameter_binding
        } else {
            &mut self.next_local_binding
        };
        let ordinal = *counter;
        *counter = counter.checked_add(1).expect("binding ordinal fits u32");
        LocalBindingId::new(function, self.parsing_binding_parameters, ordinal, spelling)
            .with_scope_depth(self.scopes.len() as u32)
            .into()
    }

    /// Whether a file-scope object declared so far has this spelling.
    fn is_file_scope_object(&self, name: &str) -> bool {
        self.globals.contains_key(name)
            || self.global_arrays.contains_key(name)
            || self.global_aggregates.contains_key(name)
            || self.global_aggregate_arrays.contains_key(name)
            || self.file_static_bindings.contains_key(name)
    }

    /// Records a parameter or local declaration in the innermost scope. A
    /// shadowing declaration gets a kernel-only identity; source references
    /// continue to resolve by their ordinary C spelling. Call right after
    /// consuming the name token so a duplicate diagnostic points at it.
    fn declare_name(&mut self, name: &str) -> Result<BindingName, CSyntaxError> {
        if matches!(name, "pthread_create" | "pthread_join") {
            self.shadowed_pthread_names.insert(name.to_string());
        }
        if self.enum_constants.contains_key(name) {
            return Err(
                self.error_at_previous(format!("`{name}` is already declared as an enum constant"))
            );
        }
        if self
            .visible_bindings
            .get(name)
            .is_some_and(|(depth, _)| *depth == self.scopes.len().saturating_sub(1))
        {
            return Err(
                self.error_at_previous(format!("`{name}` is already declared in this scope"))
            );
        }
        self.out_of_scope_names.remove(name);
        let kernel_name = self.new_automatic_binding(Some(name.to_owned()));
        let previous_visible = self.visible_bindings.insert(
            name.to_owned(),
            (self.scopes.len().saturating_sub(1), kernel_name.clone()),
        );
        if let Some(function) = &self.binding_function {
            let shadows = previous_visible.is_some() || self.is_file_scope_object(name);
            function.record_declaration_spelling(name, shadows);
        }
        // A parameter may keep the source spelling of a file-scope object.
        // Save only that object's metadata, not the translation-unit tables.
        let shadowed = self
            .variable_types
            .remove(&kernel_name)
            .map(|interface_type| VariableMetadata {
                interface_type,
                struct_name: self.variable_structs.remove(&kernel_name),
                struct_value: self.variable_struct_values.remove(&kernel_name),
                array_shape: self.variable_array_shapes.remove(&kernel_name),
                function_pointer: self.variable_function_pointers.remove(&kernel_name),
                constant: self.variable_constants.remove(&kernel_name),
                pointee_constant: self.variable_pointee_constants.remove(&kernel_name),
                incomplete_array: self.incomplete_array_names.remove(&kernel_name),
            });
        match self.scopes.last_mut() {
            Some(scope) => scope.push(ScopeBinding {
                source_name: Some(name.to_string()),
                kernel_name: kernel_name.clone(),
                shadowed,
                previous_visible: previous_visible.clone(),
            }),
            None => self.scopes.push(vec![ScopeBinding {
                source_name: Some(name.to_string()),
                kernel_name: kernel_name.clone(),
                shadowed,
                previous_visible: previous_visible.clone(),
            }]),
        }
        Ok(kernel_name)
    }

    /// Records a static local with an identity that remains unique even when
    /// two sibling blocks reuse the same C spelling. The source spelling is
    /// retained in the scope table so later expressions resolve normally.
    fn declare_static_name(&mut self, name: &str) -> Result<BindingName, CSyntaxError> {
        if matches!(name, "pthread_create" | "pthread_join") {
            self.shadowed_pthread_names.insert(name.to_string());
        }
        if self.enum_constants.contains_key(name) {
            return Err(
                self.error_at_previous(format!("`{name}` is already declared as an enum constant"))
            );
        }
        if self
            .visible_bindings
            .get(name)
            .is_some_and(|(depth, _)| *depth == self.scopes.len().saturating_sub(1))
        {
            return Err(
                self.error_at_previous(format!("`{name}` is already declared in this scope"))
            );
        }
        self.out_of_scope_names.remove(name);
        let kernel_name: BindingName = StaticBindingId::new(
            StaticBindingOwner::Function(
                self.binding_function
                    .clone()
                    .expect("C static belongs to a function"),
            ),
            self.next_static_binding,
            name.to_owned(),
        )
        .into();
        self.next_static_binding = self.next_static_binding.saturating_add(1);
        let previous_visible = self.visible_bindings.insert(
            name.to_owned(),
            (self.scopes.len().saturating_sub(1), kernel_name.clone()),
        );
        // An automatic declaration of the same spelling could resolve to
        // this static, so the spelling no longer names one declaration.
        if let Some(function) = &self.binding_function {
            function.record_declaration_spelling(name, true);
        }
        match self.scopes.last_mut() {
            Some(scope) => scope.push(ScopeBinding {
                source_name: Some(name.to_string()),
                kernel_name: kernel_name.clone(),
                shadowed: None,
                previous_visible: previous_visible.clone(),
            }),
            None => self.scopes.push(vec![ScopeBinding {
                source_name: Some(name.to_string()),
                kernel_name: kernel_name.clone(),
                shadowed: None,
                previous_visible: previous_visible.clone(),
            }]),
        }
        Ok(kernel_name)
    }

    fn scalar_struct_value_layout(&self, struct_name: &str) -> Result<RecordLayout, CSyntaxError> {
        let layout = self.structs.get(struct_name).cloned().ok_or_else(|| {
            self.error_here(format!("unknown struct declaration `{struct_name}`"))
        })?;
        for field in layout.fields.values() {
            if let Some(union_name) = field.union_name.as_deref() {
                let union_layout = self.unions.get(union_name).ok_or_else(|| {
                    self.error_here(format!("unknown union declaration `{union_name}`"))
                })?;
                if union_layout
                    .fields
                    .values()
                    .any(|member| !member.kernel_copyable())
                {
                    return Err(self.error_here(format!(
                        "struct-by-value union `{union_name}` contains members whose typed copy is not yet supported"
                    )));
                }
                continue;
            }
            if let Some(nested_name) = field.struct_name.as_deref()
                && field.array_element_width.is_some()
                && field.array_shape.is_some()
            {
                self.scalar_struct_value_layout(nested_name)?;
                continue;
            }
            if field.interface_type == InterfaceType::Int32
                && field.struct_name.is_some()
                && field.array_element_width.is_none()
            {
                self.scalar_struct_value_layout(
                    field
                        .struct_name
                        .as_deref()
                        .expect("embedded struct field has a struct name"),
                )?;
                continue;
            }
            if field.union_name.is_some()
                || (field.struct_name.is_some()
                    && !field.interface_type.is_pointer()
                    && !matches!(field.interface_type, InterfaceType::PointerArray(_, _, _)))
                || !matches!(
                    field.interface_type,
                    InterfaceType::Bool
                        | InterfaceType::Int8 | InterfaceType::Int16
                        | InterfaceType::Int32
                        | InterfaceType::Char(_)
                        | InterfaceType::UInt8
                        | InterfaceType::UInt16
                        | InterfaceType::UInt32
                        | InterfaceType::Int64(_)
                        | InterfaceType::UInt64(_)
                        | InterfaceType::Float32
                        | InterfaceType::Float64
                        | InterfaceType::Int32Array(_)
                        | InterfaceType::UInt32Array(_)
                        | InterfaceType::Int128Array(_)
                        | InterfaceType::Int64Array(_, _)
                        | InterfaceType::UInt128Array(_)
                        | InterfaceType::UInt64Array(_, _)
                        | InterfaceType::CharArray(_, _)
                        | InterfaceType::UInt8Array(_)
                        | InterfaceType::Float32Array(_)
                        | InterfaceType::Float64Array(_)
                        | InterfaceType::PointerArray(_, _, _)
                        | InterfaceType::Int32Pointer
                        | InterfaceType::CharPointer(_)
                        | InterfaceType::UInt8Pointer
                        | InterfaceType::UInt32Pointer
                        | InterfaceType::Float32Pointer
                        | InterfaceType::Float64Pointer
                        | InterfaceType::Int32PointerPointer
                        | InterfaceType::CharPointerPointer(_)
                        | InterfaceType::UInt8PointerPointer
                        | InterfaceType::Float32PointerPointer
                        | InterfaceType::Float64PointerPointer
                        // A callback field is an eight-byte pointer value like
                        // any data pointer; the layout keeps its signature so
                        // a load through it still dispatches exactly.
                        | InterfaceType::FunctionPointer(_)
                )
            {
                return Err(self.error_here(format!(
                    "struct-by-value currently supports int16, int32, uint8, uint16, uint32, int64, uint64, named enum fields, fixed scalar arrays, fixed-dimensional embedded-struct arrays, data-pointer fields, function-pointer fields, embedded struct fields, and named union fields; `struct {struct_name}` contains an unsupported field shape"
                )));
            }
        }
        Ok(layout)
    }

    fn is_type_start(&self) -> bool {
        self.peek_ident().is_some_and(|name| {
            name == "const"
                || name == "volatile"
                || is_builtin_type_start(name)
                || self.typedefs.contains_key(name)
        })
    }

    /// The source position of the next unconsumed token, or of the end of
    /// input when every token has been consumed.
    fn here(&self) -> Option<SourcePosition> {
        self.positions
            .get(self.position)
            .or_else(|| self.positions.last())
            .cloned()
    }

    fn mint_field_source_id(
        &mut self,
        field_name: String,
        position: Option<SourcePosition>,
    ) -> Option<CFieldSource> {
        let function_name = self.current_function_source_name.clone()?;
        let position = position?;
        let occurrence = self.next_field_source_ordinal;
        self.next_field_source_ordinal = self.next_field_source_ordinal.checked_add(1)?;
        Some(CFieldSource {
            id: CFieldSourceId {
                source_identity: self.source_identity.clone(),
                function_name,
                occurrence,
            },
            position,
            field_name,
        })
    }

    /// One unit of parsing work per top-level declaration, and a
    /// cooperative checkpoint: a translation unit as large as the program
    /// stops at the run's work budget or crash-containment bound instead of
    /// parsing to its end first.
    fn checkpoint(&self) -> Result<(), CSyntaxError> {
        if crate::instrumentation::deadline_exceeded() {
            let mut error = self.error_here(format!(
                "C parsing stopped: {}",
                crate::instrumentation::deadline_context()
            ));
            error.limit_exceeded = true;
            Err(error)
        } else {
            Ok(())
        }
    }

    /// An error at the next unconsumed token.
    fn error_here(&self, message: impl Into<String>) -> CSyntaxError {
        match self.here() {
            Some(position) => CSyntaxError::at(position, message),
            None => CSyntaxError::new(message),
        }
    }

    /// An error at the most recently consumed token; use after `next()` has
    /// already advanced past the offending token.
    fn error_at_previous(&self, message: impl Into<String>) -> CSyntaxError {
        let index = self.position.saturating_sub(1);
        match self.positions.get(index).or_else(|| self.positions.last()) {
            Some(position) => CSyntaxError::at(position.clone(), message),
            None => CSyntaxError::new(message),
        }
    }

    /// Uses a captured expression position when a lowering error is reported
    /// after parsing has advanced past the original source token.
    fn error_at_position(
        &self,
        position: Option<SourcePosition>,
        message: impl Into<String>,
    ) -> CSyntaxError {
        match position {
            Some(position) => CSyntaxError::at(position, message),
            None => self.error_here(message),
        }
    }

    fn link_function_global_objects(
        &self,
        function: ImportedFunction,
    ) -> Result<ImportedFunction, CSyntaxError> {
        let function = function
            .with_globals(self.globals.clone())
            .with_global_arrays(self.global_arrays.clone())
            .with_global_aggregates(self.global_aggregates.clone())
            .with_global_aggregate_arrays(self.global_aggregate_arrays.clone());
        function.validate_static_initializers()?;
        Ok(function)
    }

    fn parse_function(mut self) -> Result<ImportedFunction, CSyntaxError> {
        self.parse_declarations()?;
        let function = self.parse_function_definition(false)?;
        self.parse_declarations()?;
        self.expect_end(function.name())?;
        self.prepare_file_static_bindings();
        self.link_function_global_objects(function)
    }

    fn parse_functions(self) -> Result<Vec<ImportedFunction>, CSyntaxError> {
        let unit = self.parse_translation_unit()?;
        if unit.functions.is_empty() {
            return Err(CSyntaxError::new(
                "C source must define at least one function",
            ));
        }
        Ok(unit.functions)
    }

    fn parse_translation_unit(mut self) -> Result<CTranslationUnit, CSyntaxError> {
        self.parse_declarations()?;
        let mut functions = Vec::new();
        while self.peek().is_some() {
            self.checkpoint()?;
            let is_extern = if self.peek_ident() == Some("extern") {
                self.position += 1;
                true
            } else {
                false
            };
            let is_static = if self.peek_ident() == Some("static") {
                self.position += 1;
                true
            } else {
                false
            };
            let is_inline = if self.peek_inline_specifier() {
                self.position += 1;
                true
            } else {
                false
            };
            let (has_always_inline_attribute, prefix_weak, prefix_returns_twice, prefix_opaque) =
                self.consume_function_attributes()?;
            if is_inline && !is_static {
                return Err(self.error_here(
                    "inline function definitions require `static inline` or `static __always_inline` in this slice",
                ));
            }
            if has_always_inline_attribute && !is_static {
                return Err(self.error_here(format!(
                    "the GNU {} attribute requires `static inline` or `static __always_inline`",
                    self.static_inline_attribute
                )));
            }
            if !self.is_type_start() {
                return Err(self.error_here(format!(
                    "expected function declaration, got {}",
                    self.peek()
                        .map(Token::describe)
                        .unwrap_or_else(|| "end of input".to_string())
                )));
            }
            // A `static` function has internal linkage whether or not it is
            // also `inline`; the two differ only in an optimization hint.
            let mut header = self.parse_function_header(is_static)?;
            self.consume_function_asm_label(&mut header)?;
            let (
                has_trailing_always_inline_attribute,
                suffix_weak,
                suffix_returns_twice,
                suffix_opaque,
            ) = self.consume_function_attributes()?;
            header.weak_linkage = prefix_weak || suffix_weak;
            header.returns_twice = prefix_returns_twice || suffix_returns_twice;
            header.opaque_attributes = prefix_opaque || suffix_opaque;
            if (has_always_inline_attribute || has_trailing_always_inline_attribute)
                && !(is_static && is_inline)
            {
                return Err(self.error_here(format!(
                    "the GNU {} attribute requires `static inline` or `static __always_inline`",
                    self.static_inline_attribute
                )));
            }
            if self.peek() == Some(&Token::LBrace) {
                self.reject_variadic_definition(&header)?;
                if header.weak_linkage || header.returns_twice {
                    return Err(self.error_here(
                        "weak or returns-twice function definitions need a control-flow and linkage model",
                    ));
                }
                if is_extern {
                    return Err(self.error_here(
                        "`extern` function definitions are not supported; use `extern` only for prototypes",
                    ));
                }
                self.register_function_declaration(&header, true)?;
                functions.push(self.finish_function_definition(header)?);
            } else {
                if self.peek() != Some(&Token::Semicolon) {
                    return Err(self.error_here(format!(
                        "expected function body or `;` after `{}`",
                        header.source_name
                    )));
                }
                self.pop_scope();
                self.expect(Token::Semicolon)?;
                self.register_function_declaration(&header, false)?;
            }
            self.parse_declarations()?;
        }
        self.prepare_file_static_bindings();
        let functions = functions
            .into_iter()
            .map(|function| self.link_function_global_objects(function))
            .collect::<Result<Vec<_>, _>>()?;
        Ok(CTranslationUnit {
            functions,
            function_declarations: self.function_declarations,
            function_declaration_lines: self.function_declaration_lines,
            builtin_pthread_declarations: BTreeSet::new(),
            shadowed_pthread_names: self.shadowed_pthread_names,
            structs: self.structs,
            unions: self.unions,
            globals: self.globals,
            global_arrays: self.global_arrays,
            global_aggregates: self.global_aggregates,
            global_aggregate_arrays: self.global_aggregate_arrays,
            referenced_external_objects: self.referenced_external_objects,
            head_typedefs: self
                .typedefs
                .iter()
                .map(|(name, parsed)| (name.clone(), CHeadTypedef::of(parsed)))
                .collect(),
        })
    }

    fn parse_header(mut self) -> Result<(), CSyntaxError> {
        self.header_mode = true;
        self.parse_declarations()?;
        while self.peek().is_some() {
            let is_extern = if self.peek_ident() == Some("extern") {
                self.position += 1;
                true
            } else {
                false
            };
            let is_static = if self.peek_ident() == Some("static") {
                self.position += 1;
                true
            } else {
                false
            };
            let is_inline = if self.peek_inline_specifier() {
                self.position += 1;
                true
            } else {
                false
            };
            let (has_always_inline_attribute, prefix_weak, prefix_returns_twice, prefix_opaque) =
                self.consume_function_attributes()?;
            if is_inline && !is_static {
                return Err(self.error_here(
                    "inline function definitions in headers require `static inline` or `static __always_inline`",
                ));
            }
            if has_always_inline_attribute && !is_static {
                return Err(self.error_here(format!(
                    "the GNU {} attribute requires `static inline` or `static __always_inline`",
                    self.static_inline_attribute
                )));
            }
            if !self.is_type_start() {
                return Err(self.error_here(format!(
                    "expected a header declaration, got {}",
                    self.peek()
                        .map(Token::describe)
                        .unwrap_or_else(|| "end of input".to_string())
                )));
            }
            let mut header = self.parse_function_header(is_static && is_inline)?;
            self.consume_function_asm_label(&mut header)?;
            let (
                has_trailing_always_inline_attribute,
                suffix_weak,
                suffix_returns_twice,
                suffix_opaque,
            ) = self.consume_function_attributes()?;
            header.weak_linkage = prefix_weak || suffix_weak;
            header.returns_twice = prefix_returns_twice || suffix_returns_twice;
            header.opaque_attributes = prefix_opaque || suffix_opaque;
            if (has_always_inline_attribute || has_trailing_always_inline_attribute) && !is_static {
                return Err(self.error_here(format!(
                    "the GNU {} attribute requires `static inline` or `static __always_inline`",
                    self.static_inline_attribute
                )));
            }
            if self.peek() == Some(&Token::LBrace) {
                self.reject_variadic_definition(&header)?;
                if header.weak_linkage || header.returns_twice {
                    return Err(self.error_here(
                        "weak or returns-twice function definitions need a control-flow and linkage model",
                    ));
                }
                if is_extern || !is_static || !is_inline {
                    self.pop_scope();
                    return Err(self.error_here(format!(
                        "function definitions in headers require `static inline` or `static __always_inline`; `{}` has a body",
                        header.source_name
                    )));
                }
                self.register_function_declaration(&header, true)?;
                self.finish_function_definition(header)?;
                self.parse_declarations()?;
                continue;
            }
            if self.peek() != Some(&Token::Semicolon) {
                self.pop_scope();
                return Err(self.error_here(format!(
                    "expected `;` after header declaration `{}`",
                    header.source_name
                )));
            }
            self.pop_scope();
            self.expect(Token::Semicolon)?;
            self.register_function_declaration(&header, false)?;
            self.parse_declarations()?;
        }
        Ok(())
    }

    fn parse_function_definition(
        &mut self,
        internal_linkage: bool,
    ) -> Result<ImportedFunction, CSyntaxError> {
        let (prefix_inline, prefix_weak, prefix_returns_twice, prefix_opaque) =
            self.consume_function_attributes()?;
        let mut header = self.parse_function_header(internal_linkage)?;
        self.consume_function_asm_label(&mut header)?;
        let (suffix_inline, suffix_weak, suffix_returns_twice, suffix_opaque) =
            self.consume_function_attributes()?;
        header.weak_linkage = prefix_weak || suffix_weak;
        header.returns_twice = prefix_returns_twice || suffix_returns_twice;
        header.opaque_attributes = prefix_opaque || suffix_opaque;
        self.reject_variadic_definition(&header)?;
        if header.weak_linkage || header.returns_twice {
            return Err(self.error_here(
                "weak or returns-twice function definitions need a control-flow and linkage model",
            ));
        }
        if (prefix_inline || suffix_inline) && !internal_linkage {
            return Err(self.error_here(format!(
                "the GNU {} attribute requires `static inline` or `static __always_inline`",
                self.static_inline_attribute
            )));
        }
        self.register_function_declaration(&header, true)?;
        if self.peek() != Some(&Token::LBrace) {
            return Err(self.error_here(format!(
                "expected function body after `{}`",
                header.source_name
            )));
        }
        self.finish_function_definition(header)
    }

    fn finish_function_definition(
        &mut self,
        header: CFunctionHeader,
    ) -> Result<ImportedFunction, CSyntaxError> {
        self.next_static_binding = 0;
        let previous_function_source_name = self
            .current_function_source_name
            .replace(header.source_name.clone());
        let previous_field_source_ordinal =
            std::mem::replace(&mut self.next_field_source_ordinal, 0);
        let previous_return_struct_name = std::mem::replace(
            &mut self.current_return_struct_name,
            header.return_struct_name.clone(),
        );
        let previous_return_pointer_struct_name = std::mem::replace(
            &mut self.current_return_pointer_struct_name,
            header.return_pointer_struct_name.clone(),
        );
        let previous_return_type =
            std::mem::replace(&mut self.current_return_type, header.return_type);
        let previous_return_pointee_constant = std::mem::replace(
            &mut self.current_return_pointee_constant,
            header.return_pointee_constant,
        );
        let previous_address_taken_variables = std::mem::take(&mut self.address_taken_variables);
        let previous_callback_sources = std::mem::take(&mut self.callback_statement_sources);
        let previous_source_regions = std::mem::replace(
            &mut self.source_regions,
            vec![Some((std::sync::Arc::from([]), 0))],
        );
        let previous_literal_flag =
            std::mem::replace(&mut self.function_has_compound_literals, false);
        let previous_goto_flag = std::mem::replace(&mut self.function_has_goto, false);
        let previous_bit_field_flag = std::mem::replace(&mut self.function_has_bit_fields, false);
        let body_result = self.parse_block_statement();
        self.function_has_compound_literals = previous_literal_flag;
        self.function_has_goto = previous_goto_flag;
        self.function_has_bit_fields = previous_bit_field_flag;
        self.source_regions = previous_source_regions;
        let callback_statement_sources = std::mem::replace(
            &mut self.callback_statement_sources,
            previous_callback_sources,
        );
        self.current_function_source_name = previous_function_source_name;
        self.next_field_source_ordinal = previous_field_source_ordinal;
        self.current_return_struct_name = previous_return_struct_name;
        self.current_return_pointer_struct_name = previous_return_pointer_struct_name;
        self.current_return_type = previous_return_type;
        self.current_return_pointee_constant = previous_return_pointee_constant;
        self.address_taken_variables = previous_address_taken_variables;
        let mut body = body_result?;
        self.pop_scope();
        self.out_of_scope_names.clear();
        validate_function_returns(&body, header.return_type)?;
        if header.return_type == InterfaceType::Void {
            body = CStatement::Seq(
                Box::new(body),
                Box::new(CStatement::Return(CExpression::Void, CSite::NONE)),
            );
        }
        let control_targets = validate_direct_forward_gotos(&body)?;

        for object in self.static_locals.values() {
            object.prepare_static_binding();
        }
        for object in self.static_arrays.values() {
            object.prepare_static_binding();
        }
        for object in self.static_aggregates.values() {
            object.prepare_static_binding();
        }
        for object in self.static_aggregate_arrays.values() {
            object.prepare_static_binding();
        }
        let static_locals = std::mem::take(&mut self.static_locals);
        let local_struct_pointers = std::mem::take(&mut self.local_struct_pointers)
            .into_iter()
            .filter_map(|(name, struct_name)| Some((name, struct_name?)))
            .collect();
        let local_struct_values = std::mem::take(&mut self.local_struct_values)
            .into_iter()
            .filter_map(|(name, struct_name)| Some((name, struct_name?)))
            .collect();
        let local_pointers = std::mem::take(&mut self.local_pointers)
            .into_iter()
            .filter_map(|(name, pointer)| pointer.then_some(name))
            .collect();
        let string_literals = std::mem::take(&mut self.string_literals);
        let inline_body = header.name != header.source_name;
        Ok(ImportedFunction {
            source_sites: None,
            return_type: header.return_type,
            return_pointee_constant: header.return_pointee_constant,
            return_reference: false,
            return_struct_name: header.return_struct_name,
            aggregate_return_mode: crate::kernel::AggregateReturnMode::Copy,
            return_pointer_struct_name: header.return_pointer_struct_name,
            source_name: header.source_name,
            name: header.name,
            inline_body,
            requires_read_only_contract: false,
            requires_nonthrowing_contract: false,
            positional_parameters: false,
            closure_captures: 0,
            trait_interface: None,
            generic_instance: None,
            dispatched_method: None,
            receiver_calls: Vec::new(),
            program_entry_state: None,
            prelowered_kernel_function: None,
            parameters: header.parameters,
            body,
            callback_statement_sources: std::sync::Arc::new(
                callback_statement_sources.into_iter().collect(),
            ),
            control_targets,
            structs: self.structs.clone(),
            prepared_record_layouts: std::sync::Arc::default(),
            enums: self.enums.clone(),
            unions: self.unions.clone(),
            globals: self.globals.clone(),
            global_arrays: self.global_arrays.clone(),
            global_aggregates: self.global_aggregates.clone(),
            global_aggregate_arrays: self.global_aggregate_arrays.clone(),
            static_locals,
            static_arrays: std::mem::take(&mut self.static_arrays),
            static_aggregates: std::mem::take(&mut self.static_aggregates),
            static_aggregate_arrays: std::mem::take(&mut self.static_aggregate_arrays),
            local_struct_pointers,
            local_struct_values,
            local_references: BTreeSet::new(),
            local_pointers,
            string_literals,
            loop_iterators: Vec::new(),
        })
    }

    /// A variadic body would read its variable arguments through `va_arg`,
    /// which has no model. Only the body-less prototype is retained.
    fn reject_variadic_definition(&self, header: &CFunctionHeader) -> Result<(), CSyntaxError> {
        if header.opaque_attributes {
            return Err(self.error_here(format!(
                "function definition `{}` uses declaration-only compiler attributes",
                header.source_name
            )));
        }
        if header.opaque_signature {
            return Err(self.error_here(format!(
                "function definition `{}` uses declaration-only signature (__builtin_va_list or long double); its call ABI and value operations are not modeled",
                header.source_name
            )));
        }
        if header.has_unnamed_parameter {
            return Err(self.error_here(format!(
                "function definition `{}` has an unnamed parameter; only a body-less prototype may omit parameter names",
                header.source_name
            )));
        }
        if header.variadic {
            return Err(self.error_here(format!(
                "variadic function definitions (`...`) are not supported by Click; only a body-less prototype of `{}` can be declared",
                header.source_name
            )));
        }
        Ok(())
    }

    fn parse_function_header(
        &mut self,
        internal_linkage: bool,
    ) -> Result<CFunctionHeader, CSyntaxError> {
        let declaration_line = self.positions[self.position].line;
        self.parsing_function_header = true;
        self.opaque_function_signature = false;
        self.opaque_signature_types.clear();
        let parsed_return_type = self.parse_signature_type()?;
        if parsed_return_type.function_pointer_signature.is_some() {
            return Err(
                self.error_here("function-pointer return values need nested callback ABI metadata")
            );
        }
        if parsed_return_type.is_constant {
            return Err(self.error_here(
                "const-qualified function return types are not supported in this slice",
            ));
        }
        if parsed_return_type.is_volatile {
            return Err(self.error_here("volatile qualifies objects, not function return types"));
        }
        if parsed_return_type.union_name.is_some() {
            return Err(self.error_here(
                "tagged union return values are not supported; access an active scalar member",
            ));
        }
        let return_struct_name = if is_plain_struct_type(&parsed_return_type) {
            let name = parsed_return_type
                .struct_name
                .as_deref()
                .expect("plain struct return carries its name");
            self.scalar_struct_value_layout(name)?;
            Some(name.to_string())
        } else {
            None
        };
        let return_pointer_struct_name = parsed_return_type
            .struct_name
            .as_ref()
            .filter(|_| parsed_return_type.interface_type.is_pointer())
            .cloned();
        // A pointer return retains its nominal tag without requiring the
        // pointee's layout. Field access, sizeof, and by-value operations still
        // require a complete definition through their ordinary layout checks.
        let return_type = if let Some(name) = &return_struct_name {
            record_value_type(
                self.structs
                    .get(name)
                    .expect("validated struct return has a layout"),
            )
        } else {
            parsed_return_type.interface_type
        };
        if self.peek() == Some(&Token::LParen) {
            return Err(self.error_here("function-pointer declarations are not supported by Click"));
        }
        let name_position = self.here();
        let source_name = self.expect_ident("function name")?;
        self.expect(Token::LParen)?;
        self.push_scope();
        let empty_parameter_list = self.peek() == Some(&Token::RParen);
        self.binding_function = Some(LocalFunctionId::new(
            self.source_identity.clone(),
            source_name.clone(),
        ));
        self.parsing_binding_parameters = true;
        self.next_parameter_binding = 0;
        self.next_local_binding = 0;
        let unnamed_before = self.unnamed_parameters;
        let parameters = self.parse_parameters()?;
        self.parsing_binding_parameters = false;
        let has_unnamed_parameter = self.unnamed_parameters != unnamed_before;
        let variadic = self.peek() == Some(&Token::Ellipsis);
        if variadic {
            self.position += 1;
        }
        self.expect(Token::RParen)?;
        let name = if internal_linkage {
            self.inline_function_kernel_name(&source_name)
        } else {
            source_name.clone()
        };
        self.parsing_function_header = false;
        let opaque_signature = std::mem::take(&mut self.opaque_function_signature);
        // Ordinary trailing types carry their own checked ABI. Keep only the
        // positions needed to distinguish opaque types, so f() and f(void)
        // retain the parser's ordinary compatibility behavior.
        while self.opaque_signature_types.last() == Some(&(false, false)) {
            self.opaque_signature_types.pop();
        }
        Ok(CFunctionHeader {
            declaration_line,
            name_position,
            opaque_signature,
            opaque_signature_types: std::mem::take(&mut self.opaque_signature_types),
            opaque_attributes: false,
            return_type,
            return_pointee_constant: parsed_return_type.pointee_constant,
            return_struct_name,
            return_pointer_struct_name,
            source_name,
            name,
            internal_linkage,
            weak_linkage: false,
            returns_twice: false,
            variadic,
            has_unnamed_parameter,
            empty_parameter_list,
            compile_time_error: false,
            parameters,
        })
    }

    /// Consume the explicitly supported declaration annotations, returning
    /// linkage restrictions, returns-twice behavior, and declaration opacity.
    /// `nothrow` adds no proof facts: C has no exception semantics, and the
    /// annotation says nothing about termination, memory effects, or safety.
    /// `leaf`, `const`, `nonnull`, `noreturn`, and `deprecated` are also accepted without using their
    /// restrictions as proof assumptions. Calls retain their ordinary checked
    /// contracts, including their ordinary argument obligations. Unmodeled
    /// purity/allocation attributes retain prototypes but prohibit uses.
    fn consume_function_attributes(&mut self) -> Result<(bool, bool, bool, bool), CSyntaxError> {
        let mut opaque_attributes = false;
        let mut always_inline = false;
        let mut weak = false;
        let mut returns_twice = false;
        while self.peek_ident() == Some("__attribute__") {
            self.position += 1;
            self.expect(Token::LParen)?;
            self.expect(Token::LParen)?;
            loop {
                let attribute = self.expect_ident("GNU function attribute")?;
                if self.refuse_promises
                    && let Some(reason) = optimizer_promise(&attribute)
                {
                    let refusal = self.error_at_previous(format!(
                        "GNU function attribute `{attribute}` is refused under an optimizing compiler-option profile: {reason}"
                    ));
                    // `compiletime_assert`'s block-scope declaration is
                    // decided once its `error` attribute has been seen.
                    if matches!(attribute.as_str(), "noreturn" | "__noreturn__")
                        && self.error_attribute.is_some()
                    {
                        self.pending_noreturn = Some(refusal);
                    } else {
                        return Err(refusal);
                    }
                }
                match attribute.as_str() {
                    "always_inline" | "__always_inline__" => {
                        always_inline = true;
                        self.static_inline_attribute = "always-inline";
                    }
                    // On a `static inline` function `gnu_inline` selects
                    // nothing: it changes only when a non-static inline
                    // definition is emitted. It is refused anywhere else.
                    "gnu_inline" | "__gnu_inline__" => {
                        always_inline = true;
                        self.static_inline_attribute = "gnu-inline";
                    }
                    // Keep these prototypes for source/type closure, but no
                    // body, call or function address may use their promises.
                    "pure" | "__pure__" | "malloc" | "__malloc__" => {
                        opaque_attributes = true;
                    }
                    "alloc_size" | "__alloc_size__" | "alloc_align" | "__alloc_align__" => {
                        let maximum = if matches!(attribute.as_str(), "alloc_size" | "__alloc_size__") { 2 } else { 1 };
                        self.expect(Token::LParen)?;
                        for index in 0..maximum {
                            let Some(Token::Number(value)) = self.next() else {
                                return Err(self.error_here("allocation attribute requires positive parameter indices"));
                            };
                            if value.parse::<u32>().ok().filter(|value| *value > 0).is_none() {
                                return Err(self.error_at_previous("allocation attribute requires positive parameter indices"));
                            }
                            if index + 1 == maximum || self.peek() != Some(&Token::Comma) {
                                break;
                            }
                            self.position += 1;
                        }
                        self.expect(Token::RParen)?;
                        opaque_attributes = true;
                    }
                    "weak" | "__weak__" => weak = true,
                    "returns_twice" | "__returns_twice__" => returns_twice = true,
                    "access" | "__access__" => {
                        self.expect(Token::LParen)?;
                        let mode = self.expect_ident("GNU access mode")?;
                        if !matches!(
                            mode.as_str(),
                            "none" | "__none__" | "read_only" | "__read_only__"
                                | "read_write" | "__read_write__" | "write_only"
                                | "__write_only__"
                        ) {
                            return Err(self.error_at_previous(format!(
                                "unsupported GNU access mode `{mode}`"
                            )));
                        }
                        self.expect(Token::Comma)?;
                        for argument in ["pointer", "size"] {
                            let Some(Token::Number(index)) = self.next() else {
                                return Err(self.error_at_previous(format!(
                                    "GNU access {argument} index must be positive"
                                )));
                            };
                            if index.parse::<u32>().ok().filter(|index| *index > 0).is_none() {
                                return Err(self.error_at_previous(format!(
                                    "GNU access {argument} index must be positive"
                                )));
                            }
                            if self.peek() != Some(&Token::Comma) {
                                break;
                            }
                            self.position += 1;
                        }
                        self.expect(Token::RParen)?;
                    }
                    // `unused` silences a warning and
                    // `no_instrument_function` omits profiling hooks; neither
                    // changes what the function computes.
                    "nothrow" | "__nothrow__" | "leaf" | "__leaf__" | "const"
                    | "__const__" | "noreturn" | "__noreturn__" | "deprecated"
                    | "__deprecated__" | "unused" | "__unused__"
                    | "no_instrument_function" | "__no_instrument_function__"
                    | "cold" | "__cold__" | "warn_unused_result" | "__warn_unused_result__" => {},
                    "error" | "__error__" if self.error_attribute.is_some() => {
                        self.expect(Token::LParen)?;
                        let Some(Token::StringLiteral(_)) = self.next() else {
                            return Err(self.error_at_previous(
                                "the GNU error attribute requires one string literal",
                            ));
                        };
                        self.expect(Token::RParen)?;
                        self.error_attribute = Some(true);
                    }
                    "nonnull" | "__nonnull__" => {
                        if self.peek() == Some(&Token::LParen) {
                            self.position += 1;
                            loop {
                                let Some(Token::Number(index)) = self.next() else {
                                    return Err(self.error_at_previous(
                                        "GNU nonnull attribute requires positive parameter indices",
                                    ));
                                };
                                if index.parse::<u32>().ok().filter(|index| *index > 0).is_none() {
                                    return Err(self.error_at_previous(
                                        "GNU nonnull attribute requires positive parameter indices",
                                    ));
                                }
                                if self.peek() != Some(&Token::Comma) {
                                    break;
                                }
                                self.position += 1;
                            }
                            self.expect(Token::RParen)?;
                        }
                    }
                    _ => return Err(self.error_at_previous(format!(
                        "unsupported GNU function attribute `{attribute}`; only `always_inline`, `gnu_inline`, `nothrow`, `leaf`, `const`, `nonnull`, `noreturn`, `deprecated`, `unused`, `no_instrument_function`, `weak`, `returns_twice`, `access`, `cold`, `warn_unused_result`, and declaration-only `pure`, `malloc`, `alloc_size`, `alloc_align` are supported in this slice"
                    ))),
                }
                if self.peek() != Some(&Token::Comma) {
                    break;
                }
                self.position += 1;
            }
            self.expect(Token::RParen)?;
            self.expect(Token::RParen)?;
        }
        Ok((always_inline, weak, returns_twice, opaque_attributes))
    }

    /// A declaration's GNU asm label changes the linked symbol, not its C
    /// source spelling. Adjacent string literals are concatenated as in C.
    fn consume_function_asm_label(
        &mut self,
        header: &mut CFunctionHeader,
    ) -> Result<(), CSyntaxError> {
        if self.peek_ident() != Some("__asm__") {
            return Ok(());
        }
        if header.internal_linkage {
            return Err(self.error_here("GNU asm labels on inline functions are not supported"));
        }
        self.position += 1;
        self.expect(Token::LParen)?;
        let mut bytes = Vec::new();
        let mut count = 0;
        while let Some(Token::StringLiteral(_)) = self.peek() {
            let Some(Token::StringLiteral(piece)) = self.next() else {
                unreachable!();
            };
            bytes.extend(piece);
            count += 1;
        }
        if count == 0 || bytes.is_empty() || bytes.contains(&0) {
            return Err(self.error_here("GNU function asm label needs a nonempty string"));
        }
        self.expect(Token::RParen)?;
        header.name = String::from_utf8(bytes)
            .map_err(|_| self.error_here("GNU function asm label must be UTF-8"))?;
        Ok(())
    }

    /// Consume the one layout-affecting GNU attribute needed by the imported
    /// rbtree headers. This deliberately accepts only the exact constant
    /// spelling used by those headers; silently dropping another attribute
    /// would make the imported ABI unsound.
    fn consume_struct_alignment_attribute(&mut self) -> Result<Option<u32>, CSyntaxError> {
        if self.peek_ident() != Some("__attribute__") {
            return Ok(None);
        }
        self.position += 1;
        self.expect(Token::LParen)?;
        self.expect(Token::LParen)?;
        let attribute = self.expect_ident("GNU struct attribute")?;
        if attribute != "aligned" && attribute != "__aligned__" {
            return Err(self.error_at_previous(format!(
                "unsupported GNU struct attribute `{attribute}`; only `aligned` is supported in this slice"
            )));
        }
        self.expect(Token::LParen)?;
        self.expect_ident_spelling("sizeof")?;
        self.expect(Token::LParen)?;
        self.expect_ident_spelling("long")?;
        self.expect(Token::RParen)?;
        self.expect(Token::RParen)?;
        self.expect(Token::RParen)?;
        self.expect(Token::RParen)?;
        Ok(Some(8))
    }

    fn consume_field_alignment_attribute(&mut self) -> Result<Option<u32>, CSyntaxError> {
        if self.peek_ident() != Some("__attribute__") {
            return Ok(None);
        }
        self.position += 1;
        self.expect(Token::LParen)?;
        self.expect(Token::LParen)?;
        let attribute = self.expect_ident("GNU field attribute")?;
        if attribute != "aligned" && attribute != "__aligned__" {
            return Err(
                self.error_at_previous(format!("unsupported GNU field attribute `{attribute}`"))
            );
        }
        self.expect(Token::LParen)?;
        let alignment = match self.peek_ident() {
            Some("__alignof__" | "__alignof" | "_Alignof" | "sizeof") => {
                let operation = self.expect_ident("alignment operator")?;
                self.expect(Token::LParen)?;
                let parsed = self.parse_type_with_anonymous_struct(false, true, false)?;
                self.expect(Token::RParen)?;
                if let Some(name) = parsed.struct_name.as_deref()
                    && !parsed.interface_type.is_pointer()
                {
                    let layout = self.structs.get(name).ok_or_else(|| {
                        self.error_here(format!("unknown struct declaration `{name}`"))
                    })?;
                    if operation == "sizeof" {
                        layout.size_bytes()
                    } else {
                        layout.alignment_bytes()
                    }
                } else if let Some(name) = parsed.union_name.as_deref()
                    && !parsed.interface_type.is_pointer()
                {
                    let layout = self.unions.get(name).ok_or_else(|| {
                        self.error_here(format!("unknown union declaration `{name}`"))
                    })?;
                    if operation == "sizeof" {
                        layout.size_bytes()
                    } else {
                        layout.alignment_bytes()
                    }
                } else if parsed.long_double {
                    16
                } else if operation == "sizeof" {
                    self.abi.size_and_alignment(parsed.interface_type).0
                } else {
                    self.abi.size_and_alignment(parsed.interface_type).1
                }
            }
            _ => {
                let expression = self.parse_expression()?;
                let value = evaluate_static_integer_expression(&expression).map_err(|_| {
                    self.error_here("GNU field alignment must be an integer constant")
                })?;
                match value {
                    StaticIntegerValue::Signed { value, .. } => u32::try_from(value),
                    StaticIntegerValue::Unsigned { value, .. } => u32::try_from(value),
                }
                .map_err(|_| self.error_here("GNU field alignment is out of range"))?
            }
        };
        self.expect(Token::RParen)?;
        self.expect(Token::RParen)?;
        self.expect(Token::RParen)?;
        if alignment == 0 || !alignment.is_power_of_two() {
            return Err(self.error_here("GNU field alignment must be a positive power of two"));
        }
        Ok(Some(alignment))
    }

    fn register_function_declaration(
        &mut self,
        header: &CFunctionHeader,
        definition: bool,
    ) -> Result<(), CSyntaxError> {
        if let Some((name, prototype, compatible)) = library_function_prototype(header) {
            if definition {
                return Err(self.error_at_position(header.name_position.clone(), format!(
                    "definition of the C library function `{name}` is not supported: the name is reserved for the library (C11 7.1.3), GCC and Clang compile a call to `{name}` as a call to the library's `{prototype}` and may evaluate it by the library's specification rather than this body unless the translation unit is built with `-ffreestanding` or `-fno-builtin`, which no Click target is, and Click checks each call against its specification of `{name}`; rename the function, or give it internal linkage with `static`"
                )));
            }
            if !compatible {
                return Err(self.error_at_position(header.name_position.clone(), format!(
                    "declaration of `{}` has type `{}`, which is incompatible with the C library's `{prototype}` (C11 6.7.6.3p15); Clang diagnoses it as an incompatible redeclaration of the library function, GCC and Clang reject it when the library's header is included, and Click specifies `{name}` only with the library's type; include `<{library_header}>` instead of declaring `{name}`, or declare it exactly as `{prototype}`",
                    header.source_name,
                    describe_function_header_type(header),
                    library_header = if matches!(name, "malloc" | "calloc" | "realloc" | "free") {
                        "stdlib.h"
                    } else {
                        "string.h"
                    },
                )));
            }
        }
        if let Some(previous_source) = self.function_source_names.get(&header.name)
            && previous_source != &header.source_name
        {
            return Err(self.error_here(format!(
                "functions `{previous_source}` and `{}` have the same linked symbol `{}`",
                header.source_name, header.name
            )));
        }
        self.function_declaration_lines
            .entry(header.source_name.clone())
            .or_default()
            .push(header.declaration_line);
        if self.globals.contains_key(&header.source_name)
            || self.global_arrays.contains_key(&header.source_name)
            || self.global_aggregates.contains_key(&header.source_name)
            || self
                .global_aggregate_arrays
                .contains_key(&header.source_name)
        {
            return Err(self.error_here(format!(
                "function `{}` conflicts with a global declaration",
                header.source_name
            )));
        }
        if let Some(previous) = self.function_declarations.get(&header.source_name) {
            if !function_headers_compatible(previous, header) {
                let mut message = format!(
                    "conflicting declarations for function `{}`",
                    header.source_name
                );
                if previous.internal_linkage || header.internal_linkage {
                    message.push_str(
                        "; translation-unit-local inline helpers must keep matching linkage and signatures",
                    );
                }
                return Err(self.error_here(message));
            }
        } else {
            self.function_declarations
                .insert(header.source_name.clone(), header.clone());
            self.function_source_names
                .insert(header.name.clone(), header.source_name.clone());
        }
        if definition && !self.defined_functions.insert(header.source_name.clone()) {
            let mut message = format!("duplicate function definition `{}`", header.source_name);
            if header.internal_linkage {
                message.push_str(
                    "; a translation-unit-local inline helper must be defined once per translation unit",
                );
            }
            return Err(self.error_here(message));
        }
        Ok(())
    }

    fn parse_declarations(&mut self) -> Result<(), CSyntaxError> {
        while self.peek().is_some() {
            self.checkpoint()?;
            // This GNU spelling only suppresses a compiler diagnostic. The
            // following declaration still passes all ordinary semantic checks.
            if self.peek_ident() == Some("__extension__") {
                self.position += 1;
                continue;
            }
            if (self.peek_ident() == Some("static")
                && self.peek_n(1).is_some_and(Self::is_inline_specifier))
                || self.peek_inline_specifier()
            {
                break;
            } else if self.peek_ident() == Some("static") {
                if !self.header_mode && self.static_function_declarator_ahead() {
                    break;
                }
                self.parse_global_declaration()?;
            } else if self.peek_ident() == Some("_Static_assert") {
                self.parse_static_assert()?;
            } else if self.peek_ident() == Some("typedef") {
                self.parse_typedef_declaration()?;
            } else if self.peek_ident() == Some("struct") && self.peek_n(2) == Some(&Token::LBrace)
            {
                self.parse_struct_declaration()?;
            } else if self.peek_ident() == Some("struct")
                && matches!(self.peek_n(1), Some(Token::Ident(_)))
                && self.peek_n(2) == Some(&Token::Semicolon)
            {
                // A forward declaration has no layout. Keep later uses on
                // the ordinary complete-type checks rather than inventing one.
                self.position += 2;
                self.expect(Token::Semicolon)?;
            } else if self.peek_ident() == Some("enum")
                && (self.peek_n(1) == Some(&Token::LBrace)
                    || self.peek_n(2) == Some(&Token::LBrace))
            {
                self.parse_enum_declaration()?;
            } else if self.peek_ident() == Some("union") && self.peek_n(2) == Some(&Token::LBrace) {
                self.parse_union_declaration()?;
            } else if self.global_declaration_ahead()? {
                self.parse_global_declaration()?;
            } else {
                break;
            }
        }
        Ok(())
    }

    fn parse_parameters(&mut self) -> Result<Vec<ImportedParameter>, CSyntaxError> {
        let mut parameters = Vec::new();
        if self.peek() == Some(&Token::RParen) {
            return Ok(parameters);
        }

        loop {
            // A trailing `...` is left for the caller: only a function
            // prototype may consume it, so every other parameter list
            // rejects it at its closing parenthesis.
            if self.peek() == Some(&Token::Ellipsis) {
                if parameters.is_empty() {
                    return Err(self.error_here(
                        "a variadic parameter list (`...`) requires a preceding named parameter",
                    ));
                }
                return Ok(parameters);
            }
            let parsed_type = self.parse_signature_type()?;
            if parsed_type.union_name.is_some() && !parsed_type.interface_type.is_pointer() {
                return Err(self.error_here(
                    "union value parameters are not supported; pass a pointer to the union",
                ));
            }
            self.validate_volatile_type(&parsed_type)?;
            if parsed_type.is_volatile && self.peek() == Some(&Token::LParen) {
                return Err(self.error_here(
                    "the small volatile model does not support volatile function-pointer objects",
                ));
            }
            if let Some((name, interface_type, signature)) =
                self.parse_function_pointer_declarator(parsed_type.clone())?
            {
                let kernel_name = self.declare_name(&name)?;
                self.variable_types
                    .insert(kernel_name.clone(), interface_type);
                self.variable_function_pointers
                    .insert(kernel_name.clone(), signature.clone());
                parameters.push(ImportedParameter {
                    interface_type,
                    name: kernel_name,
                    volatile: false,
                    pointee_volatile: false,
                    constant: false,
                    pointee_constant: false,
                    reference: false,
                    struct_layout: None,
                    pointee_struct_layout: None,
                    function_pointer_signature: Some(signature),
                    struct_name: None,
                    union_name: None,
                    array_element_width: None,
                    pointee_struct_class: None,
                    slice_length_parameter: None,
                    fixed_reference_bounds: None,
                });
                if self.peek() != Some(&Token::Comma) {
                    return Ok(parameters);
                }
                self.position += 1;
                continue;
            }
            if parsed_type.interface_type == InterfaceType::Void {
                if parameters.is_empty()
                    && self.peek() == Some(&Token::RParen)
                    && !parsed_type.is_constant
                    && !parsed_type.is_volatile
                {
                    return Ok(parameters);
                }
                return Err(self.error_here("function parameters cannot have type `void`"));
            }
            // An unnamed prototype parameter still has its own declaration
            // identity. Definitions must spell every parameter's source name.
            let kernel_name = if matches!(self.peek(), Some(Token::Comma | Token::RParen)) {
                self.unnamed_parameters += 1;
                let binding = self.new_automatic_binding(None);
                self.scopes
                    .last_mut()
                    .expect("parameter scope")
                    .push(ScopeBinding {
                        source_name: None,
                        kernel_name: binding.clone(),
                        shadowed: None,
                        previous_visible: None,
                    });
                binding
            } else {
                let name = self.expect_ident("parameter name")?;

                self.declare_name(&name)?
            };
            if parsed_type.is_volatile && self.peek() == Some(&Token::LBracket) {
                return Err(self.error_here(
                    "the small volatile model does not support volatile array parameters",
                ));
            }
            let struct_array =
                parsed_type.struct_name.is_some() && self.peek() == Some(&Token::LBracket);
            let struct_value = is_plain_struct_type(&parsed_type) && !struct_array;
            if struct_value && parsed_type.is_constant {
                return Err(self.error_here(
                    "const-qualified struct value parameters are not supported in this slice",
                ));
            }
            let struct_value_layout = if struct_value {
                Some(
                    self.scalar_struct_value_layout(
                        parsed_type
                            .struct_name
                            .as_deref()
                            .expect("plain struct parameter carries its name"),
                    )?,
                )
            } else {
                None
            };
            // A parameter of array type, written `int values[3]` or through
            // a typedef, `triple values`, is adjusted to a pointer to its
            // element (C11 6.7.6.3p7).
            let typedef_array = parsed_type.interface_type.array_length().is_some();
            let array_parameter = self.peek() == Some(&Token::LBracket) || typedef_array;
            let interface_type = if typedef_array {
                let element = parsed_type
                    .interface_type
                    .pointee_type()
                    .expect("an array type has an element type");
                self.array_parameter_pointer(element)?
            } else {
                struct_value_layout
                    .as_ref()
                    .map(record_value_type)
                    .unwrap_or(self.parse_parameter_array_suffix(parsed_type.interface_type)?)
            };
            if parsed_type.union_name.is_some() && array_parameter {
                return Err(self.error_here("arrays of union parameters are not supported yet"));
            }
            let object_volatile = parsed_type.object_is_volatile();
            let pointee_volatile = parsed_type.pointee_is_volatile();
            let object_constant = parsed_type.is_constant && !array_parameter;
            let pointee_constant =
                parsed_type.pointee_constant || (parsed_type.is_constant && array_parameter);
            self.variable_types
                .insert(kernel_name.clone(), interface_type);
            if let Some(signature) = &parsed_type.function_pointer_signature {
                self.variable_function_pointers
                    .insert(kernel_name.clone(), signature.clone());
            }
            if object_constant {
                self.variable_constants.insert(kernel_name.clone());
            }
            if pointee_constant {
                self.variable_pointee_constants.insert(kernel_name.clone());
            }
            let struct_name = parsed_type.struct_name;
            if struct_name.is_some() {
                if interface_type != parsed_type.interface_type && !struct_array && !struct_value {
                    return Err(
                        self.error_here("array parameters of struct type are not supported")
                    );
                }
                let struct_name_value = struct_name.clone().expect("struct_name checked above");
                self.variable_structs
                    .insert(kernel_name.clone(), struct_name_value.clone());
                if struct_value {
                    self.variable_struct_values
                        .insert(kernel_name.clone(), struct_name_value.clone());
                    parameters.push(ImportedParameter {
                        interface_type,
                        name: kernel_name,
                        volatile: object_volatile,
                        pointee_volatile,
                        constant: object_constant,
                        pointee_constant,
                        reference: false,
                        struct_layout: struct_value_layout,
                        pointee_struct_layout: (interface_type.is_pointer() && !array_parameter)
                            .then(|| {
                                struct_name
                                    .as_ref()
                                    .and_then(|name| self.structs.get(name).cloned())
                            })
                            .flatten(),
                        function_pointer_signature: None,
                        struct_name,
                        union_name: None,
                        array_element_width: None,
                        pointee_struct_class: None,
                        slice_length_parameter: None,
                        fixed_reference_bounds: None,
                    });
                    if self.peek() != Some(&Token::Comma) {
                        return Ok(parameters);
                    }
                    self.position += 1;
                    continue;
                }
                if struct_array {
                    let element_width = self
                        .structs
                        .get(&struct_name_value)
                        .ok_or_else(|| {
                            self.error_here(format!(
                                "unknown struct declaration `{struct_name_value}`"
                            ))
                        })?
                        .size_bytes;
                    self.variable_array_shapes
                        .insert(kernel_name.clone(), vec![1]);
                    // The declarator's bound is not part of the function's
                    // pointer type. Keep the placeholder shape for ABI
                    // lowering, but do not treat its `1` as a runtime bound.
                    self.incomplete_array_names.insert(kernel_name.clone());
                    parameters.push(ImportedParameter {
                        interface_type,
                        name: kernel_name,
                        volatile: object_volatile,
                        pointee_volatile,
                        constant: object_constant,
                        pointee_constant,
                        reference: false,
                        struct_layout: self.structs.get(&struct_name_value).cloned(),
                        pointee_struct_layout: None,
                        function_pointer_signature: None,
                        struct_name,
                        union_name: None,
                        array_element_width: Some(element_width),
                        pointee_struct_class: None,
                        slice_length_parameter: None,
                        fixed_reference_bounds: None,
                    });
                    if self.peek() != Some(&Token::Comma) {
                        return Ok(parameters);
                    }
                    self.position += 1;
                    continue;
                }
            }
            parameters.push(ImportedParameter {
                interface_type,
                name: kernel_name,
                slice_length_parameter: None,
                fixed_reference_bounds: None,
                volatile: object_volatile,
                pointee_volatile,
                constant: object_constant,
                pointee_constant,
                reference: false,
                struct_layout: struct_name
                    .as_ref()
                    .and_then(|name| self.structs.get(name))
                    .cloned(),
                pointee_struct_layout: None,
                function_pointer_signature: parsed_type.function_pointer_signature,
                pointee_struct_class: struct_name
                    .as_deref()
                    .and_then(|name| {
                        struct_pointer_class(
                            interface_type,
                            crate::kernel::effective_type::CPointeeBase::Struct(
                                self.struct_class(name),
                            ),
                        )
                    })
                    .and_then(|class| class.pointee()),
                struct_name,
                union_name: parsed_type.union_name,
                array_element_width: None,
            });

            if self.peek() != Some(&Token::Comma) {
                return Ok(parameters);
            }
            self.position += 1;
        }
    }

    fn parse_signature_type(&mut self) -> Result<ParsedType, CSyntaxError> {
        if !self.parsing_function_header {
            return self.parse_type();
        }
        let ty = self.parse_type_with_anonymous_struct(false, true, true)?;
        self.opaque_function_signature |= ty.opaque_builtin || ty.long_double;
        self.opaque_signature_types
            .push((ty.opaque_builtin, ty.long_double));
        Ok(ty)
    }

    fn parse_type(&mut self) -> Result<ParsedType, CSyntaxError> {
        self.parse_type_with_anonymous_struct(false, false, false)
    }

    fn parse_type_with_anonymous_struct(
        &mut self,
        allow_anonymous_struct: bool,
        allow_long_double_layout: bool,
        allow_opaque_declaration: bool,
    ) -> Result<ParsedType, CSyntaxError> {
        let is_constant = if self.peek_ident() == Some("const") {
            self.position += 1;
            true
        } else {
            false
        };
        let is_volatile = if self.peek_ident() == Some("volatile") {
            self.position += 1;
            true
        } else {
            false
        };
        let parsed = match self.next() {
            Some(Token::Ident(name)) if name == "typeof" || name == "__typeof__" => {
                self.parse_typeof_type()?
            }
            Some(Token::Ident(name)) if name == "struct" => ParsedType {
                compatibility_identity: CompatibilityIdentity::Direct,
                // The C model has no struct-value representation. Keep the tag on the
                // parsed type while using the scalar slot as an internal
                // placeholder so `typedef struct S S_t;` can later become
                // `struct S*` when the declarator supplies `*`.
                interface_type: InterfaceType::Int32,
                long_double: false,
                aligned_typedef: false,
                opaque_builtin: false,
                function_pointer_signature: None,
                struct_name: Some(
                    if allow_anonymous_struct && self.peek() == Some(&Token::LBrace) {
                        // Anonymous types have nominal identity per declaration,
                        // never the typedef spelling or an invented visible tag.
                        // The source and token position are stable on reparse and
                        // keep unrelated translation units and declarations apart.
                        let name = format!(
                            "#anonymous-struct:{}:{}",
                            self.source_identity.as_deref().unwrap_or("source"),
                            self.position
                        );
                        self.parse_struct_body(name.clone(), false)?;
                        name
                    } else {
                        let name = self.expect_ident("struct name")?;
                        if allow_anonymous_struct && self.peek() == Some(&Token::LBrace) {
                            self.parse_struct_body(name.clone(), false)?;
                        }
                        name
                    },
                ),
                enum_name: None,
                union_name: None,
                is_volatile: false,
                volatile_levels: 0,
                is_constant: false,
                pointee_constant: false,
                pointer_depth: 0,
            },
            Some(Token::Ident(name)) if name == "union" => ParsedType {
                compatibility_identity: CompatibilityIdentity::Direct,
                // A union has no runtime aggregate value in the C model. Keep its tag
                // on the parsed type while using an int32 placeholder for
                // the address-backed member-selection path.
                interface_type: InterfaceType::Int32,
                long_double: false,
                aligned_typedef: false,
                opaque_builtin: false,
                function_pointer_signature: None,
                struct_name: None,
                enum_name: None,
                union_name: {
                    let union_name =
                        if allow_anonymous_struct && self.peek() == Some(&Token::LBrace) {
                            let name = format!(
                                "#anonymous-union:{}:{}",
                                self.source_identity.as_deref().unwrap_or("source"),
                                self.position
                            );
                            self.parse_union_body(name.clone())?;
                            name
                        } else {
                            let name = self.expect_ident("union name")?;
                            if allow_anonymous_struct && self.peek() == Some(&Token::LBrace) {
                                self.parse_union_body(name.clone())?;
                            } else if !self.unions.contains_key(&name) {
                                return Err(
                                    self.error_here(format!("unknown union declaration `{name}`"))
                                );
                            }
                            name
                        };
                    Some(union_name)
                },
                is_volatile: false,
                volatile_levels: 0,
                is_constant: false,
                pointee_constant: false,
                pointer_depth: 0,
            },
            Some(Token::Ident(name)) if name == "enum" => {
                // A typedef may define the enumeration it names, as in
                // `typedef enum { A, B } kind_t;`.
                let enum_name = if allow_anonymous_struct
                    && (self.peek() == Some(&Token::LBrace)
                        || self.peek_next() == Some(&Token::LBrace))
                {
                    self.position -= 1;
                    self.parse_enum_specifier_body()?
                } else {
                    self.expect_ident("enum name")?
                };
                let Some(definition) = self.enums.get(&enum_name) else {
                    return Err(self.error_here(format!("unknown enum declaration `{enum_name}`")));
                };
                ParsedType {
                    compatibility_identity: CompatibilityIdentity::Direct,
                    interface_type: definition.compatible_type,
                    long_double: false,
                    aligned_typedef: false,
                    opaque_builtin: false,
                    function_pointer_signature: None,
                    struct_name: None,
                    union_name: None,
                    enum_name: Some(enum_name),
                    is_volatile: false,
                    volatile_levels: 0,
                    is_constant: false,
                    pointee_constant: false,
                    pointer_depth: 0,
                }
            }
            Some(Token::Ident(name)) => self.parse_named_type(name)?,
            Some(token) => {
                return Err(self.error_at_previous(format!(
                    "expected type `void`, integer, `float`, `double`, `enum`, or `struct`, got {}",
                    token.describe()
                )));
            }
            None => {
                return Err(self.error_here(
                    "expected type `void`, integer, `float`, `double`, `enum`, or `struct`, got end of input",
                ));
            }
        };

        let mut interface_type = parsed.interface_type;
        let mut volatile_levels = parsed.volatile_levels;
        if is_volatile {
            volatile_levels |= 1;
        }
        let mut object_constant = is_constant || parsed.is_constant;
        let mut pointee_constant = parsed.pointee_constant;
        if self.peek_ident() == Some("volatile") {
            self.position += 1;
            volatile_levels |= 1;
        }
        if self.peek_ident() == Some("const") {
            self.position += 1;
            object_constant = true;
        }
        let mut saw_pointer = false;
        let mut pointer_depth: u8 = 0;
        while self.peek() == Some(&Token::Star) {
            pointer_depth = pointer_depth.saturating_add(1);
            // Only the immediate pointee's const qualification is recorded.
            // A qualifier deeper than that, as in `const char *const *`,
            // changes no behavior; the pointer values stored in the cells
            // carry their own pointee qualification.
            let base_constant = object_constant;
            object_constant = false;
            self.position += 1;
            volatile_levels <<= 1;
            interface_type = match interface_type {
                InterfaceType::Parameter(_) | InterfaceType::ParameterPointer(_) => {
                    return Err(
                        self.error_at_previous("pointers to an abstract type are not supported")
                    );
                }
                InterfaceType::Bool => {
                    return Err(self.error_at_previous(
                        "pointers to `_Bool` are not supported in Click's current C pointer model",
                    ));
                }
                InterfaceType::Int8 => InterfaceType::Int8Pointer,
                InterfaceType::Int16 => InterfaceType::Int16Pointer,
                InterfaceType::Int32 if parsed.union_name.is_some() && !saw_pointer => {
                    InterfaceType::VoidPointer
                }
                InterfaceType::Int32 => InterfaceType::Int32Pointer,
                InterfaceType::Char(plain) => InterfaceType::CharPointer(plain),
                InterfaceType::UInt8 => InterfaceType::UInt8Pointer,
                InterfaceType::UInt16 => InterfaceType::UInt16Pointer,
                InterfaceType::UInt32 => InterfaceType::UInt32Pointer,
                InterfaceType::Int64(rank) => InterfaceType::Int64Pointer(rank),
                InterfaceType::Int128 => InterfaceType::Int128Pointer,
                InterfaceType::UInt64(rank) => InterfaceType::UInt64Pointer(rank),
                InterfaceType::UInt128 => InterfaceType::UInt128Pointer,
                InterfaceType::Float32 => InterfaceType::Float32Pointer,
                InterfaceType::Float64 => InterfaceType::Float64Pointer,
                InterfaceType::Int8Pointer => InterfaceType::Int8PointerPointer,
                InterfaceType::Int16Pointer => InterfaceType::Int16PointerPointer,
                InterfaceType::UInt16Pointer => InterfaceType::UInt16PointerPointer,
                InterfaceType::Int32Pointer => InterfaceType::Int32PointerPointer,
                InterfaceType::CharPointer(plain) => InterfaceType::CharPointerPointer(plain),
                InterfaceType::UInt8Pointer => InterfaceType::UInt8PointerPointer,
                InterfaceType::UInt32Pointer => InterfaceType::UInt32PointerPointer,
                InterfaceType::Int64Pointer(rank) => InterfaceType::Int64PointerPointer(rank),
                InterfaceType::Int128Pointer => InterfaceType::Int128PointerPointer,
                InterfaceType::UInt64Pointer(rank) => InterfaceType::UInt64PointerPointer(rank),
                InterfaceType::UInt128Pointer => InterfaceType::UInt128PointerPointer,
                InterfaceType::Float32Pointer => InterfaceType::Float32PointerPointer,
                InterfaceType::Float64Pointer => InterfaceType::Float64PointerPointer,
                InterfaceType::Void => InterfaceType::VoidPointer,
                InterfaceType::VoidPointer => InterfaceType::VoidPointerPointer,
                // An opaque prototype may retain this nominal pointee, but
                // cannot use the placeholder's byte-array layout as an ABI.
                InterfaceType::UInt8Array(16) if parsed.long_double && allow_opaque_declaration => {
                    InterfaceType::VoidPointer
                }
                InterfaceType::Int8PointerPointer => {
                    return Err(
                        self.error_at_previous("pointer depth beyond `**` is not supported")
                    );
                }
                InterfaceType::Int16PointerPointer
                | InterfaceType::VoidPointerPointer
                | InterfaceType::UInt16PointerPointer
                | InterfaceType::Int32PointerPointer
                | InterfaceType::CharPointerPointer(_)
                | InterfaceType::UInt8PointerPointer
                | InterfaceType::UInt32PointerPointer
                | InterfaceType::Int128PointerPointer
                | InterfaceType::Int64PointerPointer(_)
                | InterfaceType::UInt128PointerPointer
                | InterfaceType::UInt64PointerPointer(_) => {
                    return Err(
                        self.error_at_previous("pointer depth beyond `**` is not supported")
                    );
                }
                InterfaceType::Float32PointerPointer | InterfaceType::Float64PointerPointer => {
                    return Err(
                        self.error_at_previous("pointer depth beyond `**` is not supported")
                    );
                }
                InterfaceType::Int8Array(_) => {
                    return Err(self.error_at_previous("pointer-to-array types are not supported"));
                }
                InterfaceType::PointerArray(_, _, _) => {
                    return Err(self.error_at_previous("pointer-to-array types are not supported"));
                }
                InterfaceType::Int32Array(_)
                | InterfaceType::CharArray(_, _)
                | InterfaceType::UInt8Array(_)
                | InterfaceType::Int16Array(_)
                | InterfaceType::UInt16Array(_)
                | InterfaceType::UInt32Array(_)
                | InterfaceType::Int128Array(_)
                | InterfaceType::Int64Array(_, _)
                | InterfaceType::UInt128Array(_)
                | InterfaceType::UInt64Array(_, _) => {
                    return Err(self.error_at_previous("pointer-to-array types are not supported"));
                }
                InterfaceType::Float32Array(_) | InterfaceType::Float64Array(_) => {
                    return Err(self.error_at_previous("pointer-to-array types are not supported"));
                }
                InterfaceType::FunctionPointer(_) => {
                    return Err(
                        self.error_at_previous("pointers to function pointers are not supported")
                    );
                }
            };
            pointee_constant = base_constant;
            loop {
                match self.peek_ident() {
                    Some("const") => object_constant = true,
                    Some("volatile") => volatile_levels |= 1,
                    // Restrict constrains aliases used by a valid C program.
                    // Click never infers ownership or separation from it,
                    // and it does not check it either, so it is refused
                    // where GCC's optimizer relies on it.
                    Some("restrict" | "__restrict" | "__restrict__") if self.refuse_promises => {
                        return Err(self.error_here(
                            "`restrict` is refused under an optimizing compiler-option profile: GCC at -O2 assumes restrict pointers do not alias, and Click does not check it",
                        ));
                    }
                    Some("restrict" | "__restrict" | "__restrict__") => {}
                    _ => break,
                }
                self.position += 1;
            }
            saw_pointer = true;
            if parsed.union_name.is_some() && pointer_depth > 1 {
                return Err(
                    self.error_at_previous("pointer depth beyond `union *` is not supported yet")
                );
            }
            if parsed.enum_name.is_some() && interface_type.is_pointer() {
                return Err(self.error_at_previous("pointers to enum values are not supported"));
            }
        }
        if parsed.opaque_builtin && !allow_opaque_declaration {
            return Err(self.error_here(
                "__builtin_va_list is declaration-only; its layout and value operations are not modeled",
            ));
        }
        if parsed.aligned_typedef && !saw_pointer {
            return Err(self.error_here(
                "GNU aligned typedef values need modeled object alignment; pointer uses are supported",
            ));
        }
        if parsed.long_double && !allow_long_double_layout {
            return Err(
                self.error_here("long double value operations need an extended-precision model")
            );
        }
        Ok(ParsedType {
            compatibility_identity: if saw_pointer
                && (parsed.compatibility_identity == CompatibilityIdentity::TypeofStruct
                    || parsed.pointee_constant)
            {
                CompatibilityIdentity::Unavailable
            } else {
                parsed.compatibility_identity
            },
            interface_type,
            long_double: parsed.long_double,
            aligned_typedef: false,
            opaque_builtin: parsed.opaque_builtin,
            function_pointer_signature: parsed.function_pointer_signature,
            struct_name: parsed.struct_name,
            enum_name: parsed.enum_name,
            union_name: parsed.union_name,
            is_volatile: volatile_levels != 0,
            volatile_levels,
            is_constant: object_constant,
            pointee_constant,
            pointer_depth,
        })
    }

    fn validate_volatile_type(&self, parsed_type: &ParsedType) -> Result<(), CSyntaxError> {
        if !parsed_type.is_volatile {
            return Ok(());
        }
        // The sequential model tracks the object and its immediate pointee
        // independently. A qualifier below that boundary would require a
        // recursive qualified-type representation that the C memory model
        // intentionally does not provide.
        if parsed_type.has_deeper_volatile()
            || parsed_type.union_name.is_some()
            || parsed_type.enum_name.is_some()
            || (parsed_type.struct_name.is_some()
                && (!parsed_type.interface_type.is_pointer()
                    || (parsed_type.pointee_is_volatile()
                        && !parsed_type
                            .interface_type
                            .pointee_type()
                            .is_some_and(InterfaceType::is_pointer))))
        {
            return Err(self.error_here(
                "the sequential volatile model supports scalar objects and pointers to scalar objects",
            ));
        }
        Ok(())
    }

    fn typeof_has_exact_struct_identity(&self, expression: &CExpression) -> bool {
        // Layout origin can survive a pointer cast, but GNU type
        // compatibility asks for the C type of the expression itself.
        match expression {
            CExpression::StatementExpression {
                aggregate_lvalue: true,
                ..
            } => true,
            CExpression::Variable(name) => self.variable_struct_values.contains_key(name),
            CExpression::Field {
                field_type: InterfaceType::Int32,
                field_struct_name: Some(_),
                ..
            } => true,
            CExpression::Load(pointer, _) | CExpression::AggregateAddress { pointer, .. } => {
                // Member lowering inserts byte offsets before the aggregate
                // wrapper. These offsets preserve the declared member type.
                let mut pointer = pointer.as_ref();
                while let CExpression::PointerOffsetBytes { pointer: base, .. }
                | CExpression::Subobject { pointer: base, .. } = pointer
                {
                    pointer = base;
                }
                match pointer {
                    CExpression::Variable(name) => {
                        self.variable_types.get(name) == Some(&InterfaceType::Int32Pointer)
                            && self.variable_structs.contains_key(name)
                    }
                    CExpression::Cast {
                        interface_type: InterfaceType::Int32Pointer,
                        struct_name: Some(_),
                        ..
                    }
                    | CExpression::ScalarUpdate {
                        interface_type: InterfaceType::Int32Pointer,
                        struct_name: Some(_),
                        ..
                    }
                    | CExpression::Field {
                        field_type: InterfaceType::Int32Pointer,
                        field_struct_name: Some(_),
                        ..
                    } => true,
                    _ => false,
                }
            }
            _ => false,
        }
    }

    fn parse_unevaluated_type_operand(&mut self) -> Result<CExpression, CSyntaxError> {
        let previous = std::mem::replace(&mut self.unevaluated_operand, true);
        let operand =
            self.without_bit_field_operands(Self::parse_expression_allow_direct_aggregate);
        self.unevaluated_operand = previous;
        operand
    }

    /// GNU `typeof` accepts either a type-name or an expression. The
    /// expression form is inspected only for its already-modeled type; it is
    /// never emitted as an executable read, which matches the extension's
    /// unevaluated operand semantics.
    fn parse_typeof_type(&mut self) -> Result<ParsedType, CSyntaxError> {
        self.expect(Token::LParen)?;
        if self.is_type_start() {
            let parsed = self.parse_type()?;
            self.expect(Token::RParen)?;
            return Ok(parsed);
        }

        let expression = self.parse_unevaluated_type_operand()?;
        self.expect(Token::RParen)?;
        if let CExpression::Variable(name) = &expression
            && self.incomplete_array_names.contains(name)
        {
            return Err(self.error_here("GNU `typeof` of an incomplete array is not supported"));
        }
        let struct_name = self
            .struct_pointer_name(&expression)
            .or_else(|| self.aggregate_struct_name(&expression));
        let interface_type = self
            .source_expression_type(&expression)
            .or_else(|| struct_name.as_ref().map(|_| InterfaceType::Int32));
        let Some(interface_type) = interface_type else {
            return Err(self.error_here(
                "GNU `typeof` requires an expression with a modeled scalar, pointer, or struct type",
            ));
        };
        Ok(ParsedType {
            compatibility_identity: if interface_type == InterfaceType::Int32
                && struct_name.is_some()
                && self.typeof_has_exact_struct_identity(&expression)
            {
                CompatibilityIdentity::TypeofStruct
            } else {
                CompatibilityIdentity::Unavailable
            },
            interface_type,
            long_double: false,
            aligned_typedef: false,
            opaque_builtin: false,
            function_pointer_signature: self.function_pointer_signature(&expression),
            struct_name,
            enum_name: None,
            union_name: None,
            is_volatile: false,
            volatile_levels: 0,
            is_constant: self.expression_is_constant_lvalue(&expression),
            pointee_constant: self.expression_pointee_is_constant(&expression),
            pointer_depth: 0,
        })
    }

    /// Parses the parenthesized declarator in `int32 (*callback)(int32)`.
    /// The kernel receives a structural signature key, while the returned
    /// metadata retains nominal struct-pointer tags for C boundary checks.
    fn parse_function_pointer_declarator(
        &mut self,
        return_type: ParsedType,
    ) -> Result<Option<(String, InterfaceType, CallbackInterface)>, CSyntaxError> {
        if self.peek() != Some(&Token::LParen) {
            return Ok(None);
        }
        if return_type.function_pointer_signature.is_some() {
            return Err(self.error_here("nested function-pointer signatures are not supported"));
        }
        if return_type.union_name.is_some()
            || return_type.enum_name.is_some()
            || return_type.is_volatile
            || return_type.long_double
            || return_type.opaque_builtin
        {
            return Err(
                self.error_here("callback return type needs unsupported signature metadata")
            );
        }
        if return_type.struct_name.is_some() && !return_type.interface_type.is_pointer() {
            return Err(self.error_here(
                "function-pointer return values must use modeled scalars or struct pointers",
            ));
        }
        if let Some(struct_name) = &return_type.struct_name
            && !self.structs.contains_key(struct_name)
        {
            return Err(self.error_here(format!("unknown struct declaration `{struct_name}`")));
        }
        self.position += 1;
        self.expect(Token::Star)?;
        let name = self.expect_ident("function-pointer name")?;
        self.expect(Token::RParen)?;
        self.expect(Token::LParen)?;
        let mut parameters = Vec::new();
        if self.peek() != Some(&Token::RParen) {
            loop {
                if self.peek() == Some(&Token::Ellipsis) {
                    return Err(self.error_here(
                        "variadic function-pointer signatures (`...`) are not supported by Click",
                    ));
                }
                let parsed_type = self.parse_type()?;
                if parsed_type.function_pointer_signature.is_some() {
                    return Err(
                        self.error_here("nested function-pointer signatures are not supported")
                    );
                }
                if parsed_type.union_name.is_some() || parsed_type.enum_name.is_some() {
                    return Err(self.error_here(
                        "callback parameter type needs unsupported signature metadata",
                    ));
                }
                if parsed_type.is_volatile {
                    return Err(self.error_here(
                        "volatile function-pointer parameters are not supported by the small model",
                    ));
                }
                if parsed_type.interface_type == InterfaceType::Void {
                    if parameters.is_empty() && self.peek() == Some(&Token::RParen) {
                        break;
                    }
                    return Err(self
                        .error_here("`void` must be the sole unnamed function-pointer parameter"));
                }
                let parameter_type =
                    self.parse_parameter_array_suffix(parsed_type.interface_type)?;
                if parsed_type.struct_name.is_some()
                    && parsed_type.interface_type == InterfaceType::Int32
                {
                    return Err(
                        self.error_here("function-pointer parameters cannot pass structs by value")
                    );
                }
                if let Some(struct_name) = &parsed_type.struct_name
                    && !self.structs.contains_key(struct_name)
                {
                    return Err(
                        self.error_here(format!("unknown struct declaration `{struct_name}`"))
                    );
                }
                parameters.push(CallbackParameter::new(
                    parameter_type,
                    parsed_type.struct_name,
                    parsed_type.pointee_constant,
                ));
                if matches!(self.peek(), Some(Token::Ident(_))) {
                    self.position += 1;
                }
                match self.peek() {
                    Some(Token::Comma) => self.position += 1,
                    Some(Token::RParen) => break,
                    Some(token) => {
                        return Err(self.error_here(format!(
                            "expected `,` or `)` in function-pointer parameter list, got {}",
                            token.describe()
                        )));
                    }
                    None => return Err(self.error_here(
                        "expected `,` or `)` in function-pointer parameter list, got end of input",
                    )),
                }
            }
        }
        self.expect(Token::RParen)?;
        if parameters.len() > 13 {
            return Err(
                self.error_here("function-pointer signatures support at most 13 parameters")
            );
        }
        let parameter_types = parameters
            .iter()
            .map(|parameter| {
                (
                    parameter.interface_type.to_kernel_type(),
                    parameter.pointee_constant,
                )
            })
            .collect::<Vec<_>>();
        let signature = crate::kernel::ProgramType::qualified_function_pointer_signature(
            return_type.interface_type.to_kernel_type(),
            return_type.pointee_constant,
            &parameter_types,
        );
        if signature == crate::kernel::CallbackSignature::UNSPECIFIED {
            return Err(
                self.error_here("function-pointer signature uses an unsupported modeled type")
            );
        }
        let function_pointer_signature = CallbackInterface::new(
            return_type.interface_type,
            return_type.struct_name,
            parameters,
            return_type.pointee_constant,
        );
        Ok(Some((
            name,
            InterfaceType::FunctionPointer(signature),
            function_pointer_signature,
        )))
    }

    fn parse_named_type(&mut self, name: String) -> Result<ParsedType, CSyntaxError> {
        if name == "long" && self.peek_ident() == Some("double") {
            self.position += 1;
            return Ok(ParsedType {
                compatibility_identity: CompatibilityIdentity::Direct,
                // The byte-array slot is a layout placeholder only. The
                // `long_double` marker prevents array or binary64 operations.
                interface_type: InterfaceType::UInt8Array(16),
                long_double: true,
                aligned_typedef: false,
                opaque_builtin: false,
                function_pointer_signature: None,
                struct_name: None,
                enum_name: None,
                union_name: None,
                is_volatile: false,
                volatile_levels: 0,
                is_constant: false,
                pointee_constant: false,
                pointer_depth: 0,
            });
        }
        let integer = crate::languages::c::integer_specifiers::parse(
            std::iter::once(name.as_str()).chain(self.tokens[self.position..].iter().map_while(
                |token| match token {
                    Token::Ident(word) => Some(word.as_str()),
                    _ => None,
                },
            )),
            Some(self.plain_char),
        )
        .map_err(|message| self.error_at_previous(message))?;
        let interface_type = if let Some((interface_type, count)) = integer {
            self.position += count - 1;
            interface_type
        } else {
            match name.as_str() {
                // Only a header bookkeeping slot: opaque_builtin forbids
                // every operation that could interpret it as a pointer or
                // infer a layout. This does not model the real va_list ABI.
                "__builtin_va_list" => InterfaceType::VoidPointer,
                "void" => InterfaceType::Void,
                "_Bool" | "bool" => InterfaceType::Bool,
                "int8" | "int8_t" => InterfaceType::Int8,
                "int16" | "int16_t" => InterfaceType::Int16,
                "int32" | "int32_t" => InterfaceType::Int32,
                "uint8" | "uint8_t" => InterfaceType::UInt8,
                "uint16" | "uint16_t" => InterfaceType::UInt16,
                "uint32" | "uint32_t" => InterfaceType::UInt32,
                "int64" | "ssize_t" => InterfaceType::Int64(LongRank::Long),
                "uint64" | "size_t" => InterfaceType::UInt64(LongRank::Long),
                "int64_t" => InterfaceType::Int64(self.int64_t_rank),
                "uint64_t" => InterfaceType::UInt64(self.int64_t_rank),
                "float" => InterfaceType::Float32,
                "double" => InterfaceType::Float64,
                "volatile" => {
                    return Err(self
                        .error_at_previous("the `volatile` qualifier is not supported by Click"));
                }
                _ => {
                    let Some(typedef) = self.typedefs.get(&name) else {
                        return Err(self.error_at_previous(format!(
                        "unknown C type `{name}`; expected a supported standard spelling, typedef, or `struct`"
                    )));
                    };
                    return Ok(typedef.clone());
                }
            }
        };
        Ok(ParsedType {
            compatibility_identity: CompatibilityIdentity::Direct,
            interface_type,
            long_double: false,
            aligned_typedef: false,
            opaque_builtin: name == "__builtin_va_list",
            function_pointer_signature: None,
            struct_name: None,
            enum_name: None,
            union_name: None,
            is_volatile: false,
            volatile_levels: 0,
            is_constant: false,
            pointee_constant: false,
            pointer_depth: 0,
        })
    }

    fn parse_parameter_array_suffix(
        &mut self,
        interface_type: InterfaceType,
    ) -> Result<InterfaceType, CSyntaxError> {
        if self.peek() != Some(&Token::LBracket) {
            return Ok(interface_type);
        }
        let pointer_type = self.array_parameter_pointer(interface_type)?;
        self.position += 1;
        if matches!(self.peek(), Some(Token::Number(_))) {
            self.position += 1;
        }
        self.expect(Token::RBracket)?;
        Ok(pointer_type)
    }

    /// The pointer type an array parameter of `element`s is adjusted to.
    fn array_parameter_pointer(
        &self,
        element: InterfaceType,
    ) -> Result<InterfaceType, CSyntaxError> {
        Ok(match element {
            InterfaceType::Int8 => InterfaceType::Int8Pointer,
            InterfaceType::Int16 => InterfaceType::Int16Pointer,
            InterfaceType::UInt16 => InterfaceType::UInt16Pointer,
            InterfaceType::Int32 => InterfaceType::Int32Pointer,
            InterfaceType::Char(plain) => InterfaceType::CharPointer(plain),
            InterfaceType::UInt8 => InterfaceType::UInt8Pointer,
            InterfaceType::UInt32 => InterfaceType::UInt32Pointer,
            InterfaceType::Int64(rank) => InterfaceType::Int64Pointer(rank),
            InterfaceType::Int128 => InterfaceType::Int128Pointer,
            InterfaceType::UInt64(rank) => InterfaceType::UInt64Pointer(rank),
            InterfaceType::UInt128 => InterfaceType::UInt128Pointer,
            InterfaceType::Float32 => InterfaceType::Float32Pointer,
            InterfaceType::Float64 => InterfaceType::Float64Pointer,
            InterfaceType::Int8Pointer => InterfaceType::Int8PointerPointer,
            InterfaceType::Int16Pointer => InterfaceType::Int16PointerPointer,
            InterfaceType::UInt16Pointer => InterfaceType::UInt16PointerPointer,
            InterfaceType::Int32Pointer => InterfaceType::Int32PointerPointer,
            InterfaceType::CharPointer(plain) => InterfaceType::CharPointerPointer(plain),
            InterfaceType::UInt8Pointer => InterfaceType::UInt8PointerPointer,
            InterfaceType::UInt32Pointer => InterfaceType::UInt32PointerPointer,
            InterfaceType::Int64Pointer(rank) => InterfaceType::Int64PointerPointer(rank),
            InterfaceType::Int128Pointer => InterfaceType::Int128PointerPointer,
            InterfaceType::UInt64Pointer(rank) => InterfaceType::UInt64PointerPointer(rank),
            InterfaceType::UInt128Pointer => InterfaceType::UInt128PointerPointer,
            _ => {
                return Err(
                    self.error_here("only scalar and pointer array parameters are supported")
                );
            }
        })
    }

    fn parse_local_array_shape(
        &mut self,
        parsed_type: &ParsedType,
    ) -> Result<(InterfaceType, Option<Vec<u32>>, bool), CSyntaxError> {
        if self.peek() != Some(&Token::LBracket) {
            return Ok((parsed_type.interface_type, None, false));
        }
        let (element_width, element_name, struct_array) = if is_plain_struct_type(parsed_type) {
            let struct_name = parsed_type
                .struct_name
                .as_deref()
                .expect("plain struct array has a tag");
            let element_width = self
                .structs
                .get(struct_name)
                .ok_or_else(|| {
                    self.error_here(format!("unknown struct declaration `{struct_name}`"))
                })?
                .size_bytes;
            (element_width, format!("struct {struct_name}"), true)
        } else {
            if array_type_for_element(parsed_type.interface_type, 1).is_none() {
                return Err(
                    self.error_here("only modeled scalar and pointer local arrays are supported")
                );
            }
            (
                parsed_type.interface_type.abi_size_bytes(),
                parsed_type.interface_type.diagnostic_name(),
                false,
            )
        };

        if element_width == 0 {
            return Err(self.error_here(format!(
                "{element_name} array elements must have positive size"
            )));
        }

        let mut dimensions = Vec::new();
        let mut incomplete = false;
        let mut element_count = 1u32;
        while self.peek() == Some(&Token::LBracket) {
            self.position += 1;
            let length = if self.peek() == Some(&Token::RBracket) {
                if !dimensions.is_empty() {
                    return Err(self.error_here("only the outer local array bound may be omitted"));
                }
                if struct_array {
                    return Err(self.error_here(
                        "inferred automatic arrays of struct values are not supported",
                    ));
                }
                incomplete = true;
                0
            } else if self.peek_ident() == Some("sizeof") {
                let length = match self.parse_primary()? {
                    CExpression::SizeOfStruct { bytes, .. }
                    | CExpression::SizeOfUnion { bytes, .. }
                    | CExpression::SizeOfType { bytes, .. } => bytes,
                    CExpression::UInt64Literal(bytes) => u32::try_from(bytes)
                        .map_err(|_| self.error_here("array length is out of range"))?,
                    _ => {
                        return Err(
                            self.error_here("expected a constant sizeof as the array length")
                        );
                    }
                };
                if length == 0 {
                    return Err(self.error_here("local arrays must have positive length"));
                }
                length
            } else {
                match self.next() {
                    Some(Token::Number(number)) => {
                        let length =
                            parse_integer_literal_magnitude(&number).map_err(|reason| {
                                self.error_here(format!(
                                    "invalid array length `{number}`: {reason}"
                                ))
                            })?;
                        let length = u32::try_from(length).map_err(|_| {
                            self.error_here(format!("array length `{number}` is out of range"))
                        })?;
                        if length == 0 {
                            return Err(self.error_here("local arrays must have positive length"));
                        }
                        length
                    }
                    Some(token) => {
                        return Err(self.error_at_previous(format!(
                            "expected local array length, got {}",
                            token.describe()
                        )));
                    }
                    None => {
                        return Err(
                            self.error_here("expected local array length, got end of input")
                        );
                    }
                }
            };
            if length != 0 {
                element_count = element_count.checked_mul(length).ok_or_else(|| {
                    self.error_here(format!(
                        "array dimensions are too large for {element_name} elements"
                    ))
                })?;
            }
            dimensions.push(length);
            self.expect(Token::RBracket)?;
        }
        if element_count.checked_mul(element_width).is_none() {
            return Err(self.error_here(format!(
                "array dimensions are too large for {element_name} elements"
            )));
        }
        let array_length = if struct_array {
            element_count.checked_mul(element_width).ok_or_else(|| {
                self.error_here(format!(
                    "array dimensions are too large for {element_name} elements"
                ))
            })?
        } else {
            element_count
        };
        let shape = (incomplete || struct_array || dimensions.len() > 1).then_some(dimensions);
        let array_type = if struct_array {
            InterfaceType::UInt8Array(array_length)
        } else {
            array_type_for_element(
                parsed_type.interface_type,
                if incomplete { 0 } else { array_length },
            )
            .expect("validated local array element type")
        };
        Ok((array_type, shape, incomplete))
    }

    /// Opens the statement as written that starts here: the next child of the
    /// innermost open statement, or of the function body. Its own children
    /// are counted from here until [`Self::end_source_statement`]. A label's
    /// body reuses the label's statement.
    fn begin_source_statement(&mut self) -> Option<std::sync::Arc<[u32]>> {
        if std::mem::take(&mut self.source_label_body) {
            let frame = self.source_regions.last().cloned().flatten();
            let path = frame.as_ref().map(|(path, _)| path.clone());
            self.source_regions.push(frame);
            return path;
        }
        let path = match self.source_regions.last_mut() {
            Some(Some((parent, children))) => {
                let path = parent
                    .iter()
                    .copied()
                    .chain([*children])
                    .collect::<std::sync::Arc<[u32]>>();
                *children += 1;
                Some(path)
            }
            _ => None,
        };
        self.source_regions.push(path.clone().map(|path| (path, 0)));
        path
    }

    fn end_source_statement(&mut self) {
        self.source_regions.pop();
    }

    fn parse_block_statement(&mut self) -> Result<CStatement, CSyntaxError> {
        self.expect(Token::LBrace)?;
        if self.current_function_source_name.is_some() {
            self.function_block_depth += 1;
        }
        self.push_scope();
        let mut statements = Vec::new();
        while self.peek() != Some(&Token::RBrace) {
            if self.peek().is_none() {
                return Err(self.error_here("expected statement or `}`, got end of input"));
            }
            statements.push(self.parse_statement()?);
        }
        self.expect(Token::RBrace)?;
        let body = balanced_statement_sequence(statements).unwrap_or(CStatement::Skip);
        let body = self.lower_call_expressions(body)?;
        let body = self.finish_compound_literal_block(body);
        self.pop_scope();
        if self.current_function_source_name.is_some() {
            self.function_block_depth -= 1;
        }

        Ok(body)
    }

    /// Parses the supported C `switch` shape: a compound statement whose
    /// direct children are `case`/`default` labels and their statement bodies.
    /// Case labels are integer constant expressions. Keeping the cases in
    /// source order is what preserves C fallthrough.
    fn parse_switch_body(&mut self) -> Result<Vec<CSwitchCase>, CSyntaxError> {
        self.expect(Token::LBrace)?;
        self.push_scope();
        let mut cases = Vec::new();
        while self.peek() != Some(&Token::RBrace) {
            if self.peek().is_none() {
                return Err(self.error_here("expected switch case or `}`, got end of input"));
            }
            let label = self.peek_ident();
            let value = match label {
                Some("case") => {
                    self.position += 1;
                    let expression = self.parse_expression()?;
                    let value =
                        evaluate_static_switch_case_value(&expression).map_err(|error| {
                            let message = match error {
                                StaticIntegerEvaluationError::NotConstant => {
                                    "`case` labels require integer constant expressions"
                                }
                                StaticIntegerEvaluationError::Overflow => {
                                    "`case` label integer constant expression overflows"
                                }
                                StaticIntegerEvaluationError::DivisionByZero => {
                                    "`case` label integer constant expression divides by zero"
                                }
                                StaticIntegerEvaluationError::InvalidShift => {
                                    "`case` label integer constant expression has an invalid shift"
                                }
                                StaticIntegerEvaluationError::OutOfRange => {
                                    "`case` label integer constant expression is out of range"
                                }
                            };
                            self.error_here(message)
                        })?;
                    self.expect(Token::Colon)?;
                    if cases
                        .iter()
                        .any(|case: &CSwitchCase| case.value == Some(value))
                    {
                        return Err(
                            self.error_here(format!("duplicate `case` label value {value}"))
                        );
                    }
                    Some(value)
                }
                Some("default") => {
                    self.position += 1;
                    self.expect(Token::Colon)?;
                    if cases.iter().any(|case| case.value.is_none()) {
                        return Err(self.error_here("a `switch` may have only one `default` label"));
                    }
                    None
                }
                _ if cases.is_empty() => {
                    self.pop_scope();
                    return Err(self.error_here(
                        "a `switch` body must begin with a `case` or `default` label",
                    ));
                }
                _ => {
                    self.pop_scope();
                    return Err(self.error_here(
                        "statements in a `switch` body must follow a `case` or `default` label",
                    ));
                }
            };

            let mut statements = Vec::new();
            while self.peek() != Some(&Token::RBrace)
                && !matches!(self.peek_ident(), Some("case" | "default"))
            {
                statements.push(self.parse_statement()?);
            }
            cases.push(CSwitchCase {
                value,
                body: Box::new(balanced_statement_sequence(statements).unwrap_or(CStatement::Skip)),
            });
        }
        self.expect(Token::RBrace)?;
        let declarations = std::mem::take(
            self.compound_literal_declarations
                .last_mut()
                .expect("switch body scope"),
        );
        self.pop_scope();
        self.compound_literal_declarations
            .last_mut()
            .expect("switch statement scope")
            .extend(declarations);
        if cases.is_empty() {
            return Err(self.error_here("a `switch` body must contain a `case` or `default` label"));
        }
        Ok(cases)
    }

    /// Parses the statement controlled by `if`, `else`, `while`, or `for`.
    /// C permits a single statement in these positions, while declarations
    /// remain valid only as block items in a compound statement.
    fn parse_controlled_statement(&mut self, construct: &str) -> Result<CStatement, CSyntaxError> {
        self.controlled_statement_depth += 1;
        self.push_scope();
        let result = if self.peek() == Some(&Token::LBrace) {
            self.parse_block_statement()
        } else if self.is_type_start() {
            Err(self.error_here(format!(
                "a declaration controlled by `{construct}` must be enclosed in braces"
            )))
        } else {
            self.parse_statement()
        };
        self.controlled_statement_depth -= 1;
        let result = result.map(|body| self.finish_compound_literal_block(body));
        self.pop_scope();
        result
    }

    fn parse_loop_control_statement(
        &mut self,
        continue_statement: bool,
    ) -> Result<CStatement, CSyntaxError> {
        if continue_statement {
            let loop_context = self.loop_contexts.iter().rev().find(|context| {
                matches!(
                    context,
                    CLoopContext::While | CLoopContext::For | CLoopContext::DoWhile
                )
            });
            match loop_context {
                Some(CLoopContext::While) => {}
                Some(CLoopContext::For) => {}
                Some(CLoopContext::DoWhile) => {}
                None => return Err(self.error_here("`continue` must be inside a loop")),
                Some(CLoopContext::Switch) => unreachable!(),
            }
        } else {
            match self.loop_contexts.last().copied() {
                Some(CLoopContext::While | CLoopContext::For | CLoopContext::Switch) => {}
                Some(CLoopContext::DoWhile) => {}
                None => return Err(self.error_here("`break` must be inside a loop or switch")),
            }
        }
        self.position += 1;
        self.expect(Token::Semicolon)?;
        Ok(if continue_statement {
            CStatement::Continue
        } else {
            CStatement::Break
        })
    }

    /// Parses one statement and gives it, and every statement it lowered to
    /// that has no site of its own yet, the site where it was written.
    /// Statements nested inside it were parsed here first and keep theirs.
    #[inline(never)]
    fn parse_statement(&mut self) -> Result<CStatement, CSyntaxError> {
        if self.peek_ident() == Some("if") || self.peek() == Some(&Token::LBrace) {
            let controlled_depth = self.controlled_statement_depth;
            let result = self.parse_statement_iterative();
            self.controlled_statement_depth = controlled_depth;
            return result;
        }
        // The ordinary leaf path must keep the large conditional dispatcher
        // out of expression parsing's small-stack callers.
        let start = self.position;
        let path = self.begin_source_statement();
        let control_scope = matches!(self.peek_ident(), Some("while" | "do" | "for" | "switch"));
        if control_scope {
            self.push_scope();
        }
        let statement = self.parse_statement_unsited();
        let statement = if control_scope {
            let result = statement.map(|body| self.finish_compound_literal_block(body));
            self.pop_scope();
            result
        } else {
            statement
        };
        self.end_source_statement();
        let mut statement = statement?;
        let site = self
            .site_between(start, self.position)
            .with_source_path(path);
        fill_missing_sites(&mut statement, &site);
        Ok(statement)
    }

    /// Keep conditional bodies and their blocks off the native call stack.
    /// A completed block is already lowered; its parent need inspect only its
    /// own condition instead of walking every nested body again.
    #[inline(never)]
    fn parse_statement_iterative(&mut self) -> Result<CStatement, CSyntaxError> {
        enum Task {
            Parse(Option<&'static str>),
            Site(usize, Option<std::sync::Arc<[u32]>>),
            Controlled,
            ControlScope,
            Block(Vec<CStatement>, bool),
            BlockChild(Vec<CStatement>, bool),
            Then(Box<CExpression>),
            Else(Box<CExpression>, Box<CStatement>, bool),
        }
        let mut tasks = vec![Task::Parse(None)];
        let mut results: Vec<(CStatement, bool)> = Vec::new();
        while let Some(task) = tasks.pop() {
            crate::instrumentation::record_deterministic_work(1);
            match task {
                Task::Parse(controlled) => {
                    if let Some(construct) = controlled {
                        self.controlled_statement_depth += 1;
                        self.push_scope();
                        tasks.push(Task::Controlled);
                        if self.peek() != Some(&Token::LBrace) && self.is_type_start() {
                            return Err(self.error_here(format!(
                                "a declaration controlled by `{construct}` must be enclosed in braces"
                            )));
                        }
                    }
                    // A block an `if` controls is transparent: its items are
                    // the `if`'s children. Any other statement is one of its
                    // parent's, opened until its site is recorded.
                    if controlled.is_none() || self.peek() != Some(&Token::LBrace) {
                        let path = self.begin_source_statement();
                        tasks.push(Task::Site(self.position, path));
                    }
                    if matches!(
                        self.peek_ident(),
                        Some("if" | "while" | "do" | "for" | "switch")
                    ) {
                        self.push_scope();
                        tasks.push(Task::ControlScope);
                    }
                    if self.peek() == Some(&Token::LBrace) {
                        self.expect(Token::LBrace)?;
                        if self.current_function_source_name.is_some() {
                            self.function_block_depth += 1;
                        }
                        self.push_scope();
                        tasks.push(Task::Block(Vec::new(), false));
                    } else if self.peek_ident() == Some("if") {
                        self.position += 1;
                        self.expect(Token::LParen)?;
                        let condition = self.parse_expression()?;
                        self.expect(Token::RParen)?;
                        tasks.push(Task::Then(Box::new(condition)));
                        tasks.push(Task::Parse(Some("if")));
                    } else {
                        let statement = self.parse_statement_unsited()?;
                        let lowerable = self.statement_contains_lowerable_expression(&statement);
                        results.push((statement, lowerable));
                    }
                }
                Task::Site(start, path) => {
                    self.end_source_statement();
                    let (mut statement, lowerable) = results.pop().expect("parsed statement");
                    let site = self
                        .site_between(start, self.position)
                        .with_source_path(path);
                    fill_missing_sites(&mut statement, &site);
                    results.push((statement, lowerable));
                }
                Task::Controlled | Task::ControlScope => {
                    let controlled = matches!(task, Task::Controlled);
                    let (body, lowerable) = results.pop().expect("controlled statement");
                    let body = self.finish_compound_literal_block(body);
                    self.pop_scope();
                    if controlled {
                        self.controlled_statement_depth -= 1;
                    }
                    results.push((body, lowerable));
                }
                Task::Block(statements, lowerable) => {
                    if self.peek() == Some(&Token::RBrace) {
                        self.expect(Token::RBrace)?;
                        let body =
                            balanced_statement_sequence(statements).unwrap_or(CStatement::Skip);
                        let body = if lowerable {
                            self.lower_statement_calls(body)?
                        } else {
                            body
                        };
                        let body = self.finish_compound_literal_block(body);
                        self.pop_scope();
                        if self.current_function_source_name.is_some() {
                            self.function_block_depth -= 1;
                        }
                        results.push((body, false));
                    } else {
                        if self.peek().is_none() {
                            return Err(
                                self.error_here("expected statement or `}`, got end of input")
                            );
                        }
                        tasks.push(Task::BlockChild(statements, lowerable));
                        tasks.push(Task::Parse(None));
                    }
                }
                Task::BlockChild(mut statements, lowerable) => {
                    let (statement, child_lowerable) = results.pop().expect("block child");
                    statements.push(statement);
                    tasks.push(Task::Block(statements, lowerable || child_lowerable));
                }
                Task::Then(condition) => {
                    let (then_branch, lowerable) = results.pop().expect("then branch");
                    if self.peek_ident() == Some("else") {
                        self.position += 1;
                        tasks.push(Task::Else(condition, Box::new(then_branch), lowerable));
                        tasks.push(Task::Parse(Some("else")));
                    } else {
                        let lowerable =
                            lowerable || self.expression_contains_lowerable_expression(&condition);
                        results.push((
                            CStatement::If {
                                condition: *condition,
                                then_branch: Box::new(then_branch),
                                else_branch: Box::new(CStatement::Skip),
                                site: CSite::NONE,
                                operator: None,
                            },
                            lowerable,
                        ));
                    }
                }
                Task::Else(condition, then_branch, lowerable) => {
                    let (else_branch, else_lowerable) = results.pop().expect("else branch");
                    let lowerable = lowerable
                        || else_lowerable
                        || self.expression_contains_lowerable_expression(&condition);
                    results.push((
                        CStatement::If {
                            condition: *condition,
                            then_branch,
                            else_branch: Box::new(else_branch),
                            site: CSite::NONE,
                            operator: None,
                        },
                        lowerable,
                    ));
                }
            }
        }
        debug_assert_eq!(results.len(), 1);
        Ok(results.pop().expect("root statement").0)
    }

    /// The site of the statement written from token `start` up to (not
    /// including) token `end`: its first token's position, and its text from
    /// that token to its last token or to the end of that line, whichever is
    /// first. Comments and anything past the length limit are left out.
    fn site_between(&self, start: usize, end: usize) -> CSite {
        let mut site = self.site_between_without_bindings(start, end);
        if let Some(bindings) = self.loop_source_bindings.get(&start)
            && let Some(inner) = &mut site.0
        {
            std::sync::Arc::make_mut(inner).source_bindings = Some(bindings.clone());
        }
        site
    }

    fn site_between_without_bindings(&self, start: usize, end: usize) -> CSite {
        let Some(first) = self.positions.get(start) else {
            return CSite::NONE;
        };
        let Some(line) = first
            .line
            .checked_sub(1)
            .and_then(|line| self.source_lines.get(line))
        else {
            return CSite::NONE;
        };
        // A line a macro expansion rewrote is quoted as written. Its columns
        // match the parsed line up to the first rewrite; a statement that
        // starts after one is quoted as its whole written line.
        if let Some(written) = self.written_lines.get(&first.line) {
            let prefix = first.column.saturating_sub(1);
            let tail = if line.chars().take(prefix).eq(written.chars().take(prefix)) {
                written.chars().skip(prefix).collect::<String>()
            } else {
                written.to_string()
            };
            let continues = end
                .checked_sub(1)
                .and_then(|last| self.positions.get(last))
                .is_some_and(|last| last.line != first.line);
            return statement_site(first, &tail, continues);
        }
        let tail = line
            .chars()
            .skip(first.column.saturating_sub(1))
            .collect::<String>();
        let last = end
            .checked_sub(1)
            .filter(|last| *last >= start)
            .and_then(|last| Some((self.positions.get(last)?, self.tokens.get(last)?)));
        let (text, continues) = match last {
            Some((position, token)) if position.line == first.line => {
                match token_source_width(token) {
                    Some(width) => {
                        let length = (position.column + width).saturating_sub(first.column);
                        (tail.chars().take(length).collect::<String>(), false)
                    }
                    None => (tail, false),
                }
            }
            Some(_) => (tail, true),
            None => (tail, false),
        };
        statement_site(first, &text, continues)
    }

    /// Keep common straight-line statements off the large fallback dispatcher.
    /// This matters for callers that deliberately parse on a small stack.
    #[inline(never)]
    fn parse_statement_unsited(&mut self) -> Result<CStatement, CSyntaxError> {
        if !self.local_bit_fields.is_empty()
            && let Some(store) = self.parse_local_bit_field_store()?
        {
            return Ok(store);
        }
        if self.peek_ident() == Some("return") {
            return self.parse_return_statement();
        }
        if matches!(self.peek(), Some(Token::Ident(_)))
            && self.peek_next().is_some_and(Token::is_scalar_update)
        {
            let statement = self.parse_scalar_update_statement("statement")?;
            self.expect(Token::Semicolon)?;
            return Ok(statement);
        }
        self.parse_statement_slow()
    }

    fn parse_return_statement(&mut self) -> Result<CStatement, CSyntaxError> {
        self.position += 1;
        let mut expression = if self.peek() == Some(&Token::Semicolon) {
            CExpression::Void
        } else if self.current_return_struct_name.is_some() {
            self.parse_expression_allow_direct_aggregate()?
        } else {
            self.parse_expression()?
        };
        self.validate_struct_pointer_assignment(
            self.current_return_pointer_struct_name.as_ref(),
            Some(self.current_return_type),
            &mut expression,
        )?;
        self.reject_discarded_const_pointer(
            self.current_return_type,
            self.current_return_pointee_constant,
            &mut expression,
        )?;
        // Check wide-to-int representability at the return statement,
        // where the proof can discharge its bounds from call facts.
        // Deferring this conversion until function finalization leaves
        // those obligations outside the statement proof frontier.
        let expression = if self.current_return_type == InterfaceType::Int32
            && matches!(
                self.source_expression_type(&expression),
                Some(InterfaceType::Int64(_) | InterfaceType::UInt64(_))
            ) {
            CExpression::Cast {
                expression: Box::new(expression),
                interface_type: InterfaceType::Int32,
                struct_name: None,
                pointee_volatile: false,
                pointee_constant: false,
                explicit_qualification: false,
            }
        } else {
            expression
        };
        self.expect(Token::Semicolon)?;
        Ok(CStatement::Return(expression, CSite::NONE))
    }

    /// A block-scope `extern` function declaration, as the Linux
    /// `compiletime_assert` macro writes it:
    /// `__attribute__((__noreturn__)) extern void name(void) __attribute__((__error__("...")));`.
    /// The name is visible until its block ends. It declares no object and
    /// executes nothing.
    fn parse_block_scope_function_declaration(&mut self) -> Result<CStatement, CSyntaxError> {
        self.error_attribute = Some(false);
        self.pending_noreturn = None;
        let declaration = self.parse_block_scope_function_header();
        let compile_time_error = self.error_attribute.take() == Some(true);
        let noreturn_refusal = self.pending_noreturn.take();
        let mut header = declaration?;
        // Every call to a `compiletime_assert` error declaration lowers to a
        // check that fails on any path reaching it, so Click proves each call
        // unreachable and GCC's `noreturn` promise holds vacuously.
        if let Some(refusal) = noreturn_refusal
            && !compile_time_error
        {
            return Err(refusal);
        }
        header.compile_time_error = compile_time_error;
        if self.function_declarations.contains_key(&header.source_name) {
            return Err(self.error_here(format!(
                "block-scope declaration of `{}` redeclares a visible function; only a new name is supported",
                header.source_name
            )));
        }
        self.register_function_declaration(&header, false)?;
        self.block_function_declarations
            .push((self.scopes.len(), header.source_name));
        Ok(CStatement::Skip)
    }

    /// The Linux `barrier()` statement, exactly
    /// `__asm__ __volatile__("" : : : "memory");`: an empty template with
    /// no operands and a `memory` clobber. It emits no instruction, so in
    /// the sequential semantics it does nothing. What it tells the compiler
    /// about reordering, and so its meaning for concurrent readers, is
    /// outside that semantics. Every other inline assembly is rejected.
    fn parse_empty_memory_barrier(&mut self) -> Result<CStatement, CSyntaxError> {
        const ONLY: &str = "inline assembly is not supported, except the empty `__asm__ __volatile__(\"\" : : : \"memory\")` barrier";
        self.position += 1;
        if !matches!(self.peek_ident(), Some("volatile" | "__volatile__")) {
            return Err(self.error_here(ONLY));
        }
        self.position += 1;
        self.expect(Token::LParen)?;
        if self.next() != Some(Token::StringLiteral(Vec::new())) {
            return Err(self.error_at_previous(ONLY));
        }
        for _ in 0..3 {
            if self.next() != Some(Token::Colon) {
                return Err(self.error_at_previous(ONLY));
            }
        }
        if self.next() != Some(Token::StringLiteral(b"memory".to_vec())) {
            return Err(self.error_at_previous(ONLY));
        }
        if self.next() != Some(Token::RParen) {
            return Err(self.error_at_previous(ONLY));
        }
        self.expect(Token::Semicolon)?;
        Ok(CStatement::Skip)
    }

    fn parse_block_scope_function_header(&mut self) -> Result<CFunctionHeader, CSyntaxError> {
        let (prefix_inline, prefix_weak, prefix_returns_twice, prefix_opaque) =
            self.consume_function_attributes()?;
        if self.peek_ident() != Some("extern") {
            return Err(self.error_here(
                "a block-scope declaration that starts with an attribute must be an `extern` function declaration",
            ));
        }
        self.position += 1;
        if !self.is_type_start() {
            return Err(
                self.error_here("expected a function declaration after block-scope `extern`")
            );
        }
        let binding_context = (
            self.binding_function.clone(),
            self.parsing_binding_parameters,
            self.next_parameter_binding,
            self.next_local_binding,
        );
        let mut header = self.parse_function_header(false)?;
        self.pop_scope();
        (
            self.binding_function,
            self.parsing_binding_parameters,
            self.next_parameter_binding,
            self.next_local_binding,
        ) = binding_context;
        let (suffix_inline, suffix_weak, suffix_returns_twice, suffix_opaque) =
            self.consume_function_attributes()?;
        header.opaque_attributes = prefix_opaque || suffix_opaque;
        if prefix_inline
            || suffix_inline
            || prefix_weak
            || suffix_weak
            || prefix_returns_twice
            || suffix_returns_twice
            || header.variadic
        {
            return Err(self.error_here(
                "block-scope function declarations support only the declaration-only attributes and `error`",
            ));
        }
        if self.peek() != Some(&Token::Semicolon) {
            return Err(self.error_here(format!(
                "block-scope declaration of `{}` must be a body-less function prototype",
                header.source_name
            )));
        }
        self.position += 1;
        Ok(header)
    }

    fn parse_statement_slow(&mut self) -> Result<CStatement, CSyntaxError> {
        match self.peek() {
            Some(Token::LBrace) => self.parse_block_statement(),
            Some(Token::Semicolon) => {
                self.position += 1;
                Ok(CStatement::Skip)
            }
            Some(Token::Ident(name)) if name == "_Static_assert" => {
                self.parse_static_assert()?;
                Ok(CStatement::Skip)
            }
            Some(Token::Ident(name))
                if matches!(
                    name.as_str(),
                    "__builtin_types_compatible_p" | "__builtin_offsetof"
                ) =>
            {
                self.parse_primary()?;
                self.expect(Token::Semicolon)?;
                Ok(CStatement::Skip)
            }
            Some(Token::Ident(name)) if name == "extern" || name == "__attribute__" => {
                self.parse_block_scope_function_declaration()
            }
            Some(Token::Ident(name)) if name == "asm" || name == "__asm__" => {
                self.parse_empty_memory_barrier()
            }
            // Discarding a direct call's result is an ordinary C expression
            // statement. Preserve the call while omitting its unused value.
            Some(Token::LParen)
                if self.peek_next() == Some(&Token::Ident("void".to_string()))
                    && self.tokens.get(self.position + 2) == Some(&Token::RParen)
                    && matches!(self.peek_n(3), Some(Token::Ident(_)))
                    && self.peek_n(4) == Some(&Token::LParen) =>
            {
                self.position += 3;
                let function_name = self.expect_ident("function name after `(void)`")?;
                let arguments = self.parse_call_arguments(Some(&function_name))?;
                self.expect(Token::Semicolon)?;
                Ok(CStatement::Call {
                    function_name: self.resolve_function_name(&function_name),
                    arguments,
                    site: CSite::NONE,
                    callee: None,
                })
            }
            Some(Token::LParen)
                if self.peek_n(1) == Some(&Token::LBrace)
                    || (self.peek_next() == Some(&Token::Ident("void".to_string()))
                        && self.tokens.get(self.position + 2) == Some(&Token::RParen)) =>
            {
                self.parse_discarded_expression_statement()
            }
            // A parenthesized lvalue designates the object it encloses
            // (C11 6.5.1p5), so `(*p)++;` updates `*p`.
            Some(Token::LParen)
                if !self.is_type_start_at(1) && self.peek_n(1) != Some(&Token::LBrace) =>
            {
                let statement = if self.parenthesized_identifier_at(0)
                    && self.peek_n(3).is_some_and(Token::is_scalar_update)
                {
                    self.parse_scalar_update_statement("statement")?
                } else {
                    self.parse_memory_lvalue_statement("statement", None)?
                };
                self.expect(Token::Semicolon)?;
                Ok(statement)
            }
            Some(Token::Star) => {
                let statement = self.parse_memory_lvalue_statement("statement", None)?;
                self.expect(Token::Semicolon)?;
                Ok(statement)
            }
            Some(Token::Ident(_)) if self.peek_next() == Some(&Token::LBracket) => {
                let statement = self.parse_memory_lvalue_statement("statement", None)?;
                self.expect(Token::Semicolon)?;
                Ok(statement)
            }
            Some(Token::Ident(_)) if self.peek_next() == Some(&Token::Arrow) => {
                let start = self.position;
                if let Ok(CExpression::IndirectCall {
                    function,
                    signature,
                    arguments,
                    position,
                }) = self.parse_expression()
                    && self.peek() == Some(&Token::Semicolon)
                {
                    self.position += 1;
                    return Ok(CStatement::IndirectCall {
                        function: *function,
                        signature,
                        arguments,
                        position,
                        site: CSite::NONE,
                    });
                }
                self.position = start;
                let statement = self.parse_memory_lvalue_statement("statement", None)?;
                self.expect(Token::Semicolon)?;
                Ok(statement)
            }
            Some(Token::Ident(_)) if self.peek_next() == Some(&Token::Dot) => {
                let statement = self.parse_memory_lvalue_statement("statement", None)?;
                self.expect(Token::Semicolon)?;
                Ok(statement)
            }
            Some(Token::Ident(_)) if self.peek_ident() == Some("static") => {
                self.parse_static_local_declaration()
            }
            Some(Token::PlusPlus | Token::MinusMinus) => {
                let statement = if self.prefix_starts_memory_lvalue() {
                    let prefix = self.next();
                    self.parse_memory_lvalue_statement("statement", prefix)?
                } else {
                    self.parse_scalar_update_statement("statement")?
                };
                self.expect(Token::Semicolon)?;
                Ok(statement)
            }
            Some(Token::Ident(_)) if self.peek_next() == Some(&Token::Colon) => {
                let position = self.here();
                let name = self.expect_ident("label")?;
                self.expect(Token::Colon)?;
                let direct_function_body =
                    self.function_block_depth == 1 && self.controlled_statement_depth == 0;
                self.controlled_statement_depth += 1;
                self.source_label_body = true;
                let statement = self.parse_statement();
                self.source_label_body = false;
                self.controlled_statement_depth -= 1;
                Ok(CStatement::Label {
                    name,
                    statement: Box::new(statement?),
                    position,
                    direct_function_body,
                })
            }
            Some(Token::Ident(_)) if self.is_type_start() => self.parse_local_declaration(),
            Some(Token::Ident(_)) => match self.peek_ident() {
                Some("return") => self.parse_return_statement(),
                Some("break") => self.parse_loop_control_statement(false),
                Some("continue") => self.parse_loop_control_statement(true),
                Some("goto") => {
                    if self.function_has_bit_fields {
                        return Err(self.error_here(
                            "bit-field objects and goto in one function are not supported",
                        ));
                    }
                    if self.function_has_compound_literals {
                        return Err(self.error_here(
                            "compound literals and goto in one function are not supported",
                        ));
                    }
                    self.function_has_goto = true;
                    let position = self.here();
                    self.position += 1;
                    let target = self.expect_ident("goto target")?;
                    self.expect(Token::Semicolon)?;
                    Ok(CStatement::Goto {
                        target,
                        position,
                        direct_function_body: self.function_block_depth == 1
                            && self.controlled_statement_depth == 0,
                    })
                }
                Some("if") => {
                    self.position += 1;
                    self.expect(Token::LParen)?;
                    let condition = self.parse_expression()?;
                    self.expect(Token::RParen)?;
                    let then_branch = Box::new(self.parse_controlled_statement("if")?);
                    let else_branch = if self.peek_ident() == Some("else") {
                        self.position += 1;
                        Box::new(self.parse_controlled_statement("else")?)
                    } else {
                        Box::new(CStatement::Skip)
                    };
                    Ok(CStatement::If {
                        condition,
                        then_branch,
                        else_branch,
                        site: CSite::NONE,
                        operator: None,
                    })
                }
                Some("while") => {
                    self.loop_source_bindings.insert(
                        self.position,
                        std::sync::Arc::new(self.visible_bindings.clone()),
                    );
                    self.position += 1;
                    self.expect(Token::LParen)?;
                    let previous_repeatable_scope = self
                        .repeatable_compound_literal_scope
                        .replace(self.scopes.len());
                    let condition = self.parse_expression()?;
                    self.repeatable_compound_literal_scope = previous_repeatable_scope;
                    self.expect(Token::RParen)?;
                    self.loop_contexts.push(CLoopContext::While);
                    let body = Box::new(self.parse_controlled_statement("while")?);
                    self.loop_contexts.pop();
                    Ok(CStatement::While {
                        test: None,
                        condition,
                        body,
                        site: CSite::NONE,
                    })
                }
                Some("switch") => {
                    self.position += 1;
                    self.expect(Token::LParen)?;
                    let expression = self.parse_expression()?;
                    self.expect(Token::RParen)?;
                    self.loop_contexts.push(CLoopContext::Switch);
                    let cases = self.parse_switch_body()?;
                    self.loop_contexts.pop();
                    Ok(CStatement::Switch {
                        expression,
                        cases,
                        site: CSite::NONE,
                    })
                }
                Some("do") => {
                    self.loop_source_bindings.insert(
                        self.position,
                        std::sync::Arc::new(self.visible_bindings.clone()),
                    );
                    self.position += 1;
                    self.loop_contexts.push(CLoopContext::DoWhile);
                    let body = self.parse_controlled_statement("do")?;
                    self.loop_contexts.pop();
                    if self.peek_ident() != Some("while") {
                        return Err(self.error_here("expected `while` after `do` body"));
                    }
                    self.position += 1;
                    self.expect(Token::LParen)?;
                    let previous_repeatable_scope = self
                        .repeatable_compound_literal_scope
                        .replace(self.scopes.len());
                    let condition = self.parse_expression()?;
                    self.repeatable_compound_literal_scope = previous_repeatable_scope;
                    self.expect(Token::RParen)?;
                    self.expect(Token::Semicolon)?;
                    Ok(CStatement::DoWhile {
                        test: None,
                        condition,
                        body: Box::new(body),
                        site: CSite::NONE,
                    })
                }
                Some("for") => {
                    let loop_start = self.position;
                    self.position += 1;
                    self.expect(Token::LParen)?;
                    // A `for` declaration is scoped to the statement, so two
                    // consecutive loops may each declare `int32 i`.
                    self.push_scope();
                    let init = self.parse_for_initializer()?;
                    self.loop_source_bindings.insert(
                        loop_start,
                        std::sync::Arc::new(self.visible_bindings.clone()),
                    );
                    self.expect(Token::Semicolon)?;
                    let previous_repeatable_scope = self
                        .repeatable_compound_literal_scope
                        .replace(self.scopes.len());
                    let condition = if self.peek() == Some(&Token::Semicolon) {
                        CExpression::Int32Literal(1)
                    } else {
                        self.parse_expression()?
                    };
                    self.expect(Token::Semicolon)?;
                    let step = self.parse_for_step()?;
                    self.repeatable_compound_literal_scope = previous_repeatable_scope;
                    self.expect(Token::RParen)?;
                    self.loop_contexts.push(CLoopContext::For);
                    let body = self.parse_controlled_statement("for")?;
                    self.loop_contexts.pop();
                    let declarations = std::mem::take(
                        self.compound_literal_declarations
                            .last_mut()
                            .expect("for scope"),
                    );
                    let init = prepend_statements(declarations, init);
                    self.pop_for_scope();
                    Ok(CStatement::For {
                        test: None,
                        initializer: Box::new(init),
                        condition,
                        step: Box::new(step),
                        body: Box::new(body),
                        site: CSite::NONE,
                    })
                }
                Some(other) => {
                    if other == "free" && self.peek_next() == Some(&Token::LParen) {
                        self.position += 1;
                        let arguments = self.parse_call_arguments(Some("free"))?;
                        self.expect(Token::Semicolon)?;
                        let [pointer] = arguments.as_slice() else {
                            return Err(self.error_here(format!(
                                "`free` expects one pointer argument, got {}",
                                arguments.len()
                            )));
                        };
                        Ok(CStatement::HeapFree {
                            pointer: pointer.clone(),
                            site: CSite::NONE,
                        })
                    } else if self.peek_next() == Some(&Token::LParen) {
                        let source_name = self.expect_ident("function name")?;
                        if matches!(source_name.as_str(), "malloc" | "calloc" | "realloc") {
                            return Err(
                                self.error_here("the allocation result may not be discarded")
                            );
                        }
                        // As in an expression: a GNU builtin such as
                        // `__builtin_unreachable` is not an ordinary call.
                        if source_name.starts_with("__builtin_") {
                            return Err(self.error_at_previous(format!(
                                "unsupported GNU builtin `{source_name}`"
                            )));
                        }
                        let compile_time_error = self
                            .function_declarations
                            .get(&source_name)
                            .is_some_and(|header| header.compile_time_error)
                            && !self
                                .variable_types
                                .contains_key(&self.resolve_name(&source_name));
                        self.statement_call = true;
                        let arguments = self.parse_call_arguments(Some(&source_name));
                        self.statement_call = false;
                        let arguments = arguments?;
                        self.expect(Token::Semicolon)?;
                        if compile_time_error {
                            // The compiler accepts the program only if it
                            // removes this call, so it must be unreachable:
                            // the check fails on any path that gets here.
                            return Ok(CStatement::Assert {
                                condition: CExpression::Int32Literal(0),
                                label: format!(
                                    "call to `{source_name}`, declared with the GNU `error` attribute, is unreachable"
                                ),
                                site: CSite::NONE,
                            });
                        }
                        if let Some(statement) =
                            self.parse_kernel_primitive_statement(&source_name, &arguments)?
                        {
                            return Ok(statement);
                        }
                        Ok(CStatement::Call {
                            function_name: self.call_target(&source_name),
                            arguments,
                            site: CSite::NONE,
                            callee: None,
                        })
                    } else {
                        Err(self
                            .error_here(format!("expected statement, got identifier `{other}`")))
                    }
                }
                None => unreachable!("identifier token should have identifier form"),
            },
            Some(token) => {
                Err(self.error_here(format!("expected statement, got {}", token.describe())))
            }
            None => Err(self.error_here("expected statement, got end of input")),
        }
    }

    fn parse_local_declaration(&mut self) -> Result<CStatement, CSyntaxError> {
        let parsed_type = self.parse_type()?;
        if parsed_type
            .struct_name
            .as_ref()
            .is_some_and(|tag| self.bit_field_records.contains_key(tag))
        {
            return self.parse_local_bit_field_record(&parsed_type);
        }
        if parsed_type.union_name.is_some() {
            return Err(self.error_here(
                    "tagged union locals are not supported; access an active scalar member through a struct pointer",
                ));
        }
        if parsed_type.interface_type == InterfaceType::Void {
            return Err(self.error_here("void local declarations are not supported"));
        }
        self.validate_volatile_type(&parsed_type)?;
        if self.starts_local_row_pointer_declarator() {
            return self.parse_local_row_pointer(&parsed_type);
        }
        if parsed_type.is_volatile && self.peek() == Some(&Token::LParen) {
            return Err(self.error_here(
                "the small volatile model does not support volatile function-pointer objects",
            ));
        }
        if self.peek() == Some(&Token::LParen) {
            if parsed_type.is_constant {
                return Err(self.error_here(
                    "const-qualified function-pointer declarations are not supported in this slice",
                ));
            }
            let Some((name, interface_type, signature)) =
                self.parse_function_pointer_declarator(parsed_type)?
            else {
                unreachable!("function-pointer declarator starts with a parenthesis");
            };
            let kernel_name = self.declare_name(&name)?;
            self.variable_types
                .insert(kernel_name.clone(), interface_type);
            self.variable_function_pointers
                .insert(kernel_name.clone(), signature.clone());
            let declaration = CStatement::Declare {
                interface_type,
                name: kernel_name.clone().into(),
                volatile: false,
                pointee_volatile: false,
                constant: false,
                pointee_constant: false,
                initializer: None,
                zero_fill: None,
                declared_class: None,
                site: CSite::NONE,
            };
            let statement = if self.peek() == Some(&Token::Equal) {
                self.position += 1;
                let expression = self.parse_expression()?;
                self.validate_function_pointer_value(&signature, &expression)?;
                CStatement::Seq(
                    Box::new(declaration),
                    Box::new(CStatement::Assign {
                        name: kernel_name,
                        expression,
                        site: CSite::NONE,
                        prior_result: None,
                    }),
                )
            } else {
                declaration
            };
            self.expect(Token::Semicolon)?;
            return Ok(statement);
        }

        let struct_value_candidate = is_plain_struct_type(&parsed_type);
        if struct_value_candidate && parsed_type.is_constant {
            return Err(
                self.error_here("const-qualified struct locals are not supported in this slice")
            );
        }
        let mut declarations = Vec::new();
        let mut first_declarator = true;
        loop {
            // C writes each declarator's pointer `*` with the declarator, not
            // with the type specifier, so `struct rb_node *parent, *gparent;`
            // repeats the star the type specifier already carries. Accept a
            // repetition of exactly that depth, which gives every declarator
            // the type the first one has, and refuse any other depth by name
            // rather than typing a later declarator from the first one's.
            if !first_declarator {
                let mut declarator_depth: u8 = 0;
                while self.peek() == Some(&Token::Star) {
                    declarator_depth = declarator_depth.saturating_add(1);
                    self.position += 1;
                }
                if declarator_depth != parsed_type.pointer_depth {
                    return Err(self.error_here(format!(
                        "a declarator with {declarator_depth} pointer `*` in a declaration whose type specifier writes {}; declare it separately",
                        parsed_type.pointer_depth
                    )));
                }
            }
            first_declarator = false;
            let source_name = self.expect_ident("local name")?;
            let name = self.declare_name(&source_name)?;
            let struct_value_layout =
                if struct_value_candidate && self.peek() != Some(&Token::LBracket) {
                    let struct_name = parsed_type
                        .struct_name
                        .as_deref()
                        .expect("plain struct local carries its name");
                    // An uninitialized object needs storage, not a typed copy.
                    // Keep copy/initializer validation at the operations that
                    // actually read or construct aggregate values.
                    Some(if self.peek() == Some(&Token::Equal) {
                        self.scalar_struct_value_layout(struct_name)?
                    } else {
                        self.structs.get(struct_name).cloned().ok_or_else(|| {
                            self.error_here(format!("unknown struct declaration `{struct_name}`"))
                        })?
                    })
                } else {
                    None
                };
            if let Some(layout) = &struct_value_layout {
                let interface_type = record_value_type(layout);
                let struct_name = parsed_type
                    .struct_name
                    .clone()
                    .expect("plain struct local carries its name");
                self.variable_types.insert(name.clone(), interface_type);
                self.variable_structs
                    .insert(name.clone(), struct_name.clone());
                self.variable_struct_values
                    .insert(name.clone(), struct_name.clone());
                self.local_struct_values
                    .entry(name.clone())
                    .and_modify(|existing| {
                        if existing.as_deref() != Some(struct_name.as_str()) {
                            *existing = None;
                        }
                    })
                    .or_insert_with(|| Some(struct_name.clone()));
                let declaration = CStatement::DeclareStructValue {
                    name: name.clone().into(),
                    layout: layout.clone(),
                    site: CSite::NONE,
                };
                let statement = if self.peek() == Some(&Token::Equal) {
                    self.position += 1;
                    if self.peek() == Some(&Token::LBrace) {
                        let initializer =
                            self.parse_struct_value_initializer(&name, &struct_name)?;
                        CStatement::Seq(Box::new(declaration), Box::new(initializer))
                    } else if matches!(self.peek(), Some(Token::Ident(_)))
                        && !matches!(
                            self.peek_ident(),
                            Some("sizeof" | "__builtin_types_compatible_p" | "__builtin_offsetof")
                        )
                        && self.peek_next() == Some(&Token::LParen)
                    {
                        let source_name = self.expect_ident("function name")?;
                        let arguments = self.parse_call_arguments(Some(&source_name))?;
                        let call = self.call_assignment_statement(
                            name.clone(),
                            self.call_target(&source_name),
                            arguments,
                        )?;
                        CStatement::Seq(Box::new(declaration), Box::new(call))
                    } else {
                        let expression = self.parse_expression_allow_direct_aggregate()?;
                        let copy = self.struct_value_copy_statement(&name, expression)?;
                        CStatement::Seq(Box::new(declaration), Box::new(copy))
                    }
                } else {
                    declaration
                };
                declarations.push(statement);
                if self.peek() != Some(&Token::Comma) {
                    break;
                }
                self.position += 1;
                continue;
            }
            let (mut interface_type, mut array_shape, incomplete_array) =
                self.parse_local_array_shape(&parsed_type)?;
            if incomplete_array && !supports_local_array_initializer(interface_type) {
                return Err(self.error_here(
                    "inferred local array element type does not support automatic initialization",
                ));
            }

            if parsed_type.is_volatile
                && (array_shape.is_some()
                    || matches!(
                        interface_type,
                        InterfaceType::Int8Array(_)
                            | InterfaceType::Int16Array(_)
                            | InterfaceType::CharArray(_, _)
                            | InterfaceType::UInt8Array(_)
                            | InterfaceType::UInt16Array(_)
                            | InterfaceType::UInt32Array(_)
                            | InterfaceType::Int128Array(_)
                            | InterfaceType::Int64Array(_, _)
                            | InterfaceType::UInt128Array(_)
                            | InterfaceType::UInt64Array(_, _)
                            | InterfaceType::Int32Array(_)
                    ))
            {
                return Err(
                    self.error_here("the small volatile model does not support volatile arrays")
                );
            }
            if parsed_type.struct_name.is_some()
                && parsed_type.interface_type == InterfaceType::Int32Pointer
                && array_shape.is_none()
                && self
                    .structs
                    .get(
                        parsed_type
                            .struct_name
                            .as_ref()
                            .expect("struct pointer has a struct name"),
                    )
                    .is_some_and(|layout| !layout.size_bytes.is_multiple_of(4))
            {
                // Unaligned struct sizes cannot use the kernel's int32
                // pointer allocation width. Use a byte-addressed local for
                // those allocations; aligned structs retain the historical
                // pointer representation.
                interface_type = InterfaceType::UInt8Pointer;
            }
            self.variable_types.insert(name.clone(), interface_type);
            let pointer = interface_type.is_pointer() && array_shape.is_none();
            self.local_pointers
                .entry(name.clone())
                .and_modify(|existing| *existing &= pointer)
                .or_insert(pointer);
            if let Some(signature) = &parsed_type.function_pointer_signature {
                self.variable_function_pointers
                    .insert(name.clone(), signature.clone());
            }
            let object_volatile = parsed_type.object_is_volatile();
            let pointee_volatile = parsed_type.pointee_is_volatile();
            let object_constant = parsed_type.is_constant;
            let pointee_constant = parsed_type.pointee_constant;
            if object_constant {
                self.variable_constants.insert(name.clone());
            }
            if pointee_constant {
                self.variable_pointee_constants.insert(name.clone());
            }
            if let Some(shape) = array_shape.clone() {
                self.variable_array_shapes.insert(name.clone(), shape);
            }
            if parsed_type.struct_name.is_some() {
                if is_plain_struct_type(&parsed_type)
                    && interface_type == parsed_type.interface_type
                {
                    return Err(self.error_here("only pointer-to-struct types are supported"));
                }
                if interface_type != parsed_type.interface_type
                    && !matches!(
                        interface_type,
                        InterfaceType::UInt8Array(_)
                            | InterfaceType::UInt8Pointer
                            | InterfaceType::PointerArray(_, _, _)
                    )
                {
                    return Err(self.error_here("local arrays of struct type are not supported"));
                }
                let struct_name = parsed_type
                    .struct_name
                    .clone()
                    .expect("struct_name checked above");
                self.variable_structs
                    .insert(name.clone(), struct_name.clone());
                // A sidecar spells a local by its source name, so index this
                // declaration under that spelling. Two declarations of one
                // spelling with different struct types leave no layout.
                if array_shape.is_none()
                    && matches!(
                        interface_type,
                        InterfaceType::Int32Pointer | InterfaceType::UInt8Pointer
                    )
                {
                    self.local_struct_pointers
                        .entry(name.clone())
                        .and_modify(|existing| {
                            if existing.as_deref() != Some(struct_name.as_str()) {
                                *existing = None;
                            }
                        })
                        .or_insert_with(|| Some(struct_name.clone()));
                }
            }
            let mut inferred_initializer = None;
            if incomplete_array {
                if self.peek() != Some(&Token::Equal) || self.peek_next() != Some(&Token::LBrace) {
                    return Err(
                        self.error_here("inferred local arrays require a brace initializer")
                    );
                }
                self.position += 1;
                self.incomplete_array_names.insert(name.clone());
                let mut shape = array_shape
                    .take()
                    .expect("incomplete array retains its shape");
                let mut written = Vec::new();
                let mut next = 0;
                shape[0] = self.parse_array_initializer_elements(
                    name.source_name(),
                    None,
                    &shape[1..],
                    &mut written,
                    &mut next,
                )?;
                if shape[0] == 0 {
                    return Err(
                        self.error_here("inferred local arrays require a non-empty initializer")
                    );
                }
                let length = array_shape_element_count(&shape)
                    .filter(|length| {
                        length
                            .checked_mul(parsed_type.interface_type.abi_size_bytes())
                            .is_some()
                    })
                    .ok_or_else(|| {
                        self.error_here("inferred local array dimensions are too large")
                    })?;
                interface_type = array_type_for_element(parsed_type.interface_type, length)
                    .expect("validated inferred array element type");
                self.variable_types.insert(name.clone(), interface_type);
                self.incomplete_array_names.remove(&name);
                if shape.len() > 1 {
                    self.variable_array_shapes
                        .insert(name.clone(), shape.clone());
                    array_shape = Some(shape);
                } else {
                    self.variable_array_shapes.remove(&name);
                }
                inferred_initializer = Some((length, written));
            }
            let declaration = CStatement::Declare {
                interface_type,
                name: name.clone().into(),
                volatile: object_volatile,
                pointee_volatile,
                constant: object_constant,
                pointee_constant,
                initializer: None,
                zero_fill: None,
                declared_class: self
                    .local_declared_class(interface_type, parsed_type.struct_name.as_deref()),
                site: CSite::NONE,
            };
            let statement = if inferred_initializer.is_some() || self.peek() == Some(&Token::Equal)
            {
                if inferred_initializer.is_none() {
                    self.position += 1;
                }
                if supports_local_array_initializer(interface_type) {
                    if object_constant
                        && (!is_arithmetic_type(parsed_type.interface_type)
                            || is_plain_struct_type(&parsed_type)
                            || parsed_type.union_name.is_some()
                            || parsed_type.long_double
                            || object_volatile
                            || pointee_volatile)
                    {
                        return Err(self.error_here(
                            "const automatic array initialization requires non-volatile arithmetic elements",
                        ));
                    }
                    // A volatile object keeps one access per element.
                    let compact = !object_volatile && !pointee_volatile;
                    let (zero_fill, initializer) =
                        if let Some((length, written)) = inferred_initializer {
                            self.finish_local_array_declaration(
                                &name,
                                parsed_type.interface_type,
                                length,
                                written,
                                compact,
                                object_constant,
                            )?
                        } else if is_plain_struct_type(&parsed_type) {
                            let struct_name = parsed_type.struct_name.as_deref().unwrap();
                            let dimensions = array_shape.as_deref().expect(
                                "local struct array initializers retain their declared dimensions",
                            );
                            self.parse_local_struct_array_initializer(
                                &name,
                                struct_name,
                                dimensions,
                                compact,
                            )?
                        } else {
                            self.parse_local_array_initializer(
                                &name,
                                interface_type,
                                array_shape.as_deref(),
                                compact,
                                object_constant,
                            )?
                        };
                    let declaration = match declaration {
                        CStatement::Declare {
                            interface_type,
                            name,
                            volatile,
                            pointee_volatile,
                            constant,
                            pointee_constant,
                            zero_fill: None,
                            declared_class,
                            ..
                        } => CStatement::Declare {
                            interface_type,
                            name,
                            volatile,
                            pointee_volatile,
                            constant,
                            pointee_constant,
                            initializer: None,
                            zero_fill,
                            declared_class,
                            site: CSite::NONE,
                        },
                        _ => unreachable!("an array declaration is a plain declaration"),
                    };
                    if object_constant {
                        declaration
                    } else {
                        CStatement::Seq(Box::new(declaration), Box::new(initializer))
                    }
                } else if !object_constant
                    && matches!(self.peek(), Some(Token::Ident(_)))
                    && !matches!(
                        self.peek_ident(),
                        Some("sizeof" | "__builtin_types_compatible_p" | "__builtin_offsetof")
                    )
                    && self.peek_next() == Some(&Token::LParen)
                {
                    let call_start = self.position;
                    let source_name = self.expect_ident("function name")?;
                    let arguments = self.parse_call_arguments(Some(&source_name))?;
                    let is_kernel_primitive = self
                        .parse_kernel_primitive_expression(
                            &source_name,
                            &arguments,
                            self.positions.get(call_start).cloned(),
                        )?
                        .is_some();
                    if !is_kernel_primitive
                        && matches!(self.peek(), Some(Token::Comma | Token::Semicolon))
                    {
                        let call = self.call_assignment_statement(
                            name.clone(),
                            self.call_target(&source_name),
                            arguments,
                        )?;
                        CStatement::Seq(Box::new(declaration), Box::new(call))
                    } else {
                        self.position = call_start;
                        let mut expression = self.parse_expression()?;
                        if let Some(signature) = self.variable_function_pointers.get(&name) {
                            self.validate_function_pointer_value(signature, &expression)?;
                        }
                        self.validate_struct_pointer_assignment(
                            self.variable_structs.get(&name),
                            Some(interface_type),
                            &mut expression,
                        )?;
                        self.reject_discarded_const_pointer(
                            interface_type,
                            pointee_constant,
                            &mut expression,
                        )?;
                        CStatement::Seq(
                            Box::new(declaration),
                            Box::new(CStatement::Assign {
                                name,
                                expression,
                                site: CSite::NONE,
                                prior_result: None,
                            }),
                        )
                    }
                } else {
                    let mut expression = self.parse_expression()?;
                    if let Some(signature) = self.variable_function_pointers.get(&name) {
                        self.validate_function_pointer_value(signature, &expression)?;
                    }
                    self.validate_struct_pointer_assignment(
                        self.variable_structs.get(&name),
                        Some(interface_type),
                        &mut expression,
                    )?;
                    self.reject_discarded_const_pointer(
                        interface_type,
                        pointee_constant,
                        &mut expression,
                    )?;
                    if object_constant {
                        let mut declaration = declaration;
                        if let CStatement::Declare { initializer, .. } = &mut declaration {
                            *initializer = Some(expression);
                        }
                        declaration
                    } else {
                        CStatement::Seq(
                            Box::new(declaration),
                            Box::new(CStatement::Assign {
                                name,
                                expression,
                                site: CSite::NONE,
                                prior_result: None,
                            }),
                        )
                    }
                }
            } else {
                if object_constant {
                    return Err(self.error_here("const automatic scalars require an initializer"));
                }
                declaration
            };
            declarations.push(statement);
            if self.peek() != Some(&Token::Comma) {
                break;
            }
            self.position += 1;
        }
        self.expect(Token::Semicolon)?;
        Ok(balanced_statement_sequence(declarations).unwrap_or(CStatement::Skip))
    }

    fn parse_static_local_declaration(&mut self) -> Result<CStatement, CSyntaxError> {
        self.expect_ident_spelling("static")?;
        let parsed_type = self.parse_type()?;
        if parsed_type.function_pointer_signature.is_some() {
            return Err(self.error_here("static function-pointer objects are not supported"));
        }
        self.validate_volatile_type(&parsed_type)?;
        let aggregate_struct = if is_plain_struct_type(&parsed_type) {
            if parsed_type.is_volatile {
                return Err(self.error_here(
                    "the small volatile model does not support volatile aggregate statics",
                ));
            }
            let struct_name = parsed_type
                .struct_name
                .clone()
                .expect("plain static aggregate carries a struct name");
            let layout = self.scalar_struct_value_layout(&struct_name)?;
            Some((struct_name, layout))
        } else {
            if parsed_type.struct_name.is_some()
                || parsed_type.enum_name.is_some()
                || parsed_type.union_name.is_some()
                || !parsed_type.interface_type.is_supported_static_scalar()
            {
                return Err(self.error_here(
                    "function-local `static` declarations currently support scalar integer, floating-point, or supported structs",
                ));
            }
            None
        };

        loop {
            let source_name = self.expect_ident("static local name")?;
            let kernel_name = self.declare_static_name(&source_name)?;
            if let Some((struct_name, layout)) = &aggregate_struct {
                if self.peek() == Some(&Token::LBracket) {
                    let shape = self
                        .parse_global_array_length(&source_name)?
                        .expect("static aggregate array suffix");
                    let bound = match shape {
                        GlobalArrayLength::Complete(shape) if shape.len() == 1 => Some(shape[0]),
                        GlobalArrayLength::Incomplete(shape) if shape.is_empty() => None,
                        _ => {
                            return Err(self.error_here(
                                "multidimensional static aggregate arrays are not supported yet",
                            ));
                        }
                    };
                    let (length, initializer) = if self.peek() == Some(&Token::Equal) {
                        self.position += 1;
                        self.parse_aggregate_array_initializer_with_bound(
                            &source_name,
                            struct_name,
                            layout,
                            bound,
                        )?
                    } else {
                        (
                            bound.ok_or_else(|| {
                                self.error_here("inferred static array requires an initializer")
                            })?,
                            Vec::new(),
                        )
                    };
                    let bytes = length
                        .checked_mul(layout.size_bytes())
                        .ok_or_else(|| self.error_here("static aggregate array size overflows"))?;
                    self.variable_types
                        .insert(kernel_name.clone(), InterfaceType::UInt8Array(bytes));
                    self.variable_array_shapes
                        .insert(kernel_name.clone(), vec![length]);
                    self.variable_structs
                        .insert(kernel_name.clone(), struct_name.clone());
                    if parsed_type.is_constant {
                        self.variable_constants.insert(kernel_name.clone());
                    }
                    self.static_aggregate_arrays.insert(
                        kernel_name.clone(),
                        CStaticAggregateArray::new(
                            source_name,
                            kernel_name,
                            struct_name.clone(),
                            layout.clone(),
                            length,
                            initializer,
                        )
                        .with_constant(parsed_type.is_constant),
                    );
                    if self.peek() != Some(&Token::Comma) {
                        break;
                    }
                    self.position += 1;
                    continue;
                }
                let initializer = if self.peek() == Some(&Token::Equal) {
                    self.position += 1;
                    self.parse_aggregate_initializer(&source_name, struct_name)?
                } else {
                    Vec::new()
                };
                self.variable_types
                    .insert(kernel_name.clone(), record_value_type(layout));
                self.variable_structs
                    .insert(kernel_name.clone(), struct_name.clone());
                if parsed_type.is_constant {
                    self.variable_constants.insert(kernel_name.clone());
                }
                self.static_aggregates.insert(
                    kernel_name.clone(),
                    CStaticAggregate::new(
                        source_name,
                        kernel_name,
                        struct_name.clone(),
                        layout.clone(),
                        initializer,
                    )
                    .with_constant(parsed_type.is_constant),
                );
                if self.peek() != Some(&Token::Comma) {
                    break;
                }
                self.position += 1;
                continue;
            }
            if self.peek() == Some(&Token::LBracket) {
                if parsed_type.is_volatile {
                    return Err(
                        self.error_here("volatile static local arrays are not supported yet")
                    );
                }
                if array_type_for_element(parsed_type.interface_type, 1).is_none() {
                    return Err(self.error_here(
                        "static array element type requires a modeled array pointer type",
                    ));
                }
                let dimensions = self
                    .parse_global_array_length(&source_name)?
                    .expect("static scalar array suffix");
                let (shape, initializer) = match dimensions {
                    GlobalArrayLength::Complete(shape) => {
                        let length = shape
                            .iter()
                            .try_fold(1u32, |n, d| n.checked_mul(*d))
                            .ok_or_else(|| self.error_here("static array size overflows"))?;
                        let initializer = if self.peek() == Some(&Token::Equal) {
                            self.position += 1;
                            if shape.len() == 1 {
                                self.parse_static_array_initializer(
                                    &source_name,
                                    parsed_type.interface_type,
                                    parsed_type.pointee_constant,
                                    length,
                                )?
                            } else {
                                self.parse_global_array_initializer(
                                    &source_name,
                                    parsed_type.interface_type,
                                    &shape,
                                )?
                            }
                        } else {
                            CArrayInitializer::zeroed(length, parsed_type.interface_type)
                        };
                        (shape, initializer)
                    }
                    GlobalArrayLength::Incomplete(inner) => {
                        if self.peek() != Some(&Token::Equal) {
                            return Err(
                                self.error_here("inferred static array requires an initializer")
                            );
                        }
                        self.position += 1;
                        if inner.is_empty() {
                            let initializer = self.parse_inferred_global_array_initializer(
                                &source_name,
                                parsed_type.interface_type,
                                parsed_type.pointee_constant,
                            )?;
                            let length = Some(initializer.length())
                                .filter(|length| *length > 0)
                                .ok_or_else(|| self.error_here("inferred static array requires a non-empty bounded initializer"))?;
                            (vec![length], initializer)
                        } else {
                            self.parse_inferred_multidimensional_global_array_initializer(
                                &source_name,
                                parsed_type.interface_type,
                                &inner,
                            )?
                        }
                    }
                };
                let length = shape
                    .iter()
                    .try_fold(1u32, |n, d| n.checked_mul(*d))
                    .ok_or_else(|| self.error_here("static array size overflows"))?;
                self.variable_array_shapes
                    .insert(kernel_name.clone(), shape.clone());
                self.variable_types.insert(
                    kernel_name.clone(),
                    array_type_for_element(parsed_type.interface_type, length)
                        .expect("validated static array element type"),
                );
                if parsed_type.is_constant {
                    self.variable_constants.insert(kernel_name.clone());
                }
                self.static_arrays.insert(
                    kernel_name.clone(),
                    CStaticArray::new(
                        source_name,
                        kernel_name.clone(),
                        parsed_type.interface_type,
                        length,
                        initializer,
                    )
                    .with_shape(shape)
                    .with_constant(parsed_type.is_constant)
                    .with_pointee_constant(parsed_type.pointee_constant),
                );
            } else {
                self.variable_types
                    .insert(kernel_name.clone(), parsed_type.interface_type);
                if parsed_type.is_constant {
                    self.variable_constants.insert(kernel_name.clone());
                }
                if parsed_type.pointee_constant {
                    self.variable_pointee_constants.insert(kernel_name.clone());
                }
                let initializer = if self.peek() == Some(&Token::Equal) {
                    self.position += 1;
                    let initializer = self.parse_expression()?;
                    normalize_static_initializer(
                        self,
                        parsed_type.interface_type,
                        parsed_type.pointee_constant,
                        &initializer,
                        "static local",
                        true,
                    )?
                } else {
                    zero_initializer(parsed_type.interface_type)
                };
                self.static_locals.insert(
                    kernel_name.clone(),
                    CStaticLocal::new(
                        source_name,
                        kernel_name,
                        parsed_type.interface_type,
                        initializer,
                    )
                    .with_volatile(parsed_type.object_is_volatile())
                    .with_pointee_volatile(parsed_type.pointee_is_volatile())
                    .with_constant(parsed_type.is_constant)
                    .with_pointee_constant(parsed_type.pointee_constant),
                );
            }
            if self.peek() != Some(&Token::Comma) {
                break;
            }
            self.position += 1;
        }
        self.expect(Token::Semicolon)?;

        // Static storage is materialized at function entry. Keeping a no-op in
        // the statement tree preserves the source declaration's position
        // without reinitializing the object on every invocation.
        Ok(CStatement::Skip)
    }

    fn parse_static_array_initializer(
        &mut self,
        name: &str,
        element_type: InterfaceType,
        pointee_constant: bool,
        length: u32,
    ) -> Result<CArrayInitializer, CSyntaxError> {
        self.parse_scalar_array_initializer(name, element_type, pointee_constant, length, true)
    }

    fn struct_value_copy_statement(
        &mut self,
        target: &BindingName,
        expression: CExpression,
    ) -> Result<CStatement, CSyntaxError> {
        let target_struct = self
            .variable_struct_values
            .get(target)
            .cloned()
            .ok_or_else(|| self.error_here(format!("`{target}` is not a struct value")))?;
        self.aggregate_copy_statement(
            CExpression::Variable(target.clone()),
            &target_struct,
            expression,
        )
    }

    fn aggregate_copy_statement(
        &mut self,
        target_pointer: CExpression,
        target_struct: &str,
        expression: CExpression,
    ) -> Result<CStatement, CSyntaxError> {
        let start = self.aggregate_expression_steps.len();
        let (prefix, expression) = self.lower_expression_calls(expression)?;
        let copy = self.aggregate_copy_statement_raw(target_pointer, target_struct, expression)?;
        let steps = self
            .aggregate_expression_steps
            .drain(start..)
            .collect::<Vec<_>>();
        let lowered = prepend_statements(prefix, copy);
        Ok(if steps.is_empty() {
            lowered
        } else {
            CStatement::Seq(
                Box::new(lowered),
                Box::new(CStatement::EndAggregateLifetimes {
                    names: Vec::new(),
                    steps,
                    site: CSite::NONE,
                }),
            )
        })
    }

    fn aggregate_copy_statement_raw(
        &self,
        target_pointer: CExpression,
        target_struct: &str,
        expression: CExpression,
    ) -> Result<CStatement, CSyntaxError> {
        self.scalar_struct_value_layout(target_struct)?;
        let is_step_result = matches!(expression, CExpression::StepResult { .. });
        let (source_pointer, source_struct) = match expression {
            expression @ CExpression::StepResult { .. } => {
                let struct_name = self.aggregate_struct_name(&expression).ok_or_else(|| {
                    self.error_here("aggregate copy requires an aggregate step result")
                })?;
                (expression, struct_name)
            }
            CExpression::Variable(name) => {
                let source_struct =
                    self.variable_struct_values
                        .get(&name)
                        .cloned()
                        .ok_or_else(|| {
                            self.error_here("aggregate copies require a struct value source")
                        })?;
                (CExpression::Variable(name), source_struct)
            }
            CExpression::AggregateAddress {
                pointer,
                struct_name,
            } => (*pointer, struct_name),
            CExpression::Load(pointer, _) => {
                let source_struct = self.struct_pointer_name(&pointer).ok_or_else(|| {
                    self.error_here("aggregate loads require a pointer to a declared struct")
                })?;
                (*pointer, source_struct)
            }
            _ => {
                return Err(self.error_here(
                    "aggregate copies require another struct value or a direct struct lvalue load",
                ));
            }
        };
        if target_struct != source_struct {
            return Err(self.error_here(format!(
                "cannot copy `struct {source_struct}` into `struct {target_struct}`"
            )));
        }
        let layout = self
            .structs
            .get(target_struct)
            .expect("validated struct value has a layout");
        if is_step_result || !layout.aggregate_unions.is_empty() {
            return Ok(CStatement::AggregateCopy {
                target: target_pointer,
                source: source_pointer,
                layout: layout.clone(),
                site: CSite::NONE,
            });
        }
        let mut stores = Vec::new();
        for field in layout.aggregate_fields() {
            let (element_type, element_count) = match field.interface_type {
                InterfaceType::Int8 => (field.interface_type, 1),
                InterfaceType::Bool
                | InterfaceType::Int16
                | InterfaceType::Int32
                | InterfaceType::Char(_)
                | InterfaceType::UInt8
                | InterfaceType::UInt16
                | InterfaceType::UInt32
                | InterfaceType::Int64(_)
                | InterfaceType::UInt64(_)
                | InterfaceType::Float32
                | InterfaceType::Float64 => (field.interface_type, 1),
                InterfaceType::Int32Array(length) => (InterfaceType::Int32, length),
                InterfaceType::Int64Array(rank, length) => (InterfaceType::Int64(rank), length),
                InterfaceType::Int128Array(length) => (InterfaceType::Int128, length),
                InterfaceType::UInt64Array(rank, length) => (InterfaceType::UInt64(rank), length),
                InterfaceType::UInt128Array(length) => (InterfaceType::UInt128, length),
                InterfaceType::CharArray(plain, length) => (InterfaceType::Char(plain), length),
                InterfaceType::UInt8Array(length) => (InterfaceType::UInt8, length),
                InterfaceType::Float32Array(length) => (InterfaceType::Float32, length),
                InterfaceType::Float64Array(length) => (InterfaceType::Float64, length),
                InterfaceType::PointerArray(element, rank, length) => {
                    (pointer_array_element_type(element, rank), length)
                }
                InterfaceType::Int32Pointer
                | InterfaceType::CharPointer(_)
                | InterfaceType::UInt8Pointer
                | InterfaceType::Float32Pointer
                | InterfaceType::Float64Pointer
                | InterfaceType::Int32PointerPointer
                | InterfaceType::CharPointerPointer(_)
                | InterfaceType::UInt8PointerPointer
                | InterfaceType::Float32PointerPointer
                | InterfaceType::Float64PointerPointer
                // A callback field copies as the eight-byte pointer value it
                // is, keeping the destination's declared signature.
                | InterfaceType::FunctionPointer(_) => (field.interface_type, 1),
                pointer if pointer.is_pointer() => (pointer, 1),
                _ => unreachable!("validated struct value field shape"),
            };
            let element_signature = matches!(element_type, InterfaceType::FunctionPointer(_))
                .then(|| {
                    layout
                        .fields
                        .get(&field.name)
                        .and_then(|field| field.function_pointer_signature.clone())
                })
                .flatten();
            let element_width = element_type.abi_size_bytes();
            for index in 0..element_count {
                let element_offset = field
                    .offset_bytes
                    .checked_add(
                        index
                            .checked_mul(element_width)
                            .expect("validated struct value field offset"),
                    )
                    .expect("validated struct value field offset");
                let target_pointer = offset_field_pointer(target_pointer.clone(), element_offset);
                let source_pointer = offset_field_pointer(source_pointer.clone(), element_offset);
                stores.push(CStatement::Store {
                    pointer: target_pointer,
                    value: CExpression::Field {
                        pointer: Box::new(source_pointer),
                        field_type: element_type,
                        pointee_constant: field.pointee_constant,
                        field_struct_name: None,
                        function_pointer_signature: element_signature.clone(),
                        array_shape: None,
                        source: None,
                        access_class: None,
                    },
                    value_type: Some(element_type),
                    lvalue_class: None,
                    pointee_constant: field.pointee_constant,
                    site: CSite::NONE,
                });
            }
        }
        Ok(balanced_statement_sequence(stores).unwrap_or(CStatement::Skip))
    }

    fn parse_for_initializer(&mut self) -> Result<CStatement, CSyntaxError> {
        if self.peek() == Some(&Token::Semicolon) {
            return Ok(CStatement::Skip);
        }
        if self.is_type_start() {
            return self.parse_for_declaration_initializer();
        }

        let mut initializers = vec![self.parse_for_assignment_initializer()?];
        while self.peek() == Some(&Token::Comma) {
            self.position += 1;
            initializers.push(self.parse_for_assignment_initializer()?);
        }
        Ok(balanced_statement_sequence(initializers).unwrap_or(CStatement::Skip))
    }

    fn parse_for_declaration_initializer(&mut self) -> Result<CStatement, CSyntaxError> {
        let parsed_type = self.parse_type()?;
        if parsed_type.union_name.is_some() {
            return Err(self.error_here(
                "tagged union loop locals are not supported; access an active scalar member through a struct pointer",
            ));
        }
        if parsed_type.interface_type == InterfaceType::Void {
            return Err(self.error_here("void for-loop locals are not supported"));
        }
        if parsed_type.is_constant {
            return Err(
                self.error_here("const-qualified for-loop locals are not supported in this slice")
            );
        }
        if is_plain_struct_type(&parsed_type) {
            return Err(self.error_here("only pointer-to-struct types are supported"));
        }
        self.validate_volatile_type(&parsed_type)?;
        let mut initializers = Vec::new();
        loop {
            let source_name = self.expect_ident("for-loop local name")?;
            let name = self.declare_name(&source_name)?;
            self.variable_types
                .insert(name.clone(), parsed_type.interface_type);
            if let Some(signature) = &parsed_type.function_pointer_signature {
                self.variable_function_pointers
                    .insert(name.clone(), signature.clone());
            }
            let object_volatile = parsed_type.object_is_volatile();
            let pointee_volatile = parsed_type.pointee_is_volatile();
            let object_constant = parsed_type.is_constant;
            let pointee_constant = parsed_type.pointee_constant;
            if object_constant {
                self.variable_constants.insert(name.clone());
            }
            if pointee_constant {
                self.variable_pointee_constants.insert(name.clone());
            }
            if self.peek() != Some(&Token::Equal) {
                return Err(self.error_here("for-loop declarations require an initializer"));
            }
            self.position += 1;
            let mut expression = self.parse_expression()?;
            if let Some(signature) = &parsed_type.function_pointer_signature {
                self.validate_function_pointer_value(signature, &expression)?;
            }
            self.reject_discarded_const_pointer(
                parsed_type.interface_type,
                pointee_constant,
                &mut expression,
            )?;
            initializers.push(CStatement::Seq(
                Box::new(CStatement::Declare {
                    interface_type: parsed_type.interface_type,
                    name: name.clone().into(),
                    volatile: object_volatile,
                    pointee_volatile,
                    constant: object_constant,
                    pointee_constant,
                    initializer: None,
                    zero_fill: None,
                    declared_class: None,
                    site: CSite::NONE,
                }),
                Box::new(CStatement::Assign {
                    name,
                    expression,
                    site: CSite::NONE,
                    prior_result: None,
                }),
            ));
            if self.peek() != Some(&Token::Comma) {
                break;
            }
            self.position += 1;
        }
        Ok(balanced_statement_sequence(initializers).unwrap_or(CStatement::Skip))
    }

    fn parse_for_assignment_initializer(&mut self) -> Result<CStatement, CSyntaxError> {
        let Some(Token::Ident(source_name)) = self.next() else {
            return Err(
                self.error_here("expected assignment target in for-loop initializer".to_string())
            );
        };
        let name = self.resolve_object_name(
            &source_name,
            self.positions.get(self.position.saturating_sub(1)).cloned(),
        )?;
        if self.variable_is_constant(&name) {
            return Err(self.error_here(format!(
                "cannot assign to const-qualified lvalue `{source_name}`"
            )));
        }
        self.expect(Token::Equal)?;
        if let Some(row) = self.local_row_pointers.get(&name).cloned() {
            return self.parse_row_pointer_update(&row, Token::Equal);
        }
        let expression = self.parse_expression()?;
        self.validate_function_pointer_assignment(&name, &expression)?;
        Ok(CStatement::Assign {
            name: (name),
            expression,
            site: CSite::NONE,
            prior_result: None,
        })
    }

    fn parse_scalar_update_statement(&mut self, context: &str) -> Result<CStatement, CSyntaxError> {
        let prefix_operator = match self.peek() {
            Some(Token::PlusPlus | Token::MinusMinus) => self.next(),
            _ => None,
        };
        let parenthesized = self.parenthesized_identifier_at(0);
        if parenthesized {
            self.position += 1;
        }
        let source_name = match self.next() {
            Some(Token::Ident(name)) if name != "int32" && name != "uint8" => name,
            Some(Token::Ident(name)) => {
                return Err(self.error_here(format!(
                    "expected scalar update target in {context}, got `{name}`"
                )));
            }
            Some(token) => {
                return Err(self.error_at_previous(format!(
                    "expected scalar update target in {context}, got {}",
                    token.describe()
                )));
            }
            None => {
                return Err(self.error_here(format!(
                    "expected scalar update target in {context}, got end of input"
                )));
            }
        };
        let name = self.resolve_object_name(
            &source_name,
            self.positions.get(self.position.saturating_sub(1)).cloned(),
        )?;
        if parenthesized {
            self.expect(Token::RParen)?;
        }
        if self.variable_is_constant(&name) {
            return Err(self.error_here(format!(
                "cannot update const-qualified lvalue `{source_name}`"
            )));
        }
        let operator = match prefix_operator {
            Some(operator) => operator,
            None => self.next().ok_or_else(|| {
                self.error_here(format!(
                    "expected scalar update operator in {context}, got end of input"
                ))
            })?,
        };
        if let Some(row) = self.local_row_pointers.get(&name).cloned() {
            return self.parse_row_pointer_update(&row, operator);
        }
        if self.variable_struct_values.contains_key(&name) {
            if operator != Token::Equal {
                return Err(self.error_here(format!(
                    "struct value `{name}` only supports whole-value assignment"
                )));
            }
            if matches!(self.peek(), Some(Token::Ident(_)))
                && !matches!(
                    self.peek_ident(),
                    Some("sizeof" | "__builtin_types_compatible_p" | "__builtin_offsetof")
                )
                && self.peek_next() == Some(&Token::LParen)
            {
                let source_name = self.expect_ident("function name")?;
                let arguments = self.parse_call_arguments(Some(&source_name))?;
                return self.call_assignment_statement(
                    name,
                    self.call_target(&source_name),
                    arguments,
                );
            }
            let expression = self.parse_expression_allow_direct_aggregate()?;
            return self.struct_value_copy_statement(&name, expression);
        }
        let expression = match operator {
            Token::Equal => {
                if matches!(self.peek(), Some(Token::Ident(_)))
                    && !matches!(
                        self.peek_ident(),
                        Some("sizeof" | "__builtin_types_compatible_p" | "__builtin_offsetof")
                    )
                    && self.peek_next() == Some(&Token::LParen)
                {
                    let call_start = self.position;
                    let source_name = self.expect_ident("function name")?;
                    let arguments = self.parse_call_arguments(Some(&source_name))?;
                    let is_kernel_primitive = self
                        .parse_kernel_primitive_expression(
                            &source_name,
                            &arguments,
                            self.positions.get(call_start).cloned(),
                        )?
                        .is_some();
                    if !is_kernel_primitive && self.peek() == Some(&Token::Semicolon) {
                        return self.call_assignment_statement(
                            name,
                            self.call_target(&source_name),
                            arguments,
                        );
                    }
                    self.position = call_start;
                }
                {
                    let mut expression = self.parse_expression()?;
                    self.reject_discarded_const_pointer(
                        self.variable_types
                            .get(&name)
                            .copied()
                            .unwrap_or(InterfaceType::Void),
                        self.variable_pointee_is_constant(&name),
                        &mut expression,
                    )?;
                    self.validate_function_pointer_assignment(&name, &expression)?;
                    expression
                }
            }
            Token::PlusPlus => CExpression::Add(
                Box::new(CExpression::Variable(name.clone())),
                Box::new(CExpression::Int32Literal(1)),
            ),
            Token::MinusMinus => CExpression::Subtract(
                Box::new(CExpression::Variable(name.clone())),
                Box::new(CExpression::Int32Literal(1)),
            ),
            Token::PlusEqual => CExpression::Add(
                Box::new(CExpression::Variable(name.clone())),
                Box::new(self.parse_expression()?),
            ),
            Token::MinusEqual => CExpression::Subtract(
                Box::new(CExpression::Variable(name.clone())),
                Box::new(self.parse_expression()?),
            ),
            Token::StarEqual => CExpression::Multiply(
                Box::new(CExpression::Variable(name.clone())),
                Box::new(self.parse_expression()?),
            ),
            Token::SlashEqual => CExpression::Divide(
                Box::new(CExpression::Variable(name.clone())),
                Box::new(self.parse_expression()?),
            ),
            Token::PercentEqual => CExpression::Remainder(
                Box::new(CExpression::Variable(name.clone())),
                Box::new(self.parse_expression()?),
            ),
            Token::ShiftLeftEqual => CExpression::ShiftLeft(
                Box::new(CExpression::Variable(name.clone())),
                Box::new(self.parse_expression()?),
            ),
            Token::ShiftRightEqual => CExpression::ShiftRight(
                Box::new(CExpression::Variable(name.clone())),
                Box::new(self.parse_expression()?),
            ),
            Token::AmpEqual => CExpression::BitwiseAnd(
                Box::new(CExpression::Variable(name.clone())),
                Box::new(self.parse_expression()?),
            ),
            Token::PipeEqual => CExpression::BitwiseOr(
                Box::new(CExpression::Variable(name.clone())),
                Box::new(self.parse_expression()?),
            ),
            Token::CaretEqual => CExpression::BitwiseXor(
                Box::new(CExpression::Variable(name.clone())),
                Box::new(self.parse_expression()?),
            ),
            token => {
                return Err(self.error_here(format!(
                    "expected scalar update operator in {context}, got {}",
                    token.describe()
                )));
            }
        };
        let mut expression = match expression {
            CExpression::Add(left, right)
                if operator == Token::PlusPlus || operator == Token::PlusEqual =>
            {
                self.scale_struct_pointer_arithmetic(*left, *right, CExpression::Add)?
            }
            CExpression::Subtract(left, right)
                if operator == Token::MinusMinus || operator == Token::MinusEqual =>
            {
                self.scale_struct_pointer_arithmetic(*left, *right, CExpression::Subtract)?
            }
            expression => expression,
        };
        if operator == Token::Equal {
            self.validate_struct_pointer_assignment(
                self.variable_structs.get(&name),
                self.variable_types.get(&name).copied(),
                &mut expression,
            )?;
            self.validate_function_pointer_assignment(&name, &expression)?;
        }
        Ok(CStatement::Assign {
            name: (name),
            expression,
            site: CSite::NONE,
            prior_result: None,
        })
    }

    fn parse_update_statement(&mut self, context: &str) -> Result<CStatement, CSyntaxError> {
        if self.peek() == Some(&Token::Star)
            || matches!(self.peek(), Some(Token::Ident(_)))
                && matches!(
                    self.peek_next(),
                    Some(Token::LBracket | Token::Dot | Token::Arrow)
                )
        {
            return self.parse_memory_lvalue_statement(context, None);
        }
        if matches!(self.peek(), Some(Token::PlusPlus | Token::MinusMinus))
            && self.prefix_starts_memory_lvalue()
        {
            let prefix = self.next();
            return self.parse_memory_lvalue_statement(context, prefix);
        }
        self.parse_scalar_update_statement(context)
    }

    fn parse_memory_lvalue_statement(
        &mut self,
        context: &str,
        prefix_operator: Option<Token>,
    ) -> Result<CStatement, CSyntaxError> {
        let target = if self.peek() == Some(&Token::Star) {
            self.position += 1;
            let pointer = self.parse_unary()?;
            self.dereference_expression(pointer)
        } else {
            self.parse_postfix_with_updates(false)?
        };
        let operator = match prefix_operator {
            Some(operator) => operator,
            None => self.next().ok_or_else(|| {
                self.error_here(format!(
                    "expected memory lvalue update operator in {context}, got end of input"
                ))
            })?,
        };
        self.reject_constant_lvalue_write(&target)?;
        if operator == Token::Equal {
            if let CExpression::AggregateAddress {
                pointer,
                struct_name,
            } = &target
            {
                let value = self.parse_expression_allow_direct_aggregate()?;
                return self.aggregate_copy_statement(pointer.as_ref().clone(), struct_name, value);
            }
            let mut value = self.parse_expression()?;
            if let Some(target_type) = self.source_expression_type(&target) {
                self.reject_discarded_const_pointer(
                    target_type,
                    self.expression_pointee_is_constant(&target),
                    &mut value,
                )?;
            }
            return match target {
                // A classed load's type rides on the store, so the kernel
                // checks the store's access class as it does the load's.
                CExpression::Load(pointer, loaded_type) => {
                    if let Some(struct_name) = self.struct_pointer_pointer_name(&pointer) {
                        self.validate_struct_pointer_value(&struct_name, &value)?;
                    }
                    Ok(CStatement::Store {
                        pointer: *pointer,
                        value,
                        value_type: loaded_type.as_ref().map(|loaded| loaded.interface_type),
                        lvalue_class: loaded_type.map(|loaded| loaded.class),
                        pointee_constant: false,
                        site: CSite::NONE,
                    })
                }
                CExpression::Field {
                    pointer,
                    field_type,
                    pointee_constant,
                    field_struct_name,
                    function_pointer_signature,
                    access_class,
                    ..
                } => {
                    if let Some(signature) = function_pointer_signature {
                        self.validate_function_pointer_value(&signature, &value)?;
                    }
                    if let Some(struct_name) = field_struct_name {
                        if matches!(field_type, InterfaceType::Int32Pointer | InterfaceType::UInt8Pointer) {
                            self.validate_struct_pointer_value(&struct_name, &value)?;
                        } else if matches!(
                            field_type,
                            InterfaceType::Int8PointerPointer
                                | InterfaceType::Int16PointerPointer
                                | InterfaceType::UInt16PointerPointer
                                | InterfaceType::Int32PointerPointer
                                | InterfaceType::CharPointerPointer(_)
                                | InterfaceType::UInt8PointerPointer
                                | InterfaceType::UInt32PointerPointer
                                | InterfaceType::Int128PointerPointer
                                | InterfaceType::Int64PointerPointer(_)
                                | InterfaceType::UInt128PointerPointer
                                | InterfaceType::UInt64PointerPointer(_)
                                | InterfaceType::Float32PointerPointer
                                | InterfaceType::Float64PointerPointer
                        ) {
                            self.validate_struct_pointer_pointer_value(&struct_name, &value)?;
                        }
                    }
                    Ok(CStatement::Store {
                        pointer: *pointer,
                        value,
                        value_type: Some(field_type),
                        lvalue_class: access_class,
                        pointee_constant,
                        site: CSite::NONE,
                    })
                }
                CExpression::AggregateAddress { .. } => unreachable!(
                    "aggregate assignment is handled before scalar memory lvalue matching"
                ),
                CExpression::UnionAddress { .. } => {
                    Err(self.error_here("assigning to a tagged union value is not supported"))
                }
                CExpression::UnionField { .. } => {
                    Err(self.error_here("writing tagged union members is not supported"))
                }
                CExpression::Index(base, index, element_type) => Ok(CStatement::Store {
                    pointer: CExpression::Add(base, index),
                    value,
                    value_type: element_type.as_ref().map(|element| element.interface_type),
                    lvalue_class: element_type.map(|element| element.class),
                    pointee_constant: false,
                    site: CSite::NONE,
                }),
                _ => Err(self.error_here(format!(
                    "expected memory lvalue assignment target in {context}, got an expression that does not designate an object"
                ))),
            };
        }

        if matches!(target, CExpression::UnionField { .. }) {
            return Err(self.error_here(
                "writing tagged union members is not supported; union accesses are read-only",
            ));
        }

        let increment = matches!(operator, Token::PlusPlus | Token::MinusMinus);
        let operator = match operator {
            Token::PlusPlus | Token::PlusEqual => CUpdateOperator::Add,
            Token::MinusMinus | Token::MinusEqual => CUpdateOperator::Subtract,
            Token::StarEqual => CUpdateOperator::Multiply,
            Token::SlashEqual => CUpdateOperator::Divide,
            Token::PercentEqual => CUpdateOperator::Remainder,
            Token::ShiftLeftEqual => CUpdateOperator::ShiftLeft,
            Token::ShiftRightEqual => CUpdateOperator::ShiftRight,
            Token::AmpEqual => CUpdateOperator::BitwiseAnd,
            Token::PipeEqual => CUpdateOperator::BitwiseOr,
            Token::CaretEqual => CUpdateOperator::BitwiseXor,
            token => {
                return Err(self.error_here(format!(
                    "expected memory lvalue update operator in {context}, got {}",
                    token.describe()
                )));
            }
        };
        let operand = if increment {
            CExpression::Int32Literal(1)
        } else {
            self.parse_expression()?
        };
        Ok(CStatement::Update {
            target,
            operator,
            operand,
            site: CSite::NONE,
        })
    }

    fn prefix_starts_memory_lvalue(&self) -> bool {
        self.peek_n(1) == Some(&Token::Star)
            || matches!(self.peek_n(1), Some(Token::Ident(_)))
                && matches!(self.peek_n(2), Some(Token::LBracket | Token::Arrow))
            || self.peek_n(1) == Some(&Token::LParen)
                && !self.parenthesized_identifier_at(1)
                && !self.is_type_start_at(2)
    }

    /// Whether the tokens at `offset` are `( name )`: a parenthesized
    /// variable, which designates the variable itself.
    fn parenthesized_identifier_at(&self, offset: usize) -> bool {
        self.peek_n(offset) == Some(&Token::LParen)
            && matches!(self.peek_n(offset + 1), Some(Token::Ident(_)))
            && self.peek_n(offset + 2) == Some(&Token::RParen)
    }

    fn parse_for_step(&mut self) -> Result<CStatement, CSyntaxError> {
        if self.peek() == Some(&Token::RParen) {
            return Ok(CStatement::Skip);
        }
        let mut steps = vec![self.parse_update_statement("for-loop step")?];
        while self.peek() == Some(&Token::Comma) {
            self.position += 1;
            steps.push(self.parse_update_statement("for-loop step")?);
        }
        Ok(balanced_statement_sequence(steps).unwrap_or(CStatement::Skip))
    }

    fn lower_aggregate_call_result(
        &mut self,
        function_name: String,
        arguments: Vec<CExpression>,
        struct_name: String,
    ) -> Result<(Vec<CStatement>, CExpression), CSyntaxError> {
        let (mut prefix, arguments) = self.lower_call_arguments(arguments)?;
        let call = self.next_call_result;
        self.next_call_result = self.next_call_result.saturating_add(1);
        // Value returns already materialize independent aggregate storage.
        // Retain its pointer; copying into the destination is a separate effect.
        let layout = self.scalar_struct_value_layout(&struct_name)?;
        self.aggregate_expression_steps.push(call);
        prefix.push(CStatement::CallResult {
            aggregate_layout: Some(layout.clone()),
            call,
            function_name: function_name.clone(),
            arguments,
            result_type: Some(InterfaceType::UInt8Pointer),
            result_aggregate_layout: Some(layout),
            result_pointee_constant: false,
            site: CSite::NONE,
            callee: None,
        });
        Ok((
            prefix,
            CExpression::StepResult {
                step: call,
                origin: crate::kernel::StepOrigin::Call(function_name),
                interface_type: Some(InterfaceType::Int32),
                pointee_constant: false,
                struct_name: Some(struct_name),
            },
        ))
    }

    fn call_assignment_statement(
        &mut self,
        target: BindingName,
        function_name: String,
        arguments: Vec<CExpression>,
    ) -> Result<CStatement, CSyntaxError> {
        if self.call_return_pointee_is_constant(&function_name)
            && self
                .variable_types
                .get(&target)
                .is_some_and(|interface_type| interface_type.is_pointer())
            && !self.variable_pointee_is_constant(&target)
        {
            return Err(self.error_here("cannot discard const qualification from a call result"));
        }
        if function_name == "realloc" {
            if arguments.len() != 2 {
                return Err(self.error_here(format!(
                    "`realloc` expects two arguments, got {}",
                    arguments.len()
                )));
            }
            let (prefix, arguments) = self.lower_call_arguments(arguments)?;
            let interface_type = self.variable_types.get(&target).copied();
            let call = self.next_call_result;
            self.next_call_result = self
                .next_call_result
                .checked_add(1)
                .expect("too many calls");
            return Ok(prepend_statements(
                prefix,
                CStatement::Seq(
                    Box::new(CStatement::CallResult {
                        aggregate_layout: None,
                        call,
                        function_name: function_name.clone(),
                        arguments,
                        result_type: interface_type,
                        result_aggregate_layout: None,
                        result_pointee_constant: false,
                        callee: None,
                        site: CSite::NONE,
                    }),
                    Box::new(CStatement::Assign {
                        name: (target.clone()),
                        expression: CExpression::StepResult {
                            step: call,
                            origin: crate::kernel::StepOrigin::Call(function_name),
                            interface_type,
                            pointee_constant: false,
                            struct_name: self.variable_structs.get(&target).cloned(),
                        },
                        prior_result: None,
                        site: CSite::NONE,
                    }),
                ),
            ));
        }
        if !matches!(function_name.as_str(), "malloc" | "calloc") {
            if self.function_declaration_for_call(&function_name).is_some() {
                let call = CExpression::Call {
                    function_name: function_name.clone(),
                    arguments: arguments.clone(),
                    position: None,
                };
                let mut value = call.clone();
                self.validate_struct_pointer_assignment(
                    self.variable_structs.get(&target),
                    self.variable_types.get(&target).copied(),
                    &mut value,
                )?;
                // A character pointer result of another character type is
                // converted as by its explicit cast: the call becomes an
                // embedded call, which lowering assigns to a temporary.
                if value != call {
                    return Ok(CStatement::Assign {
                        name: (target),
                        expression: value,
                        site: CSite::NONE,
                        prior_result: None,
                    });
                }
            }
            if let Some(struct_name) = self
                .function_declaration_for_call(&function_name)
                .and_then(|function| function.return_struct_name.clone())
                .or_else(|| self.variable_struct_values.get(&target).cloned())
            {
                if self.variable_struct_values.get(&target) != Some(&struct_name) {
                    return Err(self.error_here(format!(
                        "aggregate call result requires a destination of type `struct {struct_name}`"
                    )));
                }
                let layout = self.scalar_struct_value_layout(&struct_name)?;
                let start = self.aggregate_expression_steps.len();
                let (mut prefix, source) =
                    self.lower_aggregate_call_result(function_name, arguments, struct_name)?;
                prefix.push(CStatement::AggregateCopy {
                    target: CExpression::Variable(target),
                    source,
                    layout,
                    site: CSite::NONE,
                });
                let steps = self.aggregate_expression_steps.drain(start..).collect();
                prefix.push(CStatement::EndAggregateLifetimes {
                    names: Vec::new(),
                    steps,
                    site: CSite::NONE,
                });
                return Ok(balanced_statement_sequence(prefix).expect("call and aggregate copy"));
            }
            return Ok(CStatement::Assign {
                name: (target),
                expression: CExpression::Call {
                    function_name,
                    arguments,
                    position: None,
                },
                prior_result: None,
                site: CSite::NONE,
            });
        }
        let zeroed = function_name == "calloc";
        let bytes = if zeroed {
            let [count, element_size] = arguments.as_slice() else {
                return Err(self.error_here(format!(
                    "`calloc` expects two byte-count arguments, got {}",
                    arguments.len()
                )));
            };
            if let Some(target_struct) = self.variable_structs.get(&target) {
                let matches_target = match element_size {
                    CExpression::SizeOfStruct { name, .. } => name == target_struct,
                    CExpression::SizeOfType {
                        interface_type: InterfaceType::Int32,
                        struct_name: Some(name),
                        ..
                    } => name == target_struct,
                    _ => false,
                };
                if !matches_target {
                    return Err(self.error_here(format!(
                        "`calloc` size must be `sizeof(struct {target_struct})` for target `struct {target_struct} *`"
                    )));
                }
            } else {
                let matches_target_element = match self.variable_types.get(&target).copied() {
                    Some(InterfaceType::CharPointer(_)) => matches!(
                        element_size,
                        CExpression::Int32Literal(1)
                            | CExpression::SizeOfType {
                                interface_type: InterfaceType::Char(_),
                                struct_name: None,
                                ..
                            }
                    ),
                    Some(InterfaceType::UInt8Pointer) => matches!(
                        element_size,
                        CExpression::Int32Literal(1)
                            | CExpression::SizeOfType {
                                interface_type: InterfaceType::UInt8,
                                struct_name: None,
                                ..
                            }
                    ),
                    Some(
                        InterfaceType::Int8Pointer
                        | InterfaceType::Int16Pointer
                        | InterfaceType::UInt16Pointer
                        | InterfaceType::Int32Pointer
                        | InterfaceType::UInt32Pointer
                        | InterfaceType::Int128Pointer
                        | InterfaceType::Int64Pointer(_)
                        | InterfaceType::UInt128Pointer
                        | InterfaceType::UInt64Pointer(_)
                        | InterfaceType::Float32Pointer
                        | InterfaceType::Float64Pointer,
                    ) => {
                        let target_element = self
                            .variable_types
                            .get(&target)
                            .copied()
                            .and_then(InterfaceType::pointee_type)
                            .expect("data pointer target has a pointee type");
                        matches!(
                            element_size,
                            CExpression::Int32Literal(bytes)
                                if *bytes == target_element.abi_size_bytes()
                        ) || matches!(
                            element_size,
                            CExpression::SizeOfType {
                                interface_type,
                                struct_name: None,
                                ..
                            } if *interface_type == target_element
                        )
                    }
                    Some(
                        InterfaceType::Int8PointerPointer
                        | InterfaceType::Int16PointerPointer
                        | InterfaceType::UInt16PointerPointer
                        | InterfaceType::Int32PointerPointer
                        | InterfaceType::CharPointerPointer(_)
                        | InterfaceType::UInt8PointerPointer
                        | InterfaceType::UInt32PointerPointer
                        | InterfaceType::Int128PointerPointer
                        | InterfaceType::Int64PointerPointer(_)
                        | InterfaceType::UInt128PointerPointer
                        | InterfaceType::UInt64PointerPointer(_)
                        | InterfaceType::Float32PointerPointer
                        | InterfaceType::Float64PointerPointer,
                    ) => matches!(
                        element_size,
                        CExpression::Int32Literal(8)
                            | CExpression::SizeOfType {
                                interface_type: InterfaceType::Int8Pointer
                                    | InterfaceType::Int16Pointer
                                    | InterfaceType::UInt16Pointer
                                    | InterfaceType::Int32Pointer
                                    | InterfaceType::CharPointer(_)
                                    | InterfaceType::UInt8Pointer
                                    | InterfaceType::UInt32Pointer
                                    | InterfaceType::Int128Pointer
                                    | InterfaceType::Int64Pointer(_)
                                    | InterfaceType::UInt128Pointer
                                    | InterfaceType::UInt64Pointer(_)
                                    | InterfaceType::Float32Pointer
                                    | InterfaceType::Float64Pointer,
                                struct_name: None,
                                ..
                            }
                    ),
                    _ => matches!(
                        element_size,
                        CExpression::Int32Literal(4)
                            | CExpression::SizeOfType {
                                interface_type: InterfaceType::Int32,
                                struct_name: None,
                                ..
                            }
                    ),
                };
                if !matches_target_element {
                    return Err(self.error_here(
                        "`calloc` currently supports only `sizeof(int32)`, `sizeof(uint8)`, or a matching struct size",
                    ));
                }
            }
            CExpression::Multiply(Box::new(count.clone()), Box::new(element_size.clone()))
        } else {
            let [bytes] = arguments.as_slice() else {
                return Err(self.error_here(format!(
                    "`malloc` expects one byte-count argument, got {}",
                    arguments.len()
                )));
            };
            bytes.clone()
        };
        let object_type = self
            .variable_structs
            .get(&target)
            .filter(|_| self.variable_types.get(&target) == Some(&InterfaceType::Int32Pointer))
            .and_then(|tag| self.structs.get(tag))
            .and_then(|layout| {
                layout.class.clone().map(|class| {
                    (
                        crate::kernel::effective_type::CAccessClass::Struct(class),
                        layout.size_bytes,
                        layout.alignment_bytes,
                    )
                })
            });
        Ok(CStatement::HeapAllocate {
            target: (target),
            bytes,
            zeroed,
            object_type,
            site: CSite::NONE,
        })
    }

    fn parse_expression(&mut self) -> Result<CExpression, CSyntaxError> {
        let expression = self.parse_assignment()?;
        if self.expression_contains_aggregate(&expression) {
            return Err(self.aggregate_expression_error());
        }
        Ok(expression)
    }

    fn parse_expression_allow_direct_aggregate(&mut self) -> Result<CExpression, CSyntaxError> {
        let expression = self.parse_assignment()?;
        if self.expression_contains_aggregate(&expression)
            && self.aggregate_struct_name(&expression).is_none()
        {
            return Err(self.aggregate_expression_error());
        }
        Ok(expression)
    }

    fn aggregate_expression_error(&self) -> CSyntaxError {
        self.error_here(
            "embedded struct fields are only supported through member access or whole-struct lvalue copies; struct values are not scalar expressions, and tagged union values are not runtime aggregates",
        )
    }

    /// Parse the one assignment-expression form required by unchanged Linux
    /// rbtree guards. It has C's low precedence and right associativity, but
    /// intentionally accepts only `name = assignment-expression` for a
    /// modeled non-aggregate scalar object.
    fn parse_assignment(&mut self) -> Result<CExpression, CSyntaxError> {
        let target = self.parse_conditional()?;
        if self.peek() != Some(&Token::Equal) {
            return Ok(target);
        }

        let position = self.positions.get(self.position).cloned();
        self.position += 1;
        let CExpression::Variable(name) = target else {
            return Err(self.error_at_position(
                position,
                "assignment expressions currently require a simple scalar variable target",
            ));
        };
        if self.variable_is_constant(&name) {
            return Err(self.error_at_position(
                position,
                format!("cannot assign to const-qualified lvalue `{name}`"),
            ));
        }
        let interface_type = self.variable_types.get(&name).copied().ok_or_else(|| {
            self.error_at_position(
                position.clone(),
                format!("assignment expression target `{name}` has no supported C type"),
            )
        })?;
        if !interface_type.is_supported_static_scalar() {
            return Err(self.error_at_position(
                position.clone(),
                "assignment expressions currently require a modeled arithmetic or supported data-pointer scalar target",
            ));
        }

        let mut value = self.parse_assignment()?;
        self.reject_discarded_const_pointer(
            interface_type,
            self.variable_pointee_is_constant(&name),
            &mut value,
        )?;
        self.validate_char_pointer_assignment(interface_type, &mut value)?;
        self.validate_struct_pointer_assignment(
            self.variable_structs.get(&name),
            Some(interface_type),
            &mut value,
        )?;

        Ok(CExpression::Assignment {
            struct_name: self.variable_structs.get(&name).cloned(),
            pointee_constant: self.variable_pointee_is_constant(&name),
            name,
            value: Box::new(value),
            interface_type,
            position,
        })
    }

    fn aggregate_struct_name(&self, expression: &CExpression) -> Option<String> {
        match expression {
            CExpression::StepResult {
                interface_type: Some(InterfaceType::Int32),
                struct_name,
                ..
            } => struct_name.clone(),
            CExpression::StepResult { .. } => None,
            CExpression::Variable(name) => self
                .variable_struct_values
                .get(name)
                .cloned()
                .or_else(|| self.local_struct_values.get(name).cloned().flatten()),
            CExpression::Call { function_name, .. } => self
                .function_declaration(function_name)
                .and_then(|function| function.return_struct_name.clone()),
            CExpression::IndirectCall { signature, .. } => signature.return_struct_name.clone(),
            CExpression::StatementExpression {
                interface_type: InterfaceType::Int32,
                struct_name: Some(struct_name),
                ..
            } => Some(struct_name.clone()),
            CExpression::AggregateAddress { struct_name, .. } => Some(struct_name.clone()),
            CExpression::Field {
                field_type: InterfaceType::Int32,
                field_struct_name: Some(struct_name),
                ..
            } => Some(struct_name.clone()),
            CExpression::Field { .. } => None,
            CExpression::Load(pointer, _) => self.struct_pointer_name(pointer),
            CExpression::Ternary {
                then_branch,
                else_branch,
                ..
            } => {
                let then_struct = self.aggregate_struct_name(then_branch);
                let else_struct = self.aggregate_struct_name(else_branch);
                (then_struct == else_struct)
                    .then_some(then_struct)
                    .flatten()
            }
            CExpression::UnionAddress { .. }
            | CExpression::UnionField { .. }
            | CExpression::StatementExpression { .. }
            | CExpression::Assignment { .. }
            | CExpression::ScalarUpdate { .. }
            | CExpression::StringLiteral(_)
            | CExpression::Void
            | CExpression::FunctionAddress(_)
            | CExpression::Int32Literal(_)
            | CExpression::UInt8Literal(_)
            | CExpression::UInt32Literal(_)
            | CExpression::Int64Literal(_)
            | CExpression::UInt64Literal(_)
            | CExpression::Float32Literal(_)
            | CExpression::Float64Literal(_)
            | CExpression::SizeOfStruct { .. }
            | CExpression::SizeOfUnion { .. }
            | CExpression::SizeOfType { .. }
            | CExpression::Cast { .. }
            | CExpression::FloatNegate(_)
            | CExpression::FloatClassification { .. }
            | CExpression::AddressOf(_)
            | CExpression::PointerOffsetBytes { .. }
            | CExpression::Subobject { .. }
            | crate::languages::c::syntax::c_comparison!(_, _)
            | CExpression::Not(_)
            | CExpression::And(_, _)
            | CExpression::Or(_, _)
            | CExpression::Add(_, _)
            | CExpression::Subtract(_, _)
            | CExpression::Multiply(_, _)
            | CExpression::Divide(_, _)
            | CExpression::Remainder(_, _)
            | CExpression::ShiftLeft(_, _)
            | CExpression::ShiftRight(_, _)
            | CExpression::BitwiseAnd(_, _)
            | CExpression::BitwiseOr(_, _)
            | CExpression::BitwiseXor(_, _)
            | CExpression::BitwiseNot(_)
            | CExpression::SequentialRead { .. }
            | CExpression::SequentialWrite { .. }
            | CExpression::Index(_, _, _)
            | CExpression::CheckedArrayIndex { .. } => None,
        }
    }

    fn expression_contains_aggregate(&self, expression: &CExpression) -> bool {
        if contains_aggregate_value(expression) || self.aggregate_struct_name(expression).is_some()
        {
            return true;
        }
        match expression {
            CExpression::ScalarUpdate { .. } => false,
            CExpression::Call { .. }
            | CExpression::IndirectCall { .. }
            | CExpression::StatementExpression { .. }
            | CExpression::AddressOf(_)
            | CExpression::StringLiteral(_)
            | CExpression::Void
            | CExpression::Variable(_)
            | CExpression::StepResult { .. }
            | CExpression::FunctionAddress(_)
            | CExpression::Int32Literal(_)
            | CExpression::UInt8Literal(_)
            | CExpression::UInt32Literal(_)
            | CExpression::Int64Literal(_)
            | CExpression::UInt64Literal(_)
            | CExpression::Float32Literal(_)
            | CExpression::Float64Literal(_)
            | CExpression::SizeOfStruct { .. }
            | CExpression::SizeOfUnion { .. }
            | CExpression::SizeOfType { .. }
            | CExpression::AggregateAddress { .. }
            | CExpression::UnionAddress { .. }
            | CExpression::UnionField { .. } => false,
            CExpression::SequentialRead { target, .. } => {
                self.expression_contains_aggregate(target)
            }
            CExpression::SequentialWrite { target, value, .. } => {
                self.expression_contains_aggregate(target)
                    || self.expression_contains_aggregate(value)
            }
            CExpression::Assignment { value, .. } => self.expression_contains_aggregate(value),
            CExpression::Cast { expression, .. }
            | CExpression::FloatNegate(expression)
            | CExpression::FloatClassification { expression, .. }
            | CExpression::PointerOffsetBytes {
                pointer: expression,
                ..
            }
            | CExpression::Subobject {
                pointer: expression,
                ..
            }
            | CExpression::Not(expression)
            | CExpression::BitwiseNot(expression)
            | CExpression::Load(expression, _) => self.expression_contains_aggregate(expression),
            CExpression::Ternary {
                condition,
                then_branch,
                else_branch,
            } => {
                self.expression_contains_aggregate(condition)
                    || self.expression_contains_aggregate(then_branch)
                    || self.expression_contains_aggregate(else_branch)
            }
            CExpression::Field { .. } => false,
            CExpression::CheckedArrayIndex { index, .. } => {
                self.expression_contains_aggregate(index)
            }
            crate::languages::c::syntax::binary_c_expression!(left, right) => {
                self.expression_contains_aggregate(left)
                    || self.expression_contains_aggregate(right)
            }
        }
    }

    fn string_literal_expression(&mut self, bytes: Vec<u8>) -> CExpression {
        let ordinal = u32::try_from(self.string_literals.len()).expect("literal count fits u32");
        let identity = self.current_function_source_name.as_ref().map(|function| {
            let mut id = crate::kernel::StringLiteralId::new(function.clone(), ordinal);
            if let Some(source) = &self.source_identity {
                id = id.with_source(source);
            }
            id
        });
        let literal = std::sync::Arc::new(CStringLiteral::new(identity, bytes, self.plain_char));
        if literal.identity.is_some() {
            self.string_literals.push(literal.as_ref().clone());
        }
        CExpression::StringLiteral(literal)
    }

    fn lower_call_expressions(
        &mut self,
        statement: CStatement,
    ) -> Result<CStatement, CSyntaxError> {
        if !self.statement_contains_lowerable_expression(&statement) {
            return Ok(statement);
        }
        self.lower_statement_calls(statement)
    }

    /// Keep the common no-call path iterative. The parser deliberately
    /// represents long straight-line blocks as deeply nested sequences, so a
    /// recursive lowering walk here would consume the small parser stack even
    /// when there is nothing to lower.
    fn statement_contains_lowerable_expression(&self, statement: &CStatement) -> bool {
        let mut statements = vec![statement];
        while let Some(statement) = statements.pop() {
            match statement {
                CStatement::Assign { expression, .. }
                | CStatement::HeapAllocate {
                    bytes: expression, ..
                }
                | CStatement::HeapFree {
                    pointer: expression,
                    ..
                }
                | CStatement::Return(expression, _) => {
                    if self.expression_contains_lowerable_expression(expression) {
                        return true;
                    }
                }
                CStatement::Call { arguments, .. } | CStatement::CallResult { arguments, .. } => {
                    if arguments
                        .iter()
                        .any(|expression| self.expression_contains_lowerable_expression(expression))
                    {
                        return true;
                    }
                }
                CStatement::IndirectCall { .. } => return true,
                CStatement::Assert { condition, .. }
                | CStatement::LoopTest { condition, .. }
                | CStatement::StepValue {
                    expression: condition,
                    ..
                } => {
                    if self.expression_contains_lowerable_expression(condition) {
                        return true;
                    }
                }
                CStatement::Store { pointer, value, .. } => {
                    if self.expression_contains_lowerable_expression(pointer)
                        || self.expression_contains_lowerable_expression(value)
                    {
                        return true;
                    }
                }
                CStatement::SequentialStore { target, value, .. } => {
                    if self.expression_contains_lowerable_expression(target)
                        || self.expression_contains_lowerable_expression(value)
                    {
                        return true;
                    }
                }
                CStatement::AggregateCopy { target, source, .. } => {
                    if self.expression_contains_lowerable_expression(target)
                        || self.expression_contains_lowerable_expression(source)
                    {
                        return true;
                    }
                }
                CStatement::Update {
                    target, operand, ..
                } => {
                    if self.expression_contains_lowerable_expression(target)
                        || self.expression_contains_lowerable_expression(operand)
                    {
                        return true;
                    }
                }
                CStatement::Seq(first, second) => {
                    statements.push(first);
                    statements.push(second);
                }
                CStatement::If {
                    condition,
                    then_branch,
                    else_branch,
                    ..
                } => {
                    if self.expression_contains_lowerable_expression(condition) {
                        return true;
                    }
                    statements.push(then_branch);
                    statements.push(else_branch);
                }
                CStatement::While {
                    test,
                    condition,
                    body,
                    ..
                }
                | CStatement::DoWhile {
                    test,
                    condition,
                    body,
                    ..
                } => {
                    if self.expression_contains_lowerable_expression(condition) {
                        return true;
                    }
                    statements.push(body);
                    if let Some(test) = test {
                        statements.push(test);
                    }
                }
                CStatement::For {
                    test,
                    initializer,
                    condition,
                    step,
                    body,
                    ..
                } => {
                    if self.expression_contains_lowerable_expression(condition) {
                        return true;
                    }
                    statements.push(initializer);
                    statements.push(step);
                    statements.push(body);
                    if let Some(test) = test {
                        statements.push(test);
                    }
                }
                CStatement::Switch {
                    expression, cases, ..
                } => {
                    if self.expression_contains_lowerable_expression(expression) {
                        return true;
                    }
                    for case in cases {
                        statements.push(&case.body);
                    }
                }
                CStatement::Label { statement, .. } => statements.push(statement),
                CStatement::EndAggregateLifetimes { .. }
                | CStatement::FillArrayTail { .. }
                | CStatement::Skip
                | CStatement::Break
                | CStatement::Continue
                | CStatement::Goto { .. }
                | CStatement::Declare {
                    initializer: None, ..
                }
                | CStatement::DeclareStructValue { .. } => {}
                CStatement::Declare {
                    initializer: Some(expression),
                    ..
                } => {
                    if self.expression_contains_lowerable_expression(expression) {
                        return true;
                    }
                }
            }
        }
        false
    }

    fn expression_contains_lowerable_expression(&self, expression: &CExpression) -> bool {
        let mut expressions = vec![expression];
        while let Some(expression) = expressions.pop() {
            if self.aggregate_struct_name(expression).is_some() {
                return true;
            }
            match expression {
                CExpression::Call { .. }
                | CExpression::IndirectCall { .. }
                | CExpression::Assignment { .. }
                | CExpression::ScalarUpdate { .. }
                | CExpression::StatementExpression { .. } => return true,
                CExpression::Cast { expression, .. }
                | CExpression::FloatNegate(expression)
                | CExpression::FloatClassification { expression, .. }
                | CExpression::AddressOf(expression)
                | CExpression::PointerOffsetBytes {
                    pointer: expression,
                    ..
                }
                | CExpression::Subobject {
                    pointer: expression,
                    ..
                }
                | CExpression::Not(expression)
                | CExpression::BitwiseNot(expression)
                | CExpression::Load(expression, _) => expressions.push(expression),
                CExpression::SequentialRead { target, .. } => expressions.push(target),
                CExpression::SequentialWrite { .. } => return true,
                CExpression::AggregateAddress { pointer, .. }
                | CExpression::UnionAddress { pointer, .. }
                | CExpression::Field { pointer, .. }
                | CExpression::UnionField { pointer, .. } => expressions.push(pointer),
                CExpression::CheckedArrayIndex { .. } => return true,
                CExpression::Ternary {
                    condition,
                    then_branch,
                    else_branch,
                } => {
                    expressions.push(condition);
                    expressions.push(then_branch);
                    expressions.push(else_branch);
                }
                crate::languages::c::syntax::binary_c_expression!(left, right) => {
                    expressions.push(left);
                    expressions.push(right);
                }
                CExpression::StringLiteral(_)
                | CExpression::Void
                | CExpression::Variable(_)
                | CExpression::StepResult { .. }
                | CExpression::FunctionAddress(_)
                | CExpression::Int32Literal(_)
                | CExpression::UInt8Literal(_)
                | CExpression::UInt32Literal(_)
                | CExpression::Int64Literal(_)
                | CExpression::UInt64Literal(_)
                | CExpression::Float32Literal(_)
                | CExpression::Float64Literal(_)
                | CExpression::SizeOfStruct { .. }
                | CExpression::SizeOfUnion { .. }
                | CExpression::SizeOfType { .. } => {}
            }
        }
        false
    }

    fn expression_has_runtime_effect(&self, expression: &CExpression) -> bool {
        let mut expressions = vec![expression];
        while let Some(expression) = expressions.pop() {
            match expression {
                CExpression::Call { .. }
                | CExpression::IndirectCall { .. }
                | CExpression::Assignment { .. }
                | CExpression::ScalarUpdate { .. }
                | CExpression::StatementExpression { .. } => return true,
                CExpression::Cast { expression, .. }
                | CExpression::FloatNegate(expression)
                | CExpression::FloatClassification { expression, .. }
                | CExpression::AddressOf(expression)
                | CExpression::PointerOffsetBytes {
                    pointer: expression,
                    ..
                }
                | CExpression::Subobject {
                    pointer: expression,
                    ..
                }
                | CExpression::Not(expression)
                | CExpression::BitwiseNot(expression)
                | CExpression::Load(expression, _) => expressions.push(expression),
                CExpression::SequentialRead { target, .. } => expressions.push(target),
                CExpression::SequentialWrite { .. } => return true,
                CExpression::AggregateAddress { pointer, .. }
                | CExpression::UnionAddress { pointer, .. }
                | CExpression::Field { pointer, .. }
                | CExpression::UnionField { pointer, .. } => expressions.push(pointer),
                CExpression::Ternary {
                    condition,
                    then_branch,
                    else_branch,
                } => {
                    expressions.push(condition);
                    expressions.push(then_branch);
                    expressions.push(else_branch);
                }
                crate::languages::c::syntax::binary_c_expression!(left, right) => {
                    expressions.push(left);
                    expressions.push(right);
                }
                CExpression::StringLiteral(_)
                | CExpression::Void
                | CExpression::Variable(_)
                | CExpression::StepResult { .. }
                | CExpression::FunctionAddress(_)
                | CExpression::Int32Literal(_)
                | CExpression::UInt8Literal(_)
                | CExpression::UInt32Literal(_)
                | CExpression::Int64Literal(_)
                | CExpression::UInt64Literal(_)
                | CExpression::Float32Literal(_)
                | CExpression::Float64Literal(_)
                | CExpression::SizeOfStruct { .. }
                | CExpression::SizeOfUnion { .. }
                | CExpression::SizeOfType { .. }
                | CExpression::CheckedArrayIndex { .. } => {}
            }
        }
        false
    }

    /// Whether evaluating `expression` outside one of its embedded calls reads
    /// mutable runtime state. Call bodies can change any mutable scalar or
    /// memory cell visible through aliases, so such a read cannot safely stay
    /// behind a hoisted call when C leaves their relative order unspecified.
    ///
    /// This deliberately recognizes only the small, demonstrably stable
    /// boundary needed by call lowering. It does not attempt per-call effect
    /// analysis: constants, fixed object addresses, array decay, and automatic
    /// scalar cells whose address is never formed are stable; memory loads,
    /// static-storage scalars, and address-exposed automatic scalars are not.
    fn expression_reads_potentially_changed_value(&self, expression: &CExpression) -> bool {
        match expression {
            // A call's result is the term the call returned: nothing the
            // statement does afterwards changes it.
            CExpression::StepResult { .. } => false,
            CExpression::StringLiteral(_)
            | CExpression::Void
            | CExpression::Call { .. }
            | CExpression::IndirectCall { .. }
            | CExpression::FunctionAddress(_)
            | CExpression::StatementExpression { .. }
            | CExpression::Int32Literal(_)
            | CExpression::UInt8Literal(_)
            | CExpression::UInt32Literal(_)
            | CExpression::Int64Literal(_)
            | CExpression::UInt64Literal(_)
            | CExpression::Float32Literal(_)
            | CExpression::Float64Literal(_)
            | CExpression::SizeOfStruct { .. }
            | CExpression::SizeOfUnion { .. }
            | CExpression::SizeOfType { .. } => false,
            CExpression::ScalarUpdate { .. } => true,
            CExpression::Assignment { value, .. } => {
                self.expression_reads_potentially_changed_value(value)
            }
            CExpression::Variable(name) => {
                if self.variable_is_constant(name) {
                    return false;
                }
                if self.variable_struct_values.contains_key(name) {
                    return true;
                }
                let is_array = matches!(
                    self.variable_types.get(name),
                    Some(
                        InterfaceType::Int8Array(_)
                            | InterfaceType::Int16Array(_)
                            | InterfaceType::Int32Array(_)
                            | InterfaceType::CharArray(_, _)
                            | InterfaceType::UInt8Array(_)
                            | InterfaceType::UInt16Array(_)
                            | InterfaceType::UInt32Array(_)
                            | InterfaceType::Int128Array(_)
                            | InterfaceType::Int64Array(_, _)
                            | InterfaceType::UInt128Array(_)
                            | InterfaceType::UInt64Array(_, _)
                            | InterfaceType::Float32Array(_)
                            | InterfaceType::Float64Array(_)
                    )
                );
                !is_array
                    && (self.address_taken_variables.contains(name)
                        || self.variable_has_static_storage(name))
            }
            CExpression::AddressOf(target) => {
                self.lvalue_address_reads_potentially_changed_value(target)
            }
            CExpression::Load(_, _)
            | CExpression::SequentialRead { .. }
            | CExpression::SequentialWrite { .. }
            | CExpression::Field { .. }
            | CExpression::UnionField { .. }
            | CExpression::AggregateAddress { .. }
            | CExpression::UnionAddress { .. }
            | CExpression::Index(_, _, _) => true,
            CExpression::Cast { expression, .. }
            | CExpression::FloatNegate(expression)
            | CExpression::FloatClassification { expression, .. }
            | CExpression::PointerOffsetBytes {
                pointer: expression,
                ..
            }
            | CExpression::Subobject {
                pointer: expression,
                ..
            }
            | CExpression::Not(expression)
            | CExpression::BitwiseNot(expression)
            | CExpression::CheckedArrayIndex {
                index: expression, ..
            } => self.expression_reads_potentially_changed_value(expression),
            CExpression::Ternary {
                condition,
                then_branch,
                else_branch,
            } => {
                self.expression_reads_potentially_changed_value(condition)
                    || self.expression_reads_potentially_changed_value(then_branch)
                    || self.expression_reads_potentially_changed_value(else_branch)
            }
            crate::languages::c::syntax::binary_c_operation!(left, right) => {
                self.expression_reads_potentially_changed_value(left)
                    || self.expression_reads_potentially_changed_value(right)
            }
        }
    }

    /// Address formation does not read the designated object, but it can read
    /// mutable pointer and index values used to find that object.
    fn lvalue_address_reads_potentially_changed_value(&self, expression: &CExpression) -> bool {
        match expression {
            CExpression::Variable(_) => false,
            CExpression::Load(pointer, _) => {
                self.expression_reads_potentially_changed_value(pointer)
            }
            CExpression::Index(base, index, _) => {
                self.expression_reads_potentially_changed_value(base)
                    || self.expression_reads_potentially_changed_value(index)
            }
            CExpression::Field { pointer, .. }
            | CExpression::UnionField { pointer, .. }
            | CExpression::AggregateAddress { pointer, .. }
            | CExpression::UnionAddress { pointer, .. } => {
                self.expression_reads_potentially_changed_value(pointer)
            }
            expression => self.expression_reads_potentially_changed_value(expression),
        }
    }

    fn variable_has_static_storage(&self, name: &BindingName) -> bool {
        self.static_locals.contains_key(name)
            || self
                .globals
                .values()
                .any(|global| name == global.kernel_name())
    }

    fn convert_struct_array_decay(
        &self,
        target: &BindingName,
        expression: CExpression,
    ) -> CExpression {
        let Some(interface_type) = self
            .variable_types
            .get(target)
            .copied()
            .filter(|ty| ty.is_pointer())
        else {
            return expression;
        };
        let Some(struct_name) = self.variable_structs.get(target) else {
            return expression;
        };
        if matches!(
            self.source_expression_type(&expression),
            Some(InterfaceType::UInt8Array(_))
        ) && self.struct_pointer_name(&expression).as_ref() == Some(struct_name)
        {
            CExpression::Cast {
                expression: Box::new(expression),
                interface_type,
                struct_name: Some(struct_name.clone()),
                pointee_volatile: false,
                pointee_constant: self.variable_pointee_is_constant(target),
                explicit_qualification: false,
            }
        } else {
            expression
        }
    }

    /// Lowers embedded calls in a statement. Only the arms that nest
    /// statements recurse; every other statement is lowered by
    /// [`Self::lower_flat_statement_calls`], kept out of line so that each
    /// level of statement nesting costs one small frame, not the
    /// locals of every statement kind (zlib's `DO16` nests deeply).
    fn lower_statement_calls(&mut self, statement: CStatement) -> Result<CStatement, CSyntaxError> {
        match statement {
            CStatement::Seq(first, second) => Ok(CStatement::Seq(
                Box::new(self.lower_statement_calls(*first)?),
                Box::new(self.lower_statement_calls(*second)?),
            )),
            CStatement::If {
                condition,
                then_branch,
                else_branch,
                site,
                operator,
            } => {
                let start = self.aggregate_expression_steps.len();
                let (prefix, condition) = self.lower_expression_calls(condition)?;
                let steps = self
                    .aggregate_expression_steps
                    .drain(start..)
                    .collect::<Vec<_>>();
                let before_arm = |arm| {
                    if steps.is_empty() {
                        arm
                    } else {
                        CStatement::Seq(
                            Box::new(CStatement::EndAggregateLifetimes {
                                names: Vec::new(),
                                steps: steps.clone(),
                                site: CSite::NONE,
                            }),
                            Box::new(arm),
                        )
                    }
                };
                let then_branch = before_arm(self.lower_statement_calls(*then_branch)?);
                let else_branch = before_arm(self.lower_statement_calls(*else_branch)?);
                Ok(prepend_statements(
                    prefix,
                    CStatement::If {
                        condition,
                        then_branch: Box::new(then_branch),
                        else_branch: Box::new(else_branch),
                        site,
                        operator,
                    },
                ))
            }
            CStatement::While {
                test,
                condition,
                body,
                site,
            } => {
                let start = self.aggregate_expression_steps.len();
                let (prefix, condition) = self.lower_expression_calls(condition)?;
                let aggregate_steps = self
                    .aggregate_expression_steps
                    .drain(start..)
                    .collect::<Vec<_>>();
                let body = self.lower_statement_calls(*body)?;
                let (test, condition) = if prefix.is_empty() {
                    (test, condition)
                } else {
                    (
                        Some(Box::new(prepend_statements(
                            prefix,
                            CStatement::LoopTest {
                                aggregate_steps,
                                condition,
                                site: site.clone(),
                            },
                        ))),
                        CExpression::Int32Literal(1),
                    )
                };
                Ok(CStatement::While {
                    test,
                    condition,
                    body: Box::new(body),
                    site,
                })
            }
            CStatement::DoWhile {
                test,
                condition,
                body,
                site,
            } => {
                let start = self.aggregate_expression_steps.len();
                let (prefix, condition) = self.lower_expression_calls(condition)?;
                let aggregate_steps = self
                    .aggregate_expression_steps
                    .drain(start..)
                    .collect::<Vec<_>>();
                let body = self.lower_statement_calls(*body)?;
                let (test, condition) = if prefix.is_empty() {
                    (test, condition)
                } else {
                    (
                        Some(Box::new(prepend_statements(
                            prefix,
                            CStatement::LoopTest {
                                aggregate_steps,
                                condition,
                                site: site.clone(),
                            },
                        ))),
                        CExpression::Int32Literal(1),
                    )
                };
                Ok(CStatement::DoWhile {
                    test,
                    condition,
                    body: Box::new(body),
                    site,
                })
            }
            CStatement::For {
                test,
                initializer,
                condition,
                step,
                body,
                site,
            } => {
                let start = self.aggregate_expression_steps.len();
                let (prefix, condition) = self.lower_expression_calls(condition)?;
                let aggregate_steps = self
                    .aggregate_expression_steps
                    .drain(start..)
                    .collect::<Vec<_>>();
                let initializer = self.lower_statement_calls(*initializer)?;
                let step = self.lower_statement_calls(*step)?;
                let body = self.lower_statement_calls(*body)?;
                let (test, condition) = if prefix.is_empty() {
                    (test, condition)
                } else {
                    (
                        Some(Box::new(prepend_statements(
                            prefix,
                            CStatement::LoopTest {
                                aggregate_steps,
                                condition,
                                site: site.clone(),
                            },
                        ))),
                        CExpression::Int32Literal(1),
                    )
                };
                Ok(CStatement::For {
                    test,
                    initializer: Box::new(initializer),
                    condition,
                    step: Box::new(step),
                    body: Box::new(body),
                    site,
                })
            }
            CStatement::Switch {
                expression,
                cases,
                site,
            } => {
                let start = self.aggregate_expression_steps.len();
                let (prefix, expression) = self.lower_expression_calls(expression)?;
                let steps = self
                    .aggregate_expression_steps
                    .drain(start..)
                    .collect::<Vec<_>>();
                let cases = cases
                    .into_iter()
                    .map(|case| {
                        Ok(CSwitchCase {
                            value: case.value,
                            body: Box::new({
                                let body = self.lower_statement_calls(*case.body)?;
                                if steps.is_empty() {
                                    body
                                } else {
                                    CStatement::Seq(
                                        Box::new(CStatement::EndAggregateLifetimes {
                                            names: Vec::new(),
                                            steps: steps.clone(),
                                            site: CSite::NONE,
                                        }),
                                        Box::new(body),
                                    )
                                }
                            }),
                        })
                    })
                    .collect::<Result<Vec<_>, CSyntaxError>>()?;
                let lowered = prepend_statements(
                    prefix,
                    CStatement::Switch {
                        expression,
                        cases,
                        site: site.clone(),
                    },
                );
                Ok(if steps.is_empty() {
                    lowered
                } else {
                    CStatement::Seq(
                        Box::new(lowered),
                        Box::new(CStatement::EndAggregateLifetimes {
                            names: Vec::new(),
                            steps,
                            site,
                        }),
                    )
                })
            }
            statement => self.lower_flat_statement_calls(statement),
        }
    }

    /// [`Self::lower_statement_calls`] for a statement that nests no
    /// statement.
    #[inline(never)]
    fn lower_flat_statement_calls(
        &mut self,
        statement: CStatement,
    ) -> Result<CStatement, CSyntaxError> {
        let start = self.aggregate_expression_steps.len();
        let site = statement.site().cloned().unwrap_or(CSite::NONE);
        let is_return = matches!(statement, CStatement::Return(..));
        let lowered = self.lower_flat_statement_calls_inner(statement)?;
        let steps = self
            .aggregate_expression_steps
            .drain(start..)
            .collect::<Vec<_>>();
        if steps.is_empty() || is_return {
            return Ok(lowered);
        }
        Ok(CStatement::Seq(
            Box::new(lowered),
            Box::new(CStatement::EndAggregateLifetimes {
                names: Vec::new(),
                steps,
                site,
            }),
        ))
    }

    fn lower_flat_statement_calls_inner(
        &mut self,
        statement: CStatement,
    ) -> Result<CStatement, CSyntaxError> {
        match statement {
            CStatement::EndAggregateLifetimes { .. }
            | CStatement::FillArrayTail { .. }
            | CStatement::Skip
            | CStatement::Break
            | CStatement::Continue
            | CStatement::Goto { .. }
            | CStatement::Declare {
                initializer: None, ..
            }
            | CStatement::DeclareStructValue { .. } => Ok(statement),
            CStatement::Declare {
                initializer: Some(expression),
                interface_type,
                name,
                volatile,
                pointee_volatile,
                constant,
                pointee_constant,
                zero_fill,
                declared_class,
                site,
            } => {
                let (prefix, expression) = self.lower_expression_calls(expression)?;
                Ok(prepend_statements(
                    prefix,
                    CStatement::Declare {
                        initializer: Some(expression),
                        interface_type,
                        name,
                        volatile,
                        pointee_volatile,
                        constant,
                        pointee_constant,
                        zero_fill,
                        declared_class,
                        site,
                    },
                ))
            }
            CStatement::Label {
                name,
                statement,
                position,
                direct_function_body,
            } => Ok(CStatement::Label {
                name,
                statement: Box::new(self.lower_statement_calls(*statement)?),
                position,
                direct_function_body,
            }),
            CStatement::Assert {
                condition,
                label,
                site,
            } => {
                let (prefix, condition) = self.lower_expression_calls(condition)?;
                Ok(prepend_statements(
                    prefix,
                    CStatement::Assert {
                        condition,
                        label,
                        site,
                    },
                ))
            }
            CStatement::LoopTest {
                condition,
                site,
                mut aggregate_steps,
            } => {
                let start = self.aggregate_expression_steps.len();
                let (prefix, condition) = self.lower_expression_calls(condition)?;
                aggregate_steps.extend(self.aggregate_expression_steps.drain(start..));
                Ok(prepend_statements(
                    prefix,
                    CStatement::LoopTest {
                        condition,
                        site,
                        aggregate_steps,
                    },
                ))
            }
            CStatement::StepValue {
                aggregate_layout,
                steps,
                expression,
                interface_type,
                pointee_constant,
                site,
                ..
            } => {
                let (prefix, expression) = self.lower_expression_calls(expression)?;
                Ok(prepend_statements(
                    prefix,
                    CStatement::StepValue {
                        aggregate_layout,
                        steps,
                        expression,
                        interface_type,
                        pointee_constant,
                        site,
                    },
                ))
            }
            CStatement::Assign {
                name,
                expression,
                site,
                prior_result,
            } => {
                let expression = self.convert_struct_array_decay(&name, expression);
                let (prefix, expression) = self.lower_expression_calls(expression)?;
                Ok(prepend_statements(
                    prefix,
                    CStatement::Assign {
                        name,
                        expression,
                        site,
                        prior_result,
                    },
                ))
            }
            CStatement::Call {
                function_name,
                arguments,
                site,
                callee,
            } => {
                let (prefix, arguments) = self.lower_call_arguments(arguments)?;
                Ok(prepend_statements(
                    prefix,
                    CStatement::Call {
                        function_name,
                        arguments,
                        site,
                        callee,
                    },
                ))
            }
            statement @ CStatement::CallResult { .. } => Ok(statement),
            CStatement::IndirectCall {
                function,
                signature,
                arguments,
                position,
                site,
            } => {
                self.validate_function_designator_argument_order(&function, &arguments)?;
                let (mut prefix, function) = self.lower_expression_calls(function)?;
                let (argument_prefix, arguments) = self.lower_call_arguments(arguments)?;
                if prefix_has_non_assertion(&prefix) && prefix_has_non_assertion(&argument_prefix) {
                    return Err(self.error_at_position(
                        position,
                        "multiple unsequenced calls in one expression are not supported",
                    ));
                }
                prefix.extend(argument_prefix);
                // The call goes through the pointer itself, named as the
                // source writes it.
                let function_name = callee_source_text(&function);
                self.callback_statement_sources
                    .insert((function_name.clone()).into(), function.clone());
                prefix.push(CStatement::Call {
                    function_name,
                    arguments,
                    callee: Some(CCallee {
                        pointer: function,
                        signature,
                    }),
                    site,
                });
                Ok(balanced_statement_sequence(prefix)
                    .expect("indirect call has a non-empty prefix"))
            }
            CStatement::HeapAllocate {
                target,
                bytes,
                zeroed,
                object_type,
                site,
            } => {
                let (prefix, bytes) = self.lower_expression_calls(bytes)?;
                Ok(prepend_statements(
                    prefix,
                    CStatement::HeapAllocate {
                        target,
                        bytes,
                        zeroed,
                        object_type,
                        site,
                    },
                ))
            }
            CStatement::HeapFree { pointer, site } => {
                let (prefix, pointer) = self.lower_expression_calls(pointer)?;
                Ok(prepend_statements(
                    prefix,
                    CStatement::HeapFree { pointer, site },
                ))
            }
            CStatement::Return(expression, site) => {
                let (prefix, expression) = self.lower_expression_calls(expression)?;
                Ok(prepend_statements(
                    prefix,
                    CStatement::Return(expression, site),
                ))
            }
            CStatement::Store {
                pointer,
                value,
                value_type,
                lvalue_class,
                pointee_constant,
                site,
            } => {
                let (prefix, pointer, value) = self.lower_expression_pair(pointer, value)?;
                Ok(prepend_statements(
                    prefix,
                    CStatement::Store {
                        pointer,
                        value,
                        value_type,
                        lvalue_class,
                        pointee_constant,
                        site,
                    },
                ))
            }
            CStatement::SequentialStore {
                target,
                value,
                value_type,
                pointee_constant,
                site,
            } => {
                // The macro contract evaluates the value into a temporary
                // before evaluating the destination access. This makes the
                // one-access guarantee explicit even if either argument
                // contains a lowerable call or checked index.
                let (mut prefix, value) = self.lower_expression_calls(value)?;
                let (target_prefix, target) = self.lower_expression_calls(target)?;
                prefix.extend(target_prefix);
                Ok(prepend_statements(
                    prefix,
                    CStatement::SequentialStore {
                        target,
                        value,
                        value_type,
                        pointee_constant,
                        site,
                    },
                ))
            }
            CStatement::AggregateCopy {
                target,
                source,
                layout,
                site,
            } => {
                let (prefix, target, source) = self.lower_expression_pair(target, source)?;
                Ok(prepend_statements(
                    prefix,
                    CStatement::AggregateCopy {
                        target,
                        source,
                        layout,
                        site,
                    },
                ))
            }
            CStatement::Update {
                target,
                operator,
                operand,
                site,
            } => {
                let (prefix, target, operand) = self.lower_expression_pair(target, operand)?;
                Ok(prepend_statements(
                    prefix,
                    CStatement::Update {
                        target,
                        operator,
                        operand,
                        site,
                    },
                ))
            }
            CStatement::Seq(..)
            | CStatement::If { .. }
            | CStatement::While { .. }
            | CStatement::DoWhile { .. }
            | CStatement::For { .. }
            | CStatement::Switch { .. } => {
                unreachable!("nested statements are lowered by lower_statement_calls")
            }
        }
    }

    fn lower_call_arguments(
        &mut self,
        arguments: Vec<CExpression>,
    ) -> Result<(Vec<CStatement>, Vec<CExpression>), CSyntaxError> {
        let mut prefix = Vec::new();
        let mut lowered_arguments = Vec::with_capacity(arguments.len());
        let mut earlier_call_position = None;
        let mut earlier_argument_reads = false;
        let mut earlier_assignment_position = None;
        let mut earlier_argument_value_reads = false;
        for argument in arguments {
            let argument_position = first_embedded_call_position(&argument);
            let assignment_position = first_assignment_position(&argument);
            let argument_reads = self.expression_reads_potentially_changed_value(&argument);
            let argument_value_reads = expression_reads_runtime_value(&argument);
            let (argument_prefix, argument) = self.lower_expression_calls(argument)?;
            if prefix_has_non_assertion(&prefix) && prefix_has_non_assertion(&argument_prefix) {
                if earlier_call_position.is_none() || argument_position.is_none() {
                    return Err(self.error_at_position(
                        assignment_position.clone().or(argument_position.clone()),
                        "multiple unsequenced expression side effects in function arguments are not supported",
                    ));
                }
                return Err(self.error_at_position(
                    argument_position.clone(),
                    "multiple unsequenced calls in one expression are not supported",
                ));
            }
            if argument_reads && let Some(position) = earlier_call_position.clone() {
                return Err(self.error_at_position(
                    Some(position),
                    "an expression call and a potentially aliased read in separate function arguments are not supported",
                ));
            }
            if earlier_argument_reads && argument_position.is_some() {
                return Err(self.error_at_position(
                    argument_position.clone(),
                    "an expression call and a potentially aliased read in separate function arguments are not supported",
                ));
            }
            if argument_value_reads && let Some(position) = earlier_assignment_position.clone() {
                return Err(self.error_at_position(
                    Some(position),
                    "an assignment expression and an unsequenced read in separate function arguments are not supported",
                ));
            }
            if earlier_argument_value_reads && let Some(position) = assignment_position.clone() {
                return Err(self.error_at_position(
                    Some(position),
                    "an assignment expression and an unsequenced read in separate function arguments are not supported",
                ));
            }
            prefix.extend(argument_prefix);
            lowered_arguments.push(argument);
            earlier_argument_reads |= argument_reads;
            earlier_argument_value_reads |= argument_value_reads;
            if earlier_call_position.is_none() {
                earlier_call_position = argument_position;
            }
            if earlier_assignment_position.is_none() {
                earlier_assignment_position = assignment_position;
            }
        }
        Ok((prefix, lowered_arguments))
    }

    fn validate_function_designator_argument_order(
        &self,
        function: &CExpression,
        arguments: &[CExpression],
    ) -> Result<(), CSyntaxError> {
        let argument_call_position = arguments.iter().find_map(first_embedded_call_position);
        if self.expression_reads_potentially_changed_value(function)
            && argument_call_position.is_some()
        {
            return Err(self.error_at_position(
                argument_call_position,
                "an expression call and a potentially aliased function-designator read are not supported",
            ));
        }
        let function_call_position = first_embedded_call_position(function);
        if function_call_position.is_some()
            && arguments
                .iter()
                .any(|argument| self.expression_reads_potentially_changed_value(argument))
        {
            return Err(self.error_at_position(
                function_call_position,
                "an expression call and a potentially aliased argument read are not supported",
            ));
        }
        Ok(())
    }

    /// Whether evaluating `expression` reads nothing but named scalar
    /// locals outside `assigned`: no load through a pointer, no call, no
    /// static object, and no aggregate value. Such an evaluation cannot
    /// read or write any object an assignment to a name in `assigned`
    /// modifies, whatever the program's aliasing.
    fn reads_only_locals_other_than(
        &self,
        expression: &CExpression,
        assigned: &[BindingName],
    ) -> bool {
        match expression {
            // Taking an object's address does not read its stored value,
            // even when an unsequenced operand updates a scalar local.
            CExpression::AddressOf(target)
                if matches!(target.as_ref(), CExpression::Variable(_)) =>
            {
                true
            }
            CExpression::Int32Literal(_)
            | CExpression::UInt8Literal(_)
            | CExpression::UInt32Literal(_)
            | CExpression::Int64Literal(_)
            | CExpression::UInt64Literal(_) => true,
            CExpression::Variable(name)
                if self
                    .variable_types
                    .get(name)
                    .is_some_and(|ty| ty.array_length().is_some()) =>
            {
                // Decay computes an address, independently of the array's contents.
                true
            }
            CExpression::Add(base, offset)
                if matches!(offset.as_ref(), CExpression::Int32Literal(_)) =>
            {
                self.reads_only_locals_other_than(base, assigned)
            }
            CExpression::Variable(name) => {
                !assigned.contains(name)
                    && self.variable_types.contains_key(name)
                    && !self.variable_struct_values.contains_key(name)
                    && !self.variable_has_static_storage(name)
            }
            CExpression::Cast { expression, .. }
            | CExpression::PointerOffsetBytes {
                pointer: expression,
                ..
            }
            | CExpression::Subobject {
                pointer: expression,
                ..
            } => self.reads_only_locals_other_than(expression, assigned),
            _ => false,
        }
    }

    fn lower_expression_pair(
        &mut self,
        left: CExpression,
        right: CExpression,
    ) -> Result<(Vec<CStatement>, CExpression, CExpression), CSyntaxError> {
        let left_position = first_embedded_call_position(&left);
        let right_position = first_embedded_call_position(&right);
        let left_assignment = first_assignment_position(&left);
        let right_assignment = first_assignment_position(&right);
        let left_reads = self.expression_reads_potentially_changed_value(&left);
        let right_reads = self.expression_reads_potentially_changed_value(&right);
        let left_value_reads = expression_reads_runtime_value(&left);
        let right_value_reads = expression_reads_runtime_value(&right);
        // An assignment's side effect is unsequenced relative to the other
        // operand, which C leaves undefined only when that operand reads or
        // writes the assigned object. An operand built solely from direct
        // reads of other named locals cannot touch it.
        let left_disjoint_from_right_assignment = assignment_chain_targets(&right)
            .is_some_and(|targets| self.reads_only_locals_other_than(&left, &targets));
        let right_disjoint_from_left_assignment = assignment_chain_targets(&left)
            .is_some_and(|targets| self.reads_only_locals_other_than(&right, &targets));
        // A call is indeterminately sequenced with a read in the other
        // operand. When that read is of named non-volatile static storage,
        // both orders are checked rather than one chosen: see
        // `sequence_reread_around_call`.
        let left_rereads = (left_reads && right_position.is_some())
            .then(|| self.reread_storage_names(&left))
            .flatten();
        let right_rereads = (right_reads && left_position.is_some())
            .then(|| self.reread_storage_names(&right))
            .flatten();
        let (left_prefix, left) = self.lower_expression_calls(left)?;
        let (right_prefix, right) = self.lower_expression_calls(right)?;
        if let Some(names) = right_rereads
            && right_prefix.is_empty()
            && prefix_has_non_assertion(&left_prefix)
        {
            let prefix = self.sequence_reread_around_call(&names, left_prefix);
            return Ok((prefix, left, right));
        }
        if let Some(names) = left_rereads
            && left_prefix.is_empty()
            && prefix_has_non_assertion(&right_prefix)
        {
            let prefix = self.sequence_reread_around_call(&names, right_prefix);
            return Ok((prefix, left, right));
        }
        if prefix_has_non_assertion(&left_prefix) && prefix_has_non_assertion(&right_prefix) {
            if left_position.is_none() || right_position.is_none() {
                return Err(self.error_at_position(
                    right_assignment.clone().or(right_position.clone()),
                    "multiple unsequenced expression side effects are not supported",
                ));
            }
            return Err(self.error_at_position(
                right_position.clone(),
                "multiple unsequenced calls in one expression are not supported",
            ));
        }
        if right_reads && left_position.is_some() {
            return Err(self.error_at_position(
                left_position,
                "an expression call and a potentially aliased operand read are not supported",
            ));
        }
        if left_reads && right_position.is_some() {
            return Err(self.error_at_position(
                right_position,
                "an expression call and a potentially aliased operand read are not supported",
            ));
        }
        if right_value_reads
            && !right_disjoint_from_left_assignment
            && let Some(position) = left_assignment
        {
            return Err(self.error_at_position(
                Some(position),
                "an assignment expression and an unsequenced operand read are not supported",
            ));
        }
        if left_value_reads
            && !left_disjoint_from_right_assignment
            && let Some(position) = right_assignment
        {
            return Err(self.error_at_position(
                Some(position),
                "an assignment expression and an unsequenced operand read are not supported",
            ));
        }
        let mut prefix = left_prefix;
        prefix.extend(right_prefix);
        Ok((prefix, left, right))
    }

    /// The static-storage names an operand reads, when it is safe to read it
    /// again on the other side of an indeterminately sequenced call: built
    /// only from integer literals, casts, integer arithmetic and named
    /// non-volatile, non-floating scalar objects, so a second read has no
    /// effect and the same value means the same result. Locals the call
    /// cannot reach need no state. `None` keeps the existing refusal.
    fn reread_storage_names(&self, expression: &CExpression) -> Option<Vec<BindingName>> {
        match expression {
            CExpression::Int32Literal(_)
            | CExpression::UInt8Literal(_)
            | CExpression::UInt32Literal(_)
            | CExpression::Int64Literal(_)
            | CExpression::UInt64Literal(_) => Some(Vec::new()),
            CExpression::Variable(name) => {
                if self.variable_struct_values.contains_key(name) {
                    return None;
                }
                let interface_type = self.variable_types.get(name).copied()?;
                // Integer and object-pointer values compare exactly; a float
                // can be NaN, which `==` would refuse spuriously.
                let integer = matches!(
                    interface_type,
                    InterfaceType::Bool
                        | InterfaceType::Int8
                        | InterfaceType::Int16
                        | InterfaceType::Int32
                        | InterfaceType::Char(_)
                        | InterfaceType::UInt8
                        | InterfaceType::UInt16
                        | InterfaceType::UInt32
                        | InterfaceType::Int64(_)
                        | InterfaceType::UInt64(_)
                );
                if !(integer || interface_type.is_object_pointer()) {
                    return None;
                }
                let volatile = if let Some(global) = self
                    .globals
                    .values()
                    .find(|global| name == global.kernel_name())
                {
                    global.is_volatile()
                } else if let Some(static_local) = self.static_locals.get(name) {
                    static_local.is_volatile()
                } else if self.address_taken_variables.contains(name) {
                    // An address-taken local's qualifiers are not tracked here.
                    return None;
                } else {
                    return Some(Vec::new());
                };
                (!volatile).then(|| vec![name.clone()])
            }
            CExpression::Cast { expression, .. } => self.reread_storage_names(expression),
            CExpression::Add(left, right)
            | CExpression::Subtract(left, right)
            | CExpression::Multiply(left, right)
            | CExpression::BitwiseAnd(left, right)
            | CExpression::BitwiseOr(left, right)
            | CExpression::BitwiseXor(left, right) => {
                let mut names = self.reread_storage_names(left)?;
                for name in self.reread_storage_names(right)? {
                    if !names.contains(&name) {
                        names.push(name);
                    }
                }
                Some(names)
            }
            _ => None,
        }
    }

    /// C leaves a call and a read in the other operand indeterminately
    /// sequenced, so either may happen first. Rather than choose an order,
    /// read each named object before the call, run the call, and require it
    /// to hold the same value afterwards: the read must then be defined in
    /// both orders and give one value. The operand itself is evaluated after
    /// the call, as the lowering always has.
    fn sequence_reread_around_call(
        &mut self,
        names: &[BindingName],
        call_prefix: Vec<CStatement>,
    ) -> Vec<CStatement> {
        let mut prefix = Vec::new();
        let mut checks = Vec::new();
        for name in names {
            let interface_type = self.variable_types[name];
            let pointee_constant = self.variable_pointee_constants.contains(name);
            let step = self.next_call_result;
            self.next_call_result = self.next_call_result.saturating_add(1);
            prefix.push(CStatement::StepValue {
                aggregate_layout: None,
                steps: vec![step],
                expression: CExpression::Variable(name.clone()),
                interface_type: Some(interface_type),
                pointee_constant,
                site: CSite::NONE,
            });
            checks.push(CStatement::Assert {
                condition: CExpression::Equal(
                    Box::new(CExpression::Variable(name.clone())),
                    Box::new(CExpression::StepResult {
                        step,
                        origin: crate::kernel::StepOrigin::Value("the read before the call"),
                        interface_type: Some(interface_type),
                        pointee_constant,
                        struct_name: None,
                    }),
                ),
                label: format!(
                    "the call leaves `{name}`, read in the other operand, unchanged, so the read gives one value in either order"
                ),
                site: CSite::NONE,
            });
        }
        prefix.extend(call_prefix);
        prefix.extend(checks);
        prefix
    }

    fn reject_unsequenced_updated_memory_read(
        &self,
        expression: &CExpression,
    ) -> Result<(), CSyntaxError> {
        let Some(position) = first_assignment_position(expression) else {
            return Ok(());
        };
        if Self::compound_literal_storage_address(expression) {
            return Ok(());
        }
        let Some(targets) = assignment_chain_targets(expression) else {
            return Err(self.error_at_position(Some(position),
                "an expression update and a potentially aliased memory read require a separation model"));
        };
        if targets.iter().any(|name| {
            self.address_taken_variables.contains(name) || self.variable_has_static_storage(name)
        }) {
            return Err(self.error_at_position(Some(position),
                "an expression update and a potentially aliased memory read require a separation model"));
        }
        Ok(())
    }

    fn lower_expression_calls(
        &mut self,
        expression: CExpression,
    ) -> Result<(Vec<CStatement>, CExpression), CSyntaxError> {
        match expression {
            CExpression::ScalarUpdate {
                name,
                increment,
                prefix: result_is_updated,
                interface_type,
                struct_name,
                pointee_constant,
                ..
            } => {
                // The update is an assignment step of its own. `++x` is the
                // value `x` holds after it; `x++` the value it held before,
                // which the step keeps as its result.
                let update = self.scale_struct_pointer_arithmetic(
                    CExpression::Variable(name.clone()),
                    CExpression::Int32Literal(1),
                    if increment {
                        CExpression::Add
                    } else {
                        CExpression::Subtract
                    },
                )?;
                let step = (!result_is_updated).then(|| {
                    let step = self.next_call_result;
                    self.next_call_result = self.next_call_result.saturating_add(1);
                    step
                });
                let value = match step {
                    Some(step) => CExpression::StepResult {
                        step,
                        origin: crate::kernel::StepOrigin::Prior(name.source_name().to_owned()),
                        interface_type: Some(interface_type),
                        pointee_constant,
                        struct_name,
                    },
                    None => CExpression::Variable(name.clone()),
                };
                Ok((
                    vec![CStatement::Assign {
                        name,
                        expression: update,
                        prior_result: step,
                        site: CSite::NONE,
                    }],
                    value,
                ))
            }
            CExpression::Assignment { name, value, .. } => {
                let value = self.convert_struct_array_decay(&name, *value);
                let (mut prefix, value) = self.lower_expression_calls(value)?;
                // The assignment is a step of its own; the expression's value
                // is the target's value after it, which C gives the
                // assignment (C11 6.5.16p3). A volatile target is read again,
                // which may give any value, as C permits.
                prefix.push(CStatement::Assign {
                    name: name.clone(),
                    expression: value,
                    site: CSite::NONE,
                    prior_result: None,
                });
                Ok((prefix, CExpression::Variable(name)))
            }
            CExpression::Call {
                function_name,
                arguments,
                position,
            } => {
                if matches!(
                    function_name.as_str(),
                    "malloc" | "calloc" | "realloc" | "free"
                ) {
                    return Err(self.error_at_position(
                        position,
                        "allocation and deallocation builtins must be used in statement form",
                    ));
                }
                let (mut prefix, arguments) = self.lower_call_arguments(arguments)?;
                let return_struct_name = self
                    .function_declaration(&function_name)
                    .and_then(|function| function.return_struct_name.clone());
                if let Some(struct_name) = return_struct_name {
                    let layout = self.structs.get(&struct_name).cloned().ok_or_else(|| {
                        self.error_here(format!("unknown struct declaration `{struct_name}`"))
                    })?;
                    let call = self.next_call_result;
                    self.next_call_result = self.next_call_result.saturating_add(1);
                    self.aggregate_expression_steps.push(call);
                    prefix.push(CStatement::CallResult {
                        call,
                        function_name: function_name.clone(),
                        arguments,
                        result_type: None,
                        result_pointee_constant: false,
                        result_aggregate_layout: Some(layout.clone()),
                        aggregate_layout: Some(layout),
                        callee: None,
                        site: CSite::NONE,
                    });
                    return Ok((
                        prefix,
                        CExpression::StepResult {
                            step: call,
                            origin: crate::kernel::StepOrigin::Call(function_name),
                            interface_type: Some(InterfaceType::Int32),
                            pointee_constant: false,
                            struct_name: Some(struct_name),
                        },
                    ));
                }
                // The call is a step of its own; the rest of the expression
                // reads the term it returns by the call's number.
                let call = self.next_call_result;
                self.next_call_result = self.next_call_result.saturating_add(1);
                let (interface_type, pointee_constant, struct_name) =
                    if let Some(function) = self.function_declaration_for_call(&function_name) {
                        (
                            Some(function.return_type),
                            function.return_pointee_constant,
                            function.return_pointer_struct_name.clone(),
                        )
                    } else if let Some(signature) = self
                        .variable_function_pointers
                        .get(&self.resolve_name(&function_name))
                    {
                        (
                            Some(signature.return_type),
                            signature.return_pointee_constant,
                            signature.return_struct_name.clone(),
                        )
                    } else if function_name == CONSTANT_P_UNKNOWN {
                        // `__builtin_constant_p` has type `int`.
                        (Some(InterfaceType::Int32), false, None)
                    } else {
                        (None, false, None)
                    };
                prefix.push(CStatement::CallResult {
                    aggregate_layout: None,
                    call,
                    function_name: function_name.clone(),
                    arguments,
                    result_type: interface_type,
                    result_aggregate_layout: None,
                    result_pointee_constant: pointee_constant,
                    site: CSite::NONE,
                    callee: None,
                });
                Ok((
                    prefix,
                    CExpression::StepResult {
                        step: call,
                        origin: crate::kernel::StepOrigin::Call(function_name),
                        interface_type,
                        pointee_constant,
                        struct_name,
                    },
                ))
            }
            CExpression::IndirectCall {
                function,
                signature,
                arguments,
                position,
            } => self.lower_function_pointer_call(*function, signature, arguments, position),
            CExpression::Cast {
                expression,
                interface_type,
                struct_name,
                pointee_volatile,
                pointee_constant,
                explicit_qualification,
            } => {
                let (prefix, expression) = self.lower_expression_calls(*expression)?;
                Ok((
                    prefix,
                    CExpression::Cast {
                        expression: Box::new(expression),
                        interface_type,
                        struct_name,
                        pointee_volatile,
                        pointee_constant,
                        explicit_qualification,
                    },
                ))
            }
            CExpression::Ternary {
                condition,
                then_branch,
                else_branch,
            } => {
                let (mut prefix, condition) = self.lower_expression_calls(*condition)?;
                let (then_prefix, then_branch) = self.lower_expression_calls(*then_branch)?;
                let (else_prefix, else_branch) = self.lower_expression_calls(*else_branch)?;
                let then_struct = self.aggregate_struct_name(&then_branch);
                let else_struct = self.aggregate_struct_name(&else_branch);
                if then_struct != else_struct && (then_struct.is_some() || else_struct.is_some()) {
                    return Err(self.error_here(
                        "conditional aggregate branches must have the same struct type",
                    ));
                }
                if let Some(struct_name) = then_struct {
                    let layout = self.structs.get(&struct_name).cloned().ok_or_else(|| {
                        self.error_here(format!("unknown struct declaration `{struct_name}`"))
                    })?;
                    let step = self.next_call_result;
                    self.next_call_result = self.next_call_result.saturating_add(1);
                    self.aggregate_expression_steps.push(step);
                    let value = |expression| CStatement::StepValue {
                        steps: vec![step],
                        expression,
                        interface_type: None,
                        pointee_constant: false,
                        aggregate_layout: Some(layout.clone()),
                        site: CSite::NONE,
                    };
                    prefix.push(CStatement::If {
                        condition,
                        then_branch: Box::new(prepend_statements(then_prefix, value(then_branch))),
                        else_branch: Box::new(prepend_statements(else_prefix, value(else_branch))),
                        site: CSite::NONE,
                        operator: Some(COperator {
                            kind: crate::kernel::OperatorKind::Ternary,
                            step,
                        }),
                    });
                    return Ok((
                        prefix,
                        CExpression::StepResult {
                            step,
                            origin: crate::kernel::StepOrigin::Operator(
                                crate::kernel::OperatorKind::Ternary,
                            ),
                            interface_type: Some(InterfaceType::Int32),
                            pointee_constant: false,
                            struct_name: Some(struct_name),
                        },
                    ));
                }
                if then_prefix.is_empty() && else_prefix.is_empty() {
                    return Ok((
                        prefix,
                        CExpression::Ternary {
                            condition: Box::new(condition),
                            then_branch: Box::new(then_branch),
                            else_branch: Box::new(else_branch),
                        },
                    ));
                }
                // The ternary operator decides which operand runs: an `if` of
                // its own, whose arms end in its value on their path, with
                // the operator's common result type. Branches whose types are
                // both traceable and genuinely incompatible were rejected by
                // parse-time validation; branches whose types are untraceable
                // (a call to a function defined in another translation unit)
                // keep the inherited scalar ABI slot.
                let interface_type = ternary_expression_type(
                    self.source_expression_type(&then_branch),
                    self.source_expression_type(&else_branch),
                    &then_branch,
                    &else_branch,
                )
                .unwrap_or(InterfaceType::Int32);
                let step = self.next_call_result;
                self.next_call_result = self.next_call_result.saturating_add(1);
                let value = |expression| CStatement::StepValue {
                    aggregate_layout: None,
                    steps: vec![step],
                    expression,
                    interface_type: Some(interface_type),
                    pointee_constant: false,
                    site: CSite::NONE,
                };
                prefix.push(CStatement::If {
                    condition,
                    then_branch: Box::new(prepend_statements(then_prefix, value(then_branch))),
                    else_branch: Box::new(prepend_statements(else_prefix, value(else_branch))),
                    operator: Some(COperator {
                        kind: crate::kernel::OperatorKind::Ternary,
                        step,
                    }),
                    site: CSite::NONE,
                });
                Ok((
                    prefix,
                    CExpression::StepResult {
                        step,
                        origin: crate::kernel::StepOrigin::Operator(
                            crate::kernel::OperatorKind::Ternary,
                        ),
                        interface_type: Some(interface_type),
                        pointee_constant: false,
                        struct_name: None,
                    },
                ))
            }
            CExpression::StatementExpression {
                aggregate_lvalue,
                scope_lifetimes,
                body,
                value,
                interface_type,
                struct_name,
                pointee_constant,
                ..
            } => {
                if aggregate_lvalue {
                    if interface_type.array_length().is_some() {
                        let CExpression::Variable(name) = *value else {
                            unreachable!("an array compound literal has a hidden array binding");
                        };
                        // Only this initializer references the hidden name in the
                        // frontend. Its stores use the fixed address of the array.
                        self.variable_types.insert(name.clone(), interface_type);
                        let body = self.lower_statement_calls(*body);
                        self.variable_types.remove(&name);
                        // The unevaluated contexts already used the array type.
                        // Keep the decayed type on the value for enclosing operators.
                        return Ok((
                            vec![body?],
                            CExpression::Cast {
                                expression: Box::new(CExpression::Variable(name)),
                                interface_type: decay_to_pointer(interface_type),
                                struct_name: None,
                                pointee_volatile: false,
                                pointee_constant: false,
                                explicit_qualification: false,
                            },
                        ));
                    }
                    return Ok((vec![self.lower_statement_calls(*body)?], *value));
                }
                // The body runs, then the value is a step the rest of the
                // expression reads: `S.region(j).result`.
                let body = self.lower_statement_calls(*body)?;
                let (value_prefix, value) = self.lower_expression_calls(*value)?;
                let step = self.next_call_result;
                self.next_call_result = self.next_call_result.saturating_add(1);
                let mut prefix = vec![body];
                prefix.extend(value_prefix);
                prefix.push(CStatement::StepValue {
                    aggregate_layout: None,
                    steps: vec![step],
                    expression: value,
                    interface_type: Some(interface_type),
                    pointee_constant,
                    site: CSite::NONE,
                });
                if !scope_lifetimes.is_empty() {
                    prefix.push(CStatement::EndAggregateLifetimes {
                        names: scope_lifetimes,
                        steps: Vec::new(),
                        site: CSite::NONE,
                    });
                }
                Ok((
                    prefix,
                    CExpression::StepResult {
                        step,
                        origin: crate::kernel::StepOrigin::Value("the statement expression"),
                        interface_type: Some(interface_type),
                        pointee_constant,
                        struct_name,
                    },
                ))
            }
            CExpression::FloatNegate(expression) => {
                let (prefix, expression) = self.lower_expression_calls(*expression)?;
                Ok((prefix, CExpression::FloatNegate(Box::new(expression))))
            }
            CExpression::FloatClassification {
                expression,
                classification,
            } => {
                let (prefix, expression) = self.lower_expression_calls(*expression)?;
                Ok((
                    prefix,
                    CExpression::FloatClassification {
                        expression: Box::new(expression),
                        classification,
                    },
                ))
            }
            CExpression::AddressOf(expression) => {
                let literal_struct = match expression.as_ref() {
                    CExpression::StatementExpression {
                        aggregate_lvalue: true,
                        struct_name,
                        ..
                    } => struct_name.clone(),
                    _ => None,
                };
                let (prefix, expression) = self.lower_expression_calls(*expression)?;
                let address = CExpression::AddressOf(Box::new(expression));
                // Aggregate storage is byte-backed; the C value of &literal
                // has the nominal struct-pointer interface, including inside
                // value-producing conditional branches.
                let address = if let Some(struct_name) = literal_struct {
                    CExpression::Cast {
                        expression: Box::new(address),
                        interface_type: InterfaceType::Int32Pointer,
                        struct_name: Some(struct_name),
                        pointee_volatile: false,
                        pointee_constant: false,
                        explicit_qualification: false,
                    }
                } else {
                    address
                };
                Ok((prefix, address))
            }
            CExpression::PointerOffsetBytes { pointer, bytes } => {
                let (prefix, pointer) = self.lower_expression_calls(*pointer)?;
                Ok((
                    prefix,
                    CExpression::PointerOffsetBytes {
                        pointer: Box::new(pointer),
                        bytes,
                    },
                ))
            }
            CExpression::Subobject { pointer, width } => {
                let (prefix, pointer) = self.lower_expression_calls(*pointer)?;
                Ok((
                    prefix,
                    CExpression::Subobject {
                        pointer: Box::new(pointer),
                        width,
                    },
                ))
            }
            CExpression::Not(expression) => {
                let (prefix, expression) = self.lower_expression_calls(*expression)?;
                Ok((prefix, CExpression::Not(Box::new(expression))))
            }
            CExpression::BitwiseNot(expression) => {
                let (prefix, expression) = self.lower_expression_calls(*expression)?;
                Ok((prefix, CExpression::BitwiseNot(Box::new(expression))))
            }
            CExpression::Load(pointer, loaded_type) => {
                self.reject_unsequenced_updated_memory_read(&pointer)?;
                let (prefix, pointer) = self.lower_expression_calls(*pointer)?;
                Ok((prefix, CExpression::Load(Box::new(pointer), loaded_type)))
            }
            CExpression::SequentialRead {
                target,
                interface_type,
                struct_name,
                pointee_constant,
            } => {
                let (prefix, target) = self.lower_expression_calls(*target)?;
                Ok((
                    prefix,
                    CExpression::SequentialRead {
                        pointee_constant,
                        target: Box::new(target),
                        interface_type,
                        struct_name,
                    },
                ))
            }
            CExpression::SequentialWrite {
                target,
                value,
                interface_type,
                struct_name,
            } => {
                // WRITE_ONCE is expression-valued in the Linux headers. Its
                // value is evaluated once, as a value step read twice: by the
                // ordered store, a statement transition, and by the rest of
                // the expression.
                let (mut prefix, value) = self.lower_expression_calls(*value)?;
                let (target_prefix, target) = self.lower_expression_calls(*target)?;
                prefix.extend(target_prefix);
                let pointee_constant = self.expression_pointee_is_constant(&target);
                let stored = self.next_call_result;
                let result = stored.saturating_add(1);
                self.next_call_result = result.saturating_add(1);
                let read = |step| CExpression::StepResult {
                    step,
                    origin: crate::kernel::StepOrigin::Value("WRITE_ONCE"),
                    interface_type: Some(interface_type),
                    pointee_constant,
                    struct_name: struct_name.clone(),
                };
                prefix.push(CStatement::StepValue {
                    aggregate_layout: None,
                    steps: vec![stored, result],
                    expression: value,
                    interface_type: Some(interface_type),
                    pointee_constant,
                    site: CSite::NONE,
                });
                prefix.push(CStatement::SequentialStore {
                    target,
                    value: read(stored),
                    value_type: interface_type,
                    pointee_constant,
                    site: CSite::NONE,
                });
                Ok((prefix, read(result)))
            }
            CExpression::AggregateAddress {
                pointer,
                struct_name,
            } => {
                let (prefix, pointer) = self.lower_expression_calls(*pointer)?;
                Ok((
                    prefix,
                    CExpression::AggregateAddress {
                        pointer: Box::new(pointer),
                        struct_name,
                    },
                ))
            }
            CExpression::Field {
                pointer,
                field_type,
                pointee_constant,
                field_struct_name,
                function_pointer_signature,
                array_shape,
                source,
                access_class,
            } => {
                self.reject_unsequenced_updated_memory_read(&pointer)?;
                let (prefix, pointer) = self.lower_expression_calls(*pointer)?;
                Ok((
                    prefix,
                    CExpression::Field {
                        pointer: Box::new(pointer),
                        field_type,
                        pointee_constant,
                        field_struct_name,
                        function_pointer_signature,
                        array_shape,
                        source,
                        access_class,
                    },
                ))
            }
            CExpression::UnionField {
                pointer,
                field_type,
                union_name,
                pointee_constant,
            } => {
                self.reject_unsequenced_updated_memory_read(&pointer)?;
                let (prefix, pointer) = self.lower_expression_calls(*pointer)?;
                Ok((
                    prefix,
                    CExpression::UnionField {
                        pointer: Box::new(pointer),
                        field_type,
                        union_name,
                        pointee_constant,
                    },
                ))
            }
            CExpression::LessThan(left, right) => {
                self.lower_binary_calls(*left, *right, CExpression::LessThan)
            }
            CExpression::LessEqual(left, right) => {
                self.lower_binary_calls(*left, *right, CExpression::LessEqual)
            }
            CExpression::GreaterThan(left, right) => {
                self.lower_binary_calls(*left, *right, CExpression::GreaterThan)
            }
            CExpression::GreaterEqual(left, right) => {
                self.lower_binary_calls(*left, *right, CExpression::GreaterEqual)
            }
            CExpression::Equal(left, right) => {
                self.lower_binary_calls(*left, *right, CExpression::Equal)
            }
            CExpression::NotEqual(left, right) => {
                self.lower_binary_calls(*left, *right, CExpression::NotEqual)
            }
            CExpression::Add(left, right) => {
                self.lower_binary_calls(*left, *right, CExpression::Add)
            }
            CExpression::Subtract(left, right) => {
                self.lower_binary_calls(*left, *right, CExpression::Subtract)
            }
            CExpression::Multiply(left, right) => {
                self.lower_binary_calls(*left, *right, CExpression::Multiply)
            }
            CExpression::Divide(left, right) => {
                self.lower_binary_calls(*left, *right, CExpression::Divide)
            }
            CExpression::Remainder(left, right) => {
                self.lower_binary_calls(*left, *right, CExpression::Remainder)
            }
            CExpression::ShiftLeft(left, right) => {
                self.lower_binary_calls(*left, *right, CExpression::ShiftLeft)
            }
            CExpression::ShiftRight(left, right) => {
                self.lower_binary_calls(*left, *right, CExpression::ShiftRight)
            }
            CExpression::BitwiseAnd(left, right) => {
                self.lower_binary_calls(*left, *right, CExpression::BitwiseAnd)
            }
            CExpression::BitwiseOr(left, right) => {
                self.lower_binary_calls(*left, *right, CExpression::BitwiseOr)
            }
            CExpression::BitwiseXor(left, right) => {
                self.lower_binary_calls(*left, *right, CExpression::BitwiseXor)
            }
            CExpression::And(left, right) => self.lower_short_circuit_calls(*left, *right, true),
            CExpression::Or(left, right) => self.lower_short_circuit_calls(*left, *right, false),
            CExpression::CheckedArrayIndex { index, length } => {
                let (mut prefix, index) = self.lower_expression_calls(*index)?;
                let lower = CExpression::GreaterEqual(
                    Box::new(index.clone()),
                    Box::new(CExpression::Int32Literal(0)),
                );
                let upper = CExpression::LessThan(
                    Box::new(index.clone()),
                    Box::new(CExpression::Int32Literal(length)),
                );
                prefix.push(CStatement::Assert {
                    condition: CExpression::And(Box::new(lower), Box::new(upper)),
                    label: format!(
                        "array subobject index must be at least 0 and less than {length}"
                    ),
                    site: CSite::NONE,
                });
                Ok((prefix, index))
            }
            CExpression::Index(left, right, element_type) => {
                self.reject_unsequenced_updated_memory_read(&left)?;
                self.reject_unsequenced_updated_memory_read(&right)?;
                let (prefix, left, right) = self.lower_expression_pair(*left, *right)?;
                Ok((
                    prefix,
                    CExpression::Index(Box::new(left), Box::new(right), element_type),
                ))
            }
            expression => Ok((Vec::new(), expression)),
        }
    }

    fn lower_function_pointer_call(
        &mut self,
        function: CExpression,
        signature: CallbackInterface,
        arguments: Vec<CExpression>,
        position: Option<SourcePosition>,
    ) -> Result<(Vec<CStatement>, CExpression), CSyntaxError> {
        self.validate_function_designator_argument_order(&function, &arguments)?;
        let (mut prefix, function) = self.lower_expression_calls(function)?;
        let (argument_prefix, arguments) = self.lower_call_arguments(arguments)?;
        if prefix_has_non_assertion(&prefix) && prefix_has_non_assertion(&argument_prefix) {
            return Err(self.error_at_position(
                position,
                "multiple unsequenced calls in one expression are not supported",
            ));
        }
        prefix.extend(argument_prefix);

        // The call goes through the pointer itself, named as the source
        // writes it; the rest of the expression reads its result.
        let function_name = callee_source_text(&function);
        self.callback_statement_sources
            .insert((function_name.clone()).into(), function.clone());
        let call = self.next_call_result;
        self.next_call_result = self.next_call_result.saturating_add(1);
        let (interface_type, pointee_constant, struct_name) = (
            signature.return_type,
            signature.return_pointee_constant,
            signature.return_struct_name.clone(),
        );
        prefix.push(CStatement::CallResult {
            aggregate_layout: None,
            call,
            function_name: function_name.clone(),
            arguments,
            result_type: Some(interface_type),
            result_aggregate_layout: None,
            result_pointee_constant: pointee_constant,
            callee: Some(CCallee {
                pointer: function,
                signature,
            }),
            site: CSite::NONE,
        });
        Ok((
            prefix,
            CExpression::StepResult {
                step: call,
                origin: crate::kernel::StepOrigin::Call(function_name),
                interface_type: Some(interface_type),
                pointee_constant,
                struct_name,
            },
        ))
    }

    fn lower_binary_calls(
        &mut self,
        left: CExpression,
        right: CExpression,
        constructor: fn(Box<CExpression>, Box<CExpression>) -> CExpression,
    ) -> Result<(Vec<CStatement>, CExpression), CSyntaxError> {
        let (prefix, left, right) = self.lower_expression_pair(left, right)?;
        Ok((prefix, constructor(Box::new(left), Box::new(right))))
    }

    fn lower_short_circuit_calls(
        &mut self,
        left: CExpression,
        right: CExpression,
        is_and: bool,
    ) -> Result<(Vec<CStatement>, CExpression), CSyntaxError> {
        let right_position = first_embedded_call_position(&right);
        let right_assignment = first_assignment_position(&right);
        let (left_prefix, left) = self.lower_expression_calls(left)?;
        let (right_prefix, right) = self.lower_expression_calls(right)?;
        if right_position.is_none() {
            if !right_prefix.is_empty() {
                return Err(self.error_at_position(
                    right_assignment,
                    "assignment expressions in the short-circuit right operand are not supported",
                ));
            }
            let expression = if is_and {
                CExpression::And(Box::new(left), Box::new(right))
            } else {
                CExpression::Or(Box::new(left), Box::new(right))
            };
            return Ok((left_prefix, expression));
        }
        if right_assignment.is_some() {
            return Err(self.error_at_position(
                right_assignment,
                "assignment expressions in the short-circuit right operand are not supported",
            ));
        }

        // The operator decides whether its right operand runs: an `if` of the
        // operator's own, whose arms end in the operator's value on their path.
        let kind = if is_and {
            crate::kernel::OperatorKind::And
        } else {
            crate::kernel::OperatorKind::Or
        };
        let step = self.next_call_result;
        self.next_call_result = self.next_call_result.saturating_add(1);
        let value = |expression| CStatement::StepValue {
            aggregate_layout: None,
            steps: vec![step],
            expression,
            interface_type: Some(InterfaceType::Int32),
            pointee_constant: false,
            site: CSite::NONE,
        };
        let right_value = prepend_statements(
            right_prefix,
            value(CExpression::Not(Box::new(CExpression::Not(Box::new(
                right,
            ))))),
        );
        let (then_branch, else_branch) = if is_and {
            (right_value, value(CExpression::Int32Literal(0)))
        } else {
            (value(CExpression::Int32Literal(1)), right_value)
        };
        let mut prefix = left_prefix;
        prefix.push(CStatement::If {
            condition: left,
            then_branch: Box::new(then_branch),
            else_branch: Box::new(else_branch),
            operator: Some(COperator { kind, step }),
            site: CSite::NONE,
        });
        Ok((
            prefix,
            CExpression::StepResult {
                step,
                origin: crate::kernel::StepOrigin::Operator(kind),
                interface_type: Some(InterfaceType::Int32),
                pointee_constant: false,
                struct_name: None,
            },
        ))
    }

    fn parse_conditional(&mut self) -> Result<CExpression, CSyntaxError> {
        let condition = self.parse_logical_or()?;
        if self.peek() != Some(&Token::Question) {
            return Ok(condition);
        }
        if self.expression_contains_aggregate(&condition) {
            return Err(self.aggregate_expression_error());
        }
        self.position += 1;
        let then_branch = self.parse_expression_allow_direct_aggregate()?;
        self.expect(Token::Colon)?;
        // C's middle operand is an expression, while the third operand is a
        // conditional-expression. An assignment there therefore requires
        // parentheses; accepting it directly would give `=` the wrong
        // precedence now that assignment expressions exist.
        let else_branch = self.parse_conditional()?;
        if let Some(then_type) = self.source_expression_type(&then_branch) {
            self.validate_char_pointer_operands(then_type, &else_branch)?;
        }
        let then_struct = self.aggregate_struct_name(&then_branch);
        let else_struct = self.aggregate_struct_name(&else_branch);
        if then_struct != else_struct && (then_struct.is_some() || else_struct.is_some()) {
            return Err(
                self.error_here("conditional aggregate branches must have the same struct type")
            );
        }
        let common_type = ternary_expression_type(
            self.source_expression_type(&then_branch),
            self.source_expression_type(&else_branch),
            &then_branch,
            &else_branch,
        );
        if common_type.is_none()
            && self.source_expression_type(&then_branch).is_some()
            && self.source_expression_type(&else_branch).is_some()
        {
            return Err(self.error_here("conditional operator branches have incompatible types"));
        }
        // Pointers to different struct types share a kernel pointer type
        // but are not compatible C types.
        if let (Some(then_pointee), Some(else_pointee)) = (
            self.struct_pointer_name(&then_branch),
            self.struct_pointer_name(&else_branch),
        ) && then_pointee != else_pointee
        {
            return Err(self.error_here(format!(
                "conditional operator branches have incompatible types `struct {then_pointee} *` and `struct {else_pointee} *`"
            )));
        }
        let then_branch = if let Some(common_type) = common_type {
            self.coerce_conditional_branch(then_branch, common_type)
        } else {
            then_branch
        };
        let else_branch = if let Some(common_type) = common_type {
            self.coerce_conditional_branch(else_branch, common_type)
        } else {
            else_branch
        };
        Ok(CExpression::Ternary {
            condition: Box::new(condition),
            then_branch: Box::new(then_branch),
            else_branch: Box::new(else_branch),
        })
    }

    fn coerce_conditional_branch(
        &self,
        expression: CExpression,
        common_type: InterfaceType,
    ) -> CExpression {
        let Some(expression_type) = self.source_expression_type(&expression) else {
            return expression;
        };
        // With a pointer as the other operand, a null pointer constant is
        // converted to that pointer type; the null pointer is the same
        // value at every pointer type.
        if common_type.is_object_pointer()
            && expression_type != common_type
            && is_null_pointer_constant(&expression)
        {
            return CExpression::Int32Literal(0);
        }
        if expression_type == common_type
            || !is_arithmetic_type(expression_type)
            || !is_arithmetic_type(common_type)
        {
            return expression;
        }
        CExpression::Cast {
            expression: Box::new(expression),
            interface_type: common_type,
            struct_name: None,
            pointee_volatile: false,
            pointee_constant: false,
            explicit_qualification: false,
        }
    }

    /// The modeled memory functions describe their native `void *` arguments
    /// as byte ranges. Retag an object pointer for that contract after the
    /// native call's qualifier checks. This is an implicit conversion: it
    /// retains the argument's provenance, subobject bounds and qualifiers.
    /// Ordinary functions, indirect calls and internal-linkage names keep
    /// their own declared interfaces.
    fn adapt_library_memory_argument(
        &self,
        function_name: Option<&str>,
        index: usize,
        expression: &mut CExpression,
    ) {
        crate::instrumentation::record_deterministic_work(1);
        let Some(name) = function_name else { return };
        if self.variable_types.contains_key(&self.resolve_name(name)) {
            return;
        }
        let Some(header) = self.function_declarations.get(name) else {
            return;
        };
        let Some((library, _, true)) = library_function_prototype(header) else {
            return;
        };
        if !matches!(library, "memcpy" | "memcmp" | "memset") {
            return;
        }
        let Some(parameter) = header.parameters.get(index) else {
            return;
        };
        if parameter.interface_type != InterfaceType::VoidPointer
            || !self
                .source_expression_type(expression)
                .is_some_and(|ty| decay_to_pointer(ty).is_object_pointer())
        {
            return;
        }
        *expression = CExpression::Cast {
            expression: Box::new(std::mem::replace(expression, CExpression::Void)),
            interface_type: InterfaceType::UInt8Pointer,
            struct_name: None,
            pointee_volatile: false,
            pointee_constant: parameter.pointee_is_constant(),
            explicit_qualification: false,
        };
    }

    fn parse_call_arguments(
        &mut self,
        function_name: Option<&str>,
    ) -> Result<Vec<CExpression>, CSyntaxError> {
        // Only the call the statement itself makes is a statement call; calls
        // among its arguments are not.
        let statement_call = std::mem::take(&mut self.statement_call);
        // Every direct call, in statement or expression position, reaches
        // its arguments through here, so the declarations whose calls have
        // no model are refused at one place.
        if let Some(source_name) = function_name
            && !self
                .variable_types
                .contains_key(&self.resolve_name(source_name))
            && let Some(header) = self.function_declarations.get(source_name)
        {
            if header.opaque_attributes {
                return Err(self.error_at_previous(format!("function `{source_name}` uses declaration-only compiler attributes; calls require modeled semantics")));
            }
            if header.opaque_signature {
                return Err(self.error_at_previous(format!(
                    "function `{source_name}` uses declaration-only signature (__builtin_va_list or long double); calls require a modeled ABI"
                )));
            }
            if header.weak_linkage {
                return Err(self.error_at_previous(format!(
                    "weak function `{source_name}` may be absent; calls need an availability model"
                )));
            }
            if header.returns_twice {
                return Err(self.error_at_previous(format!(
                    "returns-twice function `{source_name}` needs a checked control-flow model"
                )));
            }
            if header.compile_time_error && !(statement_call && header.parameters.is_empty()) {
                return Err(self.error_at_previous(format!(
                    "function `{source_name}` is declared with the GNU `error` attribute; only a discarded call with no arguments is supported"
                )));
            }
            if header.variadic {
                if formatted_output_prototype(header) {
                    return self.parse_formatted_output_arguments(source_name);
                }
                return Err(self.error_at_previous(format!(
                    "calls to variadic function `{source_name}` are not supported by Click; its variable arguments are not modeled"
                )));
            }
        }
        self.expect(Token::LParen)?;
        let mut arguments = Vec::new();
        if self.peek() == Some(&Token::RParen) {
            self.position += 1;
            return Ok(arguments);
        }

        loop {
            let argument_index = arguments.len();
            let mut expression = self.parse_expression_allow_direct_aggregate()?;
            if let Some(parameter) = function_name
                .and_then(|name| {
                    self.variable_function_pointers
                        .get(&self.resolve_name(name))
                })
                .and_then(|signature| signature.parameters.get(argument_index))
            {
                self.reject_discarded_const_pointer(
                    parameter.interface_type,
                    parameter.pointee_constant,
                    &mut expression,
                )?;
            }
            if let Some((parameter_type, struct_name, function_pointer_signature)) =
                self.call_parameter_metadata(function_name, argument_index)
            {
                if let Some(signature) = function_pointer_signature.as_ref() {
                    self.validate_function_pointer_value(signature, &expression)?;
                } else if let Some(struct_name) = struct_name.as_ref() {
                    self.validate_struct_pointer_assignment(
                        Some(struct_name),
                        Some(parameter_type),
                        &mut expression,
                    )?;
                }
            }
            let known_scalar_parameter = function_name
                .and_then(|name| self.function_declarations.get(name))
                .and_then(|function| function.parameters.get(argument_index))
                .is_some_and(|parameter| !parameter.is_struct_value());
            if let Some(parameter) = function_name
                .and_then(|name| self.function_declarations.get(name))
                .and_then(|function| function.parameters.get(argument_index))
                && parameter.interface_type.is_pointer()
            {
                if parameter.pointee_is_constant() {
                    self.validate_char_pointer_assignment(
                        parameter.interface_type,
                        &mut expression,
                    )?;
                } else {
                    self.reject_discarded_const_pointer(
                        parameter.interface_type,
                        parameter.pointee_is_constant(),
                        &mut expression,
                    )?;
                }
            }
            if let Some(parameter) = function_name
                .and_then(|name| self.function_declarations.get(name))
                .and_then(|function| function.parameters.get(argument_index))
                && !parameter.interface_type.is_pointer()
            {
                convert_integer_constant(parameter.interface_type, &mut expression);
            }
            if known_scalar_parameter && self.expression_contains_aggregate(&expression) {
                return Err(self.aggregate_expression_error());
            }
            if function_name == Some("free") && self.expression_contains_aggregate(&expression) {
                return Err(self.error_here("`free` requires a pointer, not an aggregate value"));
            }
            self.adapt_library_memory_argument(function_name, argument_index, &mut expression);
            arguments.push(expression);
            match self.peek() {
                Some(Token::Comma) => {
                    self.position += 1;
                }
                Some(Token::RParen) => {
                    self.position += 1;
                    return Ok(arguments);
                }
                Some(token) => {
                    return Err(self.error_at_previous(format!(
                        "expected `,` or `)`, got {}",
                        token.describe()
                    )));
                }
                None => {
                    return Err(self.error_here("expected `,` or `)`, got end of input"));
                }
            }
        }
    }

    /// The arguments of a call to `snprintf` whose format is a string
    /// literal: the buffer, its size, and one argument for each conversion,
    /// each checked against the type its conversion reads (C11 7.21.6.1p9).
    /// The call becomes a call to the format's fixed-arity function, which
    /// [`Self::call_target`] then names, and that function is declared here.
    fn parse_formatted_output_arguments(
        &mut self,
        source_name: &str,
    ) -> Result<Vec<CExpression>, CSyntaxError> {
        use crate::languages::c::formatted_output::{self, FormatArgument};
        self.expect(Token::LParen)?;
        let buffer = self.parse_expression()?;
        if !matches!(
            self.source_expression_type(&buffer),
            Some(InterfaceType::CharPointer(_) | InterfaceType::CharArray(..))
        ) {
            return Err(self.error_here(format!(
                "the buffer argument of `{source_name}` must be a `char *`"
            )));
        }
        if self.expression_pointee_is_constant(&buffer) {
            return Err(self.error_here(format!(
                "the buffer argument of `{source_name}` must not point to const characters"
            )));
        }
        self.expect(Token::Comma)?;
        let size = self.parse_expression()?;
        if !self
            .source_expression_type(&size)
            .is_some_and(is_integer_type)
        {
            return Err(self.error_here(format!(
                "the size argument of `{source_name}` must have an integer type"
            )));
        }
        self.expect(Token::Comma)?;
        let mut format = Vec::new();
        while let Some(Token::StringLiteral(piece)) = self.peek().cloned() {
            self.position += 1;
            format.extend(piece);
        }
        if format.is_empty()
            && self.tokens.get(self.position.wrapping_sub(1)) == Some(&Token::Comma)
        {
            return Err(self.error_here(format!(
                "Click models a call to `{source_name}` only with a string-literal format"
            )));
        }
        // The format is lowered into the callee's specification, but its C
        // literal object still has a source occurrence and static storage.
        let _ = self.string_literal_expression(format.clone());
        let pieces = formatted_output::parse_format(&format).map_err(|reason| {
            self.error_at_previous(format!("`{source_name}` format: {reason}"))
        })?;
        let mut arguments = vec![buffer, size];
        let mut parameters = vec![
            ImportedParameter::new(
                InterfaceType::CharPointer(self.plain_char),
                "buffer".to_string(),
                None,
            ),
            ImportedParameter::new(
                InterfaceType::UInt64(LongRank::Long),
                "size".to_string(),
                None,
            ),
        ];
        for argument in pieces.iter().filter_map(|piece| piece.argument()) {
            let position = arguments.len() - 2;
            if self.peek() != Some(&Token::Comma) {
                return Err(self.error_here(format!(
                    "the `{source_name}` format converts more arguments than the call passes"
                )));
            }
            self.position += 1;
            let mut expression = self.parse_expression()?;
            let source_type = self.source_expression_type(&expression);
            let constant = evaluate_static_integer_expression(&expression).ok();
            let (interface_type, pointee_constant, conversion) = match argument {
                FormatArgument::UnsignedInt => {
                    (InterfaceType::UInt32, false, "`%u` reads an `unsigned int`")
                }
                FormatArgument::Int => (InterfaceType::Int32, false, "`%d` reads an `int`"),
                FormatArgument::String => (
                    InterfaceType::CharPointer(self.plain_char),
                    true,
                    "`%s` reads a `char *`",
                ),
            };
            let accepted = match argument {
                FormatArgument::UnsignedInt => {
                    if let Some(value) = constant
                        && static_integer_fits(InterfaceType::UInt32, value)
                    {
                        expression = static_integer_literal_for_type(InterfaceType::UInt32, value)
                            .expect("a fitting constant has a literal");
                        true
                    } else {
                        source_type == Some(InterfaceType::UInt32)
                    }
                }
                FormatArgument::Int => {
                    if let Some(value) = constant
                        && static_integer_fits(InterfaceType::Int32, value)
                    {
                        expression = static_integer_literal_for_type(InterfaceType::Int32, value)
                            .expect("a fitting constant has a literal");
                        true
                    } else {
                        // The default argument promotions convert a
                        // narrower integer to `int` (C11 6.5.2.2p6).
                        match source_type {
                            Some(InterfaceType::Int32) => true,
                            Some(
                                InterfaceType::Bool
                                | InterfaceType::Char(_)
                                | InterfaceType::Int8
                                | InterfaceType::UInt8
                                | InterfaceType::Int16
                                | InterfaceType::UInt16,
                            ) => {
                                expression = CExpression::Cast {
                                    expression: Box::new(expression),
                                    interface_type: InterfaceType::Int32,
                                    struct_name: None,
                                    pointee_volatile: false,
                                    pointee_constant: false,
                                    explicit_qualification: false,
                                };
                                true
                            }
                            _ => false,
                        }
                    }
                }
                FormatArgument::String => matches!(
                    source_type,
                    Some(InterfaceType::CharPointer(_) | InterfaceType::CharArray(..))
                ),
            };
            if !accepted {
                return Err(self.error_here(format!(
                    "argument {} of `{source_name}`: {conversion}, got `{}`",
                    position + 4,
                    source_type.map_or_else(
                        || "an unmodeled value".to_string(),
                        |interface_type| interface_type.diagnostic_name().to_string()
                    )
                )));
            }
            parameters.push(
                ImportedParameter::new(interface_type, format!("a{position}"), None)
                    .with_pointee_constant(pointee_constant),
            );
            arguments.push(expression);
        }
        if self.peek() == Some(&Token::Comma) {
            return Err(self.error_here(format!(
                "the call passes more arguments than the `{source_name}` format converts"
            )));
        }
        self.expect(Token::RParen)?;
        let name = formatted_output::function_name(&format);
        self.function_declarations
            .entry(name.clone())
            .or_insert_with(|| CFunctionHeader {
                declaration_line: 0,
                name_position: None,
                return_type: InterfaceType::Int32,
                return_pointee_constant: false,
                return_struct_name: None,
                return_pointer_struct_name: None,
                source_name: name.clone(),
                name: name.clone(),
                internal_linkage: false,
                weak_linkage: false,
                returns_twice: false,
                variadic: false,
                has_unnamed_parameter: false,
                empty_parameter_list: false,
                opaque_signature: false,
                opaque_signature_types: Vec::new(),
                opaque_attributes: false,
                compile_time_error: false,
                parameters,
            });
        self.formatted_output_call.replace(Some(name));
        Ok(arguments)
    }

    /// The function a direct call to `source_name` whose arguments were just
    /// parsed calls: a formatted-output call's fixed-arity function, or the
    /// function `source_name` declares.
    fn call_target(&self, source_name: &str) -> String {
        self.formatted_output_call
            .take()
            .unwrap_or_else(|| self.resolve_function_name(source_name))
    }

    fn parse_function_pointer_call_arguments(
        &mut self,
        signature: &CallbackInterface,
    ) -> Result<Vec<CExpression>, CSyntaxError> {
        let mut arguments = self.parse_call_arguments(None)?;
        for (argument, parameter) in arguments.iter_mut().zip(signature.parameters()) {
            self.reject_discarded_const_pointer(
                parameter.interface_type,
                parameter.pointee_constant,
                argument,
            )?;
            let expected_struct = parameter.struct_name().map(str::to_owned);
            self.validate_struct_pointer_assignment(
                expected_struct.as_ref(),
                Some(parameter.interface_type()),
                argument,
            )?;
        }
        Ok(arguments)
    }

    fn call_parameter_metadata(
        &self,
        function_name: Option<&str>,
        argument_index: usize,
    ) -> Option<(InterfaceType, Option<String>, Option<CallbackInterface>)> {
        let function_name = function_name?;
        if let Some(signature) = self
            .variable_function_pointers
            .get(&self.resolve_name(function_name))
        {
            return signature.parameters.get(argument_index).map(|parameter| {
                (
                    parameter.interface_type,
                    parameter.struct_name.clone(),
                    None,
                )
            });
        }
        self.function_declarations
            .get(function_name)
            .and_then(|function| function.parameters.get(argument_index))
            .map(|parameter| {
                (
                    parameter.interface_type,
                    parameter.struct_name.clone(),
                    parameter.function_pointer_signature.clone(),
                )
            })
    }

    fn call_return_pointee_is_constant(&self, name: &str) -> bool {
        self.variable_function_pointers
            .get(&self.resolve_name(name))
            .map_or_else(
                || {
                    self.function_declaration_for_call(name)
                        .is_some_and(|function| function.return_pointee_constant)
                },
                |signature| signature.return_pointee_constant,
            )
    }

    fn function_pointer_signature(&self, expression: &CExpression) -> Option<CallbackInterface> {
        match expression {
            CExpression::Variable(name) => self.variable_function_pointers.get(name).cloned(),
            CExpression::FunctionAddress(name) => self
                .function_declarations
                .get(name)
                .map(function_pointer_signature_from_header),
            CExpression::Ternary {
                then_branch,
                else_branch,
                ..
            } => {
                let then_signature = self.function_pointer_signature(then_branch)?;
                let else_signature = self.function_pointer_signature(else_branch)?;
                (then_signature == else_signature).then_some(then_signature)
            }
            CExpression::Cast { expression, .. } => self.function_pointer_signature(expression),
            CExpression::StatementExpression {
                function_pointer_signature: Some(signature),
                ..
            } => Some(signature.clone()),
            CExpression::Field {
                function_pointer_signature: Some(signature),
                ..
            } => Some(signature.clone()),
            _ => None,
        }
    }

    fn validate_function_pointer_value(
        &self,
        expected: &CallbackInterface,
        expression: &CExpression,
    ) -> Result<(), CSyntaxError> {
        if matches!(expression, CExpression::Int32Literal(0)) {
            return Ok(());
        }
        match self.function_pointer_signature(expression) {
            Some(actual) if actual == *expected => Ok(()),
            Some(actual) => Err(self.error_here(format!(
                "callback signature mismatch: expected {}, got {}",
                describe_function_pointer_signature(expected),
                describe_function_pointer_signature(&actual)
            ))),
            None if matches!(expression, CExpression::FunctionAddress(_)) => Ok(()),
            None => {
                // A bare name here decayed to a function address when this
                // translation unit declared it as a function. If it names no
                // object either, the identifier is simply undeclared, and
                // saying so beats reporting an incompatible pointer.
                if let CExpression::Variable(name) = expression
                    && !self.declares_resolved_object(name)
                {
                    return Err(self.error_here(format!("use of undeclared identifier `{name}`")));
                }
                Err(self.error_here("expected a compatible function pointer"))
            }
        }
    }

    fn validate_function_pointer_assignment(
        &self,
        target: &BindingName,
        expression: &CExpression,
    ) -> Result<(), CSyntaxError> {
        let Some(expected) = self.variable_function_pointers.get(target) else {
            return Ok(());
        };
        self.validate_function_pointer_value(expected, expression)
    }

    fn parse_logical_or(&mut self) -> Result<CExpression, CSyntaxError> {
        let mut expression = self.parse_logical_and()?;
        loop {
            expression = match self.peek() {
                Some(Token::PipePipe) => {
                    self.position += 1;
                    let right = self.parse_logical_and()?;
                    CExpression::Or(Box::new(expression), Box::new(right))
                }
                _ => return Ok(expression),
            };
        }
    }

    fn parse_logical_and(&mut self) -> Result<CExpression, CSyntaxError> {
        let mut expression = self.parse_bitwise_or()?;
        loop {
            expression = match self.peek() {
                Some(Token::AmpAmp) => {
                    self.position += 1;
                    let right = self.parse_bitwise_or()?;
                    CExpression::And(Box::new(expression), Box::new(right))
                }
                _ => return Ok(expression),
            };
        }
    }

    fn parse_bitwise_or(&mut self) -> Result<CExpression, CSyntaxError> {
        let mut expression = self.parse_bitwise_xor()?;
        while self.peek() == Some(&Token::Pipe) {
            self.position += 1;
            let right = self.parse_bitwise_xor()?;
            expression = CExpression::BitwiseOr(Box::new(expression), Box::new(right));
        }
        Ok(expression)
    }

    fn parse_bitwise_xor(&mut self) -> Result<CExpression, CSyntaxError> {
        let mut expression = self.parse_bitwise_and()?;
        while self.peek() == Some(&Token::Caret) {
            self.position += 1;
            let right = self.parse_bitwise_and()?;
            expression = CExpression::BitwiseXor(Box::new(expression), Box::new(right));
        }
        Ok(expression)
    }

    fn parse_bitwise_and(&mut self) -> Result<CExpression, CSyntaxError> {
        let mut expression = self.parse_equality()?;
        while self.peek() == Some(&Token::Amp) {
            self.position += 1;
            let right = self.parse_equality()?;
            expression = CExpression::BitwiseAnd(Box::new(expression), Box::new(right));
        }
        Ok(expression)
    }

    /// Equality binds more loosely than the ordered comparisons, as in C
    /// (C11 6.5.8 and 6.5.9): `a == b < c` is `a == (b < c)`.
    fn parse_equality(&mut self) -> Result<CExpression, CSyntaxError> {
        let mut expression = self.parse_relational()?;
        loop {
            expression = match self.peek() {
                Some(Token::EqualEqual) => {
                    self.position += 1;
                    let mut right = self.parse_relational()?;
                    if let Some(left_type) = self.source_expression_type(&expression) {
                        self.validate_pointer_comparison_operand(left_type, &mut right)?;
                    }
                    CExpression::Equal(Box::new(expression), Box::new(right))
                }
                Some(Token::BangEqual) => {
                    self.position += 1;
                    let mut right = self.parse_relational()?;
                    if let Some(left_type) = self.source_expression_type(&expression) {
                        self.validate_pointer_comparison_operand(left_type, &mut right)?;
                    }
                    CExpression::NotEqual(Box::new(expression), Box::new(right))
                }
                _ => return Ok(expression),
            };
        }
    }

    fn parse_relational(&mut self) -> Result<CExpression, CSyntaxError> {
        let mut expression = self.parse_shift()?;
        loop {
            expression = match self.peek() {
                Some(Token::LessThan) => {
                    self.position += 1;
                    let mut right = self.parse_shift()?;
                    if let Some(left_type) = self.source_expression_type(&expression) {
                        self.validate_pointer_comparison_operand(left_type, &mut right)?;
                    }
                    CExpression::LessThan(Box::new(expression), Box::new(right))
                }
                Some(Token::LessEqual) => {
                    self.position += 1;
                    let mut right = self.parse_shift()?;
                    if let Some(left_type) = self.source_expression_type(&expression) {
                        self.validate_pointer_comparison_operand(left_type, &mut right)?;
                    }
                    CExpression::LessEqual(Box::new(expression), Box::new(right))
                }
                Some(Token::GreaterThan) => {
                    self.position += 1;
                    let mut right = self.parse_shift()?;
                    if let Some(left_type) = self.source_expression_type(&expression) {
                        self.validate_pointer_comparison_operand(left_type, &mut right)?;
                    }
                    CExpression::GreaterThan(Box::new(expression), Box::new(right))
                }
                Some(Token::GreaterEqual) => {
                    self.position += 1;
                    let mut right = self.parse_shift()?;
                    if let Some(left_type) = self.source_expression_type(&expression) {
                        self.validate_pointer_comparison_operand(left_type, &mut right)?;
                    }
                    CExpression::GreaterEqual(Box::new(expression), Box::new(right))
                }
                _ => return Ok(expression),
            };
        }
    }

    fn parse_shift(&mut self) -> Result<CExpression, CSyntaxError> {
        let mut expression = self.parse_add()?;
        loop {
            expression = match self.peek() {
                Some(Token::ShiftLeft) => {
                    self.position += 1;
                    let right = self.parse_add()?;
                    CExpression::ShiftLeft(Box::new(expression), Box::new(right))
                }
                Some(Token::ShiftRight) => {
                    self.position += 1;
                    let right = self.parse_add()?;
                    CExpression::ShiftRight(Box::new(expression), Box::new(right))
                }
                _ => return Ok(expression),
            };
        }
    }

    fn parse_add(&mut self) -> Result<CExpression, CSyntaxError> {
        let mut expression = self.parse_multiply()?;
        loop {
            expression = match self.peek() {
                Some(Token::Plus) => {
                    self.position += 1;
                    let right = self.parse_multiply()?;
                    self.scale_struct_pointer_arithmetic(expression, right, CExpression::Add)?
                }
                Some(Token::Minus) => {
                    self.position += 1;
                    let right = self.parse_multiply()?;
                    if let Some(right_type) = self.source_expression_type(&right) {
                        self.validate_char_pointer_operands(right_type, &expression)?;
                    }
                    self.scale_struct_pointer_arithmetic(expression, right, CExpression::Subtract)?
                }
                _ => return Ok(expression),
            };
        }
    }

    fn scale_struct_pointer_arithmetic(
        &self,
        pointer: CExpression,
        offset: CExpression,
        constructor: fn(Box<CExpression>, Box<CExpression>) -> CExpression,
    ) -> Result<CExpression, CSyntaxError> {
        let Some(struct_name) = self.struct_pointer_name(&pointer) else {
            return Ok(constructor(Box::new(pointer), Box::new(offset)));
        };
        let result_type = self
            .source_expression_type(&pointer)
            .filter(|ty| ty.is_pointer());
        let pointee_constant = self.expression_pointee_is_constant(&pointer);
        let element_width = self
            .structs
            .get(&struct_name)
            .ok_or_else(|| self.error_here("pointer arithmetic requires a complete struct layout"))?
            .size_bytes;
        let byte_pointer = CExpression::Cast {
            expression: Box::new(pointer),
            interface_type: InterfaceType::UInt8Pointer,
            struct_name: None,
            pointee_volatile: false,
            pointee_constant,
            explicit_qualification: false,
        };
        let byte_offset = widened_stride(offset, element_width);
        let expression = constructor(Box::new(byte_pointer), Box::new(byte_offset));
        Ok(if let Some(interface_type) = result_type {
            CExpression::Cast {
                expression: Box::new(expression),
                interface_type,
                struct_name: Some(struct_name),
                pointee_volatile: false,
                pointee_constant,
                explicit_qualification: false,
            }
        } else {
            expression
        })
    }

    fn parse_multiply(&mut self) -> Result<CExpression, CSyntaxError> {
        let mut expression = self.parse_unary()?;
        while let Some(operator) = self.peek() {
            let constructor = match operator {
                Token::Star => CExpression::Multiply,
                Token::Slash => CExpression::Divide,
                Token::Percent => CExpression::Remainder,
                _ => break,
            };
            self.position += 1;
            let right = self.parse_unary()?;
            expression = constructor(Box::new(expression), Box::new(right));
        }
        Ok(expression)
    }

    /// An expression statement whose value is discarded (C11 6.8.3p2): a GNU
    /// statement expression such as Linux's `do_div(n, base);`, which
    /// yields a remainder the caller ignores, or an operand cast to `void`.
    /// Its effects run in order, and a value the lowering has not already
    /// computed is still evaluated and discarded, so an operation that is
    /// undefined there is still checked.
    fn parse_discarded_expression_statement(&mut self) -> Result<CStatement, CSyntaxError> {
        let expression = if self.peek_n(1) == Some(&Token::LBrace) {
            self.parse_expression()?
        } else {
            self.position += 3;
            self.parse_unary()?
        };
        self.expect(Token::Semicolon)?;
        let original_variable = match &expression {
            CExpression::Variable(name) => Some(name.clone()),
            _ => None,
        };
        let (mut statements, value) = self.lower_expression_calls(expression)?;
        let computed = match &value {
            CExpression::Variable(name) => original_variable.as_ref() != Some(name),
            CExpression::Int32Literal(_)
            | CExpression::UInt32Literal(_)
            | CExpression::UInt8Literal(_) => true,
            _ => false,
        };
        if matches!(value, CExpression::StepResult { .. }) {
            // A step's value nothing reads: read it here, so it ends with
            // this statement.
            statements.push(CStatement::StepValue {
                aggregate_layout: None,
                steps: Vec::new(),
                expression: value,
                interface_type: None,
                pointee_constant: false,
                site: CSite::NONE,
            });
        } else if !computed {
            let interface_type = self
                .source_expression_type(&value)
                .filter(|interface_type| is_arithmetic_type(*interface_type) || interface_type.is_pointer())
                .filter(|_| !contains_aggregate_value(&value))
                .ok_or_else(|| {
                    self.error_here(
                        "a discarded expression statement requires a modeled scalar or pointer value",
                    )
                })?;
            let pointee_constant = self.expression_pointee_is_constant(&value);
            // Evaluated and discarded, as an expression statement's value is.
            statements.push(CStatement::StepValue {
                aggregate_layout: None,
                steps: Vec::new(),
                expression: value,
                interface_type: Some(interface_type),
                pointee_constant,
                site: CSite::NONE,
            });
        }
        Ok(balanced_statement_sequence(statements).unwrap_or(CStatement::Skip))
    }

    fn parse_cast_expression(&mut self) -> Result<CExpression, CSyntaxError> {
        let cast_position = self.error_context();
        self.position += 1;
        let parsed_type = self.parse_type()?;
        if self.peek() == Some(&Token::LBracket) {
            let (interface_type, shape, incomplete) = self.parse_local_array_shape(&parsed_type)?;
            if shape.is_some_and(|shape| shape.len() != 1) {
                return Err(self.error_here("array compound literals require one dimension"));
            }
            self.expect(Token::RParen)?;
            let bound = (!incomplete).then(|| interface_type.array_length().expect("array type"));
            let literal = self.parse_array_compound_literal(parsed_type, bound)?;
            return self.parse_postfix_tail(literal, true);
        }
        self.expect(Token::RParen)?;
        if self.peek() == Some(&Token::LBrace) {
            let literal = self.parse_struct_compound_literal(parsed_type)?;
            return self.parse_postfix_tail(literal, true);
        }
        let volatile_pointer_object_cast = parsed_type.pointee_is_volatile()
            && parsed_type
                .interface_type
                .pointee_type()
                .is_some_and(InterfaceType::is_pointer)
            && !parsed_type.has_deeper_volatile();
        if parsed_type.interface_type.is_pointer()
            && (parsed_type.is_constant
                || (parsed_type.is_volatile && !volatile_pointer_object_cast))
        {
            return Err(self.error_at_previous(
                "qualified pointer cast destinations are not supported; cast qualification cannot be discarded",
            ));
        }
        let (interface_type, struct_name) = match (
            parsed_type.interface_type,
            parsed_type.struct_name,
            parsed_type.union_name,
        ) {
            (
                InterfaceType::Int8
                | InterfaceType::Int16
                | InterfaceType::Int32
                | InterfaceType::Char(_)
                | InterfaceType::UInt8
                | InterfaceType::UInt16
                | InterfaceType::UInt32
                | InterfaceType::Int64(_)
                | InterfaceType::UInt64(_),
                None,
                None,
            ) => (parsed_type.interface_type, None),
            (InterfaceType::Float32 | InterfaceType::Float64, None, None) => {
                (parsed_type.interface_type, None)
            }
            // An object pointer target: the kernel accepts only a 64-bit
            // integer whose value carries pointer provenance, or zero.
            (interface_type, struct_name, None)
                if interface_type.is_pointer()
                    && !matches!(interface_type, InterfaceType::FunctionPointer(_)) =>
            {
                (interface_type, struct_name)
            }
            _ => {
                return Err(self.error_at_previous(
                    "casts support only modeled scalar integer or floating-point values, or object pointer types",
                ));
            }
        };
        let mut expression = self.parse_unary()?;
        self.validate_pointer_cast(
            interface_type,
            struct_name.as_deref(),
            &expression,
            &cast_position,
        )?;
        convert_integer_constant(interface_type, &mut expression);
        Ok(CExpression::Cast {
            expression: Box::new(expression),
            interface_type,
            struct_name,
            pointee_volatile: volatile_pointer_object_cast,
            pointee_constant: parsed_type.pointee_constant,
            explicit_qualification: interface_type.is_pointer(),
        })
    }

    fn parse_unary(&mut self) -> Result<CExpression, CSyntaxError> {
        if matches!(self.peek(), Some(Token::PlusPlus | Token::MinusMinus)) {
            let position = self.here();
            let increment = self.next() == Some(Token::PlusPlus);
            let target = self.parse_unary()?;
            return self.scalar_update_expression(target, increment, true, position);
        }
        if self.peek() == Some(&Token::LParen) && self.is_type_start_at(1) {
            return self.parse_cast_expression();
        }

        if self.peek() == Some(&Token::Plus) {
            self.position += 1;
            return self.parse_unary();
        }
        if self.peek() == Some(&Token::Minus) {
            self.position += 1;
            if let Some(Token::Number(number)) = self.peek().cloned() {
                if is_floating_literal(&number) {
                    self.position += 1;
                    let expression = parse_float_literal_expression(&number).map_err(|reason| {
                        self.error_here(format!(
                            "invalid floating-point literal `{number}`: {reason}"
                        ))
                    })?;
                    return negate_float_literal(expression).ok_or_else(|| {
                        self.error_here("unary negation requires a float or double literal")
                    });
                }
                self.position += 1;
                let expression = parse_integer_literal_expression(&number).map_err(|reason| {
                    self.error_here(format!("invalid integer literal `{number}`: {reason}"))
                })?;
                return Ok(negate_integer_literal_expression(expression));
            }
            let expression = self.parse_unary()?;
            if let Some(expression) = negate_float_literal(expression.clone()) {
                return Ok(expression);
            }
            if self.expression_is_float(&expression) {
                return Ok(CExpression::FloatNegate(Box::new(expression)));
            }
            return Ok(CExpression::Subtract(
                Box::new(CExpression::Int32Literal(0)),
                Box::new(expression),
            ));
        }

        if self.peek() == Some(&Token::Star) {
            self.position += 1;
            let pointer = self.parse_unary()?;
            return Ok(self.dereference_expression(pointer));
        }

        if self.peek() == Some(&Token::Amp) {
            self.position += 1;
            if let Some(object) = self.local_bit_field_object()
                && !object.is_pointer()
                && !matches!(
                    self.peek_next(),
                    Some(Token::Dot | Token::Arrow | Token::LBracket | Token::LParen)
                )
            {
                let pointer = object.source_pointer();
                self.position += 1;
                return Ok(pointer);
            }
            if let Some(Token::Ident(name)) = self.peek().cloned()
                && !self.variable_types.contains_key(&self.resolve_name(&name))
            {
                if self.out_of_scope_names.contains(&name) {
                    return Err(self.error_here(format!("use of undeclared identifier `{name}`")));
                }
                self.position += 1;
                if let Some(address) = self.bare_function_designator(&name)? {
                    return Ok(address);
                }
                return Ok(CExpression::FunctionAddress(
                    self.resolve_function_name(&name),
                ));
            }
            let target = self.without_bit_field_operands(Self::parse_unary)?;
            if matches!(
                target,
                CExpression::StatementExpression {
                    aggregate_lvalue: true,
                    ..
                }
            ) && self
                .source_expression_type(&target)
                .is_some_and(|ty| ty.array_length().is_some())
            {
                return Err(self.error_here(
                    "address of an array compound literal requires a pointer-to-array type",
                ));
            }
            if matches!(target, CExpression::ScalarUpdate { .. }) {
                return Err(self.error_here("an expression update result is not an lvalue"));
            }
            if self.is_aggregate_result_member(&target) {
                return Err(
                    self.error_here("a member of an aggregate expression result is not an lvalue")
                );
            }
            if self
                .source_expression_type(&target)
                .is_some_and(InterfaceType::is_pointer)
                && self.expression_pointee_is_constant(&target)
            {
                return Err(self.error_here(
                    "address of a pointer-to-const requires unsupported nested const qualification",
                ));
            }
            if let CExpression::Variable(name) = &target {
                self.address_taken_variables.insert(name.clone());
            }
            return Ok(CExpression::AddressOf(Box::new(target)));
        }

        if self.peek() == Some(&Token::Bang) {
            self.position += 1;
            return Ok(CExpression::Not(Box::new(self.parse_unary()?)));
        }

        if self.peek() == Some(&Token::Tilde) {
            self.position += 1;
            return Ok(CExpression::BitwiseNot(Box::new(self.parse_unary()?)));
        }

        self.parse_postfix()
    }

    /// Recognize the small, explicitly checked projection of Linux-style
    /// access macros. The macro expander preserves these calls instead of
    /// feeding their GNU statement-expression bodies to the ordinary C
    /// parser. Direct spellings are accepted as well, which keeps the
    /// imported semantics stable when a header only declares the macros.
    fn parse_kernel_primitive_expression(
        &self,
        source_name: &str,
        arguments: &[CExpression],
        position: Option<SourcePosition>,
    ) -> Result<Option<CExpression>, CSyntaxError> {
        if self.import_mode
            && matches!(
                source_name,
                "READ_ONCE" | "WRITE_ONCE" | "rcu_assign_pointer" | "likely" | "unlikely"
            )
        {
            return Ok(None);
        }
        let wrong_arity = |expected: usize| {
            self.error_at_position(
                position.clone(),
                format!(
                    "`{source_name}` expects {expected} argument{}",
                    if expected == 1 { "" } else { "s" }
                ),
            )
        };
        match source_name {
            "READ_ONCE" => {
                let [target] = arguments else {
                    return Err(wrong_arity(1));
                };
                let (interface_type, struct_name) =
                    self.sequential_access_target(target, source_name, position.clone())?;
                Ok(Some(CExpression::SequentialRead {
                    pointee_constant: self.expression_pointee_is_constant(target),
                    target: Box::new(target.clone()),
                    interface_type,
                    struct_name,
                }))
            }
            "WRITE_ONCE" => {
                let [target, value] = arguments else {
                    return Err(wrong_arity(2));
                };
                let (interface_type, struct_name) =
                    self.sequential_access_target(target, source_name, position.clone())?;
                let value = self.validate_sequential_store_value(
                    target,
                    value,
                    interface_type,
                    struct_name.as_deref(),
                )?;
                Ok(Some(CExpression::SequentialWrite {
                    target: Box::new(target.clone()),
                    value: Box::new(value),
                    interface_type,
                    struct_name,
                }))
            }
            "likely" | "unlikely" => {
                let [condition] = arguments else {
                    return Err(wrong_arity(1));
                };
                self.validate_kernel_condition(condition, source_name, position.clone())?;
                Ok(Some(condition.clone()))
            }
            "__builtin_expect" => {
                let [condition, expected] = arguments else {
                    return Err(wrong_arity(2));
                };
                self.validate_kernel_condition(condition, source_name, position.clone())?;
                let Some(expected_type) = self.source_expression_type(expected) else {
                    return Err(self.error_at_position(
                        position.clone(),
                        "`__builtin_expect` requires an integer constant prediction",
                    ));
                };
                if !is_integer_type(expected_type) {
                    return Err(self.error_at_position(
                        position.clone(),
                        "`__builtin_expect` requires an integer constant prediction",
                    ));
                }
                if self.expression_has_runtime_effect(expected) {
                    return Err(self.error_at_position(
                        position,
                        "the hint operand of `__builtin_expect` must be side-effect free",
                    ));
                }
                if evaluate_static_integer_expression(expected).is_err() {
                    return Err(self.error_at_position(
                        position,
                        "`__builtin_expect` requires an integer constant prediction",
                    ));
                }
                Ok(Some(condition.clone()))
            }
            "rcu_assign_pointer" => Err(self.error_at_position(
                position,
                "`rcu_assign_pointer` is supported only as a statement-form sequential store; the selected profile does not model release/acquire or grace-period semantics",
            )),
            name if is_unsupported_concurrency_builtin(name) => Err(self.error_at_position(
                position,
                format!(
                    "unsupported concurrency builtin `{name}`: the selected profile provides sequential access primitives only"
                ),
            )),
            _ => Ok(None),
        }
    }

    fn sequential_access_target(
        &self,
        target: &CExpression,
        primitive: &str,
        position: Option<SourcePosition>,
    ) -> Result<(InterfaceType, Option<String>), CSyntaxError> {
        if !matches!(
            target,
            CExpression::Variable(_)
                | CExpression::Load(_, _)
                | CExpression::Field { .. }
                | CExpression::UnionField { .. }
                | CExpression::Index(_, _, _)
        ) {
            return Err(self.error_at_position(
                position,
                format!("`{primitive}` requires a scalar or pointer lvalue"),
            ));
        }
        if matches!(target, CExpression::UnionField { .. }) && primitive == "WRITE_ONCE" {
            return Err(self.error_at_position(
                position,
                "writing tagged union members through `WRITE_ONCE` is not supported",
            ));
        }
        let Some(interface_type) = self.source_expression_type(target) else {
            return Err(self.error_at_position(
                position,
                format!("`{primitive}` target has no supported C type"),
            ));
        };
        if !interface_type.is_supported_static_scalar() {
            return Err(self.error_at_position(
                position,
                format!(
                    "`{primitive}` supports only modeled scalar and object-pointer cells, got `{}`",
                    interface_type.diagnostic_name()
                ),
            ));
        }
        let struct_name = if interface_type.is_object_pointer() {
            self.struct_pointer_name(target)
                .or_else(|| self.struct_pointer_pointer_name(target))
        } else {
            None
        };
        Ok((interface_type, struct_name))
    }

    fn validate_sequential_store_value(
        &self,
        target: &CExpression,
        value: &CExpression,
        interface_type: InterfaceType,
        struct_name: Option<&str>,
    ) -> Result<CExpression, CSyntaxError> {
        self.reject_constant_lvalue_write(target)?;
        let mut value = value.clone();
        self.reject_discarded_const_pointer(
            interface_type,
            self.expression_pointee_is_constant(target),
            &mut value,
        )?;
        if let Some(struct_name) = struct_name {
            let expected_struct = struct_name.to_string();
            self.validate_struct_pointer_assignment(
                Some(&expected_struct),
                Some(interface_type),
                &mut value,
            )?;
        }
        Ok(value)
    }

    fn validate_kernel_condition(
        &self,
        condition: &CExpression,
        primitive: &str,
        position: Option<SourcePosition>,
    ) -> Result<(), CSyntaxError> {
        let Some(interface_type) = self.source_expression_type(condition) else {
            return Err(self.error_at_position(
                position,
                format!("`{primitive}` requires a scalar condition"),
            ));
        };
        if !is_arithmetic_type(interface_type) && !interface_type.is_object_pointer() {
            return Err(self.error_at_position(
                position,
                format!(
                    "`{primitive}` requires a scalar condition, got `{}`",
                    interface_type.diagnostic_name()
                ),
            ));
        }
        Ok(())
    }

    fn parse_kernel_primitive_statement(
        &self,
        source_name: &str,
        arguments: &[CExpression],
    ) -> Result<Option<CStatement>, CSyntaxError> {
        if self.import_mode
            && matches!(
                source_name,
                "READ_ONCE" | "WRITE_ONCE" | "rcu_assign_pointer" | "likely" | "unlikely"
            )
        {
            return Ok(None);
        }
        match source_name {
            "WRITE_ONCE" | "rcu_assign_pointer" => {
                if arguments.len() != 2 {
                    return Err(self.error_here(format!(
                        "`{source_name}` expects 2 arguments, got {}",
                        arguments.len()
                    )));
                }
                let target = &arguments[0];
                let value = &arguments[1];
                let (interface_type, struct_name) =
                    self.sequential_access_target(target, source_name, None)?;
                let value = self.validate_sequential_store_value(
                    target,
                    value,
                    interface_type,
                    struct_name.as_deref(),
                )?;
                Ok(Some(CStatement::SequentialStore {
                    target: target.clone(),
                    value,
                    value_type: interface_type,
                    pointee_constant: self.expression_pointee_is_constant(target), site: CSite::NONE
                }))
            }
            "READ_ONCE" | "likely" | "unlikely" | "__builtin_expect" => Err(
                self.error_here(format!("`{source_name}` result may not be discarded")),
            ),
            name if is_unsupported_concurrency_builtin(name) => Err(self.error_here(format!(
                "unsupported concurrency builtin `{name}`: the selected profile provides sequential access primitives only"
            ))),
            _ => Ok(None),
        }
    }

    fn scalar_update_expression(
        &self,
        target: CExpression,
        increment: bool,
        prefix: bool,
        position: Option<SourcePosition>,
    ) -> Result<CExpression, CSyntaxError> {
        let CExpression::Variable(name) = target else {
            return Err(self
                .error_at_position(position, "expression updates require a named scalar lvalue"));
        };
        if self.variable_is_constant(&name) {
            return Err(self.error_at_position(
                position,
                format!("cannot update const-qualified lvalue `{name}`"),
            ));
        }
        let interface_type = self.variable_types.get(&name).copied().ok_or_else(|| {
            self.error_at_position(
                position.clone(),
                "expression update requires a declared scalar",
            )
        })?;
        if !interface_type.is_supported_static_scalar()
            || matches!(interface_type, InterfaceType::FunctionPointer(_))
            || self.variable_struct_values.contains_key(&name)
        {
            return Err(self.error_at_position(
                position,
                "expression updates require a modeled arithmetic or data-pointer scalar",
            ));
        }
        Ok(CExpression::ScalarUpdate {
            struct_name: self.variable_structs.get(&name).cloned(),
            pointee_constant: self.variable_pointee_is_constant(&name),
            name,
            increment,
            prefix,
            interface_type,
            position,
        })
    }

    fn parse_postfix(&mut self) -> Result<CExpression, CSyntaxError> {
        self.parse_postfix_with_updates(true)
    }

    fn parse_postfix_with_updates(
        &mut self,
        allow_updates: bool,
    ) -> Result<CExpression, CSyntaxError> {
        let expression = self.parse_primary()?;
        self.parse_postfix_tail(expression, allow_updates)
    }

    fn parse_postfix_tail(
        &mut self,
        mut expression: CExpression,
        allow_updates: bool,
    ) -> Result<CExpression, CSyntaxError> {
        if let CExpression::Variable(name) = &expression
            && let Some(row) = self.local_row_pointers.get(name).cloned()
        {
            expression = self.parse_row_pointer_access(&row)?;
        }
        loop {
            match self.peek() {
                Some(Token::PlusPlus | Token::MinusMinus) if !allow_updates => {
                    return Ok(expression);
                }
                Some(Token::PlusPlus | Token::MinusMinus) => {
                    let position = self.here();
                    let increment = self.next() == Some(Token::PlusPlus);
                    expression =
                        self.scalar_update_expression(expression, increment, false, position)?;
                }
                Some(Token::LParen) => {
                    let call_position =
                        self.positions.get(self.position.saturating_sub(1)).cloned();
                    if let CExpression::Field {
                        function_pointer_signature: Some(signature),
                        ..
                    } = &expression
                    {
                        let signature = signature.clone();
                        let arguments = self.parse_function_pointer_call_arguments(&signature)?;
                        expression = CExpression::IndirectCall {
                            function: Box::new(expression),
                            signature,
                            arguments,
                            position: call_position,
                        };
                        continue;
                    }
                    let source_name = match &expression {
                        CExpression::Variable(name) => name.source_name().to_owned(),
                        _ => {
                            return Err(self.error_here(
                                "function calls currently require an identifier or function pointer",
                            ));
                        }
                    };
                    let arguments = self.parse_call_arguments(Some(&source_name))?;
                    if let Some(result) = self.parse_kernel_primitive_expression(
                        &source_name,
                        &arguments,
                        call_position.clone(),
                    )? {
                        expression = result;
                        continue;
                    }
                    if let Some(result) = parse_float_classification_call(&source_name, &arguments)
                    {
                        expression = result.map_err(|reason| {
                            self.error_at_position(call_position.clone(), reason)
                        })?;
                        continue;
                    }
                    if source_name == "__builtin_expect" {
                        let [value, hint] = arguments.as_slice() else {
                            return Err(self.error_at_position(
                                call_position,
                                "`__builtin_expect` expects two integer arguments",
                            ));
                        };
                        for (name, operand) in [("value", value), ("hint", hint)] {
                            if !self
                                .source_expression_type(operand)
                                .is_some_and(is_integer_type)
                            {
                                return Err(self.error_at_position(
                                    call_position,
                                    format!(
                                        "`__builtin_expect` {name} operand must have an integer type"
                                    ),
                                ));
                            }
                        }
                        if self.expression_has_runtime_effect(hint) {
                            return Err(self.error_at_position(
                                call_position,
                                "the hint operand of `__builtin_expect` must be side-effect free",
                            ));
                        }
                        // The hint affects optimization only. Retaining the
                        // first operand as the C expression preserves its
                        // value and any effects in the existing lowering path.
                        expression = value.clone();
                        continue;
                    }
                    if source_name == "__builtin_constant_p" {
                        let [operand] = arguments.as_slice() else {
                            return Err(self.error_at_position(
                                call_position,
                                "`__builtin_constant_p` expects one argument",
                            ));
                        };
                        if self.expression_has_runtime_effect(operand) {
                            return Err(self.error_at_position(
                                call_position,
                                "the operand of `__builtin_constant_p` must be side-effect free",
                            ));
                        }
                        // The operand is not evaluated. Whether the compiler
                        // folds it to a constant depends on optimization, so
                        // the result is an unknown 0 or 1 and both outcomes
                        // are checked; the standard library's contract for
                        // this name says only that.
                        expression = CExpression::Call {
                            function_name: CONSTANT_P_UNKNOWN.to_string(),
                            arguments: Vec::new(),
                            position: call_position.clone(),
                        };
                        continue;
                    }
                    if source_name.starts_with("__builtin_") {
                        return Err(self.error_at_position(
                            call_position,
                            format!("unsupported GNU builtin `{source_name}`"),
                        ));
                    }
                    let function_name = self.call_target(&source_name);
                    expression = CExpression::Call {
                        function_name,
                        arguments,
                        position: call_position,
                    };
                }
                Some(Token::LBracket) => {
                    self.position += 1;
                    let first_index = self.parse_expression()?;
                    self.expect(Token::RBracket)?;
                    if let Some((struct_name, element_width, shape)) =
                        self.struct_array_field_info(&expression)
                    {
                        let mut indexes = vec![first_index];
                        while self.peek() == Some(&Token::LBracket) {
                            self.position += 1;
                            indexes.push(self.parse_expression()?);
                            self.expect(Token::RBracket)?;
                        }
                        if indexes.len() != shape.len() {
                            return Err(self.error_here(format!(
                                "multidimensional struct array field requires {} indices, got {}",
                                shape.len(),
                                indexes.len()
                            )));
                        }
                        let offset = flatten_array_indices(indexes, &shape, false);
                        let stride = widened_stride(offset, element_width);
                        expression = CExpression::AggregateAddress {
                            pointer: Box::new(CExpression::Add(
                                Box::new(expression),
                                Box::new(stride),
                            )),
                            struct_name,
                        };
                        continue;
                    }
                    if let Some(shape) = self.scalar_array_field_shape(&expression) {
                        let mut indexes = vec![first_index];
                        // A further subscript indexes the element, such as
                        // a string a pointer array holds.
                        while indexes.len() < shape.len() && self.peek() == Some(&Token::LBracket) {
                            self.position += 1;
                            indexes.push(self.parse_expression()?);
                            self.expect(Token::RBracket)?;
                        }
                        if indexes.len() != shape.len() {
                            return Err(self.error_here(format!(
                                "multidimensional scalar array field requires {} indices, got {}",
                                shape.len(),
                                indexes.len()
                            )));
                        }
                        let offset = flatten_array_indices(indexes, &shape, false);
                        expression = self.index_expression(expression, offset);
                        continue;
                    }
                    let incomplete_array = match &expression {
                        CExpression::Variable(name)
                            if self.incomplete_array_names.contains(name)
                                && (name
                                    .named()
                                    .is_some_and(|name| self.global_arrays.contains_key(name))
                                    || name.named().is_some_and(|name| {
                                        self.global_aggregate_arrays.contains_key(name)
                                    })) =>
                        {
                            Some(name.clone())
                        }
                        _ => None,
                    };
                    if let Some(name) = incomplete_array {
                        if self.peek() == Some(&Token::LBracket) {
                            return Err(self.error_here(
                                "multidimensional file-scope arrays are not supported yet",
                            ));
                        }
                        let struct_array = self.variable_structs.contains_key(&name);
                        expression = self.index_expression(expression, first_index);
                        if struct_array && self.peek() != Some(&Token::Dot) {
                            return Err(self.error_here(
                                "array of struct values are only supported through field access",
                            ));
                        }
                        continue;
                    }
                    let shape = match &expression {
                        CExpression::Variable(name) => {
                            self.variable_array_shapes.get(name).cloned()
                        }
                        _ => None,
                    };
                    if let Some(shape) = shape {
                        let name = match &expression {
                            CExpression::Variable(name) => name,
                            _ => unreachable!("array shape belongs to a variable"),
                        };
                        let mut indexes = vec![first_index];
                        while indexes.len() < shape.len() && self.peek() == Some(&Token::LBracket) {
                            self.position += 1;
                            indexes.push(self.parse_expression()?);
                            self.expect(Token::RBracket)?;
                        }
                        if indexes.len() != shape.len() {
                            return Err(self.error_here(format!(
                                "multidimensional array `{name}` requires {} indices, got {}",
                                shape.len(),
                                indexes.len()
                            )));
                        }
                        let unbounded_outer = self.incomplete_array_names.contains(name)
                            || name
                                .named()
                                .and_then(|name| self.global_arrays.get(name))
                                .is_some_and(CGlobalArray::is_incomplete);
                        let offset = flatten_array_indices(indexes, &shape, unbounded_outer);
                        let struct_array = self.variable_structs.contains_key(name);
                        let offset = if struct_array {
                            let struct_name = self
                                .variable_structs
                                .get(name)
                                .expect("struct array has a struct name");
                            let element_width = self
                                .structs
                                .get(struct_name)
                                .expect("struct array has a declaration")
                                .size_bytes;
                            widened_stride(offset, element_width)
                        } else {
                            offset
                        };
                        expression = self.index_expression(expression, offset);
                        if struct_array && self.peek() != Some(&Token::Dot) {
                            return Err(self.error_here(
                                "array of struct values are only supported through field access",
                            ));
                        }
                    } else {
                        let heap_struct = self.struct_pointer_name(&expression);
                        if let Some(struct_name) = heap_struct {
                            let element_width = self
                                .structs
                                .get(&struct_name)
                                .ok_or_else(|| {
                                    self.error_here(format!(
                                        "cannot index incomplete struct `{struct_name}`"
                                    ))
                                })?
                                .size_bytes;
                            let byte_pointer = CExpression::Cast {
                                expression: Box::new(expression),
                                interface_type: InterfaceType::UInt8Pointer,
                                struct_name: None,
                                pointee_volatile: false,
                                pointee_constant: false,
                                explicit_qualification: false,
                            };
                            let offset = widened_stride(first_index, element_width);
                            expression = self.index_expression(byte_pointer, offset);
                            if self.peek() != Some(&Token::Dot) {
                                return Err(self.error_here(
                                    "array of struct values are only supported through field access",
                                ));
                            }
                        } else {
                            expression = self.index_expression(expression, first_index);
                        }
                    }
                }
                Some(Token::Dot) | Some(Token::Arrow) => {
                    let dot = self.peek() == Some(&Token::Dot);
                    let union_base = match &expression {
                        CExpression::UnionAddress { union_name, .. } => Some(union_name.clone()),
                        _ => None,
                    };
                    self.position += 1;
                    let field_position = self.here();
                    let field_name = self.expect_ident("field name")?;
                    let (
                        pointer,
                        field_type,
                        field_struct_name,
                        field_union_name,
                        function_pointer_signature,
                        array_shape,
                        pointee_constant,
                        access_class,
                    ) = if dot {
                        let struct_value = matches!(
                            &expression,
                            CExpression::Variable(name)
                                if self.variable_struct_values.contains_key(name)
                                    || (self.variable_structs.contains_key(name)
                                        && matches!(
                                            self.variable_types.get(name),
                                            Some(InterfaceType::UInt8Array(_))
                                        ))
                        );
                        let aggregate_result =
                            matches!(
                                &expression,
                                CExpression::Call { .. }
                                    | CExpression::IndirectCall { .. }
                                    | CExpression::Ternary { .. }
                                    | CExpression::StepResult { .. }
                                    | CExpression::StatementExpression { .. }
                            ) && self.aggregate_struct_name(&expression).is_some();
                        if struct_value
                            || aggregate_result
                            || matches!(&expression, CExpression::UnionAddress { .. })
                        {
                            self.resolve_field_access(&expression, &field_name)?
                        } else {
                            self.resolve_array_struct_field_access(&expression, &field_name)?
                        }
                    } else {
                        self.resolve_field_access(&expression, &field_name)?
                    };
                    expression = if let Some(union_name) = union_base {
                        CExpression::UnionField {
                            pointer: Box::new(pointer),
                            field_type,
                            union_name,
                            pointee_constant,
                        }
                    } else {
                        field_expression(
                            pointer,
                            field_type,
                            field_struct_name,
                            field_union_name,
                            function_pointer_signature,
                            array_shape,
                            self.mint_field_source_id(field_name, field_position),
                            pointee_constant,
                            access_class,
                        )
                    };
                }
                _ => return Ok(expression),
            }
        }
    }

    fn struct_array_field_info(&self, expression: &CExpression) -> Option<(String, u32, Vec<u32>)> {
        let CExpression::Field {
            field_type: InterfaceType::UInt8Array(_),
            field_struct_name: Some(struct_name),
            array_shape: Some(shape),
            ..
        } = expression
        else {
            return None;
        };
        Some((
            struct_name.clone(),
            self.structs.get(struct_name)?.size_bytes,
            shape.clone(),
        ))
    }

    fn scalar_array_field_shape(&self, expression: &CExpression) -> Option<Vec<u32>> {
        let CExpression::Field {
            field_type,
            field_struct_name,
            array_shape,
            ..
        } = expression
        else {
            return None;
        };
        let length = match field_type {
            InterfaceType::Int32Array(length)
            | InterfaceType::Int128Array(length)
            | InterfaceType::Int64Array(_, length)
            | InterfaceType::UInt128Array(length)
            | InterfaceType::UInt64Array(_, length)
            | InterfaceType::CharArray(_, length)
            | InterfaceType::UInt8Array(length)
            | InterfaceType::Float32Array(length)
            | InterfaceType::Float64Array(length) => *length,
            InterfaceType::PointerArray(_, _, length) => *length,
            _ => return None,
        };
        if field_struct_name.is_some()
            && !matches!(field_type, InterfaceType::PointerArray(_, _, _))
        {
            return None;
        }
        Some(array_shape.clone().unwrap_or_else(|| vec![length]))
    }

    fn expression_is_float(&self, expression: &CExpression) -> bool {
        match expression {
            CExpression::StepResult { interface_type, .. } => {
                matches!(
                    interface_type,
                    Some(InterfaceType::Float32 | InterfaceType::Float64)
                )
            }
            CExpression::Float32Literal(_)
            | CExpression::Float64Literal(_)
            | CExpression::FloatNegate(_) => true,
            CExpression::Variable(name) => matches!(
                self.variable_types.get(name),
                Some(InterfaceType::Float32 | InterfaceType::Float64)
            ),
            CExpression::Cast { interface_type, .. } => {
                matches!(
                    interface_type,
                    InterfaceType::Float32 | InterfaceType::Float64
                )
            }
            CExpression::Assignment { interface_type, .. }
            | CExpression::ScalarUpdate { interface_type, .. } => {
                matches!(
                    interface_type,
                    InterfaceType::Float32 | InterfaceType::Float64
                )
            }
            CExpression::StatementExpression { interface_type, .. } => {
                matches!(
                    interface_type,
                    InterfaceType::Float32 | InterfaceType::Float64
                )
            }
            CExpression::Field { field_type, .. } | CExpression::UnionField { field_type, .. } => {
                matches!(field_type, InterfaceType::Float32 | InterfaceType::Float64)
            }
            CExpression::Load(pointer, _) => self.expression_pointee_is_float(pointer),
            CExpression::SequentialRead { interface_type, .. }
            | CExpression::SequentialWrite { interface_type, .. } => {
                matches!(
                    interface_type,
                    InterfaceType::Float32 | InterfaceType::Float64
                )
            }
            CExpression::Index(base, _, _) | CExpression::CheckedArrayIndex { index: base, .. } => {
                self.expression_pointee_is_float(base)
            }
            CExpression::Ternary {
                then_branch,
                else_branch,
                ..
            } => self.expression_is_float(then_branch) || self.expression_is_float(else_branch),
            CExpression::Add(left, right)
            | CExpression::Subtract(left, right)
            | CExpression::Multiply(left, right)
            | CExpression::Divide(left, right) => {
                self.expression_is_float(left) || self.expression_is_float(right)
            }
            CExpression::StringLiteral(_)
            | CExpression::Void
            | CExpression::Call { .. }
            | CExpression::IndirectCall { .. }
            | CExpression::FunctionAddress(_)
            | CExpression::FloatClassification { .. }
            | CExpression::AddressOf(_)
            | CExpression::PointerOffsetBytes { .. }
            | CExpression::Subobject { .. }
            | CExpression::Int32Literal(_)
            | CExpression::UInt8Literal(_)
            | CExpression::UInt32Literal(_)
            | CExpression::Int64Literal(_)
            | CExpression::UInt64Literal(_)
            | CExpression::SizeOfStruct { .. }
            | CExpression::SizeOfUnion { .. }
            | CExpression::SizeOfType { .. }
            | crate::languages::c::syntax::c_comparison!(_, _)
            | CExpression::Not(_)
            | CExpression::And(_, _)
            | CExpression::Or(_, _)
            | CExpression::Remainder(_, _)
            | CExpression::ShiftLeft(_, _)
            | CExpression::ShiftRight(_, _)
            | CExpression::BitwiseAnd(_, _)
            | CExpression::BitwiseOr(_, _)
            | CExpression::BitwiseXor(_, _)
            | CExpression::BitwiseNot(_)
            | CExpression::AggregateAddress { .. }
            | CExpression::UnionAddress { .. } => false,
        }
    }

    fn expression_pointee_is_float(&self, expression: &CExpression) -> bool {
        let interface_type = match expression {
            CExpression::Variable(name) => self.variable_types.get(name).copied(),
            CExpression::Field { field_type, .. } | CExpression::UnionField { field_type, .. } => {
                Some(*field_type)
            }
            CExpression::SequentialRead { interface_type, .. }
            | CExpression::SequentialWrite { interface_type, .. } => Some(*interface_type),
            CExpression::Cast { interface_type, .. } => Some(*interface_type),
            CExpression::Assignment { interface_type, .. }
            | CExpression::ScalarUpdate { interface_type, .. } => Some(*interface_type),
            CExpression::StatementExpression { interface_type, .. } => Some(*interface_type),
            CExpression::Index(base, _, _) => {
                return self.expression_pointee_is_float(base);
            }
            _ => None,
        };
        matches!(
            interface_type,
            Some(
                InterfaceType::Float32Pointer
                    | InterfaceType::Float64Pointer
                    | InterfaceType::Float32Array(_)
                    | InterfaceType::Float64Array(_)
            )
        )
    }

    fn struct_pointer_name(&self, expression: &CExpression) -> Option<String> {
        match expression {
            CExpression::Assignment {
                interface_type,
                struct_name,
                ..
            }
            | CExpression::ScalarUpdate {
                interface_type,
                struct_name,
                ..
            } if interface_type.is_object_pointer()
                && !interface_type
                    .pointee_type()
                    .is_some_and(InterfaceType::is_pointer) =>
            {
                struct_name.clone()
            }
            CExpression::StepResult { struct_name, .. } => struct_name.clone(),
            CExpression::Variable(name)
                if matches!(
                    self.variable_types.get(name),
                    Some(
                        InterfaceType::Int32Pointer
                            | InterfaceType::UInt8Pointer
                            | InterfaceType::UInt8Array(_)
                    )
                ) =>
            {
                self.variable_structs.get(name).cloned()
            }
            CExpression::Call { function_name, .. } => self
                .function_declaration_for_call(function_name)
                .map(|function| function.return_pointer_struct_name.clone())
                .or_else(|| {
                    self.variable_function_pointers
                        .get(&self.resolve_name(function_name))
                        .map(|signature| signature.return_struct_name.clone())
                })
                .flatten(),
            CExpression::IndirectCall { signature, .. } => signature.return_struct_name.clone(),
            CExpression::Assignment { struct_name, .. }
            | CExpression::ScalarUpdate { struct_name, .. } => struct_name.clone(),
            CExpression::StatementExpression {
                interface_type: InterfaceType::Int32Pointer | InterfaceType::UInt8Pointer,
                struct_name,
                ..
            } => struct_name.clone(),
            CExpression::Field {
                field_type: InterfaceType::Int32Pointer | InterfaceType::UInt8Pointer,
                field_struct_name: Some(struct_name),
                ..
            } => Some(struct_name.clone()),
            CExpression::Index(base, _, _) => match base.as_ref() {
                CExpression::Field {
                    field_type: InterfaceType::PointerArray(_, _, _),
                    field_struct_name: Some(struct_name),
                    ..
                } => Some(struct_name.clone()),
                CExpression::Variable(name)
                    if matches!(
                        self.variable_types.get(name),
                        Some(InterfaceType::PointerArray(_, _, _))
                    ) =>
                {
                    self.variable_structs.get(name).cloned()
                }
                _ => None,
            },
            CExpression::Load(pointer, _) => self.struct_pointer_pointer_name(pointer),
            CExpression::SequentialRead { struct_name, .. }
            | CExpression::SequentialWrite { struct_name, .. } => struct_name.clone(),
            CExpression::AddressOf(target) => match target.as_ref() {
                CExpression::AggregateAddress { struct_name, .. } => Some(struct_name.clone()),
                CExpression::StatementExpression {
                    aggregate_lvalue: true,
                    ..
                } => self.aggregate_struct_name(target),
                CExpression::Variable(name) => self.variable_struct_values.get(name).cloned(),
                _ => None,
            },
            // The tag names what a one-level struct pointer points to. A cast
            // to `struct T **` points to a pointer cell, not to a struct.
            CExpression::Cast {
                struct_name: Some(struct_name),
                interface_type,
                ..
            } if !interface_type
                .pointee_type()
                .is_some_and(InterfaceType::is_pointer) =>
            {
                Some(struct_name.clone())
            }
            CExpression::Cast { interface_type, .. }
                if interface_type
                    .pointee_type()
                    .is_some_and(InterfaceType::is_pointer) =>
            {
                None
            }
            // A cast to another pointer type keeps the struct identity of
            // the pointer underneath; a cast to an integer does not, so an
            // `(unsigned long)p + 1` is integer arithmetic, not scaled
            // struct-pointer arithmetic.
            CExpression::Cast {
                expression,
                interface_type,
                ..
            } if interface_type.is_pointer() => self.struct_pointer_name(expression),
            CExpression::Add(left, _) | CExpression::Subtract(left, _) => {
                self.struct_pointer_name(left)
            }
            // `parse_conditional` has already required the two branches to
            // agree, with a null pointer constant taking the other's type.
            CExpression::Ternary {
                then_branch,
                else_branch,
                ..
            } => {
                if is_null_pointer_constant(then_branch) {
                    self.struct_pointer_name(else_branch)
                } else {
                    self.struct_pointer_name(then_branch)
                }
            }
            _ => None,
        }
    }

    fn struct_pointer_pointer_name(&self, expression: &CExpression) -> Option<String> {
        match expression {
            CExpression::StepResult { struct_name, .. } => struct_name.clone(),
            CExpression::Variable(name)
                if matches!(
                    self.variable_types.get(name),
                    Some(
                        InterfaceType::Int8PointerPointer
                            | InterfaceType::Int16PointerPointer
                            | InterfaceType::UInt16PointerPointer
                            | InterfaceType::Int32PointerPointer
                            | InterfaceType::CharPointerPointer(_)
                            | InterfaceType::UInt8PointerPointer
                            | InterfaceType::UInt32PointerPointer
                            | InterfaceType::Int128PointerPointer
                            | InterfaceType::Int64PointerPointer(_)
                            | InterfaceType::UInt128PointerPointer
                            | InterfaceType::UInt64PointerPointer(_)
                            | InterfaceType::Float32PointerPointer
                            | InterfaceType::Float64PointerPointer
                    )
                ) =>
            {
                self.variable_structs.get(name).cloned()
            }
            CExpression::Call { function_name, .. } => self
                .function_declaration_for_call(function_name)
                .map(|function| function.return_pointer_struct_name.clone())
                .or_else(|| {
                    self.variable_function_pointers
                        .get(&self.resolve_name(function_name))
                        .map(|signature| signature.return_struct_name.clone())
                })
                .flatten(),
            CExpression::IndirectCall { signature, .. } => signature.return_struct_name.clone(),
            CExpression::Assignment { struct_name, .. }
            | CExpression::ScalarUpdate { struct_name, .. } => struct_name.clone(),
            CExpression::StatementExpression {
                interface_type:
                    InterfaceType::Int8PointerPointer
                    | InterfaceType::Int16PointerPointer
                    | InterfaceType::UInt16PointerPointer
                    | InterfaceType::Int32PointerPointer
                    | InterfaceType::CharPointerPointer(_)
                    | InterfaceType::UInt8PointerPointer
                    | InterfaceType::UInt32PointerPointer
                    | InterfaceType::Int128PointerPointer
                    | InterfaceType::Int64PointerPointer(_)
                    | InterfaceType::UInt128PointerPointer
                    | InterfaceType::UInt64PointerPointer(_)
                    | InterfaceType::Float32PointerPointer
                    | InterfaceType::Float64PointerPointer,
                struct_name,
                ..
            } => struct_name.clone(),
            CExpression::Field {
                field_type:
                    InterfaceType::Int8PointerPointer
                    | InterfaceType::Int16PointerPointer
                    | InterfaceType::UInt16PointerPointer
                    | InterfaceType::Int32PointerPointer
                    | InterfaceType::CharPointerPointer(_)
                    | InterfaceType::UInt8PointerPointer
                    | InterfaceType::UInt32PointerPointer
                    | InterfaceType::Int128PointerPointer
                    | InterfaceType::Int64PointerPointer(_)
                    | InterfaceType::UInt128PointerPointer
                    | InterfaceType::UInt64PointerPointer(_)
                    | InterfaceType::Float32PointerPointer
                    | InterfaceType::Float64PointerPointer,
                field_struct_name: Some(struct_name),
                ..
            } => Some(struct_name.clone()),
            CExpression::AddressOf(target) => match target.as_ref() {
                CExpression::Variable(name)
                    if matches!(
                        self.variable_types.get(name),
                        Some(InterfaceType::Int32Pointer | InterfaceType::UInt8Pointer)
                    ) =>
                {
                    self.variable_structs.get(name).cloned()
                }
                CExpression::Field {
                    field_type: InterfaceType::Int32Pointer | InterfaceType::UInt8Pointer,
                    field_struct_name: Some(struct_name),
                    ..
                } => Some(struct_name.clone()),
                CExpression::Load(_, _) => self.struct_pointer_name(target),
                _ => None,
            },
            CExpression::SequentialRead { struct_name, .. }
            | CExpression::SequentialWrite { struct_name, .. } => struct_name.clone(),
            CExpression::Cast {
                struct_name: Some(struct_name),
                interface_type,
                ..
            } if interface_type
                .pointee_type()
                .is_some_and(InterfaceType::is_pointer) =>
            {
                Some(struct_name.clone())
            }
            CExpression::Cast { expression, .. } => self.struct_pointer_pointer_name(expression),
            CExpression::Add(left, _) | CExpression::Subtract(left, _) => {
                self.struct_pointer_pointer_name(left)
            }
            _ => None,
        }
    }

    fn validate_struct_pointer_value(
        &self,
        expected_struct: &str,
        expression: &CExpression,
    ) -> Result<(), CSyntaxError> {
        if matches!(expression, CExpression::Int32Literal(0)) {
            return Ok(());
        }
        // C permits assignment from an object-erased void pointer to an
        // object pointer without an explicit cast (C11 6.3.2.3).
        if self.source_expression_type(expression) == Some(InterfaceType::VoidPointer) {
            return Ok(());
        }
        match self.struct_pointer_name(expression) {
            Some(actual_struct) if actual_struct == expected_struct => Ok(()),
            Some(actual_struct) => Err(self.error_here(format!(
                "cannot use `struct {actual_struct} *` where `struct {expected_struct} *` is required"
            ))),
            None => Err(self.error_here(format!(
                "expected a pointer to `struct {expected_struct}`"
            ))),
        }
    }

    fn validate_struct_pointer_pointer_value(
        &self,
        expected_struct: &str,
        expression: &CExpression,
    ) -> Result<(), CSyntaxError> {
        if matches!(expression, CExpression::Int32Literal(0)) {
            return Ok(());
        }
        match self.struct_pointer_pointer_name(expression) {
            Some(actual_struct) if actual_struct == expected_struct => Ok(()),
            Some(actual_struct) => Err(self.error_here(format!(
                "cannot use `struct {actual_struct} **` where `struct {expected_struct} **` is required"
            ))),
            None => Err(self.error_here(format!(
                "expected a pointer to a pointer to `struct {expected_struct}`"
            ))),
        }
    }

    /// Retain source type identity before char and unsigned char lower to the
    /// same kernel byte type. This only inspects the expression being checked.
    fn source_expression_type(&self, expression: &CExpression) -> Option<InterfaceType> {
        match expression {
            CExpression::StepResult { interface_type, .. } => *interface_type,
            CExpression::StringLiteral(literal) => Some(InterfaceType::CharArray(
                literal.plain_char(),
                u32::try_from(literal.bytes().len()).expect("literal length fits u32"),
            )),
            CExpression::Variable(name) => self.variable_types.get(name).copied(),
            CExpression::FunctionAddress(name) => {
                self.function_declaration_for_call(name).map(|header| {
                    function_pointer_type(&function_pointer_signature_from_header(header))
                })
            }
            CExpression::Cast { interface_type, .. } => Some(*interface_type),
            CExpression::Assignment { interface_type, .. }
            | CExpression::ScalarUpdate { interface_type, .. } => Some(*interface_type),
            CExpression::StatementExpression { interface_type, .. } => Some(*interface_type),
            CExpression::Field { field_type, .. } | CExpression::UnionField { field_type, .. } => {
                Some(*field_type)
            }
            CExpression::SequentialRead { interface_type, .. }
            | CExpression::SequentialWrite { interface_type, .. } => Some(*interface_type),
            CExpression::Load(pointer, _) | CExpression::Index(pointer, _, _) => {
                self.source_expression_type(pointer)?.pointee_type()
            }
            CExpression::CheckedArrayIndex { index, .. } => self.source_expression_type(index),
            CExpression::AddressOf(value) => self.source_expression_type(value)?.pointer_type(),
            CExpression::PointerOffsetBytes { pointer, .. }
            | CExpression::Subobject { pointer, .. } => self.source_expression_type(pointer),
            CExpression::FloatNegate(value) => self.source_expression_type(value),
            CExpression::FloatClassification { .. }
            | crate::languages::c::syntax::c_comparison!(_, _)
            | CExpression::Not(_)
            | CExpression::And(_, _)
            | CExpression::Or(_, _) => Some(InterfaceType::Int32),
            CExpression::BitwiseNot(value) => {
                integer_promotion_type(self.source_expression_type(value)?)
            }
            CExpression::ShiftLeft(left, _) | CExpression::ShiftRight(left, _) => {
                integer_promotion_type(self.source_expression_type(left)?)
            }
            CExpression::Add(left, right) => {
                let left_type = self.source_expression_type(left)?;
                let right_type = self.source_expression_type(right)?;
                if left_type.is_object_pointer() && is_integer_type(right_type) {
                    Some(left_type)
                } else if right_type.is_object_pointer() && is_integer_type(left_type) {
                    Some(right_type)
                } else {
                    usual_arithmetic_conversion_type(left_type, right_type)
                }
            }
            CExpression::Subtract(left, right) => {
                let left_type = self.source_expression_type(left)?;
                let right_type = self.source_expression_type(right)?;
                if left_type.is_object_pointer() && is_integer_type(right_type) {
                    Some(left_type)
                } else if left_type.is_object_pointer() && right_type.is_object_pointer() {
                    Some(InterfaceType::Int64(LongRank::Long))
                } else {
                    usual_arithmetic_conversion_type(left_type, right_type)
                }
            }
            CExpression::Multiply(left, right)
            | CExpression::Divide(left, right)
            | CExpression::Remainder(left, right)
            | CExpression::BitwiseAnd(left, right)
            | CExpression::BitwiseOr(left, right)
            | CExpression::BitwiseXor(left, right) => usual_arithmetic_conversion_type(
                self.source_expression_type(left)?,
                self.source_expression_type(right)?,
            ),
            CExpression::Ternary {
                condition: _,
                then_branch,
                else_branch,
            } => ternary_expression_type(
                self.source_expression_type(then_branch),
                self.source_expression_type(else_branch),
                then_branch,
                else_branch,
            ),
            CExpression::Call { function_name, .. } => self
                .function_declaration_for_call(function_name)
                .map(|header| header.return_type),
            CExpression::IndirectCall { signature, .. } => Some(signature.return_type),
            CExpression::Int32Literal(_) => Some(InterfaceType::Int32),
            CExpression::UInt8Literal(_) => Some(InterfaceType::UInt8),
            CExpression::UInt32Literal(_) => Some(InterfaceType::UInt32),
            CExpression::Int64Literal(_) => Some(InterfaceType::Int64(LongRank::Long)),
            CExpression::UInt64Literal(_) => Some(InterfaceType::UInt64(LongRank::Long)),
            CExpression::SizeOfStruct { .. }
            | CExpression::SizeOfUnion { .. }
            | CExpression::SizeOfType { .. } => Some(InterfaceType::UInt64(LongRank::Long)),
            CExpression::Float32Literal(_) => Some(InterfaceType::Float32),
            CExpression::Float64Literal(_) => Some(InterfaceType::Float64),
            CExpression::Void
            | CExpression::AggregateAddress { .. }
            | CExpression::UnionAddress { .. } => None,
        }
    }

    /// Checks a value converted to `expected` by assignment, initialization,
    /// return, argument passing, or comparison. An uncast conversion between
    /// distinct pointers to one-byte character types (`char *`,
    /// `signed char *`, `unsigned char *`) is only a `-Wpointer-sign` (or, for
    /// a comparison, `-Wcompare-distinct-pointer-types`) warning in GCC and
    /// Clang, so it is accepted and lowered exactly as the explicit cast to
    /// the destination type: the kernel reads a one-byte cell through either
    /// character type as the same byte. Any other conversion between
    /// character pointers, such as `char **` to `unsigned char **`, is
    /// refused.
    fn validate_char_pointer_assignment(
        &self,
        expected: InterfaceType,
        expression: &mut CExpression,
    ) -> Result<(), CSyntaxError> {
        if let Some(interface_type) = self.character_pointer_conversion(expected, expression)? {
            let pointee_constant = self.expression_pointee_is_constant(expression);
            let value = std::mem::replace(expression, CExpression::Void);
            *expression = CExpression::Cast {
                expression: Box::new(value),
                interface_type,
                struct_name: None,
                pointee_volatile: false,
                pointee_constant,
                explicit_qualification: false,
            };
        }
        Ok(())
    }

    /// Checks the right operand of a pointer comparison against the left
    /// operand's type. Pointers to `long` and `long long` of either
    /// signedness compare after only a warning in GCC and Clang
    /// ("comparison of distinct pointer types lacks a cast"), so the operand
    /// is compared as the left operand's type; every other operand is checked
    /// as an assignment is.
    fn validate_pointer_comparison_operand(
        &self,
        expected: InterfaceType,
        expression: &mut CExpression,
    ) -> Result<(), CSyntaxError> {
        let actual = self
            .source_expression_type(expression)
            .map(decay_to_pointer);
        if actual
            .is_some_and(|actual| long_rank_pointers_differ(actual, decay_to_pointer(expected)))
        {
            let pointee_constant = self.expression_pointee_is_constant(expression);
            let value = std::mem::replace(expression, CExpression::Void);
            *expression = CExpression::Cast {
                expression: Box::new(value),
                interface_type: decay_to_pointer(expected),
                struct_name: None,
                pointee_volatile: false,
                pointee_constant,
                explicit_qualification: false,
            };
            return Ok(());
        }
        self.validate_char_pointer_assignment(expected, expression)
    }

    /// Refuses a character pointer operand that is not exactly `expected`'s
    /// type, where C gives the two operands no common type to convert to:
    /// the arms of `?:` (whose common type would be `void *`) and the
    /// operands of a pointer subtraction, which GCC and Clang refuse.
    fn validate_char_pointer_operands(
        &self,
        expected: InterfaceType,
        expression: &CExpression,
    ) -> Result<(), CSyntaxError> {
        match self.character_pointer_conversion(expected, expression)? {
            Some(interface_type) => {
                let actual = self
                    .source_expression_type(expression)
                    .map_or(interface_type, decay_to_pointer);
                Err(self.incompatible_character_pointers(interface_type, actual))
            }
            None => Ok(()),
        }
    }

    /// The pointer type an uncast character-pointer conversion of
    /// `expression` to `expected` casts to, `None` when no conversion is
    /// needed, or the refusal of an incompatible character pointer.
    fn character_pointer_conversion(
        &self,
        expected: InterfaceType,
        expression: &CExpression,
    ) -> Result<Option<InterfaceType>, CSyntaxError> {
        if !expected.is_pointer() && expected.pointee_type().is_none() {
            return Ok(None);
        }
        let Some(actual) = self.source_expression_type(expression) else {
            return Ok(None);
        };
        let initializes_array = !expected.is_pointer();
        let actual = decay_to_pointer(actual);
        let expected = decay_to_pointer(expected);
        // Preserve the existing byte-string literal extension for an array
        // the literal initializes. Its ordinary C source type remains char[].
        if initializes_array
            && expected == InterfaceType::UInt8Pointer
            && matches!(actual, InterfaceType::CharPointer(_))
            && matches!(expression, CExpression::StringLiteral(_))
        {
            return Ok(None);
        }
        if actual == expected
            || !actual.is_pointer()
            || !expected.is_pointer()
            || actual == InterfaceType::VoidPointer
            || expected == InterfaceType::VoidPointer
        {
            return Ok(None);
        }
        // GCC and Clang convert between pointers to the two signednesses of
        // one integer width with at most a `-Wpointer-sign` warning, and the
        // kernel reads a cell through either as its bits.
        // A struct or union pointer uses an integer pointer type as its
        // placeholder, so only a pointer to an actual integer converts.
        if same_width_integer_pointers(actual, expected)
            && (one_byte_pointer(actual) || self.struct_pointer_name(expression).is_none())
        {
            return Ok(Some(expected));
        }
        if long_rank_pointers_differ(actual, expected) {
            return Err(self.incompatible_long_rank_pointers(expected, actual));
        }
        // `uint8 *` also types the byte pointers lowering makes, so only the
        // other character pointer types identify a source-level mismatch.
        let is_char_pointer = |ty| {
            matches!(
                ty,
                InterfaceType::CharPointer(_)
                    | InterfaceType::CharPointerPointer(_)
                    | InterfaceType::Int8Pointer
                    | InterfaceType::Int8PointerPointer
            )
        };
        // GCC 14 rejects a pointer to `int *` converted to a pointer to
        // `unsigned int *` (`-Wincompatible-pointer-types`): only the first
        // level may differ in signedness.
        let signedness_pointer_pointers = actual
            .pointee_type()
            .zip(expected.pointee_type())
            .is_some_and(|(actual, expected)| {
                actual != expected && same_width_integer_pointers(actual, expected)
            });
        if is_char_pointer(actual) || is_char_pointer(expected) || signedness_pointer_pointers {
            return Err(self.incompatible_character_pointers(expected, actual));
        }
        Ok(None)
    }

    fn incompatible_character_pointers(
        &self,
        expected: InterfaceType,
        actual: InterfaceType,
    ) -> CSyntaxError {
        let is_character = |ty: InterfaceType| {
            let mut ty = ty;
            while let Some(pointee) = ty.pointee_type() {
                ty = pointee;
            }
            matches!(
                ty,
                InterfaceType::Char(_) | InterfaceType::Int8 | InterfaceType::UInt8
            )
        };
        let note = if is_character(expected) || is_character(actual) {
            "plain char, signed char, and unsigned char are distinct types"
        } else {
            "the signed and unsigned integer types of one width are distinct types"
        };
        self.error_here(format!(
            "incompatible C pointer types: expected `{}`, got `{}`; {note}",
            describe_pointer_cast_type(expected, None),
            describe_pointer_cast_type(actual, None),
        ))
    }

    fn incompatible_long_rank_pointers(
        &self,
        expected: InterfaceType,
        actual: InterfaceType,
    ) -> CSyntaxError {
        self.error_here(format!(
            "incompatible C pointer types: expected `{}`, got `{}`; long and long long are distinct types",
            describe_pointer_cast_type(expected, None),
            describe_pointer_cast_type(actual, None),
        ))
    }

    fn validate_pointer_cast(
        &self,
        expected: InterfaceType,
        expected_struct_name: Option<&str>,
        expression: &CExpression,
        cast_position: &ErrorContext,
    ) -> Result<(), CSyntaxError> {
        let Some(actual) = self.source_expression_type(expression) else {
            return Ok(());
        };
        let actual = decay_to_pointer(actual);
        let expected = decay_to_pointer(expected);
        if !actual.is_pointer() || !expected.is_pointer() {
            return Ok(());
        }

        let actual_struct_name = if actual.pointee_type().is_some_and(InterfaceType::is_pointer) {
            self.struct_pointer_pointer_name(expression)
        } else {
            self.struct_pointer_name(expression)
        };
        let refusal = || {
            let expected = describe_pointer_cast_type(expected, expected_struct_name);
            let actual = describe_pointer_cast_type(actual, actual_struct_name.as_deref());
            cast_position.error(format!(
                "incompatible C pointer types: retyping object-pointer casts are unsupported; expected `{expected}`, got `{actual}`"
            ))
        };
        if !actual.is_object_pointer() || !expected.is_object_pointer() {
            return Err(refusal());
        }

        // An opaque void pointer is the supported way to carry an object
        // pointer through a type-erased interface. A one-level conversion
        // between the signednesses of one integer width, or between
        // character types, is the other: C11 6.5p7 lets the signed or
        // unsigned type corresponding to an object's type access it, and the
        // kernel reads a cell of either signedness through either type as
        // its bits. Neither case retypes an ordinary typed object pointer in
        // the memory model.
        let signedness_cast = same_width_integer_pointers(expected, actual)
            && actual != expected
            && actual_struct_name.is_none()
            && expected_struct_name.is_none();
        // C character pointers inspect a local bit-field record's object
        // representation. Retyping to any wider scalar remains restricted.
        let bit_field_representation_cast = one_byte_pointer(expected)
            && actual_struct_name
                .as_ref()
                .is_some_and(|name| self.bit_field_records.contains_key(name));
        if expected == InterfaceType::VoidPointer
            || actual == InterfaceType::VoidPointer
            || signedness_cast
            || bit_field_representation_cast
        {
            return Ok(());
        }

        if actual != expected || actual_struct_name.as_deref() != expected_struct_name {
            return Err(refusal());
        }
        Ok(())
    }

    fn validate_struct_pointer_assignment(
        &self,
        expected_struct: Option<&String>,
        target_type: Option<InterfaceType>,
        expression: &mut CExpression,
    ) -> Result<(), CSyntaxError> {
        if let Some(target_type) = target_type {
            self.validate_char_pointer_assignment(target_type, expression)?;
        }
        let Some(expected_struct) = expected_struct else {
            return Ok(());
        };
        match target_type {
            Some(
                InterfaceType::Int32Pointer
                | InterfaceType::CharPointer(_)
                | InterfaceType::UInt8Pointer
                | InterfaceType::Float32Pointer
                | InterfaceType::Float64Pointer,
            ) => self.validate_struct_pointer_value(expected_struct, expression),
            Some(
                InterfaceType::Int8PointerPointer
                | InterfaceType::Int16PointerPointer
                | InterfaceType::UInt16PointerPointer
                | InterfaceType::Int32PointerPointer
                | InterfaceType::CharPointerPointer(_)
                | InterfaceType::UInt8PointerPointer
                | InterfaceType::UInt32PointerPointer
                | InterfaceType::Int128PointerPointer
                | InterfaceType::Int64PointerPointer(_)
                | InterfaceType::UInt128PointerPointer
                | InterfaceType::UInt64PointerPointer(_)
                | InterfaceType::Float32PointerPointer
                | InterfaceType::Float64PointerPointer,
            ) => self.validate_struct_pointer_pointer_value(expected_struct, expression),
            _ => Ok(()),
        }
    }

    fn dereference_expression(&self, pointer: CExpression) -> CExpression {
        if let Some(struct_name) = self.struct_pointer_name(&pointer) {
            CExpression::AggregateAddress {
                pointer: Box::new(pointer),
                struct_name,
            }
        } else {
            let loaded_type = self.classed_pointee_type(&pointer);
            CExpression::Load(Box::new(pointer), loaded_type)
        }
    }

    /// `base[index]`, carrying the element type when its access class needs
    /// it.
    fn index_expression(&self, base: CExpression, index: CExpression) -> CExpression {
        let element_type = self.classed_pointee_type(&base);
        CExpression::Index(Box::new(base), Box::new(index), element_type)
    }

    /// The type `*pointer` loads, with its access class, when the kernel
    /// type of the loaded value cannot give the class: a `long` or
    /// `long long`, a pointer whose pointee the kernel type erases, or an
    /// `int *` that `pointer` is known not to hold as a struct pointer.
    fn classed_pointee_type(&self, pointer: &CExpression) -> Option<CClassedType> {
        let pointee = self.source_expression_type(pointer)?.pointee_type()?;
        let class = pointee.access_class().or_else(|| {
            self.points_to_no_struct(pointer)
                .then(|| int_pointer_class(pointee))
                .flatten()
        })?;
        (crate::kernel::effective_type::CAccessClass::of_kernel_type(pointee.to_kernel_type())
            .as_ref()
            != Some(&class))
        .then_some(CClassedType {
            interface_type: pointee,
            class,
        })
    }

    /// Whether what `pointer` points to is known not to involve a struct:
    /// a variable or member declared without one. Other expressions are not
    /// known, and their loads stay unclassed.
    fn points_to_no_struct(&self, pointer: &CExpression) -> bool {
        match pointer {
            CExpression::Variable(name) => !self.variable_structs.contains_key(name),
            CExpression::Field {
                field_struct_name, ..
            } => field_struct_name.is_none(),
            _ => false,
        }
    }

    /// The strict-aliasing class of struct `name`
    /// (`design/effective-types.md`): what its members, embedded structs
    /// and unions contain at any depth.
    fn struct_class(&self, name: &str) -> crate::kernel::effective_type::CStructClass {
        struct_class_in(name, &self.structs, &self.unions)
    }

    /// The class a local of type `interface_type` records, when the struct it may
    /// name says more than the type: a struct pointer or an array of
    /// structs, or, when it names none, an `int *`, `int **` or byte array,
    /// whose types the frontend shares with struct pointers and arrays.
    fn local_declared_class(
        &self,
        interface_type: InterfaceType,
        struct_name: Option<&str>,
    ) -> Option<crate::kernel::effective_type::CAccessClass> {
        use crate::kernel::effective_type::{CAccessClass, CPointeeBase, CScalarClass};
        match struct_name {
            Some(name) if matches!(interface_type, InterfaceType::UInt8Array(_)) => {
                Some(CAccessClass::Struct(self.struct_class(name)))
            }
            Some(name) => struct_pointer_class(
                interface_type,
                CPointeeBase::Struct(self.struct_class(name)),
            ),
            None => match interface_type {
                InterfaceType::Int8Array(_) | InterfaceType::UInt8Array(_) => {
                    Some(CAccessClass::Scalar(CScalarClass::Char))
                }
                _ => int_pointer_class(interface_type),
            },
        }
    }

    /// The access class of a member access to `field` through struct
    /// `container`. A struct-pointer member's class carries its pointee's
    /// contents, so a pointer loaded from it designates a known struct.
    fn member_access_class(
        &self,
        container: &str,
        field: &RecordField,
    ) -> Option<crate::kernel::effective_type::CAccessClass> {
        let member = match field.struct_name.as_deref() {
            Some(name) if field.interface_type.is_pointer() => struct_pointer_class(
                field.interface_type,
                crate::kernel::effective_type::CPointeeBase::Struct(self.struct_class(name)),
            ),
            Some(_) => return None,
            None => field
                .interface_type
                .access_class()
                .or_else(|| int_pointer_class(field.interface_type)),
        };
        Some(crate::kernel::effective_type::CAccessClass::member(
            self.struct_class(container),
            member,
        ))
    }

    fn resolve_field_access(
        &self,
        base: &CExpression,
        field_name: &str,
    ) -> Result<
        (
            CExpression,
            InterfaceType,
            Option<String>,
            Option<String>,
            Option<CallbackInterface>,
            Option<Vec<u32>>,
            bool,
            Option<crate::kernel::effective_type::CAccessClass>,
        ),
        CSyntaxError,
    > {
        let (struct_name, union_name) = match base {
            CExpression::Assignment { .. } => (self.struct_pointer_name(base), None),
            CExpression::Call { .. }
            | CExpression::IndirectCall { .. }
            | CExpression::Ternary { .. }
            | CExpression::StatementExpression { .. } => (self.aggregate_struct_name(base), None),
            CExpression::StepResult { struct_name, .. } => (struct_name.clone(), None),
            CExpression::Variable(base_name) => {
                (self.variable_structs.get(base_name).cloned(), None)
            }
            CExpression::Field {
                field_struct_name, ..
            } => {
                if self.struct_array_field_info(base).is_some() {
                    return Err(self.error_here(
                        "arrays of embedded structs require an index before field access",
                    ));
                }
                (field_struct_name.clone(), None)
            }
            CExpression::Load(_, _) | CExpression::Index(_, _, _) => {
                (self.struct_pointer_name(base), None)
            }
            CExpression::SequentialRead {
                interface_type,
                struct_name,
                ..
            }
            | CExpression::SequentialWrite {
                interface_type,
                struct_name,
                ..
            } if interface_type.is_object_pointer() => (struct_name.clone(), None),
            CExpression::AggregateAddress { struct_name, .. } => (Some(struct_name.clone()), None),
            CExpression::UnionAddress { union_name, .. } => (None, Some(union_name)),
            CExpression::Cast {
                struct_name: Some(struct_name),
                ..
            } => (Some(struct_name.clone()), None),
            _ => (None, None),
        };
        if let Some(struct_name) = struct_name {
            let layout = self.structs.get(&struct_name).ok_or_else(|| {
                self.error_here(format!(
                    "cannot access field through incomplete struct `{struct_name}`"
                ))
            })?;
            let field = layout.fields.get(field_name).ok_or_else(|| {
                self.error_here(format!(
                    "struct `{struct_name}` has no field `{field_name}`"
                ))
            })?;
            if field.long_double {
                return Err(self.error_here(
                    "long double member value operations need an extended-precision model",
                ));
            }
            return Ok((
                member_pointer(base.clone(), field),
                field.interface_type,
                field.struct_name.clone(),
                field.union_name.clone(),
                field.function_pointer_signature.clone(),
                field.array_shape.clone(),
                field.pointee_constant,
                self.member_access_class(&struct_name, field),
            ));
        }
        if let Some(union_name) = union_name {
            let layout = self.unions.get(union_name).ok_or_else(|| {
                self.error_here(format!("unknown union declaration `{union_name}`"))
            })?;
            let field = layout.fields.get(field_name).ok_or_else(|| {
                self.error_here(format!("union `{union_name}` has no member `{field_name}`"))
            })?;
            if field.long_double {
                return Err(self.error_here(
                    "long double member value operations need an extended-precision model",
                ));
            }
            if field.struct_name.is_some()
                || field.union_name.is_some()
                || matches!(
                    field.interface_type,
                    InterfaceType::Int32Array(_)
                        | InterfaceType::Int128Array(_)
                        | InterfaceType::Int64Array(_, _)
                        | InterfaceType::UInt128Array(_)
                        | InterfaceType::UInt64Array(_, _)
                        | InterfaceType::CharArray(_, _)
                        | InterfaceType::UInt8Array(_)
                        | InterfaceType::Float32Array(_)
                        | InterfaceType::Float64Array(_)
                        | InterfaceType::PointerArray(_, _, _)
                )
            {
                return Err(self.error_here(format!(
                    "union `{union_name}` member `{field_name}` has a parsed ABI layout but compound member access is not yet supported"
                )));
            }
            return Ok((
                offset_field_pointer(base.clone(), field.offset_bytes),
                field.interface_type,
                None,
                None,
                None,
                None,
                field.pointee_constant,
                None,
            ));
        }
        Err(self.error_here(format!(
            "cannot access field `{field_name}` through a non-struct-pointer expression"
        )))
    }

    fn resolve_array_struct_field_access(
        &self,
        base: &CExpression,
        field_name: &str,
    ) -> Result<
        (
            CExpression,
            InterfaceType,
            Option<String>,
            Option<String>,
            Option<CallbackInterface>,
            Option<Vec<u32>>,
            bool,
            Option<crate::kernel::effective_type::CAccessClass>,
        ),
        CSyntaxError,
    > {
        let (element_pointer, struct_name) = match base {
            CExpression::Index(array, index, _) => {
                let struct_name = match array.as_ref() {
                    CExpression::Variable(name)
                        if self.variable_array_shapes.contains_key(name)
                            || self.incomplete_array_names.contains(name) =>
                    {
                        self.variable_structs.get(name).cloned()
                    }
                    CExpression::Cast {
                        expression,
                        interface_type,
                        ..
                    } if *interface_type == InterfaceType::UInt8Pointer
                        && self.struct_pointer_name(expression).is_some() =>
                    {
                        self.struct_pointer_name(expression)
                    }
                    _ => {
                        return Err(self
                            .error_here("`.` currently supports only indexed arrays of structs"));
                    }
                };
                let struct_name = struct_name.ok_or_else(|| {
                    self.error_here("`.` currently supports only indexed arrays of structs")
                })?;
                (CExpression::Add(array.clone(), index.clone()), struct_name)
            }
            CExpression::AggregateAddress {
                pointer,
                struct_name,
            } => (pointer.as_ref().clone(), struct_name.clone()),
            _ => {
                return Err(
                    self.error_here("`.` currently supports only indexed arrays of structs")
                );
            }
        };
        let layout = self.structs.get(&struct_name).ok_or_else(|| {
            self.error_here(format!("unknown struct declaration `{struct_name}`"))
        })?;
        let field = layout.fields.get(field_name).ok_or_else(|| {
            self.error_here(format!(
                "struct `{struct_name}` has no field `{field_name}`"
            ))
        })?;
        if field.long_double {
            return Err(self.error_here(
                "long double member value operations need an extended-precision model",
            ));
        }
        Ok((
            member_pointer(element_pointer, field),
            field.interface_type,
            field.struct_name.clone(),
            field.union_name.clone(),
            field.function_pointer_signature.clone(),
            field.array_shape.clone(),
            field.pointee_constant,
            self.member_access_class(&struct_name, field),
        ))
    }

    /// Constant conveniences are fallbacks, not C identifier reservations.
    /// Actual macros have already expanded before this parser sees the source.
    fn unbound_constant_expression(&self, name: &str) -> Option<CExpression> {
        let expression = match name {
            "true" => CExpression::Int32Literal(1),
            "false" => CExpression::Int32Literal(0),
            "INFINITY" => CExpression::Float64Literal(0x7ff0_0000_0000_0000),
            "NAN" => CExpression::Float64Literal(0x7ff8_0000_0000_0000),
            "INFINITYF" => CExpression::Float32Literal(0x7f80_0000),
            "NANF" => CExpression::Float32Literal(0x7fc0_0000),
            _ => return None,
        };
        if self.out_of_scope_names.contains(name)
            || self.variable_types.contains_key(&self.resolve_name(name))
            || self.function_declarations.contains_key(name)
        {
            None
        } else {
            Some(expression)
        }
    }

    fn parse_static_assert(&mut self) -> Result<(), CSyntaxError> {
        self.expect_ident_spelling("_Static_assert")?;
        self.expect(Token::LParen)?;
        let condition = self.parse_expression()?;
        self.expect(Token::Comma)?;
        let mut message = Vec::new();
        if !matches!(self.peek(), Some(Token::StringLiteral(_))) {
            return Err(self.error_here("`_Static_assert` requires a string literal message"));
        }
        while let Some(Token::StringLiteral(piece)) = self.peek().cloned() {
            self.position += 1;
            message.extend(piece);
        }
        self.expect(Token::RParen)?;
        self.expect(Token::Semicolon)?;
        let value = evaluate_static_integer_expression(&condition).map_err(|_| {
            self.error_here("`_Static_assert` requires a defined integer constant expression")
        })?;
        if !static_integer_is_true(value) {
            return Err(self.error_here(format!(
                "static assertion failed: {}",
                String::from_utf8_lossy(&message)
            )));
        }
        Ok(())
    }

    fn parse_builtin_offsetof(&mut self) -> Result<CExpression, CSyntaxError> {
        self.expect_ident_spelling("__builtin_offsetof")?;
        self.expect(Token::LParen)?;
        let ty = self.parse_type()?;
        if !is_plain_struct_type(&ty) {
            return Err(self.error_here("`__builtin_offsetof` requires a complete struct type"));
        }
        let name = ty.struct_name.as_ref().expect("plain struct has a tag");
        self.expect(Token::Comma)?;
        let member = self.expect_ident("offsetof member name")?;
        if self.peek() != Some(&Token::RParen) {
            return Err(
                self.error_here("`__builtin_offsetof` currently supports a direct struct member")
            );
        }
        self.expect(Token::RParen)?;
        let layout = self
            .structs
            .get(name)
            .or_else(|| {
                self.bit_field_records
                    .get(name)
                    .map(|record| &record.storage)
            })
            .ok_or_else(|| {
                self.error_here(format!(
                    "`__builtin_offsetof` requires complete struct `{name}`"
                ))
            })?;
        let field = layout
            .fields
            .get(&member)
            .ok_or_else(|| self.error_here(format!("struct `{name}` has no member `{member}`")))?;
        // size_t is unsigned 64-bit on both supported x86-64 targets.
        Ok(CExpression::UInt64Literal(u64::from(field.offset_bytes)))
    }

    fn parse_types_compatible_operand(&mut self) -> Result<ParsedType, CSyntaxError> {
        let ty = self.parse_type()?;
        if ty.compatibility_identity == CompatibilityIdentity::Unavailable
            || ty.enum_name.is_some()
            || ty.function_pointer_signature.is_some()
            || ty.long_double
            || ty.opaque_builtin
        {
            return Err(self.error_here("`__builtin_types_compatible_p` requires retained C type identity; expression typeof supports struct values only, and enum/function types are not supported"));
        }
        Ok(ty)
    }

    fn parse_types_compatible(&mut self) -> Result<CExpression, CSyntaxError> {
        self.position += 1;
        self.expect(Token::LParen)?;
        let left = self.parse_types_compatible_operand()?;
        self.expect(Token::Comma)?;
        let right = self.parse_types_compatible_operand()?;
        self.expect(Token::RParen)?;
        // GNU compatibility ignores only the outermost const/volatile
        // qualifiers, not the qualifications of pointed-to types.
        let compatible = left.interface_type == right.interface_type
            && left.struct_name == right.struct_name
            && left.union_name == right.union_name
            && left.pointee_constant == right.pointee_constant
            && (left.volatile_levels >> 1) == (right.volatile_levels >> 1);
        Ok(CExpression::Int32Literal(u32::from(compatible)))
    }

    fn parse_primary(&mut self) -> Result<CExpression, CSyntaxError> {
        if let Some(object) = self.local_bit_field_object().cloned() {
            if object.is_pointer()
                && !self.bit_field_forbidden_operand
                && self.peek_next() != Some(&object.member_operator())
            {
                self.position += 1;
                return Ok(object.source_pointer());
            }
            return self.parse_local_bit_field_read(object);
        }
        if self.peek_ident() == Some("__builtin_offsetof") {
            return self.parse_builtin_offsetof();
        }
        if self.peek_ident() == Some("__builtin_types_compatible_p") {
            return self.parse_types_compatible();
        }
        if self.peek() == Some(&Token::LParen) && self.peek_next() == Some(&Token::LBrace) {
            // The statements inside belong to the statement this expression
            // is part of; they are not its children as written.
            self.source_regions.push(None);
            let expression = self.parse_statement_expression();
            self.source_regions.pop();
            return expression;
        }
        if self.peek_ident() == Some("sizeof") && self.peek_next() == Some(&Token::LParen) {
            self.position += 2;
            if self.peek_ident() == Some("struct") {
                self.position += 1;
                let name = self.expect_ident("struct name")?;
                self.expect(Token::RParen)?;
                let bytes = self
                    .structs
                    .get(&name)
                    .map(|layout| layout.size_bytes)
                    .or_else(|| {
                        self.bit_field_records
                            .get(&name)
                            .map(|record| record.size_bytes())
                    })
                    .ok_or_else(|| {
                        self.error_here(format!("unknown struct declaration `{name}`"))
                    })?;
                return Ok(CExpression::SizeOfStruct { name, bytes });
            }
            if self.peek_ident() == Some("union") {
                self.position += 1;
                let name = self.expect_ident("union name")?;
                self.expect(Token::RParen)?;
                let bytes = self
                    .unions
                    .get(&name)
                    .ok_or_else(|| self.error_here(format!("unknown union declaration `{name}`")))?
                    .size_bytes;
                return Ok(CExpression::SizeOfUnion { name, bytes });
            }
            if let Some(object) = self.local_bit_field_object()
                && self.peek_next() == Some(&Token::RParen)
            {
                let bytes = if object.is_pointer() {
                    8
                } else {
                    object.size_bytes()
                };
                self.position += 2;
                return Ok(CExpression::UInt64Literal(u64::from(bytes)));
            }
            if !self.is_type_start() {
                // `sizeof(expression)`: the operand is not evaluated; only
                // its type is used, as for GNU `typeof`.
                let operand = self.parse_unevaluated_type_operand()?;
                self.expect(Token::RParen)?;
                if let CExpression::Variable(name) = &operand
                    && self.incomplete_array_names.contains(name)
                {
                    return Err(self.error_here("`sizeof` requires a complete array type"));
                }
                // A complete array object, such as `char tmp[12]` or a
                // string literal, is not converted to a pointer here: its
                // size is the whole array's (C11 6.3.2.1p3, 6.5.3.4p2).
                if matches!(
                    &operand,
                    CExpression::Variable(_)
                        | CExpression::StringLiteral(_)
                        | CExpression::StatementExpression {
                            aggregate_lvalue: true,
                            ..
                        }
                ) && let Some(interface_type) = self.source_expression_type(&operand)
                    && interface_type.array_length().is_some()
                {
                    return Ok(CExpression::SizeOfType {
                        interface_type,
                        struct_name: None,
                        bytes: interface_type.abi_size_bytes(),
                    });
                }
                if let Some(name) = self.aggregate_struct_name(&operand) {
                    let bytes = self
                        .structs
                        .get(&name)
                        .expect("aggregate operand has a layout")
                        .size_bytes;
                    return Ok(CExpression::SizeOfStruct { name, bytes });
                }
                let interface_type = self
                    .source_expression_type(&operand)
                    .filter(|interface_type| {
                        (interface_type.is_pointer() || is_arithmetic_type(*interface_type))
                            && self.aggregate_struct_name(&operand).is_none()
                    })
                    .ok_or_else(|| {
                        self.error_at_previous(
                            "`sizeof` of an expression requires a modeled scalar or pointer operand",
                        )
                    })?;
                return Ok(CExpression::SizeOfType {
                    interface_type,
                    struct_name: None,
                    bytes: interface_type.abi_size_bytes(),
                });
            }
            let parsed_type = self.parse_type_with_anonymous_struct(false, true, false)?;
            self.expect(Token::RParen)?;
            if parsed_type.interface_type == InterfaceType::Void {
                return Err(self.error_at_previous("`sizeof(void)` is not supported"));
            }
            if let (InterfaceType::Int32, Some(name)) =
                (parsed_type.interface_type, &parsed_type.struct_name)
            {
                let bytes = self
                    .structs
                    .get(name)
                    .ok_or_else(|| self.error_here(format!("unknown struct declaration `{name}`")))?
                    .size_bytes;
                return Ok(CExpression::SizeOfStruct {
                    name: (name.clone()),
                    bytes,
                });
            }
            if let (InterfaceType::Int32, Some(name)) =
                (parsed_type.interface_type, &parsed_type.union_name)
            {
                let bytes = self
                    .unions
                    .get(name)
                    .ok_or_else(|| self.error_here(format!("unknown union declaration `{name}`")))?
                    .size_bytes;
                return Ok(CExpression::SizeOfUnion {
                    name: (name.clone()),
                    bytes,
                });
            }
            return Ok(CExpression::SizeOfType {
                interface_type: parsed_type.interface_type,
                struct_name: parsed_type.struct_name,
                bytes: parsed_type.interface_type.abi_size_bytes(),
            });
        }
        let at = self.error_context();
        match self.next() {
            Some(Token::Ident(name)) => {
                if let Some(value) = self.enum_constants.get(&name) {
                    return Ok(value.clone());
                }
                if let Some(expression) = self.unbound_constant_expression(&name) {
                    return Ok(expression);
                }
                if self.peek() == Some(&Token::LParen) {
                    // A source file may call a function defined in a
                    // different C source. The translation-unit linker
                    // resolves that name after each source is parsed.
                    Ok(CExpression::Variable(self.resolve_name(&name)))
                } else if let Some(address) = self.bare_function_designator(&name)? {
                    Ok(address)
                } else {
                    Ok(CExpression::Variable(
                        self.resolve_object_name(&name, at.position)?,
                    ))
                }
            }
            Some(Token::Number(number)) => {
                if is_floating_literal(&number) {
                    parse_float_literal_expression(&number).map_err(|reason| {
                        at.error(format!(
                            "invalid floating-point literal `{number}`: {reason}"
                        ))
                    })
                } else {
                    parse_integer_literal_expression(&number).map_err(|reason| {
                        at.error(format!("invalid integer literal `{number}`: {reason}"))
                    })
                }
            }
            Some(Token::CharLiteral(value)) => Ok(self.character_constant(value)),
            Some(Token::StringLiteral(mut bytes)) => {
                // C concatenates adjacent string-literal tokens during
                // translation phase 6. Keep this at the source boundary so
                // one concatenated sequence still gets one stable literal
                // object, rather than exposing an implementation-dependent
                // pointer relationship between its pieces.
                while matches!(self.peek(), Some(Token::StringLiteral(_))) {
                    let Some(Token::StringLiteral(next)) = self.next() else {
                        unreachable!("the peeked token was a string literal")
                    };
                    bytes.extend(next);
                }
                Ok(self.string_literal_expression(bytes))
            }
            Some(Token::LParen) => {
                let expression = self.parse_expression()?;
                self.expect(Token::RParen)?;
                Ok(expression)
            }
            Some(token) => Err(at.error(format!("expected expression, got {}", token.describe()))),
            None => Err(at.error("expected expression, got end of input")),
        }
    }

    /// Parse the GNU `({ statements; value; })` expression. The final
    /// expression is kept separate from the compound body until the ordinary
    /// expression-lowering pass can materialize its value in a temporary.
    fn parse_statement_expression(&mut self) -> Result<CExpression, CSyntaxError> {
        self.expect(Token::LParen)?;
        self.expect(Token::LBrace)?;
        self.push_scope();
        let mut statements = Vec::new();

        loop {
            if self.peek().is_none() {
                return Err(self
                    .error_here("expected a final expression or `}` in GNU statement expression"));
            }
            if self.peek() == Some(&Token::RBrace) {
                return Err(
                    self.error_here("GNU statement expressions require a final scalar expression")
                );
            }

            // A statement expression's final value is an ordinary C
            // expression statement. Probe on a cloned parser so a preceding
            // assignment or control statement can still use the normal C
            // statement parser without leaking speculative state.
            let mut candidate = self.clone();
            if let Ok(value) = candidate.parse_expression()
                && candidate.peek() == Some(&Token::Semicolon)
                && candidate.peek_next() == Some(&Token::RBrace)
            {
                candidate.position += 1;
                let interface_type = candidate.source_expression_type(&value).ok_or_else(|| {
                    candidate.error_here(
                        "GNU statement expression final values must have a modeled scalar type",
                    )
                })?;
                if !(is_arithmetic_type(interface_type) || interface_type.is_pointer())
                    || contains_aggregate_value(&value)
                    || candidate.aggregate_struct_name(&value).is_some()
                {
                    return Err(candidate.error_here(
                        "GNU statement expressions require a modeled scalar or pointer final value",
                    ));
                }
                let struct_name = candidate.struct_pointer_name(&value);
                let function_pointer_signature = candidate.function_pointer_signature(&value);
                let pointee_constant = candidate.expression_pointee_is_constant(&value);
                *self = candidate;
                self.expect(Token::RBrace)?;
                self.expect(Token::RParen)?;
                let body = balanced_statement_sequence(statements).unwrap_or(CStatement::Skip);
                if statement_contains_control_transfer(&body) {
                    return Err(self.error_here(
                        "GNU statement expressions cannot contain `return`, `break`, or `continue` in this slice",
                    ));
                }
                let body = self.lower_call_expressions(body)?;
                let (body, scope_lifetimes) = self.compound_literal_block_storage(body);
                self.pop_scope();
                return Ok(CExpression::StatementExpression {
                    aggregate_lvalue: false,
                    initializer_call: None,
                    initializer_assignment: None,
                    scope_lifetimes,
                    body: Box::new(body),
                    value: Box::new(value),
                    interface_type,
                    struct_name,
                    function_pointer_signature,
                    pointee_constant,
                });
            }

            statements.push(self.parse_statement()?);
        }
    }

    fn expect(&mut self, expected: Token) -> Result<(), CSyntaxError> {
        let at = self.error_context();
        match self.next() {
            Some(token) if token == expected => Ok(()),
            Some(token) => Err(at.error(format!(
                "expected {}, got {}",
                expected.describe(),
                token.describe()
            ))),
            None => Err(at.error(format!(
                "expected {}, got end of input",
                expected.describe()
            ))),
        }
    }

    fn expect_ident(&mut self, label: &str) -> Result<String, CSyntaxError> {
        let at = self.error_context();
        match self.next() {
            Some(Token::Ident(name)) => Ok(name),
            Some(token) => Err(at.error(format!("expected {label}, got {}", token.describe()))),
            None => Err(at.error(format!("expected {label}, got end of input"))),
        }
    }

    fn expect_ident_spelling(&mut self, expected: &str) -> Result<(), CSyntaxError> {
        let at = self.error_context();
        match self.next() {
            Some(Token::Ident(name)) if name == expected => Ok(()),
            Some(token) => {
                Err(at.error(format!("expected `{expected}`, got {}", token.describe())))
            }
            None => Err(at.error(format!("expected `{expected}`, got end of input"))),
        }
    }

    /// Captures the position of the next unconsumed token so an error can
    /// still point at it after the token is consumed.
    fn error_context(&self) -> ErrorContext {
        ErrorContext {
            position: self.here(),
        }
    }

    /// `function_name` is the function just parsed, used to point at where the
    /// trailing tokens begin.
    fn expect_end(&self, function_name: &str) -> Result<(), CSyntaxError> {
        if self.position == self.tokens.len() {
            Ok(())
        } else {
            // Trailing tokens after a complete function almost always mean a
            // second function definition: name that restriction instead of
            // reporting a bare "expected end of input".
            Err(self.error_here(format!(
                "each C source file holds exactly one function; \
                 put the next definition in its own file and add another \
                 `verifying` line (got {} after the end of `{function_name}`)",
                self.tokens[self.position].describe(),
            )))
        }
    }

    fn peek(&self) -> Option<&Token> {
        self.tokens.get(self.position)
    }

    fn peek_next(&self) -> Option<&Token> {
        self.tokens.get(self.position + 1)
    }

    fn peek_n(&self, offset: usize) -> Option<&Token> {
        self.tokens.get(self.position + offset)
    }

    fn peek_inline_specifier(&self) -> bool {
        self.peek_n(0).is_some_and(Self::is_inline_specifier)
    }

    fn is_inline_specifier(token: &Token) -> bool {
        matches!(token, Token::Ident(name) if name == "inline" || name == "__always_inline")
    }

    fn is_type_start_at(&self, offset: usize) -> bool {
        match self.peek_n(offset) {
            Some(Token::Ident(name)) => {
                matches!(name.as_str(), "const" | "volatile")
                    || is_builtin_type_start(name)
                    || self.typedefs.contains_key(name)
            }
            _ => false,
        }
    }

    fn peek_ident(&self) -> Option<&str> {
        match self.peek() {
            Some(Token::Ident(name)) => Some(name),
            _ => None,
        }
    }

    fn next(&mut self) -> Option<Token> {
        let token = self.tokens.get(self.position).cloned();
        if token.is_some() {
            self.position += 1;
        }
        token
    }
}

mod bit_field_layout;
mod bit_fields;
mod compound_literals;
mod initializers;
mod row_pointers;

mod type_declarations;

mod global_declarations;

fn static_integer_value(expression: &CExpression) -> Option<u32> {
    match expression {
        CExpression::Int32Literal(value) => Some(*value),
        CExpression::UInt8Literal(value) => Some(u32::from(*value)),
        CExpression::UInt32Literal(value) => Some(*value),
        CExpression::Add(left, right) => {
            static_integer_value(left)?.checked_add(static_integer_value(right)?)
        }
        CExpression::Subtract(left, right) => {
            static_integer_value(left)?.checked_sub(static_integer_value(right)?)
        }
        CExpression::Multiply(left, right) => {
            static_integer_value(left)?.checked_mul(static_integer_value(right)?)
        }
        _ => None,
    }
}

fn flatten_array_indices(
    indexes: Vec<CExpression>,
    dimensions: &[u32],
    unbounded_outer: bool,
) -> CExpression {
    let mut terms = Vec::with_capacity(indexes.len());
    for (index, expression) in indexes.into_iter().enumerate() {
        let length = dimensions[index];
        let expression = if unbounded_outer && index == 0 {
            expression
        } else {
            match static_integer_value(&expression) {
                Some(value) if value < length => expression,
                _ => CExpression::CheckedArrayIndex {
                    index: Box::new(expression),
                    length,
                },
            }
        };
        let stride = dimensions[index + 1..]
            .iter()
            .copied()
            .fold(1u32, |stride, dimension| {
                stride
                    .checked_mul(dimension)
                    .expect("validated array shape has a representable stride")
            });
        terms.push(if stride == 1 {
            expression
        } else {
            CExpression::Multiply(
                Box::new(expression),
                Box::new(CExpression::Int32Literal(stride)),
            )
        });
    }
    let mut terms = terms.into_iter();
    let mut offset = terms
        .next()
        .expect("a multidimensional access has at least one index");
    for term in terms {
        offset = CExpression::Add(Box::new(offset), Box::new(term));
    }
    offset
}

fn parse_integer_literal_magnitude(literal: &str) -> Result<u64, &'static str> {
    let (digits, suffix) = integer_literal_parts(literal);
    let (digits, radix) = if let Some(hex_digits) = digits.strip_prefix("0x") {
        (hex_digits, 16)
    } else if let Some(hex_digits) = digits.strip_prefix("0X") {
        (hex_digits, 16)
    } else if digits.starts_with('0') && digits.len() > 1 {
        (&digits[1..], 8)
    } else {
        (digits, 10)
    };
    if digits.is_empty() {
        return Err("missing digits");
    }
    let normalized_suffix = suffix.to_ascii_lowercase();
    if suffix.contains("lL")
        || suffix.contains("Ll")
        || !matches!(
            normalized_suffix.as_str(),
            "" | "u" | "l" | "ll" | "ul" | "lu" | "ull" | "llu"
        )
    {
        return Err("unsupported integer-literal suffix");
    }
    u64::from_str_radix(digits, radix).map_err(|_| match radix {
        8 => "digits are not valid for an octal literal or the value is too large",
        16 => "digits are not valid for a hexadecimal literal or the value is too large",
        _ => "the value is too large",
    })
}

fn function_pointer_signature_from_header(header: &CFunctionHeader) -> CallbackInterface {
    CallbackInterface::new(
        header.return_type,
        header.return_pointer_struct_name.clone(),
        header
            .parameters
            .iter()
            .map(|parameter| {
                CallbackParameter::new(
                    parameter.interface_type,
                    parameter.struct_name.clone(),
                    parameter.pointee_constant,
                )
            })
            .collect(),
        header.return_pointee_constant,
    )
}

fn function_pointer_type(signature: &CallbackInterface) -> InterfaceType {
    InterfaceType::FunctionPointer(
        crate::kernel::ProgramType::qualified_function_pointer_signature(
            signature.return_type().to_kernel_type(),
            signature.return_pointee_constant,
            &signature
                .parameters()
                .iter()
                .map(|parameter| {
                    (
                        parameter.interface_type().to_kernel_type(),
                        parameter.pointee_constant,
                    )
                })
                .collect::<Vec<_>>(),
        ),
    )
}

/// Whether `left` and `right` are pointers of the same depth to 64-bit
/// integers of different `long`/`long long` rank, whatever their signedness:
/// GCC and Clang refuse to convert between them implicitly, since `long` and
/// `long long` are distinct types even where they share a representation.
fn long_rank_pointers_differ(left: InterfaceType, right: InterfaceType) -> bool {
    let depth = |ty: InterfaceType| ty.pointee_type().is_some_and(InterfaceType::is_pointer);
    left.is_pointer()
        && right.is_pointer()
        && depth(left) == depth(right)
        && matches!(
            (left.long_rank(), right.long_rank()),
            (Some(left), Some(right)) if left != right
        )
}

/// An array type's element pointer type; any other type unchanged.
/// Pointers to the two signednesses of one integer width, or to two of the
/// character types, at one level of indirection: C11 6.5p7 lets either type
/// access the object, GCC and Clang convert between them with at most a
/// `-Wpointer-sign` warning, and the kernel reads a cell through either as
/// its bits (`ProgramType::read_cell`).
fn one_byte_pointer(ty: InterfaceType) -> bool {
    matches!(
        ty,
        InterfaceType::CharPointer(_) | InterfaceType::Int8Pointer | InterfaceType::UInt8Pointer
    )
}

/// `long *` and `unsigned long long *` differ in rank as well as signedness,
/// so they are not such a pair.
fn same_width_integer_pointers(left: InterfaceType, right: InterfaceType) -> bool {
    let width = |ty| match ty {
        InterfaceType::CharPointer(_)
        | InterfaceType::Int8Pointer
        | InterfaceType::UInt8Pointer => Some((1, None)),
        InterfaceType::Int16Pointer | InterfaceType::UInt16Pointer => Some((2, None)),
        InterfaceType::Int32Pointer | InterfaceType::UInt32Pointer => Some((4, None)),
        InterfaceType::Int64Pointer(rank) | InterfaceType::UInt64Pointer(rank) => {
            Some((8, Some(rank)))
        }
        _ => None,
    };
    width(left).is_some_and(|width_left| width(right) == Some(width_left))
}

fn decay_to_pointer(ty: InterfaceType) -> InterfaceType {
    if ty.is_pointer() {
        ty
    } else {
        ty.pointee_type()
            .and_then(InterfaceType::pointer_type)
            .unwrap_or(ty)
    }
}

fn describe_pointer_cast_type(interface_type: InterfaceType, struct_name: Option<&str>) -> String {
    // The kernel spelling erases `long`/`long long` rank; spell it in C.
    let spelling = match interface_type {
        InterfaceType::CharPointer(_) => "char*".to_string(),
        InterfaceType::CharPointerPointer(_) => "char**".to_string(),
        InterfaceType::FunctionPointer(_) => return "function pointer".to_string(),
        InterfaceType::Int64Pointer(rank) => format!("{}*", rank.signed_spelling()),
        InterfaceType::UInt64Pointer(rank) => format!("{}*", rank.unsigned_spelling()),
        InterfaceType::Int64PointerPointer(rank) => format!("{}**", rank.signed_spelling()),
        InterfaceType::UInt64PointerPointer(rank) => format!("{}**", rank.unsigned_spelling()),
        _ => crate::kernel::program_type_spelling(interface_type.to_kernel_type()).to_string(),
    };
    let base = spelling.trim_end_matches('*');
    let pointers = &spelling[base.len()..];
    match struct_name {
        Some(name) => format!("struct {name} {pointers}"),
        None => format!("{base} {pointers}"),
    }
}

fn describe_function_pointer_signature(signature: &CallbackInterface) -> String {
    let parameters = signature
        .parameters
        .iter()
        .map(|parameter| {
            let ty = match &parameter.struct_name {
                Some(name) => format!("struct {name}*"),
                None => parameter.interface_type.ranked_diagnostic_name(),
            };
            if parameter.pointee_constant {
                format!("const {ty}")
            } else {
                ty
            }
        })
        .collect::<Vec<_>>()
        .join(", ");
    let return_type = match &signature.return_struct_name {
        Some(name) => format!("struct {name}*"),
        None => signature.return_type.ranked_diagnostic_name(),
    };
    let qualifier = if signature.return_pointee_constant {
        "const "
    } else {
        ""
    };
    format!("{qualifier}{return_type} ({parameters})")
}

fn integer_literal_parts(literal: &str) -> (&str, &str) {
    let suffix_start = if literal.starts_with("0x") || literal.starts_with("0X") {
        literal[2..]
            .find(|character: char| !character.is_ascii_hexdigit())
            .map_or(literal.len(), |offset| offset + 2)
    } else {
        literal
            .find(|character: char| character.is_ascii_alphabetic())
            .unwrap_or(literal.len())
    };
    literal.split_at(suffix_start)
}

// The rungs mirror C's integer-literal type ladder verbatim, including the
// final `u64::MAX` rung that a `u64` magnitude always satisfies.
#[allow(clippy::absurd_extreme_comparisons)]
fn parse_integer_literal_expression(literal: &str) -> Result<CExpression, &'static str> {
    let magnitude = parse_integer_literal_magnitude(literal)?;
    let (digits, suffix) = integer_literal_parts(literal);
    let suffix = suffix.to_ascii_lowercase();
    let is_hex = digits.starts_with("0x") || digits.starts_with("0X");
    let is_non_decimal = is_hex || digits.starts_with('0') && digits.len() > 1;
    let has_long = matches!(suffix.as_str(), "l" | "ll" | "ul" | "lu" | "ull" | "llu");
    let has_unsigned = matches!(suffix.as_str(), "u" | "ul" | "lu" | "ull" | "llu");

    if has_long {
        if has_unsigned {
            return if magnitude <= u64::MAX {
                Ok(CExpression::UInt64Literal(magnitude))
            } else {
                Err("the value is too large")
            };
        }
        return if magnitude <= i64::MAX as u64 {
            Ok(CExpression::Int64Literal(magnitude as i64))
        } else if is_non_decimal && magnitude <= u64::MAX {
            Ok(CExpression::UInt64Literal(magnitude))
        } else {
            Err("the value is too large for a signed integer literal")
        };
    }

    if has_unsigned {
        return if magnitude <= u32::MAX as u64 {
            Ok(CExpression::UInt32Literal(magnitude as u32))
        } else if magnitude <= u64::MAX {
            Ok(CExpression::UInt64Literal(magnitude))
        } else {
            Err("the value is too large")
        };
    }

    if is_non_decimal && magnitude > i32::MAX as u64 && magnitude <= u32::MAX as u64 {
        return Ok(CExpression::UInt32Literal(magnitude as u32));
    }
    if magnitude <= i32::MAX as u64 {
        Ok(CExpression::Int32Literal(magnitude as u32))
    } else if magnitude <= i64::MAX as u64 {
        Ok(CExpression::Int64Literal(magnitude as i64))
    } else if is_non_decimal && magnitude <= u64::MAX {
        Ok(CExpression::UInt64Literal(magnitude))
    } else {
        Err("the value is too large for a signed integer literal")
    }
}

fn negate_integer_literal_expression(expression: CExpression) -> CExpression {
    match expression {
        CExpression::Int32Literal(value) => CExpression::Int32Literal(0u32.wrapping_sub(value)),
        CExpression::UInt32Literal(value) => CExpression::UInt32Literal(0u32.wrapping_sub(value)),
        CExpression::Int64Literal(value) => CExpression::Int64Literal(-value),
        CExpression::UInt64Literal(value) => CExpression::UInt64Literal(0u64.wrapping_sub(value)),
        _ => unreachable!("integer literal parser returned a non-integer expression"),
    }
}

fn is_floating_literal(literal: &str) -> bool {
    !literal.starts_with("0x")
        && !literal.starts_with("0X")
        && literal
            .chars()
            .any(|character| matches!(character, '.' | 'e' | 'E'))
}

fn parse_float_literal_expression(literal: &str) -> Result<CExpression, &'static str> {
    let (number, suffix) = match literal.chars().last() {
        Some(character) if character.is_ascii_alphabetic() => {
            literal.split_at(literal.len() - character.len_utf8())
        }
        _ => (literal, ""),
    };
    match suffix {
        "" => number
            .parse::<f64>()
            .ok()
            .filter(|value| value.is_finite())
            .map(|value| CExpression::Float64Literal(value.to_bits()))
            .ok_or("value is not a finite binary64 literal"),
        "f" | "F" => number
            .parse::<f32>()
            .ok()
            .filter(|value| value.is_finite())
            .map(|value| CExpression::Float32Literal(value.to_bits()))
            .ok_or("value is not a finite binary32 literal"),
        "l" | "L" => Err("long double literals are not modeled by Click"),
        _ => Err("unsupported floating-point literal suffix"),
    }
}

fn negate_float_literal(expression: CExpression) -> Option<CExpression> {
    match expression {
        CExpression::Float32Literal(bits) => Some(CExpression::Float32Literal(bits ^ 0x8000_0000)),
        CExpression::Float64Literal(bits) => {
            Some(CExpression::Float64Literal(bits ^ 0x8000_0000_0000_0000))
        }
        _ => None,
    }
}

fn parse_float_classification_call(
    function_name: &str,
    arguments: &[CExpression],
) -> Option<Result<CExpression, &'static str>> {
    let classification = match function_name {
        "isfinite" => CFloatClassification::Finite,
        "isinf" => CFloatClassification::Infinite,
        "iszero" => CFloatClassification::Zero,
        "issubnormal" => CFloatClassification::Subnormal,
        "isnan" => CFloatClassification::Nan,
        _ => return None,
    };
    if arguments.len() != 1 {
        return Some(Err(
            "floating classification predicates require one argument",
        ));
    }
    let result = match &arguments[0] {
        CExpression::Float32Literal(bits) => {
            classify_float_bits(u64::from(*bits), 8, 23, classification_name(classification))
        }
        CExpression::Float64Literal(bits) => {
            classify_float_bits(*bits, 11, 52, classification_name(classification))
        }
        _ => {
            return Some(Ok(CExpression::FloatClassification {
                expression: Box::new(arguments[0].clone()),
                classification,
            }));
        }
    };
    Some(Ok(CExpression::Int32Literal(u32::from(result))))
}

fn classification_name(classification: CFloatClassification) -> &'static str {
    match classification {
        CFloatClassification::Finite => "isfinite",
        CFloatClassification::Infinite => "isinf",
        CFloatClassification::Zero => "iszero",
        CFloatClassification::Subnormal => "issubnormal",
        CFloatClassification::Nan => "isnan",
    }
}

fn classify_float_bits(
    bits: u64,
    exponent_bits: u32,
    fraction_bits: u32,
    classification: &str,
) -> bool {
    let exponent_mask = (1u64 << exponent_bits) - 1;
    let exponent = (bits >> fraction_bits) & exponent_mask;
    let fraction = bits & ((1u64 << fraction_bits) - 1);
    let all_ones = exponent == exponent_mask;
    let zero_exponent = exponent == 0;
    match classification {
        "isfinite" => !all_ones,
        "isinf" => all_ones && fraction == 0,
        "iszero" => zero_exponent && fraction == 0,
        "issubnormal" => zero_exponent && fraction != 0,
        "isnan" => all_ones && fraction != 0,
        _ => unreachable!("classification was validated by the caller"),
    }
}

fn tokenize(source: &str) -> Result<(Vec<Token>, Vec<SourcePosition>), CSyntaxError> {
    // Sized once from the byte length, an upper bound on the characters:
    // collecting from `chars()` regrows from a quarter of it, and each
    // regrowth touches fresh pages.
    let mut chars = Vec::with_capacity(source.len());
    chars.extend(source.chars());
    let mut cursor = SourcePositionCursor::new(None);
    let mut cursor_index = 0;
    let mut tokens = Vec::new();
    let mut positions = Vec::new();
    let mut index = 0;

    while index < chars.len() {
        let ch = chars[index];
        // Each scan below only moves `index` forward.
        for &passed in &chars[cursor_index..index] {
            cursor.advance(passed);
        }
        cursor_index = index;
        let position = cursor.position();
        if ch.is_whitespace() {
            index += 1;
            continue;
        }

        if ch == '/' && chars.get(index + 1) == Some(&'/') {
            index += 2;
            while index < chars.len() && chars[index] != '\n' {
                index += 1;
            }
            continue;
        }

        if ch == '/' && chars.get(index + 1) == Some(&'*') {
            index += 2;
            while index + 1 < chars.len() && !(chars[index] == '*' && chars[index + 1] == '/') {
                index += 1;
            }
            if index + 1 >= chars.len() {
                return Err(CSyntaxError::at(position, "unterminated block comment"));
            }
            index += 2;
            continue;
        }

        if ch == '.' && chars.get(index + 1) == Some(&'.') && chars.get(index + 2) == Some(&'.') {
            tokens.push(Token::Ellipsis);
            positions.push(position);
            index += 3;
            continue;
        }

        if is_ident_start(ch) {
            let start = index;
            index += 1;
            while index < chars.len() && is_ident_continue(chars[index]) {
                index += 1;
            }
            tokens.push(Token::Ident(chars[start..index].iter().collect()));
            positions.push(position);
            continue;
        }

        if ch.is_ascii_digit()
            || (ch == '.' && chars.get(index + 1).is_some_and(char::is_ascii_digit))
        {
            let start = index;
            if ch == '0' && matches!(chars.get(index + 1), Some('x') | Some('X')) {
                index += 2;
                while index < chars.len() && chars[index].is_ascii_hexdigit() {
                    index += 1;
                }
                if matches!(chars.get(index), Some('.' | 'p' | 'P')) {
                    return Err(CSyntaxError::at(
                        position,
                        "hexadecimal floating-point literals are not supported by Click",
                    ));
                }
            } else {
                index += 1;
                while index < chars.len() && chars[index].is_ascii_digit() {
                    index += 1;
                }
                if chars.get(index) == Some(&'.') {
                    index += 1;
                    while index < chars.len() && chars[index].is_ascii_digit() {
                        index += 1;
                    }
                }
                if matches!(chars.get(index), Some('e' | 'E')) {
                    index += 1;
                    if matches!(chars.get(index), Some('+' | '-')) {
                        index += 1;
                    }
                    while index < chars.len() && chars[index].is_ascii_digit() {
                        index += 1;
                    }
                }
            }
            while index < chars.len() && chars[index].is_ascii_alphabetic() {
                index += 1;
            }
            tokens.push(Token::Number(chars[start..index].iter().collect()));
            positions.push(position);
            continue;
        }

        if ch == '\'' {
            let (value, next_index) = parse_char_literal(&chars, index)
                .map_err(|error| error.with_position(position.clone()))?;
            tokens.push(Token::CharLiteral(value));
            positions.push(position);
            index = next_index;
            continue;
        }

        if ch == '"' {
            let (value, next_index) = parse_string_literal(&chars, index)
                .map_err(|error| error.with_position(position.clone()))?;
            tokens.push(Token::StringLiteral(value));
            positions.push(position);
            index = next_index;
            continue;
        }

        if index + 2 < chars.len() {
            let token = match (ch, chars[index + 1], chars[index + 2]) {
                ('<', '<', '=') => Some(Token::ShiftLeftEqual),
                ('>', '>', '=') => Some(Token::ShiftRightEqual),
                _ => None,
            };
            if let Some(token) = token {
                tokens.push(token);
                positions.push(position);
                index += 3;
                continue;
            }
        }

        if index + 1 < chars.len() {
            let token = match (ch, chars[index + 1]) {
                ('=', '=') => Some(Token::EqualEqual),
                ('!', '=') => Some(Token::BangEqual),
                ('&', '&') => Some(Token::AmpAmp),
                ('|', '|') => Some(Token::PipePipe),
                ('<', '<') => Some(Token::ShiftLeft),
                ('>', '>') => Some(Token::ShiftRight),
                ('<', '=') => Some(Token::LessEqual),
                ('>', '=') => Some(Token::GreaterEqual),
                ('-', '>') => Some(Token::Arrow),
                ('+', '+') => Some(Token::PlusPlus),
                ('+', '=') => Some(Token::PlusEqual),
                ('-', '-') => Some(Token::MinusMinus),
                ('-', '=') => Some(Token::MinusEqual),
                ('*', '=') => Some(Token::StarEqual),
                ('^', '=') => Some(Token::CaretEqual),
                ('/', '=') => Some(Token::SlashEqual),
                ('%', '=') => Some(Token::PercentEqual),
                ('&', '=') => Some(Token::AmpEqual),
                ('|', '=') => Some(Token::PipeEqual),
                _ => None,
            };
            if let Some(token) = token {
                tokens.push(token);
                positions.push(position);
                index += 2;
                continue;
            }
        }

        let token = match ch {
            '(' => Token::LParen,
            ')' => Token::RParen,
            '[' => Token::LBracket,
            ']' => Token::RBracket,
            '{' => Token::LBrace,
            '}' => Token::RBrace,
            ',' => Token::Comma,
            ';' => Token::Semicolon,
            '+' => Token::Plus,
            '-' => Token::Minus,
            '<' => Token::LessThan,
            '>' => Token::GreaterThan,
            '*' => Token::Star,
            '.' => Token::Dot,
            '/' => Token::Slash,
            '%' => Token::Percent,
            '&' => Token::Amp,
            '|' => Token::Pipe,
            '^' => Token::Caret,
            '~' => Token::Tilde,
            '!' => Token::Bang,
            '=' => Token::Equal,
            '?' => Token::Question,
            ':' => Token::Colon,
            _ => {
                return Err(CSyntaxError::at(
                    position,
                    format!("unexpected character `{ch}`"),
                ));
            }
        };
        tokens.push(token);
        positions.push(position);
        index += 1;
    }

    Ok((tokens, positions))
}

fn balanced_statement_sequence(mut statements: Vec<CStatement>) -> Option<CStatement> {
    while statements.len() > 1 {
        let mut next_level = Vec::with_capacity(statements.len().div_ceil(2));
        let mut iter = statements.into_iter();
        while let Some(first) = iter.next() {
            next_level.push(match iter.next() {
                Some(second) => CStatement::Seq(Box::new(first), Box::new(second)),
                None => first,
            });
        }
        statements = next_level;
    }
    statements.pop()
}

/// A site at `position` quoting `text`, without a trailing comment and
/// bounded to [`SITE_TEXT_LIMIT`] characters, with `…` marking a statement
/// that continues past it.
fn statement_site(position: &SourcePosition, text: &str, continues: bool) -> CSite {
    let text = without_trailing_comment(text).trim();
    if text.is_empty() {
        return CSite::NONE;
    }
    let mut excerpt = text.chars().take(SITE_TEXT_LIMIT).collect::<String>();
    if continues || text.chars().count() > SITE_TEXT_LIMIT {
        excerpt.push_str(" …");
    }
    CSite(Some(std::sync::Arc::new(CStatementSite {
        position: position.clone(),
        text: excerpt.into_boxed_str(),
        source_path: None,
        source_bindings: None,
    })))
}

/// The source width of a token whose spelling is fixed or recorded, so a
/// site can end its excerpt just after a statement's last token.
fn token_source_width(token: &Token) -> Option<usize> {
    Some(match token {
        Token::Ident(name) | Token::Number(name) => name.chars().count(),
        Token::CharLiteral(_) | Token::StringLiteral(_) => return None,
        Token::LParen
        | Token::RParen
        | Token::LBracket
        | Token::RBracket
        | Token::LBrace
        | Token::RBrace
        | Token::Comma
        | Token::Semicolon
        | Token::Plus
        | Token::Minus
        | Token::Dot
        | Token::LessThan
        | Token::GreaterThan
        | Token::Bang
        | Token::Star
        | Token::Slash
        | Token::Percent
        | Token::Amp
        | Token::Pipe
        | Token::Caret
        | Token::Tilde
        | Token::Equal
        | Token::Question
        | Token::Colon => 1,
        Token::PlusPlus
        | Token::PlusEqual
        | Token::Arrow
        | Token::MinusMinus
        | Token::MinusEqual
        | Token::LessEqual
        | Token::ShiftLeft
        | Token::GreaterEqual
        | Token::ShiftRight
        | Token::EqualEqual
        | Token::BangEqual
        | Token::AmpAmp
        | Token::PipePipe
        | Token::StarEqual
        | Token::CaretEqual
        | Token::SlashEqual
        | Token::PercentEqual
        | Token::AmpEqual
        | Token::PipeEqual => 2,
        Token::Ellipsis | Token::ShiftLeftEqual | Token::ShiftRightEqual => 3,
    })
}

/// `text` up to a `//` or `/*` comment that starts outside a literal.
fn without_trailing_comment(text: &str) -> &str {
    let mut quote = None;
    let mut escaped = false;
    let mut previous = None;
    for (index, character) in text.char_indices() {
        if let Some(delimiter) = quote {
            if escaped {
                escaped = false;
            } else if character == '\\' {
                escaped = true;
            } else if character == delimiter {
                quote = None;
            }
        } else if character == '"' || character == '\'' {
            quote = Some(character);
        } else if previous == Some('/') && (character == '/' || character == '*') {
            return &text[..index - 1];
        }
        previous = Some(character);
    }
    text
}

/// Gives `site` to every statement in `statement` that can carry one and has
/// none yet: the statements one source statement lowered to. A statement
/// that already has a site was filled, with everything inside it, when it
/// got that site, so its subtree is not walked again. Iterative because
/// long blocks are deep `Seq` chains.
fn fill_missing_sites(statement: &mut CStatement, site: &CSite) {
    if site.is_none() {
        return;
    }
    let mut pending = vec![statement];
    while let Some(next) = pending.pop() {
        if let Some(own) = next.site_mut() {
            if !own.is_none() {
                continue;
            }
            *own = site.clone();
        }
        match next {
            CStatement::Seq(first, second) => {
                pending.push(second);
                pending.push(first);
            }
            CStatement::Label { statement, .. } => pending.push(statement),
            CStatement::If {
                then_branch,
                else_branch,
                ..
            } => {
                pending.push(else_branch);
                pending.push(then_branch);
            }
            CStatement::While { test, body, .. } | CStatement::DoWhile { test, body, .. } => {
                pending.push(body);
                if let Some(test) = test {
                    pending.push(test);
                }
            }
            CStatement::For {
                test,
                initializer,
                step,
                body,
                ..
            } => {
                pending.push(body);
                pending.push(step);
                pending.push(initializer);
                if let Some(test) = test {
                    pending.push(test);
                }
            }
            CStatement::Switch { cases, .. } => {
                pending.extend(cases.iter_mut().map(|case| case.body.as_mut()));
            }
            _ => {}
        }
    }
}

/// `statement` after `prefix`, the statements its lowering moved ahead of
/// it; each takes the statement's site, being part of what it does.
fn prepend_statements(mut prefix: Vec<CStatement>, statement: CStatement) -> CStatement {
    if prefix.is_empty() {
        return statement;
    }
    if let Some(site) = statement.site() {
        for generated in &mut prefix {
            fill_missing_sites(generated, site);
        }
    }
    let mut statements = prefix;
    statements.push(statement);
    balanced_statement_sequence(statements).expect("the statement prefix is non-empty")
}

/// Generated array-bound checks are pure proof statements and may safely be
/// combined when one expression contains more than one indexed subobject.
/// Calls still require the existing sequencing restriction.
fn prefix_has_non_assertion(prefix: &[CStatement]) -> bool {
    prefix
        .iter()
        .any(|statement| !matches!(statement, CStatement::Assert { .. }))
}

fn first_embedded_call_position(expression: &CExpression) -> Option<SourcePosition> {
    match expression {
        CExpression::ScalarUpdate { .. } => None,
        CExpression::Call {
            position,
            arguments,
            ..
        } => position
            .clone()
            .or_else(|| arguments.iter().find_map(first_embedded_call_position)),
        CExpression::IndirectCall {
            function,
            position,
            arguments,
            ..
        } => position
            .clone()
            .or_else(|| first_embedded_call_position(function))
            .or_else(|| arguments.iter().find_map(first_embedded_call_position)),
        CExpression::StatementExpression {
            initializer_call,
            value,
            ..
        } => initializer_call
            .clone()
            .or_else(|| first_embedded_call_position(value)),
        CExpression::Assignment { value, .. } => first_embedded_call_position(value),
        CExpression::Cast { expression, .. }
        | CExpression::FloatNegate(expression)
        | CExpression::FloatClassification { expression, .. }
        | CExpression::AddressOf(expression)
        | CExpression::PointerOffsetBytes {
            pointer: expression,
            ..
        }
        | CExpression::Subobject {
            pointer: expression,
            ..
        }
        | CExpression::Not(expression)
        | CExpression::BitwiseNot(expression)
        | CExpression::Load(expression, _) => first_embedded_call_position(expression),
        CExpression::SequentialRead { target, .. } => first_embedded_call_position(target),
        CExpression::SequentialWrite { target, value, .. } => {
            first_embedded_call_position(target).or_else(|| first_embedded_call_position(value))
        }
        CExpression::AggregateAddress { pointer, .. }
        | CExpression::Field { pointer, .. }
        | CExpression::UnionField { pointer, .. }
        | CExpression::UnionAddress { pointer, .. } => first_embedded_call_position(pointer),
        CExpression::Ternary {
            condition,
            then_branch,
            else_branch,
        } => first_embedded_call_position(condition)
            .or_else(|| first_embedded_call_position(then_branch))
            .or_else(|| first_embedded_call_position(else_branch)),
        crate::languages::c::syntax::binary_c_expression!(left, right) => {
            first_embedded_call_position(left).or_else(|| first_embedded_call_position(right))
        }
        CExpression::CheckedArrayIndex { index, .. } => first_embedded_call_position(index),
        CExpression::StringLiteral(_)
        | CExpression::Void
        | CExpression::Variable(_)
        | CExpression::StepResult { .. }
        | CExpression::FunctionAddress(_)
        | CExpression::Int32Literal(_)
        | CExpression::UInt8Literal(_)
        | CExpression::UInt32Literal(_)
        | CExpression::Int64Literal(_)
        | CExpression::UInt64Literal(_)
        | CExpression::Float32Literal(_)
        | CExpression::Float64Literal(_)
        | CExpression::SizeOfStruct { .. }
        | CExpression::SizeOfUnion { .. }
        | CExpression::SizeOfType { .. } => None,
    }
}

/// The names a chain of simple assignments `a = b = value` assigns, when
/// `expression` is such a chain and `value` holds no further assignment.
fn assignment_chain_targets(expression: &CExpression) -> Option<Vec<BindingName>> {
    // A load through a post-updated automatic pointer writes only that pointer
    // cell. This permits unrelated scalar accumulators in `sum += *p++`.
    match expression {
        CExpression::ScalarUpdate { name, .. } => return Some(vec![name.clone()]),
        CExpression::Load(pointer, _)
        | CExpression::Cast {
            expression: pointer,
            ..
        }
        | CExpression::PointerOffsetBytes { pointer, .. }
        | CExpression::Subobject { pointer, .. } => {
            return assignment_chain_targets(pointer);
        }
        _ => {}
    }
    let mut targets = Vec::new();
    let mut current = expression;
    while let CExpression::Assignment { name, value, .. } = current {
        targets.push(name.clone());
        current = value;
    }
    (!targets.is_empty() && first_assignment_position(current).is_none()).then_some(targets)
}

fn first_assignment_position(expression: &CExpression) -> Option<SourcePosition> {
    match expression {
        CExpression::ScalarUpdate { position, .. } => position.clone(),
        CExpression::Assignment {
            position, value, ..
        } => position
            .clone()
            .or_else(|| first_assignment_position(value)),
        CExpression::Call { arguments, .. } => arguments.iter().find_map(first_assignment_position),
        CExpression::IndirectCall {
            function,
            arguments,
            ..
        } => first_assignment_position(function)
            .or_else(|| arguments.iter().find_map(first_assignment_position)),
        CExpression::StatementExpression {
            initializer_assignment,
            value,
            ..
        } => initializer_assignment
            .clone()
            .or_else(|| first_assignment_position(value)),
        CExpression::Cast {
            expression: value, ..
        }
        | CExpression::FloatNegate(value)
        | CExpression::FloatClassification {
            expression: value, ..
        }
        | CExpression::AddressOf(value)
        | CExpression::PointerOffsetBytes { pointer: value, .. }
        | CExpression::Subobject { pointer: value, .. }
        | CExpression::Not(value)
        | CExpression::BitwiseNot(value)
        | CExpression::Load(value, _)
        | CExpression::SequentialRead { target: value, .. }
        | CExpression::AggregateAddress { pointer: value, .. }
        | CExpression::Field { pointer: value, .. }
        | CExpression::UnionField { pointer: value, .. }
        | CExpression::UnionAddress { pointer: value, .. }
        | CExpression::CheckedArrayIndex { index: value, .. } => first_assignment_position(value),
        CExpression::SequentialWrite { target, value, .. } => {
            first_assignment_position(target).or_else(|| first_assignment_position(value))
        }
        CExpression::Ternary {
            condition,
            then_branch,
            else_branch,
        } => first_assignment_position(condition)
            .or_else(|| first_assignment_position(then_branch))
            .or_else(|| first_assignment_position(else_branch)),
        crate::languages::c::syntax::binary_c_expression!(left, right) => {
            first_assignment_position(left).or_else(|| first_assignment_position(right))
        }
        CExpression::StringLiteral(_)
        | CExpression::Void
        | CExpression::Variable(_)
        | CExpression::StepResult { .. }
        | CExpression::FunctionAddress(_)
        | CExpression::Int32Literal(_)
        | CExpression::UInt8Literal(_)
        | CExpression::UInt32Literal(_)
        | CExpression::Int64Literal(_)
        | CExpression::UInt64Literal(_)
        | CExpression::Float32Literal(_)
        | CExpression::Float64Literal(_)
        | CExpression::SizeOfStruct { .. }
        | CExpression::SizeOfUnion { .. }
        | CExpression::SizeOfType { .. } => None,
    }
}

/// A deliberately conservative companion to assignment lowering. If a
/// sibling operand computes any runtime value, moving an assignment before
/// it would choose an order C leaves unspecified (and can turn an
/// unsequenced modification/read into defined behavior), so that shape is
/// refused rather than guessed.
fn expression_reads_runtime_value(expression: &CExpression) -> bool {
    match expression {
        CExpression::ScalarUpdate { .. } => true,
        CExpression::StringLiteral(_)
        | CExpression::Void
        | CExpression::FunctionAddress(_)
        | CExpression::Int32Literal(_)
        | CExpression::UInt8Literal(_)
        | CExpression::UInt32Literal(_)
        | CExpression::Int64Literal(_)
        | CExpression::UInt64Literal(_)
        | CExpression::Float32Literal(_)
        | CExpression::Float64Literal(_)
        | CExpression::SizeOfStruct { .. }
        | CExpression::SizeOfUnion { .. }
        | CExpression::SizeOfType { .. } => false,
        CExpression::Variable(_)
        | CExpression::StepResult { .. }
        | CExpression::Call { .. }
        | CExpression::IndirectCall { .. }
        | CExpression::StatementExpression { .. }
        | CExpression::AddressOf(_)
        | CExpression::Load(_, _)
        | CExpression::SequentialRead { .. }
        | CExpression::SequentialWrite { .. }
        | CExpression::AggregateAddress { .. }
        | CExpression::Field { .. }
        | CExpression::UnionField { .. }
        | CExpression::UnionAddress { .. }
        | CExpression::Index(_, _, _) => true,
        CExpression::Assignment { value, .. }
        | CExpression::Cast {
            expression: value, ..
        }
        | CExpression::FloatNegate(value)
        | CExpression::FloatClassification {
            expression: value, ..
        }
        | CExpression::PointerOffsetBytes { pointer: value, .. }
        | CExpression::Subobject { pointer: value, .. }
        | CExpression::Not(value)
        | CExpression::BitwiseNot(value)
        | CExpression::CheckedArrayIndex { index: value, .. } => {
            expression_reads_runtime_value(value)
        }
        CExpression::Ternary {
            condition,
            then_branch,
            else_branch,
        } => {
            expression_reads_runtime_value(condition)
                || expression_reads_runtime_value(then_branch)
                || expression_reads_runtime_value(else_branch)
        }
        crate::languages::c::syntax::binary_c_operation!(left, right) => {
            expression_reads_runtime_value(left) || expression_reads_runtime_value(right)
        }
    }
}

/// Decodes the escape sequence whose backslash is at `backslash`, returning
/// its byte and the index after it. Octal escapes take up to three digits
/// and hexadecimal escapes take every following hexadecimal digit, as in C;
/// a value that does not fit one byte is rejected.
fn parse_escape(
    chars: &[char],
    backslash: usize,
    literal: &str,
) -> Result<(u8, usize), CSyntaxError> {
    let Some(escaped) = chars.get(backslash + 1).copied() else {
        return Err(CSyntaxError::new(format!("unterminated {literal} literal")));
    };
    let simple = match escaped {
        'n' => Some(b'\n'),
        'r' => Some(b'\r'),
        't' => Some(b'\t'),
        'a' => Some(0x07),
        'b' => Some(0x08),
        'f' => Some(0x0c),
        'v' => Some(0x0b),
        '\\' => Some(b'\\'),
        '\'' => Some(b'\''),
        '"' => Some(b'"'),
        '?' => Some(b'?'),
        _ => None,
    };
    if let Some(byte) = simple {
        return Ok((byte, backslash + 2));
    }
    let (radix, first_digit, max_digits) = match escaped {
        '0'..='7' => (8, backslash + 1, 3),
        'x' => (16, backslash + 2, usize::MAX),
        other => {
            return Err(CSyntaxError::new(format!(
                "unsupported {literal} escape `\\{other}`"
            )));
        }
    };
    let mut value = 0u32;
    let mut end = first_digit;
    while end - first_digit < max_digits
        && let Some(digit) = chars.get(end).and_then(|digit| digit.to_digit(radix))
    {
        value = value.saturating_mul(radix).saturating_add(digit);
        end += 1;
    }
    if end == first_digit {
        return Err(CSyntaxError::new(format!(
            "hexadecimal {literal} escape `\\x` requires at least one digit"
        )));
    }
    let byte = u8::try_from(value).map_err(|_| {
        CSyntaxError::new(format!("numeric {literal} escape does not fit one byte"))
    })?;
    Ok((byte, end))
}

fn parse_char_literal(chars: &[char], start: usize) -> Result<(u8, usize), CSyntaxError> {
    let Some(first) = chars.get(start + 1).copied() else {
        return Err(CSyntaxError::new("unterminated character literal"));
    };
    if first == '\'' {
        return Err(CSyntaxError::new(
            "character literals must contain exactly one byte",
        ));
    }
    if matches!(first, '\n' | '\r') {
        return Err(CSyntaxError::new(
            "character literals may not contain an unescaped newline",
        ));
    }
    let (value, end) = if first == '\\' {
        parse_escape(chars, start + 1, "character")?
    } else {
        if !first.is_ascii() {
            return Err(CSyntaxError::new(
                "only ASCII character literals are supported",
            ));
        }
        (first as u8, start + 2)
    };

    if chars.get(end) != Some(&'\'') {
        return Err(CSyntaxError::new(
            "character literals must contain exactly one byte",
        ));
    }

    Ok((value, end + 1))
}

fn parse_string_literal(chars: &[char], start: usize) -> Result<(Vec<u8>, usize), CSyntaxError> {
    let mut value = Vec::new();
    let mut index = start + 1;
    while let Some(ch) = chars.get(index).copied() {
        match ch {
            '"' => return Ok((value, index + 1)),
            '\\' => {
                let (byte, next) = parse_escape(chars, index, "string")?;
                value.push(byte);
                index = next;
            }
            '\n' | '\r' => {
                return Err(CSyntaxError::new(
                    "string literals may not contain an unescaped newline",
                ));
            }
            other if other.is_ascii() => {
                value.push(other as u8);
                index += 1;
            }
            _ => {
                return Err(CSyntaxError::new(
                    "only ASCII string literals are supported",
                ));
            }
        }
    }
    Err(CSyntaxError::new("unterminated string literal"))
}

fn is_ident_start(ch: char) -> bool {
    ch.is_ascii_alphabetic() || ch == '_'
}

fn is_ident_continue(ch: char) -> bool {
    ch.is_ascii_alphanumeric() || ch == '_'
}

impl ImportedFunction {
    /// The class of the object a returned pointer designates
    /// (`design/effective-types.md`): its struct for a struct pointer,
    /// otherwise the pointee type's class.
    pub fn return_pointee_class(&self) -> Option<crate::kernel::effective_type::CAccessClass> {
        if self.return_struct_name.is_some() {
            return None;
        }
        match self.return_pointer_struct_name.as_deref() {
            Some(name) => struct_pointer_class(
                self.return_type,
                crate::kernel::effective_type::CPointeeBase::Struct(struct_class_in(
                    name,
                    &self.structs,
                    &self.unions,
                )),
            )?
            .pointee(),
            None => {
                let pointee = self.return_type.pointee_type()?;
                pointee
                    .access_class()
                    .or_else(|| int_pointer_class(pointee))
            }
        }
    }

    /// The deliberately narrow natural-cycle shape admitted by the C goto
    /// slice: one direct function-body label at the entry, one or more
    /// backward gotos in the re-entered region, and optionally one or more
    /// forward gotos to a final direct function-body exit label. Every
    /// backward goto targets the entry label. There is no declaration in the
    /// cycle region. The gotos may be nested in an `if`; the proof layer wraps
    /// this exact source region in a checked loop rule while retaining the
    /// original gotos.
    pub(crate) fn natural_control_loop(
        &self,
    ) -> Option<(
        crate::kernel::ControlTargetId,
        Option<crate::kernel::ControlTargetId>,
        usize,
    )> {
        let mut statements = Vec::new();
        flatten_direct_c_statements(&self.body, &mut statements);
        if statements.len() < 2 {
            return None;
        }
        let CStatement::Label {
            name: label_name,
            direct_function_body: true,
            ..
        } = statements.first()?
        else {
            return None;
        };
        let CStatement::Label { statement, .. } = statements[0] else {
            return None;
        };
        let exit_label_index = statements
            .last()
            .is_some_and(|candidate| matches!(candidate, CStatement::Label { .. }))
            .then(|| statements.len() - 1)
            .filter(|index| *index > 0);
        let cycle_end = exit_label_index.unwrap_or(statements.len());
        if !natural_cycle_statement_supported(statement)
            || statements[1..cycle_end]
                .iter()
                .any(|statement| !natural_cycle_statement_supported(statement))
            || exit_label_index.is_some_and(|index| {
                let CStatement::Label { statement, .. } = statements[index] else {
                    unreachable!();
                };
                !natural_cycle_statement_supported(statement)
                    || natural_cycle_statement_contains_goto(statement)
            })
        {
            return None;
        }
        let mut goto_targets = Vec::new();
        collect_natural_cycle_goto_targets(statement, &mut goto_targets);
        for statement in statements.iter().skip(1).take(cycle_end - 1) {
            collect_natural_cycle_goto_targets(statement, &mut goto_targets);
        }
        if goto_targets.is_empty() || (exit_label_index.is_some() && goto_targets.len() < 2) {
            return None;
        }
        let (label_target, _) = *self.control_targets.get(label_name)?;
        let targets = goto_targets
            .iter()
            .map(|target| self.control_targets.get(*target).copied())
            .collect::<Option<Vec<_>>>()?;
        let (backedges, targets): (Vec<_>, Vec<_>) = targets
            .into_iter()
            .partition(|(target, index)| *target == label_target && *index == 0);
        let backedge = backedges.first().copied()?;
        let exit = match exit_label_index {
            Some(index) => {
                let (_, exit_name) = match statements[index] {
                    CStatement::Label { name, .. } => (index, name),
                    _ => unreachable!(),
                };
                let (exit_target, target_index) = *self.control_targets.get(exit_name)?;
                (!targets.is_empty()
                    && targets.iter().all(|(goto_target, goto_index)| {
                        *goto_target == exit_target && *goto_index == target_index
                    }))
                .then_some(exit_target)
            }
            None => None,
        };
        ((exit_label_index.is_none() && targets.is_empty()) || exit.is_some())
            .then_some((backedge.0, exit, backedge.1))
    }
}

impl ImportedParameter {
    pub fn to_kernel_parameter(&self) -> crate::kernel::ProgramParameter {
        if self.is_struct_value() {
            let layout = self
                .struct_layout
                .as_ref()
                .expect("struct value parameter has a parsed layout")
                .to_kernel_aggregate_layout();
            return crate::kernel::program_parameter_with_aggregate_layout(
                self.name.clone(),
                crate::kernel::ProgramType::UInt8Pointer,
                layout,
            )
            .with_volatile(self.is_volatile())
            .with_pointee_volatile(self.pointee_is_volatile())
            .with_constant(self.is_constant())
            .with_pointee_constant(self.pointee_is_constant());
        }
        let interface_type = self
            .array_element_width
            .map(|_| crate::kernel::ProgramType::UInt8Pointer)
            .unwrap_or_else(|| self.interface_type.to_kernel_type());
        let pointee_class = (self.struct_name.is_none() && self.array_element_width.is_none())
            .then(|| {
                let pointee = self.interface_type.pointee_type()?;
                pointee
                    .access_class()
                    .or_else(|| int_pointer_class(pointee))
            })
            .flatten()
            .or_else(|| self.pointee_struct_class.clone());
        let mut parameter = crate::kernel::program_parameter(self.name.clone(), interface_type)
            .with_volatile(self.is_volatile())
            .with_pointee_volatile(self.pointee_is_volatile())
            .with_constant(self.is_constant())
            .with_pointee_constant(self.pointee_is_constant())
            .with_pointee_class(pointee_class);
        if let Some(index) = self.slice_length_parameter {
            parameter = parameter.with_slice_length_parameter(index);
        }
        if let Some(bytes) = self.fixed_reference_bounds {
            parameter = parameter.with_fixed_reference_bounds(bytes);
        }
        parameter
    }
}

impl CGlobal {
    fn prepare_static_binding(&self) {
        let Some(id) = self.kernel_name.static_id() else {
            return;
        };

        id.initialize_metadata(StaticBindingMetadata {
            program_type: self.interface_type.to_kernel_type(),
            array_shape: None,
            struct_name: (self.struct_name.as_deref()).map(std::sync::Arc::from),
            aggregate: false,
            volatile: self.volatile,
            pointee_volatile: self.pointee_volatile,
            constant: self.constant,
            pointee_constant: self.pointee_constant,
        });
    }
}

impl CGlobalArray {
    fn prepare_static_binding(&self) {
        let Some(id) = self.kernel_name.static_id() else {
            return;
        };
        let Some(length) = self.length else {
            return;
        };
        id.initialize_metadata(StaticBindingMetadata {
            program_type: array_type_for_element(self.element_type, length)
                .expect("complete global array type")
                .to_kernel_type(),
            array_shape: (self.shape.as_deref()).map(std::sync::Arc::from),
            struct_name: None,
            aggregate: false,
            volatile: false,
            pointee_volatile: false,
            constant: self.constant,
            pointee_constant: false,
        });
    }
}

impl CGlobalAggregate {
    fn prepare_static_binding(&self) {
        let Some(id) = self.kernel_name.static_id() else {
            return;
        };

        id.initialize_metadata(StaticBindingMetadata {
            program_type: InterfaceType::UInt8Array(self.layout.size_bytes()).to_kernel_type(),
            array_shape: None,
            struct_name: Some(std::sync::Arc::from(self.struct_name.as_str())),
            aggregate: true,
            volatile: false,
            pointee_volatile: false,
            constant: self.constant,
            pointee_constant: false,
        });
    }
}

impl CGlobalAggregateArray {
    fn prepare_static_binding(&self) {
        let Some(id) = self.kernel_name.static_id() else {
            return;
        };
        let Some(length) = self.length else {
            return;
        };
        id.initialize_metadata(StaticBindingMetadata {
            program_type: InterfaceType::UInt8Array(length * self.layout.size_bytes())
                .to_kernel_type(),
            array_shape: Some(std::sync::Arc::from(&[length][..])),
            struct_name: Some(std::sync::Arc::from(self.struct_name.as_str())),
            aggregate: true,
            volatile: false,
            pointee_volatile: false,
            constant: self.constant,
            pointee_constant: false,
        });
    }
}

impl CStaticLocal {
    fn prepare_static_binding(&self) {
        let Some(id) = self.kernel_name.static_id() else {
            return;
        };

        id.initialize_metadata(StaticBindingMetadata {
            program_type: self.interface_type.to_kernel_type(),
            array_shape: None,
            struct_name: (self
                .kernel_name
                .static_id()
                .and_then(StaticBindingId::struct_name))
            .map(std::sync::Arc::from),
            aggregate: false,
            volatile: self.volatile,
            pointee_volatile: self.pointee_volatile,
            constant: self.constant,
            pointee_constant: self.pointee_constant,
        });
    }
}

impl CStaticArray {
    fn prepare_static_binding(&self) {
        let Some(id) = self.kernel_name.static_id() else {
            return;
        };

        id.initialize_metadata(StaticBindingMetadata {
            program_type: array_type_for_element(self.element_type, self.length)
                .expect("complete static array type")
                .to_kernel_type(),
            array_shape: Some(std::sync::Arc::from(self.shape.as_slice())),
            struct_name: None,
            aggregate: false,
            volatile: false,
            pointee_volatile: false,
            constant: self.constant,
            pointee_constant: self.pointee_constant,
        });
    }
}

impl CStaticAggregate {
    fn prepare_static_binding(&self) {
        let Some(id) = self.kernel_name.static_id() else {
            return;
        };

        id.initialize_metadata(StaticBindingMetadata {
            program_type: InterfaceType::UInt8Array(self.layout.size_bytes()).to_kernel_type(),
            array_shape: None,
            struct_name: Some(std::sync::Arc::from(self.struct_name.as_str())),
            aggregate: true,
            volatile: false,
            pointee_volatile: false,
            constant: self.constant,
            pointee_constant: false,
        });
    }
}

impl CStaticAggregateArray {
    fn prepare_static_binding(&self) {
        let Some(id) = self.kernel_name.static_id() else {
            return;
        };

        id.initialize_metadata(StaticBindingMetadata {
            program_type: InterfaceType::UInt8Array(self.length * self.layout.size_bytes())
                .to_kernel_type(),
            array_shape: Some(std::sync::Arc::from(&[self.length][..])),
            struct_name: Some(std::sync::Arc::from(self.struct_name.as_str())),
            aggregate: true,
            volatile: false,
            pointee_volatile: false,
            constant: self.constant,
            pointee_constant: false,
        });
    }
}

impl Parser {
    fn prepare_file_static_bindings(&self) {
        for object in self.globals.values() {
            object.prepare_static_binding();
        }
        for object in self.global_arrays.values() {
            object.prepare_static_binding();
        }
        for object in self.global_aggregates.values() {
            object.prepare_static_binding();
        }
        for object in self.global_aggregate_arrays.values() {
            object.prepare_static_binding();
        }
    }
}

#[cfg(test)]
mod scope_metadata_tests {
    use super::*;

    #[test]
    fn explicit_halfword_fields_check_width_alignment_and_separation() {
        let fields = vec![
            ("a".into(), InterfaceType::UInt16, 0, 2),
            ("b".into(), InterfaceType::UInt16, 2, 2),
        ];
        let layout = RecordLayout::from_explicit_fields(fields.clone(), 4, 2).unwrap();
        assert_eq!(layout.field("b").unwrap().offset_bytes, 2);
        assert_eq!(layout.field("b").unwrap().byte_width, 2);
        for (offset, width) in [(1, 2), (0, 2), (2, 1), (4, 2)] {
            let mut invalid = fields.clone();
            invalid[1].2 = offset;
            invalid[1].3 = width;
            assert!(RecordLayout::from_explicit_fields(invalid, 4, 2).is_err());
        }
    }

    #[test]
    fn explicit_scalar_array_fields_preserve_length_and_check_full_layout() {
        for length in [1, 1024, 1_000_000] {
            let width = length * 4;
            let fields = vec![
                (
                    "values".into(),
                    InterfaceType::UInt32Array(length),
                    0,
                    width,
                ),
                ("marker".into(), InterfaceType::UInt8, width, 1),
            ];
            let layout = RecordLayout::from_explicit_fields(fields.clone(), width + 4, 4).unwrap();
            assert_eq!(
                layout.field("values").unwrap().array_shape(),
                Some(&[length][..])
            );
            assert_eq!(layout.to_kernel_aggregate_layout().fields().len(), 2);
            for (offset, bytes) in [(1, width), (0, width - 1), (4, width)] {
                let mut bad = fields.clone();
                bad[0].2 = offset;
                bad[0].3 = bytes;
                assert!(RecordLayout::from_explicit_fields(bad, width + 4, 4).is_err());
            }
        }
        let empty = RecordLayout::from_explicit_fields(
            vec![
                ("marker".into(), InterfaceType::UInt8, 0, 1),
                ("empty".into(), InterfaceType::UInt8Array(0), 0, 0),
            ],
            1,
            1,
        )
        .unwrap();
        assert_eq!(empty.field("empty").unwrap().byte_width(), 0);
        assert!(
            RecordLayout::from_explicit_fields(
                vec![("too_big".into(), InterfaceType::UInt32Array(u32::MAX), 0, 0)],
                4,
                4
            )
            .is_err()
        );
    }

    #[test]
    fn shadow_metadata_storage_is_independent_of_unrelated_globals() {
        for count in [16, 64, 256] {
            let mut parser = Parser::new("", CAbi::SUPPORTED).unwrap();
            for index in 0..count {
                parser.variable_types.insert(
                    format!("global{index}").into(),
                    InterfaceType::UInt64(LongRank::Long),
                );
            }
            parser
                .variable_types
                .insert("p".into(), InterfaceType::UInt32Array(2));
            parser.variable_array_shapes.insert("p".into(), vec![2]);
            parser.variable_constants.insert("p".into());
            parser.push_scope();
            assert_eq!(parser.declare_name("p").unwrap(), ("p").into());
            assert_eq!(parser.scopes.last().unwrap().len(), 1);
            let saved = parser.scopes.last().unwrap()[0].shadowed.as_ref().unwrap();
            assert_eq!(saved.interface_type, InterfaceType::UInt32Array(2));
            assert_eq!(saved.array_shape.as_deref(), Some([2].as_slice()));
            assert!(saved.constant);
            assert_eq!(parser.variable_types.len(), count);
            parser
                .variable_types
                .insert("p".into(), InterfaceType::Int32Pointer);
            parser.pop_scope();
            assert_eq!(parser.variable_types.len(), count + 1);
            assert_eq!(
                parser.variable_types[&("p").into()],
                InterfaceType::UInt32Array(2)
            );
            assert_eq!(parser.variable_array_shapes[&("p").into()], vec![2]);
            assert!(parser.variable_constants.contains(&("p").into()));
        }
    }

    #[cfg(test)]
    mod scaling_tests {
        include!("../../scaling_tests/languages/c/syntax/scope_metadata_tests.rs");
    }
}
