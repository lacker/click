//! Tiny C0 syntax import for the executable C model.

use std::collections::{BTreeMap, BTreeSet};

use crate::source::{SourcePosition, character_positions};

/// Stable documentation IDs for the accepted C0 surface. This registry
/// describes source forms rather than the lowered enum variants because some
/// forms are syntax sugar and several forms share a representation.
pub const C0_PUBLIC_FORMS: &[&str] = &[
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
    "type.function-pointer",
    "type.struct-pointer",
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
    "expression.conditional",
    "expression.sizeof-struct",
    "expression.sizeof-type",
    "expression.call",
    "expression.index",
    "expression.field",
    "expression.dereference",
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

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct C0Function {
    return_type: C0Type,
    return_struct_name: Option<String>,
    return_pointer_struct_name: Option<String>,
    name: String,
    inline_body: bool,
    parameters: Vec<C0Parameter>,
    body: C0Statement,
    structs: BTreeMap<String, C0StructLayout>,
    enums: BTreeMap<String, C0EnumDefinition>,
    unions: BTreeMap<String, C0UnionLayout>,
    globals: BTreeMap<String, C0Global>,
    global_arrays: BTreeMap<String, C0GlobalArray>,
    global_aggregates: BTreeMap<String, C0GlobalAggregate>,
    global_aggregate_arrays: BTreeMap<String, C0GlobalAggregateArray>,
    static_locals: BTreeMap<String, C0StaticLocal>,
    static_arrays: BTreeMap<String, C0StaticArray>,
    static_aggregates: BTreeMap<String, C0StaticAggregate>,
    static_aggregate_arrays: BTreeMap<String, C0StaticAggregateArray>,
    string_literals: Vec<C0StringLiteral>,
}

/// One string literal occurring in a C function. The hidden name is emitted
/// into the C0 expression tree as an array object; `bytes` includes the
/// required terminating NUL byte.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct C0StringLiteral {
    name: String,
    bytes: Vec<u8>,
}

impl C0StringLiteral {
    fn new(name: String, mut bytes: Vec<u8>) -> Self {
        bytes.push(0);
        Self { name, bytes }
    }

    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn bytes(&self) -> &[u8] {
        &self.bytes
    }
}

/// A file-scope scalar declaration collected from one C translation unit.
/// `initializer` is absent for an `extern` declaration and present for the
/// definition that supplies storage (including an implicit zero initializer).
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct C0Global {
    name: String,
    kernel_name: String,
    c_type: C0Type,
    struct_name: Option<String>,
    initializer: Option<C0Expression>,
    file_static: bool,
    volatile: bool,
    constant: bool,
}

impl C0Global {
    fn declaration(name: String, c_type: C0Type, struct_name: Option<String>) -> Self {
        Self {
            kernel_name: name.clone(),
            name,
            c_type,
            struct_name,
            initializer: None,
            file_static: false,
            volatile: false,
            constant: false,
        }
    }

    fn definition(
        name: String,
        c_type: C0Type,
        struct_name: Option<String>,
        initializer: C0Expression,
    ) -> Self {
        Self {
            kernel_name: name.clone(),
            name,
            c_type,
            struct_name,
            initializer: Some(initializer),
            file_static: false,
            volatile: false,
            constant: false,
        }
    }

    fn file_static_definition(
        name: String,
        kernel_name: String,
        c_type: C0Type,
        struct_name: Option<String>,
        initializer: C0Expression,
    ) -> Self {
        Self {
            name,
            kernel_name,
            c_type,
            struct_name,
            initializer: Some(initializer),
            file_static: true,
            volatile: false,
            constant: false,
        }
    }

    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn kernel_name(&self) -> &str {
        &self.kernel_name
    }

    pub fn c_type(&self) -> C0Type {
        self.c_type
    }

    pub fn struct_name(&self) -> Option<&str> {
        self.struct_name.as_deref()
    }

    pub fn is_defined(&self) -> bool {
        self.initializer.is_some()
    }

    pub fn is_file_static(&self) -> bool {
        self.file_static
    }

    pub fn initializer(&self) -> Option<&C0Expression> {
        self.initializer.as_ref()
    }

    pub fn is_volatile(&self) -> bool {
        self.volatile
    }

    pub fn is_constant(&self) -> bool {
        self.constant
    }

    fn with_volatile(mut self, volatile: bool) -> Self {
        self.volatile = volatile;
        self
    }

    fn with_constant(mut self, constant: bool) -> Self {
        self.constant = constant;
        self
    }

    pub(crate) fn to_kernel_global(&self) -> Option<crate::kernel::CGlobal> {
        let initializer = self.initializer.as_ref()?;
        let value = match self.c_type {
            C0Type::Float32 => match initializer {
                C0Expression::Float32Literal(bits) => {
                    crate::kernel::float32(crate::kernel::Bitvector32Term::Constant(*bits))
                }
                _ => return None,
            },
            C0Type::Float64 => match initializer {
                C0Expression::Float64Literal(bits) => {
                    crate::kernel::float64(crate::kernel::Bitvector32Term::UInt64Constant(*bits))
                }
                _ => return None,
            },
            _ => kernel_integer_literal_value(self.c_type, initializer)?,
        };
        Some(
            crate::kernel::CGlobal::new_with_kernel_name(
                self.name.clone(),
                self.kernel_name.clone(),
                self.c_type.to_kernel_type(),
                value,
            )
            .with_volatile(self.is_volatile())
            .with_constant(self.is_constant()),
        )
    }
}

/// A fixed-size file-scope scalar array collected from one C translation unit.
/// `initializer` is absent for an `extern` declaration and present for the
/// definition that supplies storage. Missing elements in a definition are
/// represented explicitly as zero values.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct C0GlobalArray {
    name: String,
    kernel_name: String,
    element_type: C0Type,
    length: u32,
    initializer: Option<Vec<C0Expression>>,
    file_static: bool,
    constant: bool,
}

impl C0GlobalArray {
    fn declaration(
        name: String,
        kernel_name: String,
        element_type: C0Type,
        length: u32,
        file_static: bool,
    ) -> Self {
        Self {
            name,
            kernel_name,
            element_type,
            length,
            initializer: None,
            file_static,
            constant: false,
        }
    }

    fn definition(
        name: String,
        kernel_name: String,
        element_type: C0Type,
        length: u32,
        initializer: Vec<C0Expression>,
        file_static: bool,
    ) -> Self {
        Self {
            name,
            kernel_name,
            element_type,
            length,
            initializer: Some(initializer),
            file_static,
            constant: false,
        }
    }

    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn kernel_name(&self) -> &str {
        &self.kernel_name
    }

    pub fn element_type(&self) -> C0Type {
        self.element_type
    }

    pub fn length(&self) -> u32 {
        self.length
    }

    pub fn c_type(&self) -> C0Type {
        array_type_for_element(self.element_type, self.length)
            .expect("validated global array element type")
    }

    pub fn is_defined(&self) -> bool {
        self.initializer.is_some()
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

    pub fn initializer(&self) -> Option<&[C0Expression]> {
        self.initializer.as_deref()
    }

    pub(crate) fn to_kernel_global_array(&self) -> Option<crate::kernel::CGlobalArray> {
        let initializer = self.initializer.as_ref()?;
        let values = initializer
            .iter()
            .map(|value| kernel_integer_literal_value(self.element_type, value))
            .collect::<Option<Vec<_>>>()?;
        Some(
            crate::kernel::CGlobalArray::new_with_kernel_name(
                self.name.clone(),
                self.kernel_name.clone(),
                self.element_type.to_kernel_type(),
                self.length,
                values,
            )
            .with_constant(self.is_constant()),
        )
    }
}

/// A file-scope object with a supported struct layout. Aggregate values are
/// represented by their stable address-backed layout rather than a scalar
/// initializer value. `initializer` contains only explicitly initialized
/// scalar leaves; omitted leaves are zero-initialized by the kernel.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct C0GlobalAggregate {
    name: String,
    kernel_name: String,
    struct_name: String,
    layout: C0StructLayout,
    initializer: Option<Vec<C0AggregateInitializer>>,
    defined: bool,
    file_static: bool,
    constant: bool,
}

/// A fixed-size one-dimensional file-scope array of supported struct
/// aggregates. The initializer offsets are relative to the beginning of the
/// complete array block; omitted elements and fields are zero-initialized by
/// the kernel.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct C0GlobalAggregateArray {
    name: String,
    kernel_name: String,
    struct_name: String,
    layout: C0StructLayout,
    length: u32,
    initializer: Option<Vec<C0AggregateInitializer>>,
    file_static: bool,
    constant: bool,
}

impl C0GlobalAggregateArray {
    fn declaration(
        name: String,
        kernel_name: String,
        struct_name: String,
        layout: C0StructLayout,
        length: u32,
        file_static: bool,
    ) -> Self {
        Self {
            name,
            kernel_name,
            struct_name,
            layout,
            length,
            initializer: None,
            file_static,
            constant: false,
        }
    }

    fn definition(
        name: String,
        kernel_name: String,
        struct_name: String,
        layout: C0StructLayout,
        length: u32,
        initializer: Vec<C0AggregateInitializer>,
        file_static: bool,
    ) -> Self {
        Self {
            name,
            kernel_name,
            struct_name,
            layout,
            length,
            initializer: Some(initializer),
            file_static,
            constant: false,
        }
    }

    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn kernel_name(&self) -> &str {
        &self.kernel_name
    }

    pub fn struct_name(&self) -> &str {
        &self.struct_name
    }

    pub fn layout(&self) -> &C0StructLayout {
        &self.layout
    }

    pub fn length(&self) -> u32 {
        self.length
    }

    pub fn c_type(&self) -> C0Type {
        C0Type::UInt8Array(
            self.length
                .checked_mul(self.layout.size_bytes())
                .expect("validated aggregate array size"),
        )
    }

    pub fn is_defined(&self) -> bool {
        self.initializer.is_some()
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

    pub fn initializer(&self) -> Option<&[C0AggregateInitializer]> {
        self.initializer.as_deref()
    }

    pub(crate) fn to_kernel_global_aggregate_array(
        &self,
    ) -> Option<crate::kernel::CGlobalAggregateArray> {
        let initializer = self.initializer.as_ref()?;
        let initializers = initializer
            .iter()
            .map(C0AggregateInitializer::to_kernel)
            .collect::<Option<Vec<_>>>()?;
        Some(
            crate::kernel::CGlobalAggregateArray::new(
                self.name.clone(),
                self.kernel_name.clone(),
                self.layout.to_kernel_aggregate_layout(),
                self.length,
                initializers,
            )
            .with_constant(self.is_constant()),
        )
    }
}

impl C0GlobalAggregate {
    fn declaration(
        name: String,
        kernel_name: String,
        struct_name: String,
        layout: C0StructLayout,
        file_static: bool,
    ) -> Self {
        Self {
            name,
            kernel_name,
            struct_name,
            layout,
            initializer: None,
            defined: false,
            file_static,
            constant: false,
        }
    }

    fn definition(
        name: String,
        kernel_name: String,
        struct_name: String,
        layout: C0StructLayout,
        initializer: Vec<C0AggregateInitializer>,
        file_static: bool,
    ) -> Self {
        Self {
            name,
            kernel_name,
            struct_name,
            layout,
            initializer: Some(initializer),
            defined: true,
            file_static,
            constant: false,
        }
    }

    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn kernel_name(&self) -> &str {
        &self.kernel_name
    }

    pub fn struct_name(&self) -> &str {
        &self.struct_name
    }

    pub fn layout(&self) -> &C0StructLayout {
        &self.layout
    }

    pub fn is_defined(&self) -> bool {
        self.defined
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

    pub fn initializer(&self) -> Option<&[C0AggregateInitializer]> {
        self.initializer.as_deref()
    }

    pub(crate) fn to_kernel_global_aggregate(&self) -> Option<crate::kernel::CGlobalAggregate> {
        let initializer = self.initializer.as_ref()?;
        let initializers = initializer
            .iter()
            .map(C0AggregateInitializer::to_kernel)
            .collect::<Option<Vec<_>>>()?;
        self.defined.then(|| {
            crate::kernel::CGlobalAggregate::new(
                self.name.clone(),
                self.kernel_name.clone(),
                self.layout.to_kernel_aggregate_layout(),
                initializers,
            )
            .with_constant(self.is_constant())
        })
    }
}

fn array_type_for_element(element_type: C0Type, length: u32) -> Option<C0Type> {
    Some(match element_type {
        C0Type::Int16 => C0Type::Int16Array(length),
        C0Type::Int32 => C0Type::Int32Array(length),
        C0Type::UInt8 => C0Type::UInt8Array(length),
        C0Type::UInt16 => C0Type::UInt16Array(length),
        C0Type::UInt32 => C0Type::UInt32Array(length),
        C0Type::Int64 => C0Type::Int64Array(length),
        C0Type::UInt64 => C0Type::UInt64Array(length),
        C0Type::Float32 => C0Type::Float32Array(length),
        C0Type::Float64 => C0Type::Float64Array(length),
        _ => return None,
    })
}

fn kernel_integer_literal_value(
    c_type: C0Type,
    initializer: &C0Expression,
) -> Option<crate::kernel::CValue> {
    Some(match c_type {
        C0Type::Float32 => match initializer {
            C0Expression::Float32Literal(bits) => {
                crate::kernel::float32(crate::kernel::Bitvector32Term::Constant(*bits))
            }
            _ => return None,
        },
        C0Type::Float64 => match initializer {
            C0Expression::Float64Literal(bits) => {
                crate::kernel::float64(crate::kernel::Bitvector32Term::UInt64Constant(*bits))
            }
            _ => return None,
        },
        C0Type::Int16 => crate::kernel::int16(initializer_integer_bits(initializer)?),
        C0Type::Int32 => crate::kernel::int32(initializer_integer_bits(initializer)?),
        C0Type::UInt8 => crate::kernel::uint8(initializer_integer_bits(initializer)?),
        C0Type::UInt16 => crate::kernel::uint16(initializer_integer_bits(initializer)?),
        C0Type::UInt32 => crate::kernel::uint32(initializer_integer_bits(initializer)?),
        C0Type::Int64 => match initializer {
            C0Expression::Int64Literal(value) => {
                crate::kernel::int64(crate::kernel::Bitvector32Term::Int64Constant(*value))
            }
            C0Expression::Int32Literal(value) => {
                crate::kernel::int64(crate::kernel::Bitvector32Term::Constant(*value))
            }
            C0Expression::UInt8Literal(value) => {
                crate::kernel::int64(crate::kernel::Bitvector32Term::Constant(u32::from(*value)))
            }
            C0Expression::UInt32Literal(value) => {
                crate::kernel::int64(crate::kernel::Bitvector32Term::Constant(*value))
            }
            _ => return None,
        },
        C0Type::UInt64 => match initializer {
            C0Expression::UInt64Literal(value) => {
                crate::kernel::uint64(crate::kernel::Bitvector32Term::UInt64Constant(*value))
            }
            C0Expression::Int64Literal(value) if *value >= 0 => crate::kernel::uint64(
                crate::kernel::Bitvector32Term::UInt64Constant(*value as u64),
            ),
            C0Expression::Int32Literal(value) => {
                crate::kernel::uint64(crate::kernel::Bitvector32Term::Constant(*value))
            }
            C0Expression::UInt8Literal(value) => {
                crate::kernel::uint64(crate::kernel::Bitvector32Term::Constant(u32::from(*value)))
            }
            C0Expression::UInt32Literal(value) => {
                crate::kernel::uint64(crate::kernel::Bitvector32Term::Constant(*value))
            }
            _ => return None,
        },
        C0Type::Int16Pointer
        | C0Type::UInt16Pointer
        | C0Type::Int32Pointer
        | C0Type::UInt8Pointer
        | C0Type::UInt32Pointer
        | C0Type::Int64Pointer
        | C0Type::UInt64Pointer
        | C0Type::Float32Pointer
        | C0Type::Float64Pointer
        | C0Type::Int16PointerPointer
        | C0Type::UInt16PointerPointer
        | C0Type::Int32PointerPointer
        | C0Type::UInt8PointerPointer
        | C0Type::UInt32PointerPointer
        | C0Type::Int64PointerPointer
        | C0Type::UInt64PointerPointer
        | C0Type::Float32PointerPointer
        | C0Type::Float64PointerPointer
            if matches!(initializer, C0Expression::Int32Literal(0)) =>
        {
            crate::kernel::CValue::typed_pointer(
                crate::kernel::Pointer::null(),
                c_type.to_kernel_type(),
            )
        }
        _ => return None,
    })
}

fn kernel_aggregate_initializer_value(
    c_type: C0Type,
    initializer: &C0Expression,
) -> Option<crate::kernel::CValue> {
    match c_type {
        C0Type::Int32Pointer
        | C0Type::UInt8Pointer
        | C0Type::Float32Pointer
        | C0Type::Float64Pointer
        | C0Type::Int32PointerPointer
        | C0Type::UInt8PointerPointer
        | C0Type::Float32PointerPointer
        | C0Type::Float64PointerPointer
            if matches!(initializer, C0Expression::Int32Literal(0)) =>
        {
            Some(crate::kernel::CValue::typed_pointer(
                crate::kernel::Pointer::null(),
                c_type.to_kernel_type(),
            ))
        }
        C0Type::Int16
        | C0Type::Int32
        | C0Type::UInt8
        | C0Type::UInt16
        | C0Type::UInt32
        | C0Type::Int64
        | C0Type::UInt64
        | C0Type::Float32
        | C0Type::Float64 => kernel_integer_literal_value(c_type, initializer),
        _ => None,
    }
}

/// A function-local scalar with static storage duration. The source name is
/// what C fragments use; `kernel_name` keeps distinct block scopes distinct
/// in the lowered C0 expression tree.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct C0StaticLocal {
    source_name: String,
    kernel_name: String,
    c_type: C0Type,
    initializer: C0Expression,
    volatile: bool,
    constant: bool,
}

/// A function-local fixed-size scalar array with static storage duration.
/// The source name is what C fragments use; `kernel_name` keeps distinct
/// block scopes distinct in the lowered C0 expression tree.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct C0StaticArray {
    source_name: String,
    kernel_name: String,
    element_type: C0Type,
    length: u32,
    initializer: Vec<C0Expression>,
    constant: bool,
}

impl C0StaticArray {
    fn new(
        source_name: String,
        kernel_name: String,
        element_type: C0Type,
        length: u32,
        initializer: Vec<C0Expression>,
    ) -> Self {
        Self {
            source_name,
            kernel_name,
            element_type,
            length,
            initializer,
            constant: false,
        }
    }

    pub fn name(&self) -> &str {
        &self.source_name
    }

    pub fn kernel_name(&self) -> &str {
        &self.kernel_name
    }

    pub fn element_type(&self) -> C0Type {
        self.element_type
    }

    pub fn length(&self) -> u32 {
        self.length
    }

    pub fn c_type(&self) -> C0Type {
        array_type_for_element(self.element_type, self.length)
            .expect("validated static array element type")
    }

    pub fn initializer(&self) -> &[C0Expression] {
        &self.initializer
    }

    pub fn is_constant(&self) -> bool {
        self.constant
    }

    fn with_constant(mut self, constant: bool) -> Self {
        self.constant = constant;
        self
    }

    pub(crate) fn to_kernel_static_array(&self) -> Option<crate::kernel::CStaticArray> {
        let values = self
            .initializer
            .iter()
            .map(|value| kernel_integer_literal_value(self.element_type, value))
            .collect::<Option<Vec<_>>>()?;
        Some(crate::kernel::CStaticArray::new(
            self.source_name.clone(),
            self.kernel_name.clone(),
            self.element_type.to_kernel_type(),
            self.length,
            values,
        ))
        .map(|array| array.with_constant(self.is_constant()))
    }
}

impl C0StaticLocal {
    fn new(
        source_name: String,
        kernel_name: String,
        c_type: C0Type,
        initializer: C0Expression,
    ) -> Self {
        Self {
            source_name,
            kernel_name,
            c_type,
            initializer,
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

    pub fn c_type(&self) -> C0Type {
        self.c_type
    }

    pub fn initializer(&self) -> &C0Expression {
        &self.initializer
    }

    pub fn is_volatile(&self) -> bool {
        self.volatile
    }

    pub fn is_constant(&self) -> bool {
        self.constant
    }

    fn with_volatile(mut self, volatile: bool) -> Self {
        self.volatile = volatile;
        self
    }

    fn with_constant(mut self, constant: bool) -> Self {
        self.constant = constant;
        self
    }

    pub(crate) fn to_kernel_static(&self) -> Option<crate::kernel::CStaticLocal> {
        let value = match self.c_type {
            C0Type::Float32 => match &self.initializer {
                C0Expression::Float32Literal(bits) => {
                    crate::kernel::float32(crate::kernel::Bitvector32Term::Constant(*bits))
                }
                _ => return None,
            },
            C0Type::Float64 => match &self.initializer {
                C0Expression::Float64Literal(bits) => {
                    crate::kernel::float64(crate::kernel::Bitvector32Term::UInt64Constant(*bits))
                }
                _ => return None,
            },
            C0Type::Int16 => crate::kernel::int16(initializer_integer_bits(&self.initializer)?),
            C0Type::Int32 => crate::kernel::int32(initializer_integer_bits(&self.initializer)?),
            C0Type::UInt8 => crate::kernel::uint8(initializer_integer_bits(&self.initializer)?),
            C0Type::UInt16 => crate::kernel::uint16(initializer_integer_bits(&self.initializer)?),
            C0Type::UInt32 => crate::kernel::uint32(initializer_integer_bits(&self.initializer)?),
            _ => return None,
        };
        Some(
            crate::kernel::CStaticLocal::new(
                self.source_name.clone(),
                self.kernel_name.clone(),
                self.c_type.to_kernel_type(),
                value,
            )
            .with_volatile(self.is_volatile())
            .with_constant(self.is_constant()),
        )
    }
}

fn initializer_integer_bits(initializer: &C0Expression) -> Option<u32> {
    match initializer {
        C0Expression::Int32Literal(value) => Some(*value),
        C0Expression::UInt8Literal(value) => Some(u32::from(*value)),
        C0Expression::UInt32Literal(value) => Some(*value),
        _ => None,
    }
}

fn zero_initializer(c_type: C0Type) -> C0Expression {
    match c_type {
        C0Type::Float32 => C0Expression::Float32Literal(0),
        C0Type::Float64 => C0Expression::Float64Literal(0),
        _ => C0Expression::Int32Literal(0),
    }
}

/// A function-local aggregate with stable storage shared by every invocation
/// of its owning function.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct C0StaticAggregate {
    source_name: String,
    kernel_name: String,
    struct_name: String,
    layout: C0StructLayout,
    initializer: Vec<C0AggregateInitializer>,
    constant: bool,
}

/// A fixed-size one-dimensional function-local static array of supported
/// struct aggregates. Its storage is qualified by the owning function and is
/// initialized once for the whole symbolic execution.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct C0StaticAggregateArray {
    source_name: String,
    kernel_name: String,
    struct_name: String,
    layout: C0StructLayout,
    length: u32,
    initializer: Vec<C0AggregateInitializer>,
    constant: bool,
}

impl C0StaticAggregateArray {
    fn new(
        source_name: String,
        kernel_name: String,
        struct_name: String,
        layout: C0StructLayout,
        length: u32,
        initializer: Vec<C0AggregateInitializer>,
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

    pub fn kernel_name(&self) -> &str {
        &self.kernel_name
    }

    pub fn struct_name(&self) -> &str {
        &self.struct_name
    }

    pub fn layout(&self) -> &C0StructLayout {
        &self.layout
    }

    pub fn length(&self) -> u32 {
        self.length
    }

    pub fn c_type(&self) -> C0Type {
        C0Type::UInt8Array(
            self.length
                .checked_mul(self.layout.size_bytes())
                .expect("validated static aggregate array size"),
        )
    }

    pub fn initializer(&self) -> &[C0AggregateInitializer] {
        &self.initializer
    }

    pub fn is_constant(&self) -> bool {
        self.constant
    }

    fn with_constant(mut self, constant: bool) -> Self {
        self.constant = constant;
        self
    }

    pub(crate) fn to_kernel_static_aggregate_array(&self) -> crate::kernel::CStaticAggregateArray {
        crate::kernel::CStaticAggregateArray::new(
            self.source_name.clone(),
            self.kernel_name.clone(),
            self.layout.to_kernel_aggregate_layout(),
            self.length,
            self.initializer
                .iter()
                .map(C0AggregateInitializer::to_kernel)
                .collect::<Option<Vec<_>>>()
                .expect("validated static aggregate array initializer"),
        )
        .with_constant(self.is_constant())
    }
}

impl C0StaticAggregate {
    fn new(
        source_name: String,
        kernel_name: String,
        struct_name: String,
        layout: C0StructLayout,
        initializer: Vec<C0AggregateInitializer>,
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

    pub fn kernel_name(&self) -> &str {
        &self.kernel_name
    }

    pub fn struct_name(&self) -> &str {
        &self.struct_name
    }

    pub fn layout(&self) -> &C0StructLayout {
        &self.layout
    }

    pub fn initializer(&self) -> &[C0AggregateInitializer] {
        &self.initializer
    }

    pub fn is_constant(&self) -> bool {
        self.constant
    }

    fn with_constant(mut self, constant: bool) -> Self {
        self.constant = constant;
        self
    }

    pub(crate) fn to_kernel_static_aggregate(&self) -> crate::kernel::CStaticAggregate {
        crate::kernel::CStaticAggregate::new(
            self.source_name.clone(),
            self.kernel_name.clone(),
            self.layout.to_kernel_aggregate_layout(),
            self.initializer
                .iter()
                .map(C0AggregateInitializer::to_kernel)
                .collect::<Option<Vec<_>>>()
                .expect("validated static aggregate initializer"),
        )
        .with_constant(self.is_constant())
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct C0Parameter {
    c_type: C0Type,
    name: String,
    volatile: bool,
    pointee_volatile: bool,
    constant: bool,
    pointee_constant: bool,
    struct_name: Option<String>,
    struct_layout: Option<C0StructLayout>,
    /// The layout of the pointee when the parameter is a pointer to a struct,
    /// so `object(p)` resources can type the object's cells field by field.
    /// Distinct from `struct_layout`, which marks struct values and arrays.
    pointee_struct_layout: Option<C0StructLayout>,
    function_pointer_signature: Option<C0FunctionPointerSignature>,
    /// The ABI width of one element when the source parameter was declared as
    /// an array of structs. The public C0 type remains the compatible
    /// struct-pointer placeholder, while the kernel uses byte addressing for
    /// the lowered indexed field accesses.
    array_element_width: Option<u32>,
}

/// The nominal part of a callback signature that the kernel's structural
/// `CType::FunctionPointer` deliberately does not carry.  The ABI signature
/// remains structural; these tags are checked while parsing C0 expressions so
/// `struct left *` and `struct right *` cannot silently become interchangeable
/// callback arguments.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct C0FunctionPointerParameter {
    c_type: C0Type,
    struct_name: Option<String>,
}

impl C0FunctionPointerParameter {
    pub(crate) fn new(c_type: C0Type, struct_name: Option<String>) -> Self {
        Self {
            c_type,
            struct_name,
        }
    }

    pub fn c_type(&self) -> C0Type {
        self.c_type
    }

    pub fn struct_name(&self) -> Option<&str> {
        self.struct_name.as_deref()
    }
}

/// Nominal metadata for a function-pointer type.  `c_type` and the kernel
/// signature key still describe the ABI shape; `struct_name` retains the C
/// spelling needed for boundary checks.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct C0FunctionPointerSignature {
    return_type: C0Type,
    return_struct_name: Option<String>,
    parameters: Vec<C0FunctionPointerParameter>,
}

impl C0FunctionPointerSignature {
    pub(crate) fn new(
        return_type: C0Type,
        return_struct_name: Option<String>,
        parameters: Vec<C0FunctionPointerParameter>,
    ) -> Self {
        Self {
            return_type,
            return_struct_name,
            parameters,
        }
    }

    pub fn return_type(&self) -> C0Type {
        self.return_type
    }

    pub fn return_struct_name(&self) -> Option<&str> {
        self.return_struct_name.as_deref()
    }

    pub fn parameters(&self) -> &[C0FunctionPointerParameter] {
        &self.parameters
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct ParsedType {
    c_type: C0Type,
    struct_name: Option<String>,
    enum_name: Option<String>,
    union_name: Option<String>,
    is_volatile: bool,
    is_constant: bool,
    pointee_constant: bool,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct C0StructLayout {
    fields: BTreeMap<String, C0StructField>,
    /// Leaf fields used when a struct value is copied through the kernel.
    /// Embedded struct fields are flattened here while preserving their
    /// declared names as qualified paths and their complete ABI offsets.
    aggregate_fields: Vec<C0AggregateField>,
    size_bytes: u32,
    alignment_bytes: u32,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct C0AggregateField {
    name: String,
    offset_bytes: u32,
    c_type: C0Type,
}

/// One explicitly initialized scalar leaf in a static-storage aggregate.
/// Offsets are relative to the aggregate's base address; omitted leaves are
/// supplied by static zero initialization.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct C0AggregateInitializer {
    offset_bytes: u32,
    c_type: C0Type,
    value: C0Expression,
}

impl C0AggregateInitializer {
    fn new(offset_bytes: u32, c_type: C0Type, value: C0Expression) -> Self {
        Self {
            offset_bytes,
            c_type,
            value,
        }
    }

    pub fn offset_bytes(&self) -> u32 {
        self.offset_bytes
    }

    pub fn c_type(&self) -> C0Type {
        self.c_type
    }

    pub fn value(&self) -> &C0Expression {
        &self.value
    }

    fn to_kernel(&self) -> Option<crate::kernel::CAggregateInitializer> {
        Some(crate::kernel::CAggregateInitializer::new(
            self.offset_bytes,
            kernel_aggregate_initializer_value(self.c_type, &self.value)?,
        ))
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct C0EnumDefinition {
    values: BTreeMap<String, i32>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct C0UnionLayout {
    fields: BTreeMap<String, C0UnionField>,
    size_bytes: u32,
    alignment_bytes: u32,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct C0UnionField {
    c_type: C0Type,
    enum_name: Option<String>,
    offset_bytes: u32,
    byte_width: u32,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct C0StructField {
    c_type: C0Type,
    struct_name: Option<String>,
    enum_name: Option<String>,
    union_name: Option<String>,
    function_pointer_signature: Option<C0FunctionPointerSignature>,
    /// The ABI width of one element when this is an inline array of embedded
    /// structs. The public C0 type remains a byte-array placeholder, while
    /// member selection uses this metadata to preserve struct indexing.
    array_element_width: Option<u32>,
    /// The fixed dimensions of a multidimensional inline array, in C's
    /// declared order. The shape is retained so indexing can be flattened
    /// with the correct row-major stride.
    array_shape: Option<Vec<u32>>,
    offset_bytes: u32,
    byte_width: u32,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum C0Type {
    Void,
    /// An opaque pointer to an object of unknown type. It preserves pointer
    /// identity and provenance but deliberately has no pointee width, so it
    /// cannot be indexed, dereferenced, or used in pointer arithmetic until
    /// an explicit conversion supplies a modeled object type.
    VoidPointer,
    Int16,
    Int32,
    UInt8,
    UInt16,
    UInt32,
    Int64,
    UInt64,
    Float32,
    Float64,
    Int16Pointer,
    UInt16Pointer,
    Int32Pointer,
    UInt8Pointer,
    UInt32Pointer,
    Int64Pointer,
    UInt64Pointer,
    Float32Pointer,
    Float64Pointer,
    Int16PointerPointer,
    UInt16PointerPointer,
    Int32PointerPointer,
    UInt8PointerPointer,
    UInt32PointerPointer,
    Int64PointerPointer,
    UInt64PointerPointer,
    Float32PointerPointer,
    Float64PointerPointer,
    /// A callback signature identified by a stable, structural signature key.
    /// The key is shared with the kernel type and is deliberately opaque to
    /// ordinary C expressions: function pointers are callable, not objects.
    FunctionPointer(u64),
    Int32Array(u32),
    UInt8Array(u32),
    Int16Array(u32),
    UInt16Array(u32),
    UInt32Array(u32),
    Int64Array(u32),
    UInt64Array(u32),
    Float32Array(u32),
    Float64Array(u32),
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum CAbi {
    Lp64,
}

impl CAbi {
    pub const SUPPORTED: Self = Self::Lp64;

    fn size_and_alignment(self, c_type: C0Type) -> (u32, u32) {
        match (self, c_type) {
            (Self::Lp64, C0Type::Void) => (0, 1),
            (Self::Lp64, C0Type::VoidPointer) => (8, 8),
            (Self::Lp64, C0Type::Int16) => (2, 2),
            (Self::Lp64, C0Type::Int32) => (4, 4),
            (Self::Lp64, C0Type::UInt8) => (1, 1),
            (Self::Lp64, C0Type::UInt16) => (2, 2),
            (Self::Lp64, C0Type::UInt32) => (4, 4),
            (Self::Lp64, C0Type::Int64 | C0Type::UInt64) => (8, 8),
            (Self::Lp64, C0Type::Float32) => (4, 4),
            (Self::Lp64, C0Type::Float64) => (8, 8),
            (
                Self::Lp64,
                C0Type::Int32Pointer
                | C0Type::Int16Pointer
                | C0Type::UInt16Pointer
                | C0Type::UInt8Pointer
                | C0Type::UInt32Pointer
                | C0Type::Int64Pointer
                | C0Type::UInt64Pointer
                | C0Type::Float32Pointer
                | C0Type::Float64Pointer
                | C0Type::Int16PointerPointer
                | C0Type::UInt16PointerPointer
                | C0Type::Int32PointerPointer
                | C0Type::UInt8PointerPointer
                | C0Type::UInt32PointerPointer
                | C0Type::Int64PointerPointer
                | C0Type::UInt64PointerPointer
                | C0Type::Float32PointerPointer
                | C0Type::Float64PointerPointer,
            ) => (8, 8),
            (Self::Lp64, C0Type::FunctionPointer(_)) => (8, 8),
            (Self::Lp64, C0Type::Int32Array(length)) => (length.saturating_mul(4), 4),
            (Self::Lp64, C0Type::UInt8Array(length)) => (length, 1),
            (Self::Lp64, C0Type::Int16Array(length) | C0Type::UInt16Array(length)) => {
                (length.saturating_mul(2), 2)
            }
            (Self::Lp64, C0Type::UInt32Array(length)) => (length.saturating_mul(4), 4),
            (Self::Lp64, C0Type::Int64Array(length) | C0Type::UInt64Array(length)) => {
                (length.saturating_mul(8), 8)
            }
            (Self::Lp64, C0Type::Float32Array(length)) => (length.saturating_mul(4), 4),
            (Self::Lp64, C0Type::Float64Array(length)) => (length.saturating_mul(8), 8),
        }
    }
}

impl C0Type {
    pub(crate) fn abi_size_bytes(self) -> u32 {
        CAbi::SUPPORTED.size_and_alignment(self).0
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct C0SwitchCase {
    value: Option<u32>,
    body: Box<C0Statement>,
}

impl C0SwitchCase {
    pub fn value(&self) -> Option<u32> {
        self.value
    }

    pub fn body(&self) -> &C0Statement {
        &self.body
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum C0Statement {
    Skip,
    Break,
    Continue,
    Declare {
        c_type: C0Type,
        name: String,
        volatile: bool,
        pointee_volatile: bool,
        constant: bool,
        pointee_constant: bool,
    },
    DeclareStructValue {
        name: String,
        layout: C0StructLayout,
    },
    Assign {
        name: String,
        expression: C0Expression,
    },
    CallAssign {
        target: String,
        function_name: String,
        arguments: Vec<C0Expression>,
    },
    Call {
        function_name: String,
        arguments: Vec<C0Expression>,
    },
    /// A statement-form call through a modeled function-pointer expression.
    /// Parsing expands this to a typed callback local before kernel lowering.
    IndirectCall {
        function: C0Expression,
        signature: C0FunctionPointerSignature,
        arguments: Vec<C0Expression>,
        position: Option<SourcePosition>,
    },
    HeapAllocate {
        target: String,
        bytes: C0Expression,
        zeroed: bool,
    },
    HeapFree {
        pointer: C0Expression,
    },
    Seq(Box<C0Statement>, Box<C0Statement>),
    Return(C0Expression),
    Store {
        pointer: C0Expression,
        value: C0Expression,
        value_type: Option<C0Type>,
    },
    Update {
        target: C0Expression,
        operator: C0UpdateOperator,
        operand: C0Expression,
    },
    If {
        condition: C0Expression,
        then_branch: Box<C0Statement>,
        else_branch: Box<C0Statement>,
    },
    While {
        condition: C0Expression,
        body: Box<C0Statement>,
    },
    DoWhile {
        condition: C0Expression,
        body: Box<C0Statement>,
    },
    For {
        initializer: Box<C0Statement>,
        condition: C0Expression,
        step: Box<C0Statement>,
        body: Box<C0Statement>,
    },
    Switch {
        expression: C0Expression,
        cases: Vec<C0SwitchCase>,
    },
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum C0UpdateOperator {
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

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum C0FloatClassification {
    Finite,
    Infinite,
    Zero,
    Subnormal,
    Nan,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum C0Expression {
    Void,
    Variable(String),
    /// A C function call that is still embedded in an expression. The
    /// parser lowers these to `CallAssign` statements before the AST reaches
    /// the kernel, so the kernel continues to execute calls only as checked
    /// statement transitions. The position identifies the source call site
    /// for diagnostics emitted while performing that lowering.
    Call {
        function_name: String,
        arguments: Vec<C0Expression>,
        position: Option<SourcePosition>,
    },
    /// A call through a modeled function-pointer expression. The parser keeps
    /// the expression until lowering can materialize it in a typed callback
    /// local, then reuses the kernel's existing indirect-call statement path.
    IndirectCall {
        function: Box<C0Expression>,
        signature: C0FunctionPointerSignature,
        arguments: Vec<C0Expression>,
        position: Option<SourcePosition>,
    },
    FunctionAddress(String),
    Cast {
        expression: Box<C0Expression>,
        c_type: C0Type,
        /// The struct tag of a pointer cast target, so field access through
        /// the cast result resolves the same layout as a declared pointer.
        struct_name: Option<String>,
    },
    Conditional {
        condition: Box<C0Expression>,
        then_branch: Box<C0Expression>,
        else_branch: Box<C0Expression>,
    },
    FloatNegate(Box<C0Expression>),
    FloatClassification {
        expression: Box<C0Expression>,
        classification: C0FloatClassification,
    },
    AddressOf(Box<C0Expression>),
    PointerOffsetBytes {
        pointer: Box<C0Expression>,
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
        c_type: C0Type,
        struct_name: Option<String>,
        bytes: u32,
    },
    LessThan(Box<C0Expression>, Box<C0Expression>),
    LessEqual(Box<C0Expression>, Box<C0Expression>),
    GreaterThan(Box<C0Expression>, Box<C0Expression>),
    GreaterEqual(Box<C0Expression>, Box<C0Expression>),
    Equal(Box<C0Expression>, Box<C0Expression>),
    NotEqual(Box<C0Expression>, Box<C0Expression>),
    Not(Box<C0Expression>),
    And(Box<C0Expression>, Box<C0Expression>),
    Or(Box<C0Expression>, Box<C0Expression>),
    Add(Box<C0Expression>, Box<C0Expression>),
    Subtract(Box<C0Expression>, Box<C0Expression>),
    Multiply(Box<C0Expression>, Box<C0Expression>),
    Divide(Box<C0Expression>, Box<C0Expression>),
    Remainder(Box<C0Expression>, Box<C0Expression>),
    ShiftLeft(Box<C0Expression>, Box<C0Expression>),
    ShiftRight(Box<C0Expression>, Box<C0Expression>),
    BitwiseAnd(Box<C0Expression>, Box<C0Expression>),
    BitwiseOr(Box<C0Expression>, Box<C0Expression>),
    BitwiseXor(Box<C0Expression>, Box<C0Expression>),
    BitwiseNot(Box<C0Expression>),
    Load(Box<C0Expression>),
    /// Address of an embedded struct field. Aggregate objects have no
    /// runtime `CValue`; this node carries the aggregate place through nested
    /// member selection until a scalar field is selected.
    AggregateAddress {
        pointer: Box<C0Expression>,
        struct_name: String,
    },
    Field {
        pointer: Box<C0Expression>,
        field_type: C0Type,
        field_struct_name: Option<String>,
        function_pointer_signature: Option<C0FunctionPointerSignature>,
        array_shape: Option<Vec<u32>>,
    },
    UnionField {
        pointer: Box<C0Expression>,
        field_type: C0Type,
        union_name: String,
    },
    /// Address of an embedded union. Union members overlap at offset zero and
    /// are selected as typed scalar loads; the union itself has no runtime
    /// aggregate value.
    UnionAddress {
        pointer: Box<C0Expression>,
        union_name: String,
    },
    Index(Box<C0Expression>, Box<C0Expression>),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct C0SyntaxError {
    message: String,
    position: Option<SourcePosition>,
}

impl C0Function {
    pub(crate) fn external(
        return_type: C0Type,
        name: String,
        parameters: Vec<C0Parameter>,
    ) -> Self {
        Self {
            return_type,
            return_struct_name: None,
            return_pointer_struct_name: None,
            name,
            inline_body: false,
            parameters,
            body: C0Statement::Skip,
            structs: BTreeMap::new(),
            enums: BTreeMap::new(),
            unions: BTreeMap::new(),
            globals: BTreeMap::new(),
            global_arrays: BTreeMap::new(),
            global_aggregates: BTreeMap::new(),
            global_aggregate_arrays: BTreeMap::new(),
            static_locals: BTreeMap::new(),
            static_arrays: BTreeMap::new(),
            static_aggregates: BTreeMap::new(),
            static_aggregate_arrays: BTreeMap::new(),
            string_literals: Vec::new(),
        }
    }

    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn parameters(&self) -> &[C0Parameter] {
        &self.parameters
    }

    pub fn return_type(&self) -> C0Type {
        self.return_type
    }

    pub fn return_struct_name(&self) -> Option<&str> {
        self.return_struct_name.as_deref()
    }

    pub fn return_pointer_struct_name(&self) -> Option<&str> {
        self.return_pointer_struct_name.as_deref()
    }

    pub fn body(&self) -> &C0Statement {
        &self.body
    }

    pub fn structs(&self) -> &BTreeMap<String, C0StructLayout> {
        &self.structs
    }

    pub fn enums(&self) -> &BTreeMap<String, C0EnumDefinition> {
        &self.enums
    }

    pub fn unions(&self) -> &BTreeMap<String, C0UnionLayout> {
        &self.unions
    }

    pub fn globals(&self) -> &BTreeMap<String, C0Global> {
        &self.globals
    }

    pub fn global_arrays(&self) -> &BTreeMap<String, C0GlobalArray> {
        &self.global_arrays
    }

    pub fn global_aggregates(&self) -> &BTreeMap<String, C0GlobalAggregate> {
        &self.global_aggregates
    }

    pub fn global_aggregate_arrays(&self) -> &BTreeMap<String, C0GlobalAggregateArray> {
        &self.global_aggregate_arrays
    }

    pub fn static_locals(&self) -> &BTreeMap<String, C0StaticLocal> {
        &self.static_locals
    }

    pub fn static_arrays(&self) -> &BTreeMap<String, C0StaticArray> {
        &self.static_arrays
    }

    pub fn static_aggregates(&self) -> &BTreeMap<String, C0StaticAggregate> {
        &self.static_aggregates
    }

    pub fn static_aggregate_arrays(&self) -> &BTreeMap<String, C0StaticAggregateArray> {
        &self.static_aggregate_arrays
    }

    pub fn string_literals(&self) -> &[C0StringLiteral] {
        &self.string_literals
    }

    pub(crate) fn with_globals(mut self, globals: BTreeMap<String, C0Global>) -> Self {
        self.globals = globals;
        self
    }

    pub(crate) fn with_global_arrays(
        mut self,
        global_arrays: BTreeMap<String, C0GlobalArray>,
    ) -> Self {
        self.global_arrays = global_arrays;
        self
    }

    pub(crate) fn with_global_aggregates(
        mut self,
        global_aggregates: BTreeMap<String, C0GlobalAggregate>,
    ) -> Self {
        self.global_aggregates = global_aggregates;
        self
    }

    pub(crate) fn with_global_aggregate_arrays(
        mut self,
        global_aggregate_arrays: BTreeMap<String, C0GlobalAggregateArray>,
    ) -> Self {
        self.global_aggregate_arrays = global_aggregate_arrays;
        self
    }

    pub fn body_kernel_statement(&self) -> crate::kernel::CStatement {
        self.body.to_kernel_statement()
    }

    pub fn to_kernel_function(&self) -> crate::kernel::CFunction {
        let mut function = crate::kernel::c_function(
            if self.return_struct_name.is_some() {
                crate::kernel::CType::UInt8Pointer
            } else {
                self.return_type.to_kernel_type()
            },
            self.name.clone(),
            self.parameters
                .iter()
                .map(C0Parameter::to_kernel_parameter)
                .collect(),
            self.body.to_kernel_statement(),
        );
        if self.inline_body {
            function = function.with_inline_body();
        }
        if let Some(name) = &self.return_struct_name {
            let layout = self
                .structs
                .get(name)
                .expect("struct return has a parsed layout")
                .to_kernel_aggregate_layout();
            function = function.with_return_aggregate_layout(layout);
        }
        function
            .with_global_variables(
                self.globals
                    .values()
                    .filter_map(C0Global::to_kernel_global)
                    .collect(),
            )
            .with_global_arrays(
                self.global_arrays
                    .values()
                    .filter_map(C0GlobalArray::to_kernel_global_array)
                    .collect(),
            )
            .with_global_aggregates(
                self.global_aggregates
                    .values()
                    .filter_map(C0GlobalAggregate::to_kernel_global_aggregate)
                    .collect(),
            )
            .with_global_aggregate_arrays(
                self.global_aggregate_arrays
                    .values()
                    .filter_map(C0GlobalAggregateArray::to_kernel_global_aggregate_array)
                    .collect(),
            )
            .with_static_variables(
                self.static_locals
                    .values()
                    .filter_map(C0StaticLocal::to_kernel_static)
                    .collect(),
            )
            .with_static_arrays(
                self.static_arrays
                    .values()
                    .filter_map(C0StaticArray::to_kernel_static_array)
                    .collect(),
            )
            .with_static_aggregates(
                self.static_aggregates
                    .values()
                    .map(C0StaticAggregate::to_kernel_static_aggregate)
                    .collect(),
            )
            .with_static_aggregate_arrays(
                self.static_aggregate_arrays
                    .values()
                    .map(C0StaticAggregateArray::to_kernel_static_aggregate_array)
                    .collect(),
            )
            .with_string_literals(
                self.string_literals
                    .iter()
                    .map(|literal| {
                        crate::kernel::CStringLiteral::new(
                            literal.name.clone(),
                            literal.bytes.clone(),
                        )
                    })
                    .collect(),
            )
    }
}

impl C0StructLayout {
    pub fn fields(&self) -> &BTreeMap<String, C0StructField> {
        &self.fields
    }

    pub fn field(&self, name: &str) -> Option<&C0StructField> {
        self.fields.get(name)
    }

    pub fn size_bytes(&self) -> u32 {
        self.size_bytes
    }

    pub fn alignment_bytes(&self) -> u32 {
        self.alignment_bytes
    }

    pub(crate) fn to_kernel_aggregate_layout(&self) -> crate::kernel::CAggregateLayout {
        crate::kernel::CAggregateLayout::new(
            self.size_bytes,
            self.alignment_bytes,
            self.aggregate_fields
                .iter()
                .map(|field| {
                    crate::kernel::CAggregateField::new(
                        &field.name,
                        field.offset_bytes,
                        field.c_type.to_kernel_type(),
                    )
                })
                .collect(),
        )
    }

    fn aggregate_fields(&self) -> &[C0AggregateField] {
        &self.aggregate_fields
    }
}

impl C0EnumDefinition {
    pub fn values(&self) -> &BTreeMap<String, i32> {
        &self.values
    }

    pub fn value(&self, name: &str) -> Option<i32> {
        self.values.get(name).copied()
    }
}

impl C0UnionLayout {
    pub fn fields(&self) -> &BTreeMap<String, C0UnionField> {
        &self.fields
    }

    pub fn field(&self, name: &str) -> Option<&C0UnionField> {
        self.fields.get(name)
    }

    pub fn size_bytes(&self) -> u32 {
        self.size_bytes
    }

    pub fn alignment_bytes(&self) -> u32 {
        self.alignment_bytes
    }
}

impl C0UnionField {
    pub fn c_type(&self) -> C0Type {
        self.c_type
    }

    pub fn enum_name(&self) -> Option<&str> {
        self.enum_name.as_deref()
    }

    pub fn offset_bytes(&self) -> u32 {
        self.offset_bytes
    }

    pub fn byte_width(&self) -> u32 {
        self.byte_width
    }
}

impl C0StructField {
    pub fn c_type(&self) -> C0Type {
        self.c_type
    }

    pub fn offset_bytes(&self) -> u32 {
        self.offset_bytes
    }

    pub fn struct_name(&self) -> Option<&str> {
        self.struct_name.as_deref()
    }

    pub fn enum_name(&self) -> Option<&str> {
        self.enum_name.as_deref()
    }

    pub fn union_name(&self) -> Option<&str> {
        self.union_name.as_deref()
    }

    pub fn function_pointer_signature(&self) -> Option<&C0FunctionPointerSignature> {
        self.function_pointer_signature.as_ref()
    }

    pub fn array_element_width(&self) -> Option<u32> {
        self.array_element_width
    }

    pub fn array_shape(&self) -> Option<&[u32]> {
        self.array_shape.as_deref()
    }

    pub fn byte_width(&self) -> u32 {
        self.byte_width
    }
}

impl C0Parameter {
    pub(crate) fn new(c_type: C0Type, name: String, struct_name: Option<String>) -> Self {
        Self {
            c_type,
            name,
            volatile: false,
            pointee_volatile: false,
            constant: false,
            pointee_constant: false,
            struct_name,
            struct_layout: None,
            pointee_struct_layout: None,
            function_pointer_signature: None,
            array_element_width: None,
        }
    }

    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn c_type(&self) -> C0Type {
        self.c_type
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

    pub(crate) fn with_constant(mut self, constant: bool) -> Self {
        self.constant = constant;
        self
    }

    pub(crate) fn with_pointee_constant(mut self, pointee_constant: bool) -> Self {
        self.pointee_constant = pointee_constant;
        self
    }

    pub fn struct_name(&self) -> Option<&str> {
        self.struct_name.as_deref()
    }

    pub fn struct_layout(&self) -> Option<&C0StructLayout> {
        self.struct_layout.as_ref()
    }

    pub fn pointee_struct_layout(&self) -> Option<&C0StructLayout> {
        self.pointee_struct_layout.as_ref()
    }

    pub fn array_element_width(&self) -> Option<u32> {
        self.array_element_width
    }

    pub fn function_pointer_signature(&self) -> Option<&C0FunctionPointerSignature> {
        self.function_pointer_signature.as_ref()
    }

    pub fn is_struct_value(&self) -> bool {
        self.struct_name.is_some() && matches!(self.c_type, C0Type::UInt8Array(_))
    }

    pub fn to_kernel_parameter(&self) -> crate::kernel::CParameter {
        if self.is_struct_value() {
            let layout = self
                .struct_layout
                .as_ref()
                .expect("struct value parameter has a parsed layout")
                .to_kernel_aggregate_layout();
            return crate::kernel::c_parameter_with_aggregate_layout(
                self.name.clone(),
                crate::kernel::CType::UInt8Pointer,
                layout,
            )
            .with_volatile(self.is_volatile())
            .with_pointee_volatile(self.pointee_is_volatile())
            .with_constant(self.is_constant())
            .with_pointee_constant(self.pointee_is_constant());
        }
        let c_type = self
            .array_element_width
            .map(|_| crate::kernel::CType::UInt8Pointer)
            .unwrap_or_else(|| self.c_type.to_kernel_type());
        crate::kernel::c_parameter(self.name.clone(), c_type)
            .with_volatile(self.is_volatile())
            .with_pointee_volatile(self.pointee_is_volatile())
            .with_constant(self.is_constant())
            .with_pointee_constant(self.pointee_is_constant())
    }
}

impl C0Type {
    pub fn is_pointer(self) -> bool {
        matches!(
            self,
            Self::VoidPointer
                | Self::Int32Pointer
                | Self::Int16Pointer
                | Self::UInt16Pointer
                | Self::UInt8Pointer
                | Self::UInt32Pointer
                | Self::Int64Pointer
                | Self::UInt64Pointer
                | Self::Int16PointerPointer
                | Self::UInt16PointerPointer
                | Self::Int32PointerPointer
                | Self::UInt8PointerPointer
                | Self::UInt32PointerPointer
                | Self::Int64PointerPointer
                | Self::UInt64PointerPointer
                | Self::Float32PointerPointer
                | Self::Float64PointerPointer
                | Self::FunctionPointer(_)
        )
    }

    pub fn is_object_pointer(self) -> bool {
        self.is_pointer() && !matches!(self, Self::FunctionPointer(_))
    }

    fn is_scalar_pointer(self) -> bool {
        matches!(
            self,
            Self::Int16Pointer
                | Self::Int32Pointer
                | Self::UInt8Pointer
                | Self::UInt16Pointer
                | Self::UInt32Pointer
                | Self::Int64Pointer
                | Self::UInt64Pointer
        )
    }

    pub fn pointee_type(self) -> Option<Self> {
        match self {
            Self::Int16Pointer | Self::Int16Array(_) => Some(Self::Int16),
            Self::Int32Pointer | Self::Int32Array(_) => Some(Self::Int32),
            Self::UInt8Pointer | Self::UInt8Array(_) => Some(Self::UInt8),
            Self::UInt16Pointer | Self::UInt16Array(_) => Some(Self::UInt16),
            Self::UInt32Pointer | Self::UInt32Array(_) => Some(Self::UInt32),
            Self::Int64Pointer | Self::Int64Array(_) => Some(Self::Int64),
            Self::UInt64Pointer | Self::UInt64Array(_) => Some(Self::UInt64),
            Self::Float32Pointer | Self::Float32Array(_) => Some(Self::Float32),
            Self::Float64Pointer | Self::Float64Array(_) => Some(Self::Float64),
            Self::Int16PointerPointer => Some(Self::Int16Pointer),
            Self::UInt16PointerPointer => Some(Self::UInt16Pointer),
            Self::Int32PointerPointer => Some(Self::Int32Pointer),
            Self::UInt8PointerPointer => Some(Self::UInt8Pointer),
            Self::UInt32PointerPointer => Some(Self::UInt32Pointer),
            Self::Int64PointerPointer => Some(Self::Int64Pointer),
            Self::UInt64PointerPointer => Some(Self::UInt64Pointer),
            Self::Float32PointerPointer => Some(Self::Float32Pointer),
            Self::Float64PointerPointer => Some(Self::Float64Pointer),
            Self::Void
            | Self::VoidPointer
            | Self::Int16
            | Self::Int32
            | Self::UInt8
            | Self::UInt16
            | Self::UInt32
            | Self::Int64
            | Self::UInt64
            | Self::Float32
            | Self::Float64
            | Self::FunctionPointer(_) => None,
        }
    }

    pub fn to_kernel_type(self) -> crate::kernel::CType {
        match self {
            Self::Void => crate::kernel::CType::Void,
            Self::VoidPointer => crate::kernel::CType::VoidPointer,
            Self::Int16 => crate::kernel::CType::Int16,
            Self::Int32 => crate::kernel::CType::Int32,
            Self::UInt8 => crate::kernel::CType::UInt8,
            Self::UInt16 => crate::kernel::CType::UInt16,
            Self::UInt32 => crate::kernel::CType::UInt32,
            Self::Int64 => crate::kernel::CType::Int64,
            Self::UInt64 => crate::kernel::CType::UInt64,
            Self::Float32 => crate::kernel::CType::Float32,
            Self::Float64 => crate::kernel::CType::Float64,
            Self::Int32Pointer => crate::kernel::CType::Int32Pointer,
            Self::Int16Pointer => crate::kernel::CType::Int16Pointer,
            Self::UInt16Pointer => crate::kernel::CType::UInt16Pointer,
            Self::UInt8Pointer => crate::kernel::CType::UInt8Pointer,
            Self::UInt32Pointer => crate::kernel::CType::UInt32Pointer,
            Self::Int64Pointer => crate::kernel::CType::Int64Pointer,
            Self::UInt64Pointer => crate::kernel::CType::UInt64Pointer,
            Self::Float32Pointer => crate::kernel::CType::Float32Pointer,
            Self::Float64Pointer => crate::kernel::CType::Float64Pointer,
            Self::Int16PointerPointer => crate::kernel::CType::Int16PointerPointer,
            Self::UInt16PointerPointer => crate::kernel::CType::UInt16PointerPointer,
            Self::Int32PointerPointer => crate::kernel::CType::Int32PointerPointer,
            Self::UInt8PointerPointer => crate::kernel::CType::UInt8PointerPointer,
            Self::UInt32PointerPointer => crate::kernel::CType::UInt32PointerPointer,
            Self::Int64PointerPointer => crate::kernel::CType::Int64PointerPointer,
            Self::UInt64PointerPointer => crate::kernel::CType::UInt64PointerPointer,
            Self::Float32PointerPointer => crate::kernel::CType::Float32PointerPointer,
            Self::Float64PointerPointer => crate::kernel::CType::Float64PointerPointer,
            Self::FunctionPointer(signature) => crate::kernel::CType::FunctionPointer(signature),
            Self::Int32Array(length) => crate::kernel::CType::Int32Array(length),
            Self::UInt8Array(length) => crate::kernel::CType::UInt8Array(length),
            Self::Int16Array(length) => crate::kernel::CType::Int16Array(length),
            Self::UInt16Array(length) => crate::kernel::CType::UInt16Array(length),
            Self::UInt32Array(length) => crate::kernel::CType::UInt32Array(length),
            Self::Int64Array(length) => crate::kernel::CType::Int64Array(length),
            Self::UInt64Array(length) => crate::kernel::CType::UInt64Array(length),
            Self::Float32Array(length) => crate::kernel::CType::Float32Array(length),
            Self::Float64Array(length) => crate::kernel::CType::Float64Array(length),
        }
    }
}

impl C0Statement {
    pub fn to_kernel_statement(&self) -> crate::kernel::CStatement {
        match self {
            Self::Skip => crate::kernel::c_skip(),
            Self::Break => crate::kernel::c_break(),
            Self::Continue => crate::kernel::c_continue(),
            Self::Declare {
                c_type,
                name,
                volatile,
                pointee_volatile,
                constant,
                pointee_constant,
            } => crate::kernel::c_declare_with_all_qualifiers(
                name.clone(),
                c_type.to_kernel_type(),
                *volatile,
                *pointee_volatile,
                *constant,
                *pointee_constant,
            ),
            Self::DeclareStructValue { name, layout } => crate::kernel::c_declare_aggregate(
                name.clone(),
                layout.to_kernel_aggregate_layout(),
            ),
            Self::Assign { name, expression } => {
                crate::kernel::c_assign(name.clone(), expression.to_kernel_expression())
            }
            Self::CallAssign {
                target,
                function_name,
                arguments,
            } => crate::kernel::c_call_assign(
                target.clone(),
                function_name.clone(),
                arguments
                    .iter()
                    .map(C0Expression::to_kernel_expression)
                    .collect(),
            ),
            Self::Call {
                function_name,
                arguments,
            } => crate::kernel::c_call(
                function_name.clone(),
                arguments
                    .iter()
                    .map(C0Expression::to_kernel_expression)
                    .collect(),
            ),
            Self::IndirectCall { .. } => {
                unreachable!("indirect call statements must be lowered before kernel conversion")
            }
            Self::HeapAllocate {
                target,
                bytes,
                zeroed,
            } => crate::kernel::c_heap_allocate_sized_with_zeroed(
                target.clone(),
                bytes.to_kernel_expression(),
                *zeroed,
            ),
            Self::HeapFree { pointer } => {
                crate::kernel::c_heap_free(pointer.to_kernel_expression())
            }
            Self::Seq(first, second) => {
                crate::kernel::c_seq(first.to_kernel_statement(), second.to_kernel_statement())
            }
            Self::Return(expression) => crate::kernel::c_return(expression.to_kernel_expression()),
            Self::Store {
                pointer,
                value,
                value_type,
            } => match value_type {
                Some(value_type) => crate::kernel::c_typed_store(
                    pointer.to_kernel_expression(),
                    value.to_kernel_expression(),
                    value_type.to_kernel_type(),
                ),
                None => crate::kernel::c_store(
                    pointer.to_kernel_expression(),
                    value.to_kernel_expression(),
                ),
            },
            Self::Update {
                target,
                operator,
                operand,
            } => crate::kernel::c_update(
                target.to_kernel_expression(),
                match operator {
                    C0UpdateOperator::Add => crate::kernel::CUpdateOperator::Add,
                    C0UpdateOperator::Subtract => crate::kernel::CUpdateOperator::Subtract,
                    C0UpdateOperator::Multiply => crate::kernel::CUpdateOperator::Multiply,
                    C0UpdateOperator::Divide => crate::kernel::CUpdateOperator::Divide,
                    C0UpdateOperator::Remainder => crate::kernel::CUpdateOperator::Remainder,
                    C0UpdateOperator::ShiftLeft => crate::kernel::CUpdateOperator::ShiftLeft,
                    C0UpdateOperator::ShiftRight => crate::kernel::CUpdateOperator::ShiftRight,
                    C0UpdateOperator::BitwiseAnd => crate::kernel::CUpdateOperator::BitwiseAnd,
                    C0UpdateOperator::BitwiseOr => crate::kernel::CUpdateOperator::BitwiseOr,
                    C0UpdateOperator::BitwiseXor => crate::kernel::CUpdateOperator::BitwiseXor,
                },
                operand.to_kernel_expression(),
            ),
            Self::If {
                condition,
                then_branch,
                else_branch,
            } => crate::kernel::c_if(
                condition.to_kernel_expression(),
                then_branch.to_kernel_statement(),
                else_branch.to_kernel_statement(),
            ),
            Self::While { condition, body } => crate::kernel::c_while(
                condition.to_kernel_expression(),
                Vec::new(),
                body.to_kernel_statement(),
            ),
            Self::DoWhile { condition, body } => crate::kernel::c_do_while(
                condition.to_kernel_expression(),
                body.to_kernel_statement(),
            ),
            Self::For {
                initializer,
                condition,
                step,
                body,
            } => {
                let step = step.to_kernel_statement();
                crate::kernel::c_seq(
                    initializer.to_kernel_statement(),
                    crate::kernel::c_while(
                        condition.to_kernel_expression(),
                        Vec::new(),
                        crate::kernel::c_for_body_with_step(body.to_kernel_statement(), step),
                    ),
                )
            }
            Self::Switch { expression, cases } => crate::kernel::c_switch(
                expression.to_kernel_expression(),
                cases
                    .iter()
                    .map(|case| crate::kernel::CSwitchCase {
                        value: case.value,
                        body: Box::new(case.body.to_kernel_statement()),
                    })
                    .collect(),
            ),
        }
    }
}

impl C0Expression {
    pub fn to_kernel_expression(&self) -> crate::kernel::CExpression {
        match self {
            Self::Void => crate::kernel::c_void_value(),
            Self::Variable(name) => crate::kernel::c_variable(name.clone()),
            Self::Call { .. } => {
                unreachable!("call expressions must be lowered before kernel conversion")
            }
            Self::IndirectCall { .. } => {
                unreachable!("indirect call expressions must be lowered before kernel conversion")
            }
            Self::FunctionAddress(name) => crate::kernel::c_function_address(name.clone()),
            Self::Cast {
                expression, c_type, ..
            } => crate::kernel::c_cast(expression.to_kernel_expression(), c_type.to_kernel_type()),
            Self::Conditional {
                condition,
                then_branch,
                else_branch,
            } => crate::kernel::c_conditional(
                condition.to_kernel_expression(),
                then_branch.to_kernel_expression(),
                else_branch.to_kernel_expression(),
            ),
            Self::FloatNegate(expression) => {
                crate::kernel::c_float_negate(expression.to_kernel_expression())
            }
            Self::FloatClassification {
                expression,
                classification,
            } => crate::kernel::c_float_classification(
                expression.to_kernel_expression(),
                match classification {
                    C0FloatClassification::Finite => crate::kernel::CFloatClassification::Finite,
                    C0FloatClassification::Infinite => {
                        crate::kernel::CFloatClassification::Infinite
                    }
                    C0FloatClassification::Zero => crate::kernel::CFloatClassification::Zero,
                    C0FloatClassification::Subnormal => {
                        crate::kernel::CFloatClassification::Subnormal
                    }
                    C0FloatClassification::Nan => crate::kernel::CFloatClassification::Nan,
                },
            ),
            Self::AddressOf(target) => match target.as_ref() {
                Self::AggregateAddress { pointer, .. } | Self::UnionAddress { pointer, .. } => {
                    pointer.to_kernel_expression()
                }
                target => {
                    crate::kernel::CExpression::AddressOf(Box::new(target.to_kernel_expression()))
                }
            },
            Self::AggregateAddress { pointer, .. } => pointer.to_kernel_expression(),
            Self::UnionAddress { pointer, .. } => pointer.to_kernel_expression(),
            Self::PointerOffsetBytes { pointer, bytes } => {
                crate::kernel::c_pointer_offset_bytes(pointer.to_kernel_expression(), *bytes)
            }
            Self::Int32Literal(value) => crate::kernel::c_int32_literal(*value),
            Self::UInt8Literal(value) => crate::kernel::c_uint8_literal(*value),
            Self::UInt32Literal(value) => crate::kernel::c_uint32_literal(*value),
            Self::Int64Literal(value) => crate::kernel::c_int64_literal(*value),
            Self::UInt64Literal(value) => crate::kernel::c_uint64_literal(*value),
            Self::Float32Literal(bits) => crate::kernel::c_float32_literal(*bits),
            Self::Float64Literal(bits) => crate::kernel::c_float64_literal(*bits),
            Self::SizeOfStruct { bytes, .. } | Self::SizeOfType { bytes, .. } => {
                crate::kernel::c_int32_literal(*bytes)
            }
            Self::SizeOfUnion { bytes, .. } => crate::kernel::c_int32_literal(*bytes),
            Self::LessThan(left, right) => crate::kernel::c_less_than(
                left.to_kernel_expression(),
                right.to_kernel_expression(),
            ),
            Self::LessEqual(left, right) => crate::kernel::c_less_equal(
                left.to_kernel_expression(),
                right.to_kernel_expression(),
            ),
            Self::GreaterThan(left, right) => crate::kernel::c_greater_than(
                left.to_kernel_expression(),
                right.to_kernel_expression(),
            ),
            Self::GreaterEqual(left, right) => crate::kernel::c_greater_equal(
                left.to_kernel_expression(),
                right.to_kernel_expression(),
            ),
            Self::Equal(left, right) => {
                crate::kernel::c_equal(left.to_kernel_expression(), right.to_kernel_expression())
            }
            Self::NotEqual(left, right) => crate::kernel::c_not_equal(
                left.to_kernel_expression(),
                right.to_kernel_expression(),
            ),
            Self::Not(expression) => crate::kernel::c_not(expression.to_kernel_expression()),
            Self::And(left, right) => {
                crate::kernel::c_and(left.to_kernel_expression(), right.to_kernel_expression())
            }
            Self::Or(left, right) => {
                crate::kernel::c_or(left.to_kernel_expression(), right.to_kernel_expression())
            }
            Self::Add(left, right) => {
                crate::kernel::c_add(left.to_kernel_expression(), right.to_kernel_expression())
            }
            Self::Subtract(left, right) => {
                crate::kernel::c_subtract(left.to_kernel_expression(), right.to_kernel_expression())
            }
            Self::Multiply(left, right) => {
                crate::kernel::c_multiply(left.to_kernel_expression(), right.to_kernel_expression())
            }
            Self::Divide(left, right) => {
                crate::kernel::c_divide(left.to_kernel_expression(), right.to_kernel_expression())
            }
            Self::Remainder(left, right) => crate::kernel::c_remainder(
                left.to_kernel_expression(),
                right.to_kernel_expression(),
            ),
            Self::ShiftLeft(left, right) => crate::kernel::c_shift_left(
                left.to_kernel_expression(),
                right.to_kernel_expression(),
            ),
            Self::ShiftRight(left, right) => crate::kernel::c_shift_right(
                left.to_kernel_expression(),
                right.to_kernel_expression(),
            ),
            Self::BitwiseAnd(left, right) => crate::kernel::c_bitwise_and(
                left.to_kernel_expression(),
                right.to_kernel_expression(),
            ),
            Self::BitwiseOr(left, right) => crate::kernel::c_bitwise_or(
                left.to_kernel_expression(),
                right.to_kernel_expression(),
            ),
            Self::BitwiseXor(left, right) => crate::kernel::c_bitwise_xor(
                left.to_kernel_expression(),
                right.to_kernel_expression(),
            ),
            Self::BitwiseNot(expression) => {
                crate::kernel::c_bitwise_not(expression.to_kernel_expression())
            }
            Self::Load(pointer) => crate::kernel::c_load(pointer.to_kernel_expression()),
            Self::Field {
                pointer,
                field_type,
                field_struct_name: _,
                ..
            } => crate::kernel::c_typed_load(
                pointer.to_kernel_expression(),
                field_type.to_kernel_type(),
            ),
            Self::UnionField {
                pointer,
                field_type,
                ..
            } => crate::kernel::c_typed_load(
                pointer.to_kernel_expression(),
                field_type.to_kernel_type(),
            ),
            Self::Index(base, index) => {
                crate::kernel::c_index(base.to_kernel_expression(), index.to_kernel_expression())
            }
        }
    }
}

impl C0SyntaxError {
    fn new(message: impl Into<String>) -> Self {
        Self {
            message: message.into(),
            position: None,
        }
    }

    fn at(position: SourcePosition, message: impl Into<String>) -> Self {
        Self {
            message: message.into(),
            position: Some(position),
        }
    }

    /// Attaches `position` if the error does not already carry one.
    fn with_position(mut self, position: SourcePosition) -> Self {
        self.position.get_or_insert(position);
        self
    }

    pub fn message(&self) -> &str {
        &self.message
    }

    pub fn position(&self) -> Option<SourcePosition> {
        self.position
    }
}

impl std::fmt::Display for C0SyntaxError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.position {
            Some(position) => write!(f, "{position}: {}", self.message),
            None => write!(f, "{}", self.message),
        }
    }
}

pub fn parse_function(source: &str) -> Result<C0Function, C0SyntaxError> {
    parse_function_for_abi(source, CAbi::SUPPORTED)
}

pub fn parse_function_for_abi(source: &str, abi: CAbi) -> Result<C0Function, C0SyntaxError> {
    Parser::new(source, abi)?.parse_function()
}

/// Parses every function definition in one C source. Prototypes are accepted
/// as declarations and are used to validate later definitions, but are not
/// returned as executable functions.
pub fn parse_functions(source: &str) -> Result<Vec<C0Function>, C0SyntaxError> {
    parse_functions_for_abi(source, CAbi::SUPPORTED)
}

pub(crate) fn parse_functions_for_source(
    source: &str,
    source_identity: &str,
) -> Result<Vec<C0Function>, C0SyntaxError> {
    Parser::new_with_source_identity(source, CAbi::SUPPORTED, Some(source_identity))?
        .parse_functions()
}

pub fn parse_functions_for_abi(source: &str, abi: CAbi) -> Result<Vec<C0Function>, C0SyntaxError> {
    Parser::new(source, abi)?.parse_functions()
}

/// Validates a declaration-only C header after its includes have been
/// expanded. Headers may contain type declarations and function prototypes,
/// but never executable function definitions.
pub fn validate_header(source: &str) -> Result<(), C0SyntaxError> {
    Parser::new(source, CAbi::SUPPORTED)?.parse_header()
}

fn validate_function_returns(
    statement: &C0Statement,
    return_type: C0Type,
) -> Result<(), C0SyntaxError> {
    match statement {
        C0Statement::Return(C0Expression::Void) if return_type != C0Type::Void => {
            Err(C0SyntaxError::new("non-void functions must return a value"))
        }
        C0Statement::Return(C0Expression::Void) => Ok(()),
        C0Statement::Return(_) if return_type == C0Type::Void => {
            Err(C0SyntaxError::new("void functions cannot return a value"))
        }
        C0Statement::Seq(first, second) => {
            validate_function_returns(first, return_type)?;
            validate_function_returns(second, return_type)
        }
        C0Statement::If {
            then_branch,
            else_branch,
            ..
        } => {
            validate_function_returns(then_branch, return_type)?;
            validate_function_returns(else_branch, return_type)
        }
        C0Statement::While { body, .. }
        | C0Statement::DoWhile { body, .. }
        | C0Statement::For { body, .. } => validate_function_returns(body, return_type),
        C0Statement::Switch { cases, .. } => cases
            .iter()
            .try_for_each(|case| validate_function_returns(&case.body, return_type)),
        C0Statement::Skip
        | C0Statement::Break
        | C0Statement::Continue
        | C0Statement::Declare { .. }
        | C0Statement::DeclareStructValue { .. }
        | C0Statement::Assign { .. }
        | C0Statement::CallAssign { .. }
        | C0Statement::Call { .. }
        | C0Statement::IndirectCall { .. }
        | C0Statement::HeapAllocate { .. }
        | C0Statement::HeapFree { .. }
        | C0Statement::Return(_)
        | C0Statement::Store { .. }
        | C0Statement::Update { .. } => Ok(()),
    }
}

fn validate_global_initializer(
    parser: &Parser,
    c_type: C0Type,
    initializer: &C0Expression,
) -> Result<(), C0SyntaxError> {
    if matches!(c_type, C0Type::Float32 | C0Type::Float64) {
        let matches_type = matches!(
            (c_type, initializer),
            (C0Type::Float32, C0Expression::Float32Literal(_))
                | (C0Type::Float64, C0Expression::Float64Literal(_))
        );
        return if matches_type {
            Ok(())
        } else {
            Err(parser.error_here("floating-point global initializer has the wrong type"))
        };
    }
    if c_type.is_pointer() {
        return if matches!(initializer, C0Expression::Int32Literal(0)) {
            Ok(())
        } else {
            Err(parser.error_here(
                "pointer global initializers currently support only the null pointer literal",
            ))
        };
    }
    let bits = match initializer {
        C0Expression::Int32Literal(value) => u64::from(*value),
        C0Expression::UInt8Literal(value) => u64::from(*value),
        C0Expression::UInt32Literal(value) => u64::from(*value),
        _ => {
            return Err(
                parser.error_here("global initializers currently support only integer literals")
            );
        }
    };
    let valid = match c_type {
        C0Type::Int16 => bits <= i16::MAX as u64,
        C0Type::Int32 => bits <= i32::MAX as u64,
        C0Type::UInt8 => bits <= u8::MAX as u64,
        C0Type::UInt16 => bits <= u16::MAX as u64,
        C0Type::UInt32 => true,
        _ => false,
    };
    if valid {
        Ok(())
    } else {
        Err(parser.error_here(format!(
            "integer literal is out of range for global type {c_type:?}"
        )))
    }
}

fn validate_static_initializer(
    parser: &Parser,
    c_type: C0Type,
    initializer: &C0Expression,
) -> Result<(), C0SyntaxError> {
    if matches!(c_type, C0Type::Float32 | C0Type::Float64) {
        let matches_type = matches!(
            (c_type, initializer),
            (C0Type::Float32, C0Expression::Float32Literal(_))
                | (C0Type::Float64, C0Expression::Float64Literal(_))
        );
        return if matches_type {
            Ok(())
        } else {
            Err(parser.error_here("floating-point static initializer has the wrong type"))
        };
    }
    let bits = match initializer {
        C0Expression::Int32Literal(value) => u64::from(*value),
        C0Expression::UInt8Literal(value) => u64::from(*value),
        C0Expression::UInt32Literal(value) => u64::from(*value),
        _ => {
            return Err(parser
                .error_here("static local initializers currently support only integer literals"));
        }
    };
    let valid = match c_type {
        C0Type::Int16 => bits <= i16::MAX as u64,
        C0Type::Int32 => bits <= i32::MAX as u64,
        C0Type::UInt8 => bits <= u8::MAX as u64,
        C0Type::UInt16 => bits <= u16::MAX as u64,
        C0Type::UInt32 => true,
        _ => false,
    };
    if valid {
        Ok(())
    } else {
        Err(parser.error_here(format!(
            "integer literal is out of range for static local type {c_type:?}"
        )))
    }
}

fn validate_aggregate_initializer(
    parser: &Parser,
    c_type: C0Type,
    initializer: &C0Expression,
) -> Result<(), C0SyntaxError> {
    match c_type {
        C0Type::Int64 => {
            if matches!(
                initializer,
                C0Expression::Int32Literal(_)
                    | C0Expression::UInt8Literal(_)
                    | C0Expression::UInt32Literal(_)
                    | C0Expression::Int64Literal(_)
            ) {
                Ok(())
            } else {
                Err(parser.error_here(
                    "aggregate initializers currently support only integer, floating-point, or null-pointer literals",
                ))
            }
        }
        C0Type::UInt64 => {
            let valid = match initializer {
                C0Expression::Int32Literal(_)
                | C0Expression::UInt8Literal(_)
                | C0Expression::UInt32Literal(_)
                | C0Expression::UInt64Literal(_) => true,
                C0Expression::Int64Literal(value) => *value >= 0,
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
        C0Type::Int32Pointer
        | C0Type::UInt8Pointer
        | C0Type::Float32Pointer
        | C0Type::Float64Pointer
        | C0Type::Int32PointerPointer
        | C0Type::UInt8PointerPointer
        | C0Type::Float32PointerPointer
        | C0Type::Float64PointerPointer => {
            if matches!(initializer, C0Expression::Int32Literal(0)) {
                Ok(())
            } else {
                Err(parser.error_here(
                    "aggregate pointer initializers currently support only the null pointer literal",
                ))
            }
        }
        _ => validate_global_initializer(parser, c_type, initializer).map_err(|error| {
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

fn offset_field_pointer(base: C0Expression, offset_bytes: u32) -> C0Expression {
    if offset_bytes == 0 {
        return base;
    }
    C0Expression::PointerOffsetBytes {
        pointer: Box::new(base),
        bytes: offset_bytes,
    }
}

fn is_plain_struct_type(parsed_type: &ParsedType) -> bool {
    parsed_type.struct_name.is_some() && parsed_type.c_type == C0Type::Int32
}

fn struct_scalar_array_shape(field: &C0StructField) -> Option<(C0Type, Vec<u32>)> {
    let (element_type, length) = match field.c_type {
        C0Type::Int32Array(length) => (C0Type::Int32, length),
        C0Type::UInt8Array(length) => (C0Type::UInt8, length),
        _ => return None,
    };
    if field.struct_name.is_some() {
        return None;
    }
    Some((
        element_type,
        field.array_shape.clone().unwrap_or_else(|| vec![length]),
    ))
}

fn zero_initializer_value(c_type: C0Type) -> C0Expression {
    match c_type {
        C0Type::UInt8 => C0Expression::UInt8Literal(0),
        C0Type::UInt32 => C0Expression::UInt32Literal(0),
        C0Type::Int64 => C0Expression::Int64Literal(0),
        C0Type::UInt64 => C0Expression::UInt64Literal(0),
        C0Type::Int16
        | C0Type::Int32
        | C0Type::UInt16
        | C0Type::Int16Pointer
        | C0Type::UInt16Pointer
        | C0Type::Int32Pointer
        | C0Type::UInt8Pointer
        | C0Type::UInt32Pointer
        | C0Type::Int64Pointer
        | C0Type::UInt64Pointer
        | C0Type::Int16PointerPointer
        | C0Type::UInt16PointerPointer
        | C0Type::Int32PointerPointer
        | C0Type::UInt8PointerPointer
        | C0Type::UInt32PointerPointer
        | C0Type::Int64PointerPointer
        | C0Type::UInt64PointerPointer => C0Expression::Int32Literal(0),
        _ => unreachable!("zero initializer called for non-scalar field type"),
    }
}

fn flatten_aggregate_fields(
    fields: &BTreeMap<String, C0StructField>,
    structs: &BTreeMap<String, C0StructLayout>,
) -> Vec<C0AggregateField> {
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
        aggregate_fields: &mut Vec<C0AggregateField>,
        prefix: &str,
        base_offset: u32,
        nested_layout: &C0StructLayout,
    ) {
        for nested_field in nested_layout.aggregate_fields() {
            aggregate_fields.push(C0AggregateField {
                name: format!("{prefix}.{}", nested_field.name),
                offset_bytes: base_offset
                    .checked_add(nested_field.offset_bytes)
                    .expect("validated embedded struct field offset"),
                c_type: nested_field.c_type,
            });
        }
    }

    let mut aggregate_fields = Vec::new();
    for (field_name, field) in fields {
        if field.c_type == C0Type::Int32
            && field.struct_name.is_some()
            && field.array_element_width.is_none()
        {
            let nested_name = field
                .struct_name
                .as_ref()
                .expect("embedded struct field has a struct name");
            let nested_layout = structs
                .get(nested_name)
                .expect("embedded struct field has a parsed layout");
            append_nested_fields(
                &mut aggregate_fields,
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
            }
        } else {
            aggregate_fields.push(C0AggregateField {
                name: field_name.clone(),
                offset_bytes: field.offset_bytes,
                c_type: field.c_type,
            });
        }
    }
    aggregate_fields
}

fn struct_value_type(layout: &C0StructLayout) -> C0Type {
    C0Type::UInt8Array(layout.size_bytes)
}

fn field_expression(
    pointer: C0Expression,
    field_type: C0Type,
    field_struct_name: Option<String>,
    field_union_name: Option<String>,
    function_pointer_signature: Option<C0FunctionPointerSignature>,
    array_shape: Option<Vec<u32>>,
) -> C0Expression {
    if let Some(union_name) = field_union_name {
        return C0Expression::UnionAddress {
            pointer: Box::new(pointer),
            union_name,
        };
    }
    if field_type == C0Type::Int32 {
        if let Some(struct_name) = field_struct_name {
            return C0Expression::AggregateAddress {
                pointer: Box::new(pointer),
                struct_name,
            };
        }
    }
    C0Expression::Field {
        pointer: Box::new(pointer),
        field_type,
        field_struct_name,
        function_pointer_signature,
        array_shape,
    }
}

fn contains_aggregate_value(expression: &C0Expression) -> bool {
    match expression {
        C0Expression::AggregateAddress { .. } | C0Expression::UnionAddress { .. } => true,
        C0Expression::Field {
            field_type,
            field_struct_name,
            ..
        } => *field_type == C0Type::Int32 && field_struct_name.is_some(),
        C0Expression::UnionField { .. } => false,
        // Call arguments are checked against the callee's parameter shape
        // while they are parsed. In particular, a direct aggregate lvalue is
        // valid when the corresponding parameter is a copyable struct, so it
        // must not be rejected again by the enclosing expression check.
        C0Expression::Call { .. } | C0Expression::IndirectCall { .. } => false,
        C0Expression::AddressOf(_) => false,
        C0Expression::Cast { expression, .. }
        | C0Expression::FloatNegate(expression)
        | C0Expression::FloatClassification { expression, .. }
        | C0Expression::PointerOffsetBytes {
            pointer: expression,
            ..
        }
        | C0Expression::Not(expression)
        | C0Expression::BitwiseNot(expression)
        | C0Expression::Load(expression) => contains_aggregate_value(expression),
        C0Expression::Conditional {
            condition,
            then_branch,
            else_branch,
        } => {
            contains_aggregate_value(condition)
                || contains_aggregate_value(then_branch)
                || contains_aggregate_value(else_branch)
        }
        C0Expression::LessThan(left, right)
        | C0Expression::LessEqual(left, right)
        | C0Expression::GreaterThan(left, right)
        | C0Expression::GreaterEqual(left, right)
        | C0Expression::Equal(left, right)
        | C0Expression::NotEqual(left, right)
        | C0Expression::And(left, right)
        | C0Expression::Or(left, right)
        | C0Expression::Add(left, right)
        | C0Expression::Subtract(left, right)
        | C0Expression::Multiply(left, right)
        | C0Expression::Divide(left, right)
        | C0Expression::Remainder(left, right)
        | C0Expression::ShiftLeft(left, right)
        | C0Expression::ShiftRight(left, right)
        | C0Expression::BitwiseAnd(left, right)
        | C0Expression::BitwiseOr(left, right)
        | C0Expression::BitwiseXor(left, right)
        | C0Expression::Index(left, right) => {
            contains_aggregate_value(left) || contains_aggregate_value(right)
        }
        C0Expression::Void
        | C0Expression::Variable(_)
        | C0Expression::FunctionAddress(_)
        | C0Expression::Int32Literal(_)
        | C0Expression::UInt8Literal(_)
        | C0Expression::UInt32Literal(_)
        | C0Expression::Int64Literal(_)
        | C0Expression::UInt64Literal(_)
        | C0Expression::Float32Literal(_)
        | C0Expression::Float64Literal(_)
        | C0Expression::SizeOfStruct { .. }
        | C0Expression::SizeOfUnion { .. }
        | C0Expression::SizeOfType { .. } => false,
    }
}

fn is_builtin_type_start(name: &str) -> bool {
    matches!(
        name,
        "void"
            | "struct"
            | "union"
            | "enum"
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
            | "int16_t"
            | "int64_t"
            | "uint16_t"
            | "uint64_t"
            | "float"
            | "double"
            | "volatile"
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

impl ErrorContext {
    fn error(&self, message: impl Into<String>) -> C0SyntaxError {
        match self.position {
            Some(position) => C0SyntaxError::at(position, message),
            None => C0SyntaxError::new(message),
        }
    }
}

struct Parser {
    tokens: Vec<Token>,
    positions: Vec<SourcePosition>,
    position: usize,
    structs: BTreeMap<String, C0StructLayout>,
    enums: BTreeMap<String, C0EnumDefinition>,
    enum_constants: BTreeMap<String, i32>,
    typedefs: BTreeMap<String, ParsedType>,
    variable_structs: BTreeMap<String, String>,
    variable_struct_values: BTreeMap<String, String>,
    variable_array_shapes: BTreeMap<String, Vec<u32>>,
    variable_types: BTreeMap<String, C0Type>,
    variable_function_pointers: BTreeMap<String, C0FunctionPointerSignature>,
    variable_constants: BTreeSet<String>,
    variable_pointee_constants: BTreeSet<String>,
    unions: BTreeMap<String, C0UnionLayout>,
    /// The names declared in each open lexical scope, innermost last. The
    /// source name is retained for lookup, while `kernel_name` is the
    /// identity emitted into the C0 AST. Click's kernel keys a local by its
    /// name alone, so a shadowing declaration receives a fresh internal name
    /// instead of silently overwriting the outer object. Sibling scopes may
    /// reuse a name because the earlier object is dead.
    scopes: Vec<Vec<ScopeBinding>>,
    next_scoped_name: u32,
    next_synthesized_call: u32,
    next_synthesized_aggregate: u32,
    next_string_literal: u32,
    loop_contexts: Vec<CLoopContext>,
    function_declarations: BTreeMap<String, C0FunctionHeader>,
    defined_functions: BTreeSet<String>,
    globals: BTreeMap<String, C0Global>,
    global_arrays: BTreeMap<String, C0GlobalArray>,
    global_aggregates: BTreeMap<String, C0GlobalAggregate>,
    global_aggregate_arrays: BTreeMap<String, C0GlobalAggregateArray>,
    static_locals: BTreeMap<String, C0StaticLocal>,
    static_arrays: BTreeMap<String, C0StaticArray>,
    static_aggregates: BTreeMap<String, C0StaticAggregate>,
    static_aggregate_arrays: BTreeMap<String, C0StaticAggregateArray>,
    string_literals: Vec<C0StringLiteral>,
    header_mode: bool,
    source_identity: Option<String>,
    abi: CAbi,
    current_return_struct_name: Option<String>,
    current_return_pointer_struct_name: Option<String>,
    current_return_type: C0Type,
}

#[derive(Clone, Debug)]
struct ScopeBinding {
    source_name: String,
    kernel_name: String,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct C0FunctionHeader {
    return_type: C0Type,
    return_struct_name: Option<String>,
    return_pointer_struct_name: Option<String>,
    /// The C spelling used to resolve declarations and calls in this
    /// translation unit.
    source_name: String,
    /// The kernel identity. Internal-linkage inline definitions are qualified
    /// by the including translation unit so separate TUs get separate
    /// instances of a shared header helper.
    name: String,
    parameters: Vec<C0Parameter>,
}

fn function_headers_compatible(left: &C0FunctionHeader, right: &C0FunctionHeader) -> bool {
    left.return_type == right.return_type
        && left.return_struct_name == right.return_struct_name
        && left.return_pointer_struct_name == right.return_pointer_struct_name
        && left.parameters.len() == right.parameters.len()
        && left
            .parameters
            .iter()
            .zip(&right.parameters)
            .all(|(left, right)| {
                left.c_type == right.c_type
                    && left.struct_name == right.struct_name
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
    fn new(source: &str, abi: CAbi) -> Result<Self, C0SyntaxError> {
        Self::new_with_source_identity(source, abi, None)
    }

    fn new_with_source_identity(
        source: &str,
        abi: CAbi,
        source_identity: Option<&str>,
    ) -> Result<Self, C0SyntaxError> {
        let (tokens, positions) = tokenize(source)?;
        Ok(Self {
            tokens,
            positions,
            position: 0,
            structs: BTreeMap::new(),
            enums: BTreeMap::new(),
            enum_constants: BTreeMap::new(),
            typedefs: BTreeMap::new(),
            variable_structs: BTreeMap::new(),
            variable_struct_values: BTreeMap::new(),
            variable_array_shapes: BTreeMap::new(),
            variable_types: BTreeMap::new(),
            variable_function_pointers: BTreeMap::new(),
            variable_constants: BTreeSet::new(),
            variable_pointee_constants: BTreeSet::new(),
            unions: BTreeMap::new(),
            scopes: Vec::new(),
            next_scoped_name: 0,
            next_synthesized_call: 0,
            next_synthesized_aggregate: 0,
            next_string_literal: 0,
            loop_contexts: Vec::new(),
            function_declarations: BTreeMap::new(),
            defined_functions: BTreeSet::new(),
            globals: BTreeMap::new(),
            global_arrays: BTreeMap::new(),
            global_aggregates: BTreeMap::new(),
            global_aggregate_arrays: BTreeMap::new(),
            static_locals: BTreeMap::new(),
            static_arrays: BTreeMap::new(),
            static_aggregates: BTreeMap::new(),
            static_aggregate_arrays: BTreeMap::new(),
            string_literals: Vec::new(),
            header_mode: false,
            source_identity: source_identity.map(str::to_string),
            abi,
            current_return_struct_name: None,
            current_return_pointer_struct_name: None,
            current_return_type: C0Type::Void,
        })
    }

    fn push_scope(&mut self) {
        self.scopes.push(Vec::new());
    }

    /// Closes the innermost scope; its names, and any struct layouts they
    /// carried, are no longer visible.
    fn pop_scope(&mut self) {
        for binding in self.scopes.pop().unwrap_or_default() {
            self.variable_structs.remove(&binding.kernel_name);
            self.variable_struct_values.remove(&binding.kernel_name);
            self.variable_array_shapes.remove(&binding.kernel_name);
            self.variable_types.remove(&binding.kernel_name);
            self.variable_function_pointers.remove(&binding.kernel_name);
            self.variable_constants.remove(&binding.kernel_name);
            self.variable_pointee_constants.remove(&binding.kernel_name);
        }
    }

    fn resolve_name(&self, source_name: &str) -> String {
        self.scopes
            .iter()
            .rev()
            .flat_map(|scope| scope.iter().rev())
            .find(|binding| binding.source_name == source_name)
            .map(|binding| binding.kernel_name.clone())
            .or_else(|| {
                self.globals
                    .get(source_name)
                    .map(|global| global.kernel_name().to_string())
            })
            .or_else(|| {
                self.global_arrays
                    .get(source_name)
                    .map(|global| global.kernel_name().to_string())
            })
            .or_else(|| {
                self.global_aggregates
                    .get(source_name)
                    .map(|global| global.kernel_name().to_string())
            })
            .or_else(|| {
                self.global_aggregate_arrays
                    .get(source_name)
                    .map(|global| global.kernel_name().to_string())
            })
            .unwrap_or_else(|| source_name.to_string())
    }

    fn variable_is_constant(&self, name: &str) -> bool {
        self.variable_constants.contains(name)
            || self.globals.get(name).is_some_and(C0Global::is_constant)
            || self
                .global_arrays
                .get(name)
                .is_some_and(C0GlobalArray::is_constant)
            || self
                .global_aggregates
                .get(name)
                .is_some_and(C0GlobalAggregate::is_constant)
            || self
                .global_aggregate_arrays
                .get(name)
                .is_some_and(C0GlobalAggregateArray::is_constant)
    }

    fn variable_pointee_is_constant(&self, name: &str) -> bool {
        self.variable_pointee_constants.contains(name)
    }

    fn expression_is_constant_lvalue(&self, expression: &C0Expression) -> bool {
        match expression {
            C0Expression::Variable(name) => self.variable_is_constant(name),
            C0Expression::Load(pointer) => self.expression_pointee_is_constant(pointer),
            C0Expression::Index(base, _) => self.expression_pointee_is_constant(base),
            C0Expression::Field { pointer, .. } | C0Expression::UnionField { pointer, .. } => {
                self.expression_is_constant_lvalue(pointer)
                    || self.expression_pointee_is_constant(pointer)
            }
            C0Expression::AggregateAddress { pointer, .. }
            | C0Expression::UnionAddress { pointer, .. } => {
                self.expression_is_constant_lvalue(pointer)
            }
            _ => false,
        }
    }

    fn expression_pointee_is_constant(&self, expression: &C0Expression) -> bool {
        match expression {
            C0Expression::Variable(name) => {
                self.variable_pointee_is_constant(name)
                    || (self.variable_is_constant(name)
                        && self.variable_types.get(name).is_some_and(|c_type| {
                            matches!(
                                c_type,
                                C0Type::Int16Array(_)
                                    | C0Type::UInt8Array(_)
                                    | C0Type::UInt16Array(_)
                                    | C0Type::UInt32Array(_)
                                    | C0Type::Int32Array(_)
                                    | C0Type::Int64Array(_)
                                    | C0Type::UInt64Array(_)
                                    | C0Type::Float32Array(_)
                                    | C0Type::Float64Array(_)
                            )
                        }))
            }
            C0Expression::AddressOf(target) => self.expression_is_constant_lvalue(target),
            C0Expression::PointerOffsetBytes { pointer, .. }
            | C0Expression::Subtract(pointer, _)
            | C0Expression::Add(pointer, _) => self.expression_pointee_is_constant(pointer),
            C0Expression::Cast { expression, .. } => {
                self.expression_pointee_is_constant(expression)
            }
            C0Expression::Conditional {
                then_branch,
                else_branch,
                ..
            } => {
                self.expression_pointee_is_constant(then_branch)
                    || self.expression_pointee_is_constant(else_branch)
            }
            _ => false,
        }
    }

    fn reject_constant_lvalue_write(&self, expression: &C0Expression) -> Result<(), C0SyntaxError> {
        if self.expression_is_constant_lvalue(expression) {
            Err(self.error_here("cannot modify a const-qualified lvalue"))
        } else {
            Ok(())
        }
    }

    fn reject_discarded_const_pointer(
        &self,
        declared_type: C0Type,
        declared_pointee_constant: bool,
        expression: &C0Expression,
    ) -> Result<(), C0SyntaxError> {
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

    fn file_static_kernel_name(&self, source_name: &str) -> String {
        format!(
            "{source_name}#file-static:{}",
            self.source_identity.as_deref().unwrap_or("source")
        )
    }

    fn inline_function_kernel_name(&self, source_name: &str) -> String {
        format!(
            "{source_name}#inline:{}",
            self.source_identity.as_deref().unwrap_or("source")
        )
    }

    fn resolve_function_name(&self, source_name: &str) -> String {
        self.function_declarations
            .get(source_name)
            .map(|function| function.name.clone())
            .unwrap_or_else(|| source_name.to_string())
    }

    fn function_declaration(&self, name: &str) -> Option<&C0FunctionHeader> {
        self.function_declarations.get(name).or_else(|| {
            self.function_declarations
                .values()
                .find(|function| function.name == name)
        })
    }

    /// Records a parameter or local declaration in the innermost scope. A
    /// shadowing declaration gets a kernel-only identity; source references
    /// continue to resolve by their ordinary C spelling. Call right after
    /// consuming the name token so a duplicate diagnostic points at it.
    fn declare_name(&mut self, name: &str) -> Result<String, C0SyntaxError> {
        if self.enum_constants.contains_key(name) {
            return Err(
                self.error_at_previous(format!("`{name}` is already declared as an enum constant"))
            );
        }
        if self
            .scopes
            .last()
            .is_some_and(|scope| scope.iter().any(|binding| binding.source_name == name))
        {
            return Err(
                self.error_at_previous(format!("`{name}` is already declared in this scope"))
            );
        }
        let kernel_name = if self
            .scopes
            .iter()
            .any(|scope| scope.iter().any(|binding| binding.source_name == name))
        {
            let kernel_name = format!("{name}#scope{}", self.next_scoped_name);
            self.next_scoped_name = self.next_scoped_name.saturating_add(1);
            kernel_name
        } else {
            name.to_string()
        };
        match self.scopes.last_mut() {
            Some(scope) => scope.push(ScopeBinding {
                source_name: name.to_string(),
                kernel_name: kernel_name.clone(),
            }),
            None => self.scopes.push(vec![ScopeBinding {
                source_name: name.to_string(),
                kernel_name: kernel_name.clone(),
            }]),
        }
        Ok(kernel_name)
    }

    /// Records a static local with an identity that remains unique even when
    /// two sibling blocks reuse the same C spelling. The source spelling is
    /// retained in the scope table so later expressions resolve normally.
    fn declare_static_name(&mut self, name: &str) -> Result<String, C0SyntaxError> {
        if self.enum_constants.contains_key(name) {
            return Err(
                self.error_at_previous(format!("`{name}` is already declared as an enum constant"))
            );
        }
        if self
            .scopes
            .last()
            .is_some_and(|scope| scope.iter().any(|binding| binding.source_name == name))
        {
            return Err(
                self.error_at_previous(format!("`{name}` is already declared in this scope"))
            );
        }
        let kernel_name = format!("{name}#static{}", self.next_scoped_name);
        self.next_scoped_name = self.next_scoped_name.saturating_add(1);
        match self.scopes.last_mut() {
            Some(scope) => scope.push(ScopeBinding {
                source_name: name.to_string(),
                kernel_name: kernel_name.clone(),
            }),
            None => self.scopes.push(vec![ScopeBinding {
                source_name: name.to_string(),
                kernel_name: kernel_name.clone(),
            }]),
        }
        Ok(kernel_name)
    }

    fn scalar_struct_value_layout(
        &self,
        struct_name: &str,
    ) -> Result<C0StructLayout, C0SyntaxError> {
        let layout = self.structs.get(struct_name).cloned().ok_or_else(|| {
            self.error_here(format!("unknown struct declaration `{struct_name}`"))
        })?;
        for field in layout.fields.values() {
            if let Some(nested_name) = field.struct_name.as_deref()
                && field.array_element_width.is_some()
                && field.array_shape.is_some()
            {
                self.scalar_struct_value_layout(nested_name)?;
                continue;
            }
            if field.c_type == C0Type::Int32
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
                || (field.struct_name.is_some() && !field.c_type.is_pointer())
                || !matches!(
                    field.c_type,
                    C0Type::Int16
                        | C0Type::Int32
                        | C0Type::UInt8
                        | C0Type::UInt16
                        | C0Type::UInt32
                        | C0Type::Int64
                        | C0Type::UInt64
                        | C0Type::Float32
                        | C0Type::Float64
                        | C0Type::Int32Array(_)
                        | C0Type::UInt8Array(_)
                        | C0Type::Float32Array(_)
                        | C0Type::Float64Array(_)
                        | C0Type::Int32Pointer
                        | C0Type::UInt8Pointer
                        | C0Type::Float32Pointer
                        | C0Type::Float64Pointer
                        | C0Type::Int32PointerPointer
                        | C0Type::UInt8PointerPointer
                        | C0Type::Float32PointerPointer
                        | C0Type::Float64PointerPointer
                )
            {
                return Err(self.error_here(format!(
                    "struct-by-value currently supports int16, int32, uint8, uint16, uint32, int64, uint64, named enum fields, fixed scalar arrays, fixed-dimensional embedded-struct arrays, data-pointer fields, and embedded struct fields; `struct {struct_name}` contains a function pointer, an unsupported field shape, or a union field"
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
            .copied()
    }

    /// An error at the next unconsumed token.
    fn error_here(&self, message: impl Into<String>) -> C0SyntaxError {
        match self.here() {
            Some(position) => C0SyntaxError::at(position, message),
            None => C0SyntaxError::new(message),
        }
    }

    /// An error at the most recently consumed token; use after `next()` has
    /// already advanced past the offending token.
    fn error_at_previous(&self, message: impl Into<String>) -> C0SyntaxError {
        let index = self.position.saturating_sub(1);
        match self.positions.get(index).or_else(|| self.positions.last()) {
            Some(position) => C0SyntaxError::at(*position, message),
            None => C0SyntaxError::new(message),
        }
    }

    /// Uses a captured expression position when a lowering error is reported
    /// after parsing has advanced past the original source token.
    fn error_at_position(
        &self,
        position: Option<SourcePosition>,
        message: impl Into<String>,
    ) -> C0SyntaxError {
        match position {
            Some(position) => C0SyntaxError::at(position, message),
            None => self.error_here(message),
        }
    }

    fn parse_function(mut self) -> Result<C0Function, C0SyntaxError> {
        self.parse_declarations()?;
        let function = self.parse_function_definition(false)?;
        self.parse_declarations()?;
        self.expect_end(function.name())?;
        Ok(function)
    }

    fn parse_functions(mut self) -> Result<Vec<C0Function>, C0SyntaxError> {
        self.parse_declarations()?;
        let mut functions = Vec::new();
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
            let has_always_inline_attribute = self.consume_always_inline_attribute()?;
            if is_inline && !is_static {
                return Err(self.error_here(
                    "inline function definitions require `static inline` or `static __always_inline` in this slice",
                ));
            }
            if is_static && !is_inline {
                return Err(self.error_here(
                    "file-scope static functions require `static inline` or `static __always_inline` in this slice",
                ));
            }
            if has_always_inline_attribute && !is_static {
                return Err(self.error_here(
                    "the GNU always-inline attribute requires `static inline` or `static __always_inline`",
                ));
            }
            if !self.is_type_start() {
                return Err(self.error_here(format!(
                    "expected function declaration, got {}",
                    self.peek()
                        .map(Token::describe)
                        .unwrap_or_else(|| "end of input".to_string())
                )));
            }
            let header = self.parse_function_header(is_static && is_inline)?;
            let has_trailing_always_inline_attribute = self.consume_always_inline_attribute()?;
            if (has_always_inline_attribute || has_trailing_always_inline_attribute) && !is_static {
                return Err(self.error_here(
                    "the GNU always-inline attribute requires `static inline` or `static __always_inline`",
                ));
            }
            if self.peek() == Some(&Token::LBrace) {
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
        if functions.is_empty() {
            return Err(C0SyntaxError::new(
                "C source must define at least one function",
            ));
        }
        Ok(functions)
    }

    fn parse_header(mut self) -> Result<(), C0SyntaxError> {
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
            let has_always_inline_attribute = self.consume_always_inline_attribute()?;
            if is_inline && !is_static {
                return Err(self.error_here(
                    "inline function definitions in headers require `static inline` or `static __always_inline`",
                ));
            }
            if has_always_inline_attribute && !is_static {
                return Err(self.error_here(
                    "the GNU always-inline attribute requires `static inline` or `static __always_inline`",
                ));
            }
            if !self.is_type_start() {
                return Err(self.error_here(format!(
                    "expected a header declaration, got {}",
                    self.peek()
                        .map(Token::describe)
                        .unwrap_or_else(|| "end of input".to_string())
                )));
            }
            let header = self.parse_function_header(is_static && is_inline)?;
            let has_trailing_always_inline_attribute = self.consume_always_inline_attribute()?;
            if (has_always_inline_attribute || has_trailing_always_inline_attribute) && !is_static {
                return Err(self.error_here(
                    "the GNU always-inline attribute requires `static inline` or `static __always_inline`",
                ));
            }
            if self.peek() == Some(&Token::LBrace) {
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
    ) -> Result<C0Function, C0SyntaxError> {
        let header = self.parse_function_header(internal_linkage)?;
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
        header: C0FunctionHeader,
    ) -> Result<C0Function, C0SyntaxError> {
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
        let body_result = self.parse_block_statement();
        self.current_return_struct_name = previous_return_struct_name;
        self.current_return_pointer_struct_name = previous_return_pointer_struct_name;
        self.current_return_type = previous_return_type;
        let mut body = body_result?;
        self.pop_scope();
        validate_function_returns(&body, header.return_type)?;
        if header.return_type == C0Type::Void {
            body = C0Statement::Seq(
                Box::new(body),
                Box::new(C0Statement::Return(C0Expression::Void)),
            );
        }

        let static_locals = std::mem::take(&mut self.static_locals);
        let string_literals = std::mem::take(&mut self.string_literals);
        let inline_body = header.name != header.source_name;
        Ok(C0Function {
            return_type: header.return_type,
            return_struct_name: header.return_struct_name,
            return_pointer_struct_name: header.return_pointer_struct_name,
            name: header.name,
            inline_body,
            parameters: header.parameters,
            body,
            structs: self.structs.clone(),
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
            string_literals,
        })
    }

    fn parse_function_header(
        &mut self,
        internal_linkage: bool,
    ) -> Result<C0FunctionHeader, C0SyntaxError> {
        let parsed_return_type = self.parse_type()?;
        if parsed_return_type.is_constant || parsed_return_type.pointee_constant {
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
        if parsed_return_type.enum_name.is_some() {
            return Err(self.error_here(
                "enum return types are not supported; use enum values in struct fields",
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
            .filter(|_| parsed_return_type.c_type.is_pointer())
            .cloned();
        if let Some(struct_name) = &return_pointer_struct_name
            && !self.structs.contains_key(struct_name)
        {
            return Err(self.error_here(format!("unknown struct declaration `{struct_name}`")));
        }
        let return_type = if let Some(name) = &return_struct_name {
            struct_value_type(
                self.structs
                    .get(name)
                    .expect("validated struct return has a layout"),
            )
        } else {
            parsed_return_type.c_type
        };
        if self.peek() == Some(&Token::LParen) {
            return Err(self.error_here("function-pointer declarations are not supported in C0"));
        }
        let source_name = self.expect_ident("function name")?;
        self.expect(Token::LParen)?;
        self.push_scope();
        let parameters = self.parse_parameters()?;
        self.expect(Token::RParen)?;
        let name = if internal_linkage {
            self.inline_function_kernel_name(&source_name)
        } else {
            source_name.clone()
        };
        Ok(C0FunctionHeader {
            return_type,
            return_struct_name,
            return_pointer_struct_name,
            source_name,
            name,
            parameters,
        })
    }

    fn consume_always_inline_attribute(&mut self) -> Result<bool, C0SyntaxError> {
        if self.peek_ident() != Some("__attribute__") {
            return Ok(false);
        }
        self.position += 1;
        self.expect(Token::LParen)?;
        self.expect(Token::LParen)?;
        let attribute = self.expect_ident("GNU function attribute")?;
        if attribute != "always_inline" && attribute != "__always_inline__" {
            return Err(self.error_at_previous(format!(
                "unsupported GNU function attribute `{attribute}`; only `always_inline` is supported in this slice"
            )));
        }
        self.expect(Token::RParen)?;
        self.expect(Token::RParen)?;
        Ok(true)
    }

    /// Consume the one layout-affecting GNU attribute needed by the imported
    /// rbtree headers. This deliberately accepts only the exact constant
    /// spelling used by those headers; silently dropping another attribute
    /// would make the imported ABI unsound.
    fn consume_struct_alignment_attribute(&mut self) -> Result<Option<u32>, C0SyntaxError> {
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

    fn register_function_declaration(
        &mut self,
        header: &C0FunctionHeader,
        definition: bool,
    ) -> Result<(), C0SyntaxError> {
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
                return Err(self.error_here(format!(
                    "conflicting declarations for function `{}`",
                    header.source_name
                )));
            }
        } else {
            self.function_declarations
                .insert(header.source_name.clone(), header.clone());
        }
        if definition && !self.defined_functions.insert(header.source_name.clone()) {
            return Err(self.error_here(format!(
                "duplicate function definition `{}`",
                header.source_name
            )));
        }
        Ok(())
    }

    fn parse_declarations(&mut self) -> Result<(), C0SyntaxError> {
        while self.peek().is_some() {
            if self.peek_ident() == Some("static")
                && self.peek_n(1).is_some_and(Self::is_inline_specifier)
            {
                break;
            } else if self.peek_inline_specifier() {
                break;
            } else if self.peek_ident() == Some("static") {
                self.parse_global_declaration()?;
            } else if self.peek_ident() == Some("typedef") {
                self.parse_typedef_declaration()?;
            } else if self.peek_ident() == Some("struct") && self.peek_n(2) == Some(&Token::LBrace)
            {
                self.parse_struct_declaration()?;
            } else if self.peek_ident() == Some("enum") && self.peek_n(2) == Some(&Token::LBrace) {
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

    fn global_declaration_ahead(&mut self) -> Result<bool, C0SyntaxError> {
        let saved_position = self.position;
        if self.peek_ident() == Some("extern") {
            self.position += 1;
        }
        if !self.is_type_start() {
            self.position = saved_position;
            return Ok(false);
        }
        self.parse_type()?;
        let is_global =
            matches!(self.peek(), Some(Token::Ident(_))) && self.peek_n(1) != Some(&Token::LParen);
        self.position = saved_position;
        Ok(is_global)
    }

    fn parse_global_declaration(&mut self) -> Result<(), C0SyntaxError> {
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
        let struct_pointer_name = parsed_type
            .struct_name
            .as_ref()
            .filter(|_| parsed_type.c_type.is_pointer())
            .cloned();
        if let Some(struct_name) = &struct_pointer_name
            && !self.structs.contains_key(struct_name)
        {
            return Err(self.error_here(format!("unknown struct declaration `{struct_name}`")));
        }
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
            if (parsed_type.struct_name.is_some() && struct_pointer_name.is_none())
                || parsed_type.enum_name.is_some()
                || parsed_type.union_name.is_some()
                || (struct_pointer_name.is_none()
                    && !matches!(
                        parsed_type.c_type,
                        C0Type::Int16
                            | C0Type::Int32
                            | C0Type::UInt8
                            | C0Type::UInt16
                            | C0Type::UInt32
                            | C0Type::Float32
                            | C0Type::Float64
                    ))
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
            let name = self.expect_ident("global name")?;
            let kernel_name = if is_file_static {
                self.file_static_kernel_name(&name)
            } else {
                name.clone()
            };
            if let Some((struct_name, layout)) = &aggregate_struct {
                if self.peek() == Some(&Token::LBracket) {
                    let length = self
                        .parse_global_array_length(&name)?
                        .expect("aggregate array has an array suffix");
                    let initializer = if self.peek() == Some(&Token::Equal) {
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
                    let declaration = initializer
                        .map(|initializer| {
                            C0GlobalAggregateArray::definition(
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
                            C0GlobalAggregateArray::declaration(
                                name.clone(),
                                kernel_name.clone(),
                                struct_name.clone(),
                                layout.clone(),
                                length,
                                is_file_static,
                            )
                        })
                        .with_constant(parsed_type.is_constant);
                    self.register_global_aggregate_array_declaration(name.clone(), declaration)?;
                    let bytes = length
                        .checked_mul(layout.size_bytes())
                        .expect("validated aggregate global array size");
                    self.variable_types
                        .insert(kernel_name.clone(), C0Type::UInt8Array(bytes));
                    self.variable_array_shapes
                        .insert(kernel_name.clone(), vec![length]);
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
                let initializer = if self.peek() == Some(&Token::Equal) {
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
                let declaration = if let Some(initializer) = initializer {
                    C0GlobalAggregate::definition(
                        name.clone(),
                        kernel_name.clone(),
                        struct_name.clone(),
                        layout.clone(),
                        initializer,
                        is_file_static,
                    )
                } else {
                    C0GlobalAggregate::declaration(
                        name.clone(),
                        kernel_name.clone(),
                        struct_name.clone(),
                        layout.clone(),
                        is_file_static,
                    )
                }
                .with_constant(parsed_type.is_constant);
                self.register_global_aggregate_declaration(name.clone(), declaration)?;
                self.variable_types
                    .insert(name.clone(), struct_value_type(layout));
                self.variable_structs
                    .insert(name.clone(), struct_name.clone());
                if parsed_type.is_constant {
                    self.variable_constants.insert(name.clone());
                }
                if kernel_name != name {
                    self.variable_types
                        .insert(kernel_name.clone(), struct_value_type(layout));
                    self.variable_structs
                        .insert(kernel_name, struct_name.clone());
                }
                if self.peek() == Some(&Token::Comma) {
                    self.position += 1;
                    continue;
                }
                break;
            }
            let array_length = self.parse_global_array_length(&name)?;
            if struct_pointer_name.is_some() && array_length.is_some() {
                return Err(
                    self.error_here("file-scope arrays of struct pointers are not supported yet")
                );
            }
            if parsed_type.is_volatile && array_length.is_some() {
                return Err(self.error_here(
                    "the small volatile model supports only direct scalar integer objects",
                ));
            }
            if let Some(length) = array_length {
                let initializer = if self.peek() == Some(&Token::Equal) {
                    if is_extern {
                        return Err(self.error_here(
                            "`extern` global array declarations may not have an initializer",
                        ));
                    }
                    self.position += 1;
                    Some(self.parse_global_array_initializer(&name, parsed_type.c_type, length)?)
                } else if is_extern {
                    None
                } else {
                    Some(vec![zero_initializer(parsed_type.c_type); length as usize])
                };
                self.register_global_array_declaration(
                    name.clone(),
                    parsed_type.c_type,
                    length,
                    initializer
                        .map(|initializer| {
                            C0GlobalArray::definition(
                                name.clone(),
                                kernel_name.clone(),
                                parsed_type.c_type,
                                length,
                                initializer,
                                is_file_static,
                            )
                            .with_constant(parsed_type.is_constant)
                        })
                        .unwrap_or_else(|| {
                            C0GlobalArray::declaration(
                                name.clone(),
                                kernel_name.clone(),
                                parsed_type.c_type,
                                length,
                                is_file_static,
                            )
                            .with_constant(parsed_type.is_constant)
                        }),
                )?;
                self.variable_types.insert(
                    kernel_name,
                    array_type_for_element(parsed_type.c_type, length)
                        .expect("validated global array element type"),
                );
            } else {
                let initializer = if self.peek() == Some(&Token::Equal) {
                    if is_extern {
                        return Err(self.error_here(
                            "`extern` global declarations may not have an initializer",
                        ));
                    }
                    self.position += 1;
                    let initializer = self.parse_expression()?;
                    validate_global_initializer(self, parsed_type.c_type, &initializer)?;
                    Some(initializer)
                } else if is_extern {
                    None
                } else {
                    Some(zero_initializer(parsed_type.c_type))
                };
                self.register_global_declaration(
                    name.clone(),
                    parsed_type.c_type,
                    initializer
                        .map(|initializer| {
                            if is_file_static {
                                C0Global::file_static_definition(
                                    name.clone(),
                                    kernel_name.clone(),
                                    parsed_type.c_type,
                                    struct_pointer_name.clone(),
                                    initializer,
                                )
                                .with_volatile(parsed_type.is_volatile)
                                .with_constant(parsed_type.is_constant)
                            } else {
                                C0Global::definition(
                                    name.clone(),
                                    parsed_type.c_type,
                                    struct_pointer_name.clone(),
                                    initializer,
                                )
                                .with_volatile(parsed_type.is_volatile)
                                .with_constant(parsed_type.is_constant)
                            }
                        })
                        .unwrap_or_else(|| {
                            C0Global::declaration(
                                name.clone(),
                                parsed_type.c_type,
                                struct_pointer_name.clone(),
                            )
                            .with_volatile(parsed_type.is_volatile)
                            .with_constant(parsed_type.is_constant)
                        }),
                )?;
                self.variable_types
                    .insert(kernel_name.clone(), parsed_type.c_type);
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

    fn parse_global_array_length(&mut self, name: &str) -> Result<Option<u32>, C0SyntaxError> {
        if self.peek() != Some(&Token::LBracket) {
            return Ok(None);
        }
        self.position += 1;
        let length = match self.next() {
            Some(Token::Number(number)) => {
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
                return Err(
                    self.error_here("expected positive file-scope array length, got end of input")
                );
            }
        };
        if length == 0 {
            return Err(self.error_at_previous(format!(
                "file-scope array `{name}` must have positive length"
            )));
        }
        self.expect(Token::RBracket)?;
        if self.peek() == Some(&Token::LBracket) {
            return Err(self.error_here("multidimensional file-scope arrays are not supported yet"));
        }
        Ok(Some(length))
    }

    fn parse_global_array_initializer(
        &mut self,
        name: &str,
        element_type: C0Type,
        length: u32,
    ) -> Result<Vec<C0Expression>, C0SyntaxError> {
        self.expect(Token::LBrace)?;
        let mut values = Vec::new();
        if self.peek() != Some(&Token::RBrace) {
            loop {
                if values.len() == length as usize {
                    return Err(self.error_here(format!(
                        "too many initializers for file-scope array `{name}[{length}]`"
                    )));
                }
                let value = self.parse_expression()?;
                validate_global_initializer(self, element_type, &value)?;
                values.push(value);
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
                            "expected `,` or `}}` in file-scope array `{name}` initializer, got {}",
                            token.describe()
                        )));
                    }
                    None => {
                        return Err(self.error_here(format!(
                            "expected `,` or `}}` in file-scope array `{name}` initializer, got end of input"
                        )));
                    }
                }
            }
        }
        self.expect(Token::RBrace)?;
        values.resize(length as usize, zero_initializer(element_type));
        Ok(values)
    }

    fn register_global_declaration(
        &mut self,
        name: String,
        c_type: C0Type,
        declaration: C0Global,
    ) -> Result<(), C0SyntaxError> {
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
            if previous.c_type != c_type || previous.struct_name != declaration.struct_name {
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
            if previous.is_file_static() != declaration.is_file_static() {
                return Err(self.error_here(format!(
                    "conflicting linkage declarations for global `{name}`"
                )));
            }
            if previous.is_defined() && declaration.is_defined() {
                return Err(self.error_here(format!("duplicate definition of global `{name}`")));
            }
        }
        let merged = match (self.globals.get(&name), declaration.is_defined()) {
            (Some(previous), true) if !previous.is_defined() => declaration,
            (Some(previous), false) => previous.clone(),
            _ => declaration,
        };
        self.globals.insert(name, merged);
        Ok(())
    }

    fn register_global_array_declaration(
        &mut self,
        name: String,
        element_type: C0Type,
        length: u32,
        declaration: C0GlobalArray,
    ) -> Result<(), C0SyntaxError> {
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
            if previous.element_type != element_type || previous.length != length {
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
            if previous.is_defined() && declaration.is_defined() {
                return Err(
                    self.error_here(format!("duplicate definition of global array `{name}`"))
                );
            }
        }
        let merged = match (self.global_arrays.get(&name), declaration.is_defined()) {
            (Some(previous), true) if !previous.is_defined() => declaration,
            (Some(previous), false) => previous.clone(),
            _ => declaration,
        };
        self.global_arrays.insert(name, merged);
        Ok(())
    }

    fn register_global_aggregate_declaration(
        &mut self,
        name: String,
        declaration: C0GlobalAggregate,
    ) -> Result<(), C0SyntaxError> {
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
            if previous.is_defined() && declaration.is_defined() {
                return Err(
                    self.error_here(format!("duplicate definition of aggregate global `{name}`"))
                );
            }
        }
        let merged = match (self.global_aggregates.get(&name), declaration.is_defined()) {
            (Some(previous), true) if !previous.is_defined() => declaration,
            (Some(previous), false) => previous.clone(),
            _ => declaration,
        };
        self.global_aggregates.insert(name, merged);
        Ok(())
    }

    fn register_global_aggregate_array_declaration(
        &mut self,
        name: String,
        declaration: C0GlobalAggregateArray,
    ) -> Result<(), C0SyntaxError> {
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
                || previous.length() != declaration.length()
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
            if previous.is_defined() && declaration.is_defined() {
                return Err(self.error_here(format!(
                    "duplicate definition of aggregate global array `{name}`"
                )));
            }
        }
        let merged = match (
            self.global_aggregate_arrays.get(&name),
            declaration.is_defined(),
        ) {
            (Some(previous), true) if !previous.is_defined() => declaration,
            (Some(previous), false) => previous.clone(),
            _ => declaration,
        };
        self.global_aggregate_arrays.insert(name, merged);
        Ok(())
    }

    fn parse_typedef_declaration(&mut self) -> Result<(), C0SyntaxError> {
        self.expect_ident_spelling("typedef")?;
        let parsed_type = self.parse_type()?;
        let alias = self.expect_ident("typedef name")?;
        self.expect(Token::Semicolon)?;
        if self.typedefs.insert(alias.clone(), parsed_type).is_some() {
            return Err(self.error_at_previous(format!("duplicate typedef `{alias}`")));
        }
        Ok(())
    }

    fn parse_enum_declaration(&mut self) -> Result<(), C0SyntaxError> {
        self.expect_ident_spelling("enum")?;
        let name = self.expect_ident("enum name")?;
        if self.enums.contains_key(&name) {
            return Err(self.error_at_previous(format!("duplicate enum declaration `{name}`")));
        }
        self.expect(Token::LBrace)?;
        if self.peek() == Some(&Token::RBrace) {
            return Err(self.error_here("enum declarations must contain at least one enumerator"));
        }

        let mut values = BTreeMap::new();
        let mut next_value = 0i64;
        loop {
            let enumerator = self.expect_ident("enumerator name")?;
            if self.enum_constants.contains_key(&enumerator) {
                return Err(self.error_at_previous(format!("duplicate enumerator `{enumerator}`")));
            }
            let value = if self.peek() == Some(&Token::Equal) {
                self.position += 1;
                self.parse_enum_value(&name)?
            } else {
                i32::try_from(next_value).map_err(|_| {
                    self.error_here(format!("enum `{name}` value is outside the int32 range"))
                })?
            };
            values.insert(enumerator.clone(), value);
            self.enum_constants.insert(enumerator, value);
            next_value = i64::from(value)
                .checked_add(1)
                .ok_or_else(|| self.error_here(format!("enum `{name}` value is too large")))?;

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
                        "expected `,` or `}}` in enum `{name}`, got {}",
                        token.describe()
                    )));
                }
                None => {
                    return Err(self.error_here(format!(
                        "expected `,` or `}}` in enum `{name}`, got end of input"
                    )));
                }
            }
        }

        self.expect(Token::RBrace)?;
        self.expect(Token::Semicolon)?;
        self.enums.insert(name, C0EnumDefinition { values });
        Ok(())
    }

    fn parse_enum_value(&mut self, enum_name: &str) -> Result<i32, C0SyntaxError> {
        let negative = if self.peek() == Some(&Token::Minus) {
            self.position += 1;
            true
        } else {
            false
        };
        let Some(Token::Number(number)) = self.next() else {
            return Err(
                self.error_here(format!("enum `{enum_name}` values must be int32 literals"))
            );
        };
        let magnitude = parse_integer_literal_magnitude(&number).map_err(|reason| {
            self.error_at_previous(format!("invalid enum value `{number}`: {reason}"))
        })?;
        let signed = if negative {
            -(i64::try_from(magnitude).map_err(|_| {
                self.error_at_previous(format!("enum value `-{number}` is outside the int32 range"))
            })?)
        } else {
            i64::try_from(magnitude).map_err(|_| {
                self.error_at_previous(format!("enum value `{number}` is outside the int32 range"))
            })?
        };
        i32::try_from(signed).map_err(|_| {
            self.error_at_previous(format!("enum value `{number}` is outside the int32 range"))
        })
    }

    fn parse_union_declaration(&mut self) -> Result<(), C0SyntaxError> {
        self.expect_ident_spelling("union")?;
        let name = self.expect_ident("union name")?;
        if self.unions.contains_key(&name) {
            return Err(self.error_at_previous(format!("duplicate union declaration `{name}`")));
        }
        self.expect(Token::LBrace)?;

        let mut fields = BTreeMap::new();
        let mut union_size = 0u32;
        let mut union_alignment = 1u32;
        while self.peek() != Some(&Token::RBrace) {
            if self.peek().is_none() {
                return Err(self.error_here("expected union field or `}`, got end of input"));
            }
            let field_type = self.parse_type()?;
            loop {
                let field_name = self.expect_ident("union field name")?;
                let (c_type, field_size, field_alignment) =
                    self.parse_union_field_declarator(&field_type, &name)?;
                if fields
                    .insert(
                        field_name.clone(),
                        C0UnionField {
                            c_type,
                            enum_name: (c_type == field_type.c_type)
                                .then(|| field_type.enum_name.clone())
                                .flatten(),
                            offset_bytes: 0,
                            byte_width: field_size,
                        },
                    )
                    .is_some()
                {
                    return Err(self
                        .error_here(format!("duplicate field `{field_name}` in union `{name}`")));
                }
                union_size = union_size.max(field_size);
                union_alignment = union_alignment.max(field_alignment);
                if self.peek() != Some(&Token::Comma) {
                    break;
                }
                self.position += 1;
            }
            self.expect(Token::Semicolon)?;
        }

        self.expect(Token::RBrace)?;
        self.expect(Token::Semicolon)?;
        if fields.is_empty() {
            return Err(self.error_here("union declarations must contain at least one field"));
        }
        let size_bytes = align_up(union_size, union_alignment)
            .ok_or_else(|| self.error_here(format!("union `{name}` layout is too large")))?;
        self.unions.insert(
            name,
            C0UnionLayout {
                fields,
                size_bytes,
                alignment_bytes: union_alignment,
            },
        );
        Ok(())
    }

    fn parse_union_field_declarator(
        &mut self,
        base_type: &ParsedType,
        union_name: &str,
    ) -> Result<(C0Type, u32, u32), C0SyntaxError> {
        if base_type.is_volatile {
            return Err(self.error_here(
                "the small volatile model does not support volatile struct or union fields",
            ));
        }
        if base_type.is_constant || base_type.pointee_constant {
            return Err(self.error_here(
                "const-qualified struct or union fields are not supported in this slice",
            ));
        }
        if base_type.struct_name.is_some() || base_type.union_name.is_some() {
            return Err(self.error_here(format!(
                "union `{union_name}` fields may not contain embedded structs or unions"
            )));
        }
        if base_type.enum_name.is_some() {
            if base_type.c_type != C0Type::Int32 || self.peek() == Some(&Token::LBracket) {
                return Err(self.error_here(format!(
                    "union `{union_name}` enum members must be scalar int32 values"
                )));
            }
        }
        if self.peek() == Some(&Token::LBracket) {
            return Err(self.error_here(format!("union `{union_name}` members may not be arrays")));
        }
        let c_type = base_type.c_type;
        if !matches!(
            c_type,
            C0Type::Int32
                | C0Type::UInt8
                | C0Type::Int32Pointer
                | C0Type::UInt8Pointer
                | C0Type::Int32PointerPointer
                | C0Type::UInt8PointerPointer
        ) {
            return Err(self.error_here(format!(
                "union `{union_name}` members currently support int32, uint8, and pointer fields"
            )));
        }
        let (field_size, field_alignment) = self.abi.size_and_alignment(c_type);
        Ok((c_type, field_size, field_alignment))
    }

    fn parse_struct_declaration(&mut self) -> Result<(), C0SyntaxError> {
        self.expect_ident_spelling("struct")?;
        let name = self.expect_ident("struct name")?;
        self.expect(Token::LBrace)?;

        let mut fields = BTreeMap::new();
        let mut offset_bytes = 0u32;
        let mut struct_alignment = 1u32;
        while self.peek() != Some(&Token::RBrace) {
            if self.peek().is_none() {
                return Err(self.error_here("expected struct field or `}`, got end of input"));
            }
            let field_type = self.parse_type()?;
            if let Some((field_name, c_type, function_pointer_signature)) =
                self.parse_function_pointer_declarator(field_type.clone())?
            {
                let (field_size, field_alignment) = self.abi.size_and_alignment(c_type);
                offset_bytes = align_up(offset_bytes, field_alignment).ok_or_else(|| {
                    self.error_here(format!("struct `{name}` layout is too large"))
                })?;
                if fields
                    .insert(
                        field_name.clone(),
                        C0StructField {
                            c_type,
                            struct_name: None,
                            enum_name: None,
                            union_name: None,
                            function_pointer_signature: Some(function_pointer_signature),
                            array_element_width: None,
                            array_shape: None,
                            offset_bytes,
                            byte_width: field_size,
                        },
                    )
                    .is_some()
                {
                    return Err(self
                        .error_here(format!("duplicate field `{field_name}` in struct `{name}`")));
                }
                offset_bytes = offset_bytes.checked_add(field_size).ok_or_else(|| {
                    self.error_here(format!("struct `{name}` layout is too large"))
                })?;
                struct_alignment = struct_alignment.max(field_alignment);
                self.expect(Token::Semicolon)?;
                continue;
            }
            loop {
                let field_name = self.expect_ident("struct field name")?;
                let (
                    c_type,
                    field_size,
                    field_alignment,
                    field_struct_name,
                    array_element_width,
                    array_shape,
                ) = self.parse_struct_field_declarator(&field_type, &name)?;
                offset_bytes = align_up(offset_bytes, field_alignment).ok_or_else(|| {
                    self.error_here(format!("struct `{name}` layout is too large"))
                })?;
                if fields
                    .insert(
                        field_name.clone(),
                        C0StructField {
                            c_type,
                            struct_name: field_struct_name,
                            enum_name: (c_type == field_type.c_type)
                                .then(|| field_type.enum_name.clone())
                                .flatten(),
                            union_name: (c_type == field_type.c_type)
                                .then(|| field_type.union_name.clone())
                                .flatten(),
                            function_pointer_signature: None,
                            array_element_width,
                            array_shape,
                            offset_bytes,
                            byte_width: field_size,
                        },
                    )
                    .is_some()
                {
                    return Err(self
                        .error_here(format!("duplicate field `{field_name}` in struct `{name}`")));
                }
                offset_bytes = offset_bytes.checked_add(field_size).ok_or_else(|| {
                    self.error_here(format!("struct `{name}` layout is too large"))
                })?;
                struct_alignment = struct_alignment.max(field_alignment);
                if self.peek() != Some(&Token::Comma) {
                    break;
                }
                self.position += 1;
            }
            self.expect(Token::Semicolon)?;
        }

        self.expect(Token::RBrace)?;
        if let Some(attribute_alignment) = self.consume_struct_alignment_attribute()? {
            struct_alignment = struct_alignment.max(attribute_alignment);
        }
        self.expect(Token::Semicolon)?;

        if fields.is_empty() {
            return Err(self.error_here("struct declarations must contain at least one field"));
        }
        let size_bytes = align_up(offset_bytes, struct_alignment)
            .ok_or_else(|| self.error_here(format!("struct `{name}` layout is too large")))?;
        let aggregate_fields = flatten_aggregate_fields(&fields, &self.structs);
        if self
            .structs
            .insert(
                name.clone(),
                C0StructLayout {
                    fields,
                    aggregate_fields,
                    size_bytes,
                    alignment_bytes: struct_alignment,
                },
            )
            .is_some()
        {
            return Err(self.error_here(format!("duplicate struct declaration `{name}`")));
        }

        Ok(())
    }

    fn parse_struct_field_declarator(
        &mut self,
        base_type: &ParsedType,
        struct_name: &str,
    ) -> Result<
        (
            C0Type,
            u32,
            u32,
            Option<String>,
            Option<u32>,
            Option<Vec<u32>>,
        ),
        C0SyntaxError,
    > {
        if base_type.is_volatile {
            return Err(self.error_here(
                "the small volatile model does not support volatile struct or union fields",
            ));
        }
        if base_type.is_constant || base_type.pointee_constant {
            return Err(self.error_here(
                "const-qualified struct or union fields are not supported in this slice",
            ));
        }
        if let Some(enum_name) = base_type.enum_name.as_deref() {
            if !self.enums.contains_key(enum_name) {
                return Err(self.error_here(format!("unknown enum declaration `{enum_name}`")));
            }
            if base_type.c_type != C0Type::Int32 {
                return Err(self.error_here("pointers to enum values are not supported"));
            }
            if self.peek() == Some(&Token::LBracket) {
                return Err(self.error_here("arrays of enum fields are not supported"));
            }
            return Ok((C0Type::Int32, 4, 4, None, None, None));
        }
        if let Some(union_name) = base_type.union_name.as_deref() {
            let union_layout = self.unions.get(union_name).ok_or_else(|| {
                self.error_here(format!("unknown embedded union declaration `{union_name}`"))
            })?;
            if self.peek() == Some(&Token::LBracket) {
                return Err(
                    self.error_here("arrays of embedded unions are not supported in struct fields")
                );
            }
            return Ok((
                base_type.c_type,
                union_layout.size_bytes(),
                union_layout.alignment_bytes(),
                None,
                None,
                None,
            ));
        }
        if is_plain_struct_type(base_type) {
            let nested_name = base_type
                .struct_name
                .as_deref()
                .expect("plain struct type carries its name");
            let nested_layout = self.structs.get(nested_name).cloned().ok_or_else(|| {
                self.error_here(format!(
                    "unknown embedded struct declaration `{nested_name}`"
                ))
            })?;
            if self.peek() == Some(&Token::LBracket) {
                let mut dimensions = Vec::new();
                while self.peek() == Some(&Token::LBracket) {
                    self.position += 1;
                    let length = match self.next() {
                        Some(Token::Number(number)) => {
                            let length =
                                parse_integer_literal_magnitude(&number).map_err(|reason| {
                                    self.error_here(format!(
                                        "invalid embedded struct array length `{number}`: {reason}"
                                    ))
                                })?;
                            let length = u32::try_from(length).map_err(|_| {
                                self.error_here(format!(
                                    "embedded struct array length `{number}` is out of range"
                                ))
                            })?;
                            if length == 0 {
                                return Err(self.error_here(
                                    "embedded struct arrays must have positive length",
                                ));
                            }
                            length
                        }
                        Some(token) => {
                            return Err(self.error_at_previous(format!(
                                "expected embedded struct array length, got {}",
                                token.describe()
                            )));
                        }
                        None => {
                            return Err(self.error_here(
                                "expected embedded struct array length, got end of input",
                            ));
                        }
                    };
                    self.expect(Token::RBracket)?;
                    dimensions.push(length);
                }
                let element_count = dimensions.iter().try_fold(1u32, |count, length| {
                    count.checked_mul(*length).ok_or_else(|| {
                        self.error_here(format!("struct `{struct_name}` layout is too large"))
                    })
                })?;
                let field_size = nested_layout
                    .size_bytes
                    .checked_mul(element_count)
                    .ok_or_else(|| {
                        self.error_here(format!("struct `{struct_name}` layout is too large"))
                    })?;
                return Ok((
                    C0Type::UInt8Array(field_size),
                    field_size,
                    nested_layout.alignment_bytes(),
                    Some(nested_name.to_string()),
                    Some(nested_layout.size_bytes()),
                    Some(dimensions),
                ));
            }
            return Ok((
                base_type.c_type,
                nested_layout.size_bytes(),
                nested_layout.alignment_bytes(),
                Some(nested_name.to_string()),
                None,
                None,
            ));
        }
        let (c_type, array_shape) = if self.peek() == Some(&Token::LBracket) {
            if base_type.struct_name.is_some()
                || !matches!(
                    base_type.c_type,
                    C0Type::Int32 | C0Type::UInt8 | C0Type::Float32 | C0Type::Float64
                )
            {
                return Err(self.error_here(
                    "inline scalar arrays in structs currently support int32, uint8, float, and double elements",
                ));
            }
            let mut dimensions = Vec::new();
            let mut element_count = 1u32;
            while self.peek() == Some(&Token::LBracket) {
                self.position += 1;
                let length = match self.next() {
                    Some(Token::Number(number)) => {
                        let length =
                            parse_integer_literal_magnitude(&number).map_err(|reason| {
                                self.error_here(format!(
                                    "invalid struct array length `{number}`: {reason}"
                                ))
                            })?;
                        let length = u32::try_from(length).map_err(|_| {
                            self.error_here(format!(
                                "struct array length `{number}` is out of range"
                            ))
                        })?;
                        if length == 0 {
                            return Err(self.error_here("struct arrays must have positive length"));
                        }
                        length
                    }
                    Some(token) => {
                        return Err(self.error_at_previous(format!(
                            "expected struct array length, got {}",
                            token.describe()
                        )));
                    }
                    None => {
                        return Err(
                            self.error_here("expected struct array length, got end of input")
                        );
                    }
                };
                element_count = element_count.checked_mul(length).ok_or_else(|| {
                    self.error_here(format!(
                        "struct array dimensions are too large for `{struct_name}`"
                    ))
                })?;
                dimensions.push(length);
                self.expect(Token::RBracket)?;
            }

            let array_shape = (dimensions.len() > 1).then_some(dimensions);
            let c_type = match base_type.c_type {
                C0Type::Int32 => C0Type::Int32Array(element_count),
                C0Type::UInt8 => C0Type::UInt8Array(element_count),
                C0Type::Float32 => C0Type::Float32Array(element_count),
                C0Type::Float64 => C0Type::Float64Array(element_count),
                _ => unreachable!("validated scalar struct array element type"),
            };
            (c_type, array_shape)
        } else {
            (base_type.c_type, None)
        };

        if !matches!(
            c_type,
            C0Type::Int16
                | C0Type::Int32
                | C0Type::UInt8
                | C0Type::UInt16
                | C0Type::UInt32
                | C0Type::Int64
                | C0Type::UInt64
                | C0Type::Float32
                | C0Type::Float64
                | C0Type::Int32Pointer
                | C0Type::UInt8Pointer
                | C0Type::Float32Pointer
                | C0Type::Float64Pointer
                | C0Type::Int32PointerPointer
                | C0Type::UInt8PointerPointer
                | C0Type::Float32PointerPointer
                | C0Type::Float64PointerPointer
                | C0Type::Int32Array(_)
                | C0Type::UInt8Array(_)
                | C0Type::Float32Array(_)
                | C0Type::Float64Array(_)
        ) {
            return Err(self.error_here(format!(
                "struct `{struct_name}` fields currently support modeled integer and floating-point scalars, fixed scalar arrays, and pointer fields",
            )));
        }
        let (field_size, field_alignment) = match c_type {
            C0Type::Int32Array(length) => (
                length.checked_mul(4).ok_or_else(|| {
                    self.error_here(format!("struct `{struct_name}` layout is too large"))
                })?,
                4,
            ),
            C0Type::UInt8Array(length) => (length, 1),
            _ => self.abi.size_and_alignment(c_type),
        };
        Ok((
            c_type,
            field_size,
            field_alignment,
            base_type.struct_name.clone(),
            None,
            array_shape,
        ))
    }

    fn parse_parameters(&mut self) -> Result<Vec<C0Parameter>, C0SyntaxError> {
        let mut parameters = Vec::new();
        if self.peek() == Some(&Token::RParen) {
            return Ok(parameters);
        }

        loop {
            let parsed_type = self.parse_type()?;
            if parsed_type.union_name.is_some() {
                return Err(self.error_here(
                    "tagged union parameters are not supported; use a pointer to the containing struct",
                ));
            }
            if parsed_type.enum_name.is_some() {
                return Err(self.error_here(
                    "enum parameters are not supported; use enum values in struct fields",
                ));
            }
            if parsed_type.is_volatile
                && (parsed_type.struct_name.is_some()
                    || parsed_type.enum_name.is_some()
                    || parsed_type.union_name.is_some()
                    || (parsed_type.c_type.is_pointer() && !parsed_type.c_type.is_scalar_pointer()))
            {
                return Err(self.error_here(
                    "the sequential volatile model supports scalar objects and pointers to scalar objects",
                ));
            }
            if parsed_type.is_volatile && self.peek() == Some(&Token::LParen) {
                return Err(self.error_here(
                    "the small volatile model does not support volatile function-pointer objects",
                ));
            }
            if let Some((name, c_type, signature)) =
                self.parse_function_pointer_declarator(parsed_type.clone())?
            {
                let kernel_name = self.declare_name(&name)?;
                self.variable_types.insert(kernel_name.clone(), c_type);
                self.variable_function_pointers
                    .insert(kernel_name.clone(), signature.clone());
                parameters.push(C0Parameter {
                    c_type,
                    name: kernel_name,
                    volatile: false,
                    pointee_volatile: false,
                    constant: false,
                    pointee_constant: false,
                    struct_layout: None,
                    pointee_struct_layout: None,
                    function_pointer_signature: Some(signature),
                    struct_name: None,
                    array_element_width: None,
                });
                if self.peek() != Some(&Token::Comma) {
                    return Ok(parameters);
                }
                self.position += 1;
                continue;
            }
            if parsed_type.c_type == C0Type::Void {
                return Err(self.error_here("function parameters cannot have type `void`"));
            }
            let name = self.expect_ident("parameter name")?;
            let kernel_name = self.declare_name(&name)?;
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
            let array_parameter = self.peek() == Some(&Token::LBracket);
            let c_type = struct_value_layout
                .as_ref()
                .map(struct_value_type)
                .unwrap_or(self.parse_parameter_array_suffix(parsed_type.c_type)?);
            let object_volatile = parsed_type.is_volatile && !c_type.is_pointer();
            let pointee_volatile = parsed_type.is_volatile && c_type.is_scalar_pointer();
            let object_constant = parsed_type.is_constant && !array_parameter;
            let pointee_constant =
                parsed_type.pointee_constant || (parsed_type.is_constant && array_parameter);
            self.variable_types.insert(kernel_name.clone(), c_type);
            if object_constant {
                self.variable_constants.insert(kernel_name.clone());
            }
            if pointee_constant {
                self.variable_pointee_constants.insert(kernel_name.clone());
            }
            let struct_name = parsed_type.struct_name;
            if struct_name.is_some() {
                if c_type != parsed_type.c_type && !struct_array && !struct_value {
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
                    parameters.push(C0Parameter {
                        c_type,
                        name: kernel_name,
                        volatile: object_volatile,
                        pointee_volatile,
                        constant: object_constant,
                        pointee_constant,
                        struct_layout: struct_value_layout,
                        pointee_struct_layout: (c_type.is_pointer() && !array_parameter)
                            .then(|| {
                                struct_name
                                    .as_ref()
                                    .and_then(|name| self.structs.get(name).cloned())
                            })
                            .flatten(),
                        function_pointer_signature: None,
                        struct_name,
                        array_element_width: None,
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
                    parameters.push(C0Parameter {
                        c_type,
                        name: kernel_name,
                        volatile: object_volatile,
                        pointee_volatile,
                        constant: object_constant,
                        pointee_constant,
                        struct_layout: self.structs.get(&struct_name_value).cloned(),
                        pointee_struct_layout: None,
                        function_pointer_signature: None,
                        struct_name,
                        array_element_width: Some(element_width),
                    });
                    if self.peek() != Some(&Token::Comma) {
                        return Ok(parameters);
                    }
                    self.position += 1;
                    continue;
                }
            }
            parameters.push(C0Parameter {
                c_type,
                name: kernel_name,
                volatile: object_volatile,
                pointee_volatile,
                constant: object_constant,
                pointee_constant,
                struct_layout: struct_name
                    .as_ref()
                    .and_then(|name| self.structs.get(name))
                    .cloned(),
                pointee_struct_layout: None,
                function_pointer_signature: None,
                struct_name,
                array_element_width: None,
            });

            if self.peek() != Some(&Token::Comma) {
                return Ok(parameters);
            }
            self.position += 1;
        }
    }

    fn parse_type(&mut self) -> Result<ParsedType, C0SyntaxError> {
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
            Some(Token::Ident(name)) if name == "struct" => ParsedType {
                // C0 has no struct-value representation. Keep the tag on the
                // parsed type while using the scalar slot as an internal
                // placeholder so `typedef struct S S_t;` can later become
                // `struct S*` when the declarator supplies `*`.
                c_type: C0Type::Int32,
                struct_name: Some(self.expect_ident("struct name")?),
                enum_name: None,
                union_name: None,
                is_volatile: false,
                is_constant: false,
                pointee_constant: false,
            },
            Some(Token::Ident(name)) if name == "union" => ParsedType {
                // A union has no runtime aggregate value in C0. Keep its tag
                // on the parsed type while using an int32 placeholder for
                // the address-backed member-selection path.
                c_type: C0Type::Int32,
                struct_name: None,
                enum_name: None,
                union_name: {
                    let union_name = self.expect_ident("union name")?;
                    if !self.unions.contains_key(&union_name) {
                        return Err(
                            self.error_here(format!("unknown union declaration `{union_name}`"))
                        );
                    }
                    Some(union_name)
                },
                is_volatile: false,
                is_constant: false,
                pointee_constant: false,
            },
            Some(Token::Ident(name)) if name == "enum" => ParsedType {
                c_type: C0Type::Int32,
                struct_name: None,
                union_name: None,
                enum_name: {
                    let enum_name = self.expect_ident("enum name")?;
                    if !self.enums.contains_key(&enum_name) {
                        return Err(
                            self.error_here(format!("unknown enum declaration `{enum_name}`"))
                        );
                    }
                    Some(enum_name)
                },
                is_volatile: false,
                is_constant: false,
                pointee_constant: false,
            },
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

        let mut c_type = parsed.c_type;
        let mut object_constant = is_constant || parsed.is_constant;
        let mut pointee_constant = parsed.pointee_constant;
        if self.peek_ident() == Some("const") {
            self.position += 1;
            object_constant = true;
        }
        let mut saw_pointer = false;
        while self.peek() == Some(&Token::Star) {
            if saw_pointer && pointee_constant {
                return Err(self.error_at_previous(
                    "const qualification beyond the first pointer level is not supported",
                ));
            }
            let base_constant = object_constant;
            object_constant = false;
            self.position += 1;
            c_type = match c_type {
                C0Type::Int16 => C0Type::Int16Pointer,
                C0Type::Int32 => C0Type::Int32Pointer,
                C0Type::UInt8 => C0Type::UInt8Pointer,
                C0Type::UInt16 => C0Type::UInt16Pointer,
                C0Type::UInt32 => C0Type::UInt32Pointer,
                C0Type::Int64 => C0Type::Int64Pointer,
                C0Type::UInt64 => C0Type::UInt64Pointer,
                C0Type::Float32 => C0Type::Float32Pointer,
                C0Type::Float64 => C0Type::Float64Pointer,
                C0Type::Int16Pointer => C0Type::Int16PointerPointer,
                C0Type::UInt16Pointer => C0Type::UInt16PointerPointer,
                C0Type::Int32Pointer => C0Type::Int32PointerPointer,
                C0Type::UInt8Pointer => C0Type::UInt8PointerPointer,
                C0Type::UInt32Pointer => C0Type::UInt32PointerPointer,
                C0Type::Int64Pointer => C0Type::Int64PointerPointer,
                C0Type::UInt64Pointer => C0Type::UInt64PointerPointer,
                C0Type::Float32Pointer => C0Type::Float32PointerPointer,
                C0Type::Float64Pointer => C0Type::Float64PointerPointer,
                C0Type::Void => C0Type::VoidPointer,
                C0Type::VoidPointer => {
                    return Err(
                        self.error_at_previous("pointer depth beyond `**` is not supported")
                    );
                }
                C0Type::Int16PointerPointer
                | C0Type::UInt16PointerPointer
                | C0Type::Int32PointerPointer
                | C0Type::UInt8PointerPointer
                | C0Type::UInt32PointerPointer
                | C0Type::Int64PointerPointer
                | C0Type::UInt64PointerPointer => {
                    return Err(
                        self.error_at_previous("pointer depth beyond `**` is not supported")
                    );
                }
                C0Type::Float32PointerPointer | C0Type::Float64PointerPointer => {
                    return Err(
                        self.error_at_previous("pointer depth beyond `**` is not supported")
                    );
                }
                C0Type::Int32Array(_)
                | C0Type::UInt8Array(_)
                | C0Type::Int16Array(_)
                | C0Type::UInt16Array(_)
                | C0Type::UInt32Array(_)
                | C0Type::Int64Array(_)
                | C0Type::UInt64Array(_) => {
                    return Err(self.error_at_previous("pointer-to-array types are not supported"));
                }
                C0Type::Float32Array(_) | C0Type::Float64Array(_) => {
                    return Err(self.error_at_previous("pointer-to-array types are not supported"));
                }
                C0Type::FunctionPointer(_) => {
                    return Err(
                        self.error_at_previous("pointers to function pointers are not supported")
                    );
                }
            };
            if base_constant {
                pointee_constant = true;
            }
            if self.peek_ident() == Some("const") {
                self.position += 1;
                object_constant = true;
            }
            saw_pointer = true;
            if parsed.union_name.is_some() {
                return Err(
                    self.error_at_previous("pointers to union values are not supported yet")
                );
            }
            if parsed.enum_name.is_some() && c_type != C0Type::Int32 {
                return Err(self.error_at_previous("pointers to enum values are not supported"));
            }
        }
        Ok(ParsedType {
            c_type,
            struct_name: parsed.struct_name,
            enum_name: parsed.enum_name,
            union_name: parsed.union_name,
            is_volatile: is_volatile || parsed.is_volatile,
            is_constant: object_constant,
            pointee_constant,
        })
    }

    /// Parses the parenthesized declarator in `int32 (*callback)(int32)`.
    /// The kernel receives a structural signature key, while the returned
    /// metadata retains nominal struct-pointer tags for C0 boundary checks.
    fn parse_function_pointer_declarator(
        &mut self,
        return_type: ParsedType,
    ) -> Result<Option<(String, C0Type, C0FunctionPointerSignature)>, C0SyntaxError> {
        if self.peek() != Some(&Token::LParen) {
            return Ok(None);
        }
        if return_type.struct_name.is_some() && !return_type.c_type.is_pointer() {
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
                let parsed_type = self.parse_type()?;
                if parsed_type.is_volatile {
                    return Err(self.error_here(
                        "volatile function-pointer parameters are not supported by the small model",
                    ));
                }
                if parsed_type.c_type == C0Type::Void {
                    return Err(
                        self.error_here("function-pointer parameters cannot have type `void`")
                    );
                }
                let parameter_type = self.parse_parameter_array_suffix(parsed_type.c_type)?;
                if parsed_type.struct_name.is_some() && parsed_type.c_type == C0Type::Int32 {
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
                parameters.push(C0FunctionPointerParameter::new(
                    parameter_type,
                    parsed_type.struct_name,
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
            .map(|parameter| parameter.c_type.to_kernel_type())
            .collect::<Vec<_>>();
        let signature = crate::kernel::CType::function_pointer_signature(
            return_type.c_type.to_kernel_type(),
            &parameter_types,
        );
        if signature == 0 {
            return Err(
                self.error_here("function-pointer signature uses an unsupported modeled type")
            );
        }
        let function_pointer_signature = C0FunctionPointerSignature::new(
            return_type.c_type,
            return_type.struct_name,
            parameters,
        );
        Ok(Some((
            name,
            C0Type::FunctionPointer(signature),
            function_pointer_signature,
        )))
    }

    fn parse_named_type(&mut self, name: String) -> Result<ParsedType, C0SyntaxError> {
        let c_type = match name.as_str() {
            "void" => C0Type::Void,
            "int16" | "short" | "int16_t" => C0Type::Int16,
            "int32" | "int" | "int32_t" => C0Type::Int32,
            "uint8" | "uint8_t" => C0Type::UInt8,
            "uint16" | "uint16_t" => C0Type::UInt16,
            "uint32" | "uint32_t" => C0Type::UInt32,
            "int64" | "int64_t" | "ssize_t" => C0Type::Int64,
            "long" => {
                if self.peek_ident() == Some("double") {
                    self.position += 1;
                    return Err(self.error_at_previous(
                        "unsupported C type `long double`: extended-precision floating-point values are not modeled in C0",
                    ));
                }
                if self.peek_ident() == Some("long") {
                    self.position += 1;
                }
                C0Type::Int64
            }
            "uint64" | "size_t" | "uint64_t" => C0Type::UInt64,
            "float" => C0Type::Float32,
            "double" => C0Type::Float64,
            "unsigned" => {
                if self.peek_ident() == Some("char") {
                    self.position += 1;
                    C0Type::UInt8
                } else if self.peek_ident() == Some("int") {
                    self.position += 1;
                    C0Type::UInt32
                } else if self.peek_ident() == Some("short") {
                    self.position += 1;
                    C0Type::UInt16
                } else if self.peek_ident() == Some("long") {
                    self.position += 1;
                    if self.peek_ident() == Some("long") {
                        self.position += 1;
                    }
                    C0Type::UInt64
                } else {
                    return Err(self.error_at_previous(
                        "unsupported integer width `unsigned`; only `unsigned char`, `unsigned short`, and `unsigned int` are modeled",
                    ));
                }
            }
            "signed" => {
                if self.peek_ident() == Some("char") {
                    self.position += 1;
                    return Err(self.error_at_previous(
                        "unsupported C type `signed char`: signed char is not modeled; use `unsigned char` or `uint8_t`",
                    ));
                }
                if self.peek_ident() == Some("short") {
                    self.position += 1;
                    C0Type::Int16
                } else if self.peek_ident() == Some("long") {
                    self.position += 1;
                    if self.peek_ident() == Some("long") {
                        self.position += 1;
                    }
                    C0Type::Int64
                } else {
                    return Err(self.error_at_previous(
                        "unsupported integer width `signed`; only `signed short` is modeled among signed standard aliases",
                    ));
                }
            }
            "char" => {
                return Err(self.error_at_previous(
                    "unsupported C type `char`: signed char is not modeled; use `unsigned char` or `uint8_t`",
                ));
            }
            "volatile" => {
                return Err(
                    self.error_at_previous("the `volatile` qualifier is not supported in C0")
                );
            }
            _ => {
                let Some(typedef) = self.typedefs.get(&name) else {
                    return Err(self.error_at_previous(format!(
                        "unknown C type `{name}`; expected a supported standard spelling, typedef, or `struct`"
                    )));
                };
                return Ok(typedef.clone());
            }
        };
        Ok(ParsedType {
            c_type,
            struct_name: None,
            enum_name: None,
            union_name: None,
            is_volatile: false,
            is_constant: false,
            pointee_constant: false,
        })
    }

    fn parse_parameter_array_suffix(&mut self, c_type: C0Type) -> Result<C0Type, C0SyntaxError> {
        if self.peek() != Some(&Token::LBracket) {
            return Ok(c_type);
        }
        let pointer_type = match c_type {
            C0Type::Int16 => C0Type::Int16Pointer,
            C0Type::UInt16 => C0Type::UInt16Pointer,
            C0Type::Int32 => C0Type::Int32Pointer,
            C0Type::UInt8 => C0Type::UInt8Pointer,
            C0Type::UInt32 => C0Type::UInt32Pointer,
            C0Type::Int64 => C0Type::Int64Pointer,
            C0Type::UInt64 => C0Type::UInt64Pointer,
            C0Type::Float32 => C0Type::Float32Pointer,
            C0Type::Float64 => C0Type::Float64Pointer,
            C0Type::Int16Pointer => C0Type::Int16PointerPointer,
            C0Type::UInt16Pointer => C0Type::UInt16PointerPointer,
            C0Type::Int32Pointer => C0Type::Int32PointerPointer,
            C0Type::UInt8Pointer => C0Type::UInt8PointerPointer,
            C0Type::UInt32Pointer => C0Type::UInt32PointerPointer,
            C0Type::Int64Pointer => C0Type::Int64PointerPointer,
            C0Type::UInt64Pointer => C0Type::UInt64PointerPointer,
            _ => {
                return Err(
                    self.error_here("only scalar and pointer array parameters are supported")
                );
            }
        };

        self.position += 1;
        if matches!(self.peek(), Some(Token::Number(_))) {
            self.position += 1;
        }
        self.expect(Token::RBracket)?;
        Ok(pointer_type)
    }

    fn parse_local_array_shape(
        &mut self,
        parsed_type: &ParsedType,
    ) -> Result<(C0Type, Option<Vec<u32>>), C0SyntaxError> {
        if self.peek() != Some(&Token::LBracket) {
            return Ok((parsed_type.c_type, None));
        }
        if parsed_type.enum_name.is_some() {
            return Err(self.error_here("local arrays of enum type are not supported"));
        }
        let (array_type, element_width, element_name, struct_array): (
            fn(u32) -> C0Type,
            u32,
            String,
            bool,
        ) = if let Some(struct_name) = parsed_type.struct_name.as_deref() {
            let element_width = self
                .structs
                .get(struct_name)
                .ok_or_else(|| {
                    self.error_here(format!("unknown struct declaration `{struct_name}`"))
                })?
                .size_bytes;
            (
                C0Type::UInt8Array,
                element_width,
                format!("struct {struct_name}"),
                true,
            )
        } else {
            match parsed_type.c_type {
                C0Type::Int16 => (C0Type::Int16Array, 2u32, "int16".to_string(), false),
                C0Type::UInt16 => (C0Type::UInt16Array, 2u32, "uint16".to_string(), false),
                C0Type::Int32 => (C0Type::Int32Array, 4u32, "int32".to_string(), false),
                C0Type::UInt8 => (C0Type::UInt8Array, 1u32, "uint8".to_string(), false),
                C0Type::UInt32 => (C0Type::UInt32Array, 4u32, "uint32".to_string(), false),
                C0Type::Int64 => (C0Type::Int64Array, 8u32, "int64".to_string(), false),
                C0Type::UInt64 => (C0Type::UInt64Array, 8u32, "uint64".to_string(), false),
                C0Type::Float32 => (C0Type::Float32Array, 4u32, "float".to_string(), false),
                C0Type::Float64 => (C0Type::Float64Array, 8u32, "double".to_string(), false),
                _ => return Err(self.error_here("only scalar local arrays are supported")),
            }
        };

        if element_width == 0 {
            return Err(self.error_here(format!(
                "{element_name} array elements must have positive size"
            )));
        }

        let mut dimensions = Vec::new();
        let mut element_count = 1u32;
        while self.peek() == Some(&Token::LBracket) {
            self.position += 1;
            let length = match self.next() {
                Some(Token::Number(number)) => {
                    let length = parse_integer_literal_magnitude(&number).map_err(|reason| {
                        self.error_here(format!("invalid array length `{number}`: {reason}"))
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
                    return Err(self.error_here("expected local array length, got end of input"));
                }
            };
            element_count = element_count.checked_mul(length).ok_or_else(|| {
                self.error_here(format!(
                    "array dimensions are too large for {element_name} elements"
                ))
            })?;
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
        let shape = (struct_array || dimensions.len() > 1).then_some(dimensions);
        Ok((array_type(array_length), shape))
    }

    fn parse_block_statement(&mut self) -> Result<C0Statement, C0SyntaxError> {
        self.expect(Token::LBrace)?;
        self.push_scope();
        let mut statements = Vec::new();
        while self.peek() != Some(&Token::RBrace) {
            if self.peek().is_none() {
                return Err(self.error_here("expected statement or `}`, got end of input"));
            }
            statements.push(self.parse_statement()?);
        }
        self.expect(Token::RBrace)?;
        let body = balanced_statement_sequence(statements).unwrap_or(C0Statement::Skip);
        let body = self.lower_call_expressions(body)?;
        self.pop_scope();

        Ok(body)
    }

    /// Parses the first supported C `switch` shape: a compound statement whose
    /// direct children are `case`/`default` labels and their statement bodies.
    /// Keeping the cases in source order is what preserves C fallthrough.
    fn parse_switch_body(&mut self) -> Result<Vec<C0SwitchCase>, C0SyntaxError> {
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
                    let value = match expression {
                        C0Expression::Int32Literal(value) => value,
                        C0Expression::UInt8Literal(value) => u32::from(value),
                        C0Expression::UInt32Literal(value) => value,
                        _ => {
                            return Err(self.error_here(
                                "`case` labels currently require an integer or character literal",
                            ));
                        }
                    };
                    self.expect(Token::Colon)?;
                    if cases
                        .iter()
                        .any(|case: &C0SwitchCase| case.value == Some(value))
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
            cases.push(C0SwitchCase {
                value,
                body: Box::new(
                    balanced_statement_sequence(statements).unwrap_or(C0Statement::Skip),
                ),
            });
        }
        self.expect(Token::RBrace)?;
        self.pop_scope();
        if cases.is_empty() {
            return Err(self.error_here("a `switch` body must contain a `case` or `default` label"));
        }
        Ok(cases)
    }

    /// Parses the statement controlled by `if`, `else`, `while`, or `for`.
    /// C permits a single statement in these positions, while declarations
    /// remain valid only as block items in a compound statement.
    fn parse_controlled_statement(
        &mut self,
        construct: &str,
    ) -> Result<C0Statement, C0SyntaxError> {
        if self.peek() == Some(&Token::LBrace) {
            return self.parse_block_statement();
        }
        if self.is_type_start() {
            return Err(self.error_here(format!(
                "a declaration controlled by `{construct}` must be enclosed in braces"
            )));
        }
        self.parse_statement()
    }

    fn parse_loop_control_statement(
        &mut self,
        continue_statement: bool,
    ) -> Result<C0Statement, C0SyntaxError> {
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
            C0Statement::Continue
        } else {
            C0Statement::Break
        })
    }

    fn parse_statement(&mut self) -> Result<C0Statement, C0SyntaxError> {
        match self.peek() {
            Some(Token::Semicolon) => {
                self.position += 1;
                Ok(C0Statement::Skip)
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
                if let Ok(C0Expression::IndirectCall {
                    function,
                    signature,
                    arguments,
                    position,
                }) = self.parse_expression()
                    && self.peek() == Some(&Token::Semicolon)
                {
                    self.position += 1;
                    return Ok(C0Statement::IndirectCall {
                        function: *function,
                        signature,
                        arguments,
                        position,
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
            Some(Token::Ident(_)) if self.peek_next().is_some_and(Token::is_scalar_update) => {
                let statement = self.parse_scalar_update_statement("statement")?;
                self.expect(Token::Semicolon)?;
                Ok(statement)
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
            Some(Token::Ident(_)) if self.is_type_start() => self.parse_local_declaration(),
            Some(Token::Ident(_)) => match self.peek_ident() {
                Some("return") => {
                    self.position += 1;
                    let expression = if self.peek() == Some(&Token::Semicolon) {
                        C0Expression::Void
                    } else if self.current_return_struct_name.is_some() {
                        self.parse_expression_allow_direct_aggregate()?
                    } else {
                        self.parse_expression()?
                    };
                    self.validate_struct_pointer_assignment(
                        self.current_return_pointer_struct_name.as_ref(),
                        Some(self.current_return_type),
                        &expression,
                    )?;
                    self.expect(Token::Semicolon)?;
                    Ok(C0Statement::Return(expression))
                }
                Some("break") => self.parse_loop_control_statement(false),
                Some("continue") => self.parse_loop_control_statement(true),
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
                        Box::new(C0Statement::Skip)
                    };
                    Ok(C0Statement::If {
                        condition,
                        then_branch,
                        else_branch,
                    })
                }
                Some("while") => {
                    self.position += 1;
                    self.expect(Token::LParen)?;
                    let condition = self.parse_expression()?;
                    self.expect(Token::RParen)?;
                    self.loop_contexts.push(CLoopContext::While);
                    let body = Box::new(self.parse_controlled_statement("while")?);
                    self.loop_contexts.pop();
                    Ok(C0Statement::While { condition, body })
                }
                Some("switch") => {
                    self.position += 1;
                    self.expect(Token::LParen)?;
                    let expression = self.parse_expression()?;
                    self.expect(Token::RParen)?;
                    self.loop_contexts.push(CLoopContext::Switch);
                    let cases = self.parse_switch_body()?;
                    self.loop_contexts.pop();
                    Ok(C0Statement::Switch { expression, cases })
                }
                Some("do") => {
                    self.position += 1;
                    self.loop_contexts.push(CLoopContext::DoWhile);
                    let body = self.parse_controlled_statement("do")?;
                    self.loop_contexts.pop();
                    if self.peek_ident() != Some("while") {
                        return Err(self.error_here("expected `while` after `do` body"));
                    }
                    self.position += 1;
                    self.expect(Token::LParen)?;
                    let condition = self.parse_expression()?;
                    self.expect(Token::RParen)?;
                    self.expect(Token::Semicolon)?;
                    Ok(C0Statement::DoWhile {
                        condition,
                        body: Box::new(body),
                    })
                }
                Some("for") => {
                    self.position += 1;
                    self.expect(Token::LParen)?;
                    // A `for` declaration is scoped to the statement, so two
                    // consecutive loops may each declare `int32 i`.
                    self.push_scope();
                    let init = self.parse_for_initializer()?;
                    self.expect(Token::Semicolon)?;
                    let condition = self.parse_expression()?;
                    self.expect(Token::Semicolon)?;
                    let step = self.parse_for_step()?;
                    self.expect(Token::RParen)?;
                    self.loop_contexts.push(CLoopContext::For);
                    let body = self.parse_controlled_statement("for")?;
                    self.loop_contexts.pop();
                    self.pop_scope();
                    Ok(C0Statement::For {
                        initializer: Box::new(init),
                        condition,
                        step: Box::new(step),
                        body: Box::new(body),
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
                        Ok(C0Statement::HeapFree {
                            pointer: pointer.clone(),
                        })
                    } else if self.peek_next() == Some(&Token::LParen) {
                        let source_name = self.expect_ident("function name")?;
                        if matches!(source_name.as_str(), "malloc" | "calloc" | "realloc") {
                            return Err(
                                self.error_here("the allocation result may not be discarded")
                            );
                        }
                        let arguments = self.parse_call_arguments(Some(&source_name))?;
                        self.expect(Token::Semicolon)?;
                        Ok(C0Statement::Call {
                            function_name: self.resolve_function_name(&source_name),
                            arguments,
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

    fn parse_local_array_initializer(
        &mut self,
        name: &str,
        c_type: C0Type,
        array_shape: Option<&[u32]>,
    ) -> Result<C0Statement, C0SyntaxError> {
        let (length, element_type) = match c_type {
            C0Type::Int32Array(length) => (length, C0Type::Int32),
            C0Type::UInt8Array(length) => (length, C0Type::UInt8),
            C0Type::Int16Array(length) => (length, C0Type::Int16),
            C0Type::UInt16Array(length) => (length, C0Type::UInt16),
            C0Type::UInt32Array(length) => (length, C0Type::UInt32),
            C0Type::Int64Array(length) => (length, C0Type::Int64),
            C0Type::UInt64Array(length) => (length, C0Type::UInt64),
            C0Type::Float32Array(length) => (length, C0Type::Float32),
            C0Type::Float64Array(length) => (length, C0Type::Float64),
            _ => unreachable!("array initializer called for a scalar type"),
        };
        let zero = zero_initializer(element_type);
        let mut values = Vec::new();
        let dimensions = array_shape
            .map(ToOwned::to_owned)
            .unwrap_or_else(|| vec![length]);
        self.parse_array_initializer_level(name, &dimensions, 0, &mut values, &zero)?;

        let mut stores = Vec::with_capacity(length as usize);
        for index in 0..length {
            let value = values
                .get(index as usize)
                .cloned()
                .unwrap_or_else(|| zero.clone());
            stores.push(C0Statement::Store {
                pointer: C0Expression::Add(
                    Box::new(C0Expression::Variable(name.to_string())),
                    Box::new(C0Expression::Int32Literal(index)),
                ),
                value,
                value_type: Some(element_type),
            });
        }
        Ok(balanced_statement_sequence(stores).unwrap_or(C0Statement::Skip))
    }

    fn parse_local_struct_array_initializer(
        &mut self,
        name: &str,
        struct_name: &str,
        array_shape: &[u32],
    ) -> Result<C0Statement, C0SyntaxError> {
        if self.peek() != Some(&Token::LBrace) {
            return Err(self.error_here(
                "local struct array elements require nested `{...}` initializer groups",
            ));
        }
        let element_width = self
            .structs
            .get(struct_name)
            .expect("validated local struct array has a layout")
            .size_bytes;
        let stores = self.parse_embedded_struct_array_initializer_level(
            C0Expression::Variable(name.to_string()),
            struct_name,
            array_shape,
            0,
            0,
            element_width,
        )?;
        Ok(balanced_statement_sequence(stores).unwrap_or(C0Statement::Skip))
    }

    fn parse_array_initializer_level(
        &mut self,
        name: &str,
        dimensions: &[u32],
        depth: usize,
        values: &mut Vec<C0Expression>,
        zero: &C0Expression,
    ) -> Result<(), C0SyntaxError> {
        let child_width = dimensions[depth + 1..]
            .iter()
            .copied()
            .fold(1u32, |width, dimension| {
                width
                    .checked_mul(dimension)
                    .expect("validated array shape has a representable width")
            });
        let child_count = dimensions[depth];
        let start = values.len();
        self.expect(Token::LBrace)?;
        let mut children = 0u32;
        if self.peek() != Some(&Token::RBrace) {
            loop {
                if children == child_count {
                    return Err(self
                        .error_here(format!("too many initializers for `{name}[{child_count}]`")));
                }
                if depth + 1 == dimensions.len() {
                    values.push(self.parse_expression()?);
                } else {
                    if self.peek() != Some(&Token::LBrace) {
                        return Err(self.error_here(format!(
                            "nested initializer for `{name}` expects `{}` groups",
                            dimensions.len() - depth - 1
                        )));
                    }
                    self.parse_array_initializer_level(name, dimensions, depth + 1, values, zero)?;
                }
                children += 1;
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
                            "expected `,` or `}}` in `{name}` initializer, got {}",
                            token.describe()
                        )));
                    }
                    None => {
                        return Err(self.error_here(format!(
                            "expected `,` or `}}` in `{name}` initializer, got end of input"
                        )));
                    }
                }
            }
        }
        self.expect(Token::RBrace)?;

        let present = (values.len() - start) as u32;
        let expected = child_count
            .checked_mul(child_width)
            .expect("validated array shape has a representable length");
        for _ in present..expected {
            values.push(zero.clone());
        }
        Ok(())
    }

    fn parse_aggregate_initializer(
        &mut self,
        object_name: &str,
        struct_name: &str,
    ) -> Result<Vec<C0AggregateInitializer>, C0SyntaxError> {
        self.parse_aggregate_initializer_level(object_name, struct_name, 0)
    }

    fn parse_aggregate_array_initializer(
        &mut self,
        object_name: &str,
        struct_name: &str,
        layout: &C0StructLayout,
        length: u32,
    ) -> Result<Vec<C0AggregateInitializer>, C0SyntaxError> {
        self.expect(Token::LBrace)?;
        let mut initializers = Vec::new();
        let mut next_element_index = 0u32;
        if self.peek() != Some(&Token::RBrace) {
            loop {
                let element_index = if self.peek() == Some(&Token::LBracket) {
                    self.position += 1;
                    let index = self.parse_aggregate_array_designator(object_name, length)?;
                    self.expect(Token::Equal)?;
                    next_element_index = index
                        .checked_add(1)
                        .expect("validated aggregate array designator index");
                    index
                } else {
                    if self.peek() == Some(&Token::Dot) {
                        return Err(self.error_here(
                            "aggregate array initializers support only array index designators",
                        ));
                    }
                    let index = next_element_index;
                    next_element_index = next_element_index
                        .checked_add(1)
                        .expect("validated aggregate array initializer index");
                    index
                };
                if element_index >= length {
                    return Err(self.error_here(format!(
                        "too many initializers for aggregate array `{object_name}[{length}]`"
                    )));
                }
                if self.peek() != Some(&Token::LBrace) {
                    return Err(self.error_here(
                        "aggregate array elements require nested `{...}` initializer groups",
                    ));
                }
                let base_offset = element_index
                    .checked_mul(layout.size_bytes())
                    .expect("validated aggregate array initializer offset");
                initializers.extend(self.parse_aggregate_initializer_level(
                    object_name,
                    struct_name,
                    base_offset,
                )?);
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
                            "expected `,` or `}}` in aggregate array initializer for `{object_name}`, got {}",
                            token.describe()
                        )));
                    }
                    None => {
                        return Err(self.error_here(format!(
                            "expected `,` or `}}` in aggregate array initializer for `{object_name}`, got end of input"
                        )));
                    }
                }
            }
        }
        self.expect(Token::RBrace)?;
        Ok(initializers)
    }

    fn parse_aggregate_array_designator(
        &mut self,
        object_name: &str,
        length: u32,
    ) -> Result<u32, C0SyntaxError> {
        let index = match self.next() {
            Some(Token::Number(number)) => {
                let magnitude = parse_integer_literal_magnitude(&number).map_err(|reason| {
                    self.error_at_previous(format!(
                        "invalid aggregate array designator index `{number}`: {reason}"
                    ))
                })?;
                u32::try_from(magnitude).map_err(|_| {
                    self.error_at_previous(format!(
                        "aggregate array designator index `{number}` is out of range"
                    ))
                })?
            }
            Some(Token::CharLiteral(value)) => u32::from(value),
            Some(token) => {
                return Err(self.error_at_previous(format!(
                    "aggregate array designators currently require integer literals, got {}",
                    token.describe()
                )));
            }
            None => {
                return Err(self.error_here(
                    "aggregate array designators currently require an integer literal",
                ));
            }
        };
        self.expect(Token::RBracket)?;
        if index >= length {
            return Err(self.error_here(format!(
                "aggregate array designator index `{index}` is out of bounds for `{object_name}[{length}]`"
            )));
        }
        Ok(index)
    }

    fn parse_aggregate_initializer_level(
        &mut self,
        object_name: &str,
        struct_name: &str,
        base_offset: u32,
    ) -> Result<Vec<C0AggregateInitializer>, C0SyntaxError> {
        let mut fields = self
            .structs
            .get(struct_name)
            .expect("validated aggregate initializer has a layout")
            .fields
            .iter()
            .map(|(name, field)| (name.clone(), field.clone()))
            .collect::<Vec<_>>();
        fields.sort_by_key(|(_, field)| field.offset_bytes);

        self.expect(Token::LBrace)?;
        let mut initializers = Vec::new();
        let mut next_field_index = 0usize;
        if self.peek() != Some(&Token::RBrace) {
            loop {
                let field_index = if self.peek() == Some(&Token::Dot) {
                    self.position += 1;
                    let field_name = self.expect_ident("aggregate field name")?;
                    self.expect(Token::Equal)?;
                    let Some(index) = fields.iter().position(|(name, _)| name == &field_name)
                    else {
                        return Err(self.error_here(format!(
                            "unknown field `{field_name}` in `struct {struct_name}` initializer"
                        )));
                    };
                    next_field_index = index
                        .checked_add(1)
                        .expect("validated aggregate field index");
                    index
                } else {
                    if self.peek() == Some(&Token::LBracket) {
                        return Err(self.error_here(
                            "struct aggregate initializers support only field designators",
                        ));
                    }
                    let index = next_field_index;
                    next_field_index = next_field_index
                        .checked_add(1)
                        .expect("validated aggregate field index");
                    index
                };
                let Some((_, field)) = fields.get(field_index) else {
                    return Err(self
                        .error_here(format!("too many initializers for `struct {struct_name}`")));
                };
                initializers.extend(self.parse_aggregate_initializer_field(
                    object_name,
                    base_offset,
                    field,
                )?);
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
                            "expected `,` or `}}` in aggregate initializer for `{object_name}`, got {}",
                            token.describe()
                        )));
                    }
                    None => {
                        return Err(self.error_here(format!(
                            "expected `,` or `}}` in aggregate initializer for `{object_name}`, got end of input"
                        )));
                    }
                }
            }
        }
        self.expect(Token::RBrace)?;
        Ok(initializers)
    }

    fn parse_aggregate_initializer_field(
        &mut self,
        object_name: &str,
        base_offset: u32,
        field: &C0StructField,
    ) -> Result<Vec<C0AggregateInitializer>, C0SyntaxError> {
        let field_offset = base_offset
            .checked_add(field.offset_bytes)
            .expect("validated aggregate initializer field offset");
        if let Some(element_width) = field.array_element_width {
            let nested_name = field
                .struct_name
                .as_deref()
                .expect("embedded struct array has a struct name");
            let dimensions = field
                .array_shape
                .as_deref()
                .expect("embedded struct array has a shape");
            if self.peek() != Some(&Token::LBrace) {
                return Err(self.error_here(
                    "embedded struct array initializers require nested `{...}` groups",
                ));
            }
            return self.parse_embedded_struct_array_aggregate_initializer_level(
                object_name,
                nested_name,
                dimensions,
                0,
                0,
                field_offset,
                element_width,
            );
        }
        if field.c_type == C0Type::Int32 {
            if let Some(nested_name) = field.struct_name.as_deref() {
                if self.peek() != Some(&Token::LBrace) {
                    return Err(self.error_here(
                        "embedded struct initializers require a nested `{...}` group",
                    ));
                }
                return self.parse_aggregate_initializer_level(
                    object_name,
                    nested_name,
                    field_offset,
                );
            }
        }

        if let Some((element_type, dimensions)) = struct_scalar_array_shape(field) {
            if self.peek() != Some(&Token::LBrace) {
                return Err(self.error_here(
                    "inline scalar array initializers require a nested `{...}` group",
                ));
            }
            let zero = zero_initializer(element_type);
            let mut values = Vec::new();
            self.parse_array_initializer_level(
                "aggregate field",
                &dimensions,
                0,
                &mut values,
                &zero,
            )?;
            let mut initializers = Vec::with_capacity(values.len());
            for (index, value) in values.into_iter().enumerate() {
                validate_aggregate_initializer(self, element_type, &value)?;
                let offset = field_offset
                    .checked_add(
                        u32::try_from(index)
                            .expect("validated aggregate initializer index")
                            .checked_mul(element_type.abi_size_bytes())
                            .expect("validated aggregate initializer offset"),
                    )
                    .expect("validated aggregate initializer offset");
                initializers.push(C0AggregateInitializer::new(offset, element_type, value));
            }
            return Ok(initializers);
        }

        let value = self.parse_expression()?;
        validate_aggregate_initializer(self, field.c_type, &value)?;
        Ok(vec![C0AggregateInitializer::new(
            field_offset,
            field.c_type,
            value,
        )])
    }

    fn parse_embedded_struct_array_aggregate_initializer_level(
        &mut self,
        object_name: &str,
        struct_name: &str,
        dimensions: &[u32],
        depth: usize,
        flat_prefix: u32,
        element_offset: u32,
        element_width: u32,
    ) -> Result<Vec<C0AggregateInitializer>, C0SyntaxError> {
        let child_count = dimensions[depth];
        let child_width = dimensions[depth + 1..]
            .iter()
            .copied()
            .fold(1u32, |width, dimension| {
                width
                    .checked_mul(dimension)
                    .expect("validated embedded struct array initializer width")
            });
        self.expect(Token::LBrace)?;
        let mut initializers = Vec::new();
        let mut child_index = 0u32;
        if self.peek() != Some(&Token::RBrace) {
            loop {
                if child_index == child_count {
                    return Err(
                        self.error_here("too many initializers for an embedded struct array")
                    );
                }
                let flat_index = flat_prefix
                    .checked_add(
                        child_index
                            .checked_mul(child_width)
                            .expect("validated embedded struct array initializer index"),
                    )
                    .expect("validated embedded struct array initializer index");
                let child_offset = element_offset
                    .checked_add(
                        flat_index
                            .checked_mul(element_width)
                            .expect("validated embedded struct array initializer offset"),
                    )
                    .expect("validated embedded struct array initializer offset");
                if depth + 1 == dimensions.len() {
                    if self.peek() != Some(&Token::LBrace) {
                        return Err(self.error_here(
                            "embedded struct array elements require nested `{...}` groups",
                        ));
                    }
                    initializers.extend(self.parse_aggregate_initializer_level(
                        object_name,
                        struct_name,
                        child_offset,
                    )?);
                } else {
                    if self.peek() != Some(&Token::LBrace) {
                        return Err(self.error_here(
                            "nested embedded struct array initializers require `{...}` groups",
                        ));
                    }
                    initializers.extend(
                        self.parse_embedded_struct_array_aggregate_initializer_level(
                            object_name,
                            struct_name,
                            dimensions,
                            depth + 1,
                            flat_index,
                            element_offset,
                            element_width,
                        )?,
                    );
                }
                child_index += 1;
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
                            "expected `,` or `}}` in embedded struct array initializer for `{object_name}`, got {}",
                            token.describe()
                        )));
                    }
                    None => {
                        return Err(self.error_here(format!(
                            "expected `,` or `}}` in embedded struct array initializer for `{object_name}`, got end of input"
                        )));
                    }
                }
            }
        }
        self.expect(Token::RBrace)?;
        Ok(initializers)
    }

    fn parse_struct_value_initializer(
        &mut self,
        target: &str,
        struct_name: &str,
    ) -> Result<C0Statement, C0SyntaxError> {
        let stores = self.parse_struct_initializer_level(
            C0Expression::Variable(target.to_string()),
            struct_name,
        )?;
        Ok(balanced_statement_sequence(stores).unwrap_or(C0Statement::Skip))
    }

    fn parse_struct_initializer_level(
        &mut self,
        target_pointer: C0Expression,
        struct_name: &str,
    ) -> Result<Vec<C0Statement>, C0SyntaxError> {
        let mut fields = self
            .structs
            .get(struct_name)
            .expect("validated struct initializer has a layout")
            .fields
            .values()
            .cloned()
            .collect::<Vec<_>>();
        // `fields` is a BTreeMap for name lookup, but C initializer order is
        // declaration order. ABI offsets are already assigned in declaration
        // order, so they provide the stable source-order key here.
        fields.sort_by_key(|field| field.offset_bytes);

        self.expect(Token::LBrace)?;
        let mut stores = Vec::new();
        let mut field_index = 0usize;
        let mut has_designated_initializer = false;
        if self.peek() != Some(&Token::RBrace) {
            loop {
                if self.peek() == Some(&Token::Dot) {
                    has_designated_initializer = true;
                    let (designated_index, parent_pointer, field) = self
                        .parse_struct_field_designator(
                            target_pointer.clone(),
                            struct_name,
                            &fields,
                        )?;
                    stores.extend(self.parse_struct_initializer_field(parent_pointer, &field)?);
                    // C continues positional initialization after the
                    // top-level field selected by a designator. Nested field
                    // designators therefore advance past their outer field.
                    field_index = designated_index + 1;
                } else {
                    if self.peek() == Some(&Token::LBracket) {
                        return Err(self.error_here(
                            "array designators in struct initializers are not supported",
                        ));
                    }
                    let Some(field) = fields.get(field_index) else {
                        return Err(self.error_here(format!(
                            "too many initializers for `struct {struct_name}`"
                        )));
                    };
                    stores.extend(
                        self.parse_struct_initializer_field(target_pointer.clone(), field)?,
                    );
                    field_index += 1;
                }
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
                            "expected `,` or `}}` in `struct {struct_name}` initializer, got {}",
                            token.describe()
                        )));
                    }
                    None => {
                        return Err(self.error_here(format!(
                            "expected `,` or `}}` in `struct {struct_name}` initializer, got end of input"
                        )));
                    }
                }
            }
        }
        self.expect(Token::RBrace)?;

        if has_designated_initializer {
            // A designated initializer may arrive out of declaration order or
            // initialize only a nested leaf. Start from a complete zero value
            // so every omitted member has the same semantics as a positional
            // initializer, then apply explicit stores in source order.
            let mut zero_stores =
                self.zero_struct_initializer_level(target_pointer.clone(), struct_name);
            zero_stores.extend(stores);
            stores = zero_stores;
        } else {
            for field in fields.iter().skip(field_index) {
                stores.extend(self.zero_struct_initializer_field(target_pointer.clone(), field));
            }
        }
        Ok(stores)
    }

    /// Parses one or more `.field` designators for a struct initializer. The
    /// returned pointer addresses the parent of the final field, so the
    /// ordinary field initializer path can retain all of its nested aggregate
    /// and scalar-array handling.
    fn parse_struct_field_designator(
        &mut self,
        target_pointer: C0Expression,
        struct_name: &str,
        root_fields: &[C0StructField],
    ) -> Result<(usize, C0Expression, C0StructField), C0SyntaxError> {
        let mut current_struct_name = struct_name.to_string();
        let mut parent_pointer = target_pointer;
        let mut root_index = None;

        loop {
            self.expect(Token::Dot)?;
            let field_name = self.expect_ident("struct field designator")?;
            let layout = self.structs.get(&current_struct_name).ok_or_else(|| {
                self.error_here(format!(
                    "unknown struct declaration `{current_struct_name}`"
                ))
            })?;
            let field = layout.fields.get(&field_name).cloned().ok_or_else(|| {
                self.error_here(format!(
                    "struct `{current_struct_name}` has no field `{field_name}`"
                ))
            })?;

            if root_index.is_none() {
                root_index = root_fields
                    .iter()
                    .position(|candidate| candidate.offset_bytes == field.offset_bytes);
            }

            if self.peek() == Some(&Token::LBracket) {
                return Err(
                    self.error_here("array designators in struct initializers are not supported")
                );
            }
            if self.peek() == Some(&Token::Dot) {
                if field.array_element_width.is_some()
                    || field.c_type != C0Type::Int32
                    || field.struct_name.is_none()
                {
                    return Err(self
                        .error_here("nested field designators require an embedded struct field"));
                }
                parent_pointer = offset_field_pointer(parent_pointer, field.offset_bytes);
                current_struct_name = field
                    .struct_name
                    .expect("embedded struct designator has a struct name");
                continue;
            }

            self.expect(Token::Equal)?;
            let root_index = root_index.expect("root field designator belongs to the root layout");
            return Ok((root_index, parent_pointer, field));
        }
    }

    fn parse_struct_initializer_field(
        &mut self,
        target_pointer: C0Expression,
        field: &C0StructField,
    ) -> Result<Vec<C0Statement>, C0SyntaxError> {
        let field_pointer = offset_field_pointer(target_pointer, field.offset_bytes);
        if let Some(element_width) = field.array_element_width {
            let struct_name = field
                .struct_name
                .as_deref()
                .expect("embedded struct array has a struct name");
            let shape = field
                .array_shape
                .as_deref()
                .expect("embedded struct array has a shape");
            if self.peek() != Some(&Token::LBrace) {
                return Err(self.error_here(
                    "embedded struct array initializers require nested `{...}` groups",
                ));
            }
            return self.parse_embedded_struct_array_initializer_level(
                field_pointer,
                struct_name,
                shape,
                0,
                0,
                element_width,
            );
        }
        if field.c_type == C0Type::Int32 {
            if let Some(struct_name) = field.struct_name.as_deref() {
                if self.peek() != Some(&Token::LBrace) {
                    return Err(self.error_here(
                        "embedded struct initializers require a nested `{...}` group",
                    ));
                }
                return self.parse_struct_initializer_level(field_pointer, struct_name);
            }
        }

        if let Some((element_type, dimensions)) = struct_scalar_array_shape(field) {
            if self.peek() != Some(&Token::LBrace) {
                return Err(self.error_here(
                    "inline scalar array initializers require a nested `{...}` group",
                ));
            }
            let mut values = Vec::new();
            let zero = zero_initializer(element_type);
            self.parse_array_initializer_level("struct field", &dimensions, 0, &mut values, &zero)?;
            return Ok(values
                .into_iter()
                .enumerate()
                .map(|(index, value)| C0Statement::Store {
                    pointer: offset_field_pointer(
                        field_pointer.clone(),
                        u32::try_from(index)
                            .expect("validated struct array initializer index")
                            .checked_mul(element_type.abi_size_bytes())
                            .expect("validated struct array initializer offset"),
                    ),
                    value,
                    value_type: Some(element_type),
                })
                .collect());
        }

        let value = self.parse_expression()?;
        Ok(vec![C0Statement::Store {
            pointer: field_pointer,
            value,
            value_type: Some(field.c_type),
        }])
    }

    fn parse_embedded_struct_array_initializer_level(
        &mut self,
        target_pointer: C0Expression,
        struct_name: &str,
        dimensions: &[u32],
        depth: usize,
        flat_prefix: u32,
        element_width: u32,
    ) -> Result<Vec<C0Statement>, C0SyntaxError> {
        let child_count = dimensions[depth];
        self.expect(Token::LBrace)?;
        let mut stores = Vec::new();
        let mut next_child_index = 0u32;
        let mut initialized_children = BTreeSet::new();
        if self.peek() != Some(&Token::RBrace) {
            loop {
                let child_index = if self.peek() == Some(&Token::LBracket) {
                    self.position += 1;
                    let index =
                        self.parse_local_struct_array_designator(struct_name, depth, child_count)?;
                    self.expect(Token::Equal)?;
                    next_child_index = index
                        .checked_add(1)
                        .expect("validated local struct array designator index");
                    index
                } else {
                    let index = next_child_index;
                    next_child_index = next_child_index
                        .checked_add(1)
                        .expect("validated local struct array initializer index");
                    index
                };
                if child_index >= child_count {
                    return Err(
                        self.error_here("too many initializers for an embedded struct array")
                    );
                }
                initialized_children.insert(child_index);
                let flat_index = flat_prefix
                    .checked_mul(child_count)
                    .and_then(|index| index.checked_add(child_index))
                    .expect("validated embedded struct array initializer index");
                if depth + 1 == dimensions.len() {
                    if self.peek() != Some(&Token::LBrace) {
                        return Err(self.error_here(
                            "embedded struct array elements require nested `{...}` groups",
                        ));
                    }
                    stores.extend(
                        self.parse_struct_initializer_level(
                            offset_field_pointer(
                                target_pointer.clone(),
                                flat_index
                                    .checked_mul(element_width)
                                    .expect("validated embedded struct array initializer offset"),
                            ),
                            struct_name,
                        )?,
                    );
                } else {
                    if self.peek() != Some(&Token::LBrace) {
                        return Err(self.error_here(
                            "nested embedded struct array initializers require `{...}` groups",
                        ));
                    }
                    stores.extend(self.parse_embedded_struct_array_initializer_level(
                        target_pointer.clone(),
                        struct_name,
                        dimensions,
                        depth + 1,
                        flat_index,
                        element_width,
                    )?);
                }
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
                            "expected `,` or `}}` in embedded struct array initializer, got {}",
                            token.describe()
                        )));
                    }
                    None => {
                        return Err(self.error_here(
                            "expected `,` or `}` in embedded struct array initializer, got end of input",
                        ));
                    }
                }
            }
        }
        self.expect(Token::RBrace)?;

        for child_index in 0..child_count {
            if initialized_children.contains(&child_index) {
                continue;
            }
            let flat_index = flat_prefix
                .checked_mul(child_count)
                .and_then(|index| index.checked_add(child_index))
                .expect("validated embedded struct array initializer index");
            if depth + 1 == dimensions.len() {
                stores.extend(
                    self.zero_struct_initializer_level(
                        offset_field_pointer(
                            target_pointer.clone(),
                            flat_index
                                .checked_mul(element_width)
                                .expect("validated embedded struct array initializer offset"),
                        ),
                        struct_name,
                    ),
                );
            } else {
                stores.extend(self.zero_embedded_struct_array_initializer_level(
                    target_pointer.clone(),
                    struct_name,
                    dimensions,
                    depth + 1,
                    flat_index,
                    element_width,
                ));
            }
        }
        Ok(stores)
    }

    fn parse_local_struct_array_designator(
        &mut self,
        struct_name: &str,
        depth: usize,
        length: u32,
    ) -> Result<u32, C0SyntaxError> {
        let index = match self.next() {
            Some(Token::Number(number)) => {
                let magnitude = parse_integer_literal_magnitude(&number).map_err(|reason| {
                    self.error_at_previous(format!(
                        "invalid local struct array designator index `{number}`: {reason}"
                    ))
                })?;
                u32::try_from(magnitude).map_err(|_| {
                    self.error_at_previous(format!(
                        "local struct array designator index `{number}` is out of range"
                    ))
                })?
            }
            Some(Token::CharLiteral(value)) => u32::from(value),
            Some(token) => {
                return Err(self.error_at_previous(format!(
                    "local struct array designators currently require integer literals, got {}",
                    token.describe()
                )));
            }
            None => {
                return Err(self.error_here(
                    "local struct array designators currently require an integer literal",
                ));
            }
        };
        self.expect(Token::RBracket)?;
        if index >= length {
            return Err(self.error_here(format!(
                "local struct array designator index `{index}` is out of bounds for `struct {struct_name}` dimension {depth} of length {length}"
            )));
        }
        Ok(index)
    }

    fn zero_struct_initializer_level(
        &self,
        target_pointer: C0Expression,
        struct_name: &str,
    ) -> Vec<C0Statement> {
        let mut fields = self
            .structs
            .get(struct_name)
            .expect("validated struct initializer has a layout")
            .fields
            .values()
            .cloned()
            .collect::<Vec<_>>();
        fields.sort_by_key(|field| field.offset_bytes);
        fields
            .iter()
            .flat_map(|field| self.zero_struct_initializer_field(target_pointer.clone(), field))
            .collect()
    }

    fn zero_struct_initializer_field(
        &self,
        target_pointer: C0Expression,
        field: &C0StructField,
    ) -> Vec<C0Statement> {
        let field_pointer = offset_field_pointer(target_pointer, field.offset_bytes);
        if let Some(element_width) = field.array_element_width {
            let struct_name = field
                .struct_name
                .as_deref()
                .expect("embedded struct array has a struct name");
            let shape = field
                .array_shape
                .as_deref()
                .expect("embedded struct array has a shape");
            return self.zero_embedded_struct_array_initializer_level(
                field_pointer,
                struct_name,
                shape,
                0,
                0,
                element_width,
            );
        }
        if field.c_type == C0Type::Int32 {
            if let Some(struct_name) = field.struct_name.as_deref() {
                return self.zero_struct_initializer_level(field_pointer, struct_name);
            }
        }

        if let Some((element_type, dimensions)) = struct_scalar_array_shape(field) {
            let element_count = dimensions.iter().product::<u32>();
            return (0..element_count)
                .map(|index| C0Statement::Store {
                    pointer: offset_field_pointer(
                        field_pointer.clone(),
                        index
                            .checked_mul(element_type.abi_size_bytes())
                            .expect("validated struct array initializer offset"),
                    ),
                    value: zero_initializer_value(element_type),
                    value_type: Some(element_type),
                })
                .collect();
        }

        vec![C0Statement::Store {
            pointer: field_pointer,
            value: zero_initializer_value(field.c_type),
            value_type: Some(field.c_type),
        }]
    }

    fn zero_embedded_struct_array_initializer_level(
        &self,
        target_pointer: C0Expression,
        struct_name: &str,
        dimensions: &[u32],
        depth: usize,
        flat_prefix: u32,
        element_width: u32,
    ) -> Vec<C0Statement> {
        let child_count = dimensions[depth];
        let mut stores = Vec::new();
        for child_index in 0..child_count {
            let flat_index = flat_prefix
                .checked_mul(child_count)
                .and_then(|index| index.checked_add(child_index))
                .expect("validated embedded struct array initializer index");
            if depth + 1 == dimensions.len() {
                stores.extend(
                    self.zero_struct_initializer_level(
                        offset_field_pointer(
                            target_pointer.clone(),
                            flat_index
                                .checked_mul(element_width)
                                .expect("validated embedded struct array initializer offset"),
                        ),
                        struct_name,
                    ),
                );
            } else {
                stores.extend(self.zero_embedded_struct_array_initializer_level(
                    target_pointer.clone(),
                    struct_name,
                    dimensions,
                    depth + 1,
                    flat_index,
                    element_width,
                ));
            }
        }
        stores
    }

    fn parse_local_declaration(&mut self) -> Result<C0Statement, C0SyntaxError> {
        let parsed_type = self.parse_type()?;
        if parsed_type.union_name.is_some() {
            return Err(self.error_here(
                    "tagged union locals are not supported; access an active scalar member through a struct pointer",
                ));
        }
        if parsed_type.c_type == C0Type::Void {
            return Err(self.error_here("void local declarations are not supported"));
        }
        if parsed_type.enum_name.is_some() {
            return Err(self.error_here(
                "enum local declarations are not supported; use enum values in struct fields",
            ));
        }
        if parsed_type.is_constant {
            return Err(self.error_here(
                "const-qualified local objects are not supported in this slice; use file-scope or static storage",
            ));
        }
        if parsed_type.is_volatile
            && (parsed_type.struct_name.is_some()
                || parsed_type.enum_name.is_some()
                || parsed_type.union_name.is_some()
                || (parsed_type.c_type.is_pointer() && !parsed_type.c_type.is_scalar_pointer()))
        {
            return Err(self.error_here(
                "the sequential volatile model supports scalar objects and pointers to scalar objects",
            ));
        }
        if parsed_type.is_volatile && self.peek() == Some(&Token::LParen) {
            return Err(self.error_here(
                "the small volatile model does not support volatile function-pointer objects",
            ));
        }
        if self.peek() == Some(&Token::LParen) {
            if parsed_type.is_constant || parsed_type.pointee_constant {
                return Err(self.error_here(
                    "const-qualified function-pointer declarations are not supported in this slice",
                ));
            }
            let Some((name, c_type, signature)) =
                self.parse_function_pointer_declarator(parsed_type)?
            else {
                unreachable!("function-pointer declarator starts with a parenthesis");
            };
            let kernel_name = self.declare_name(&name)?;
            self.variable_types.insert(kernel_name.clone(), c_type);
            self.variable_function_pointers
                .insert(kernel_name.clone(), signature.clone());
            let declaration = C0Statement::Declare {
                c_type,
                name: kernel_name.clone(),
                volatile: false,
                pointee_volatile: false,
                constant: false,
                pointee_constant: false,
            };
            let statement = if self.peek() == Some(&Token::Equal) {
                self.position += 1;
                let expression = self.parse_expression()?;
                self.validate_function_pointer_value(&signature, &expression)?;
                C0Statement::Seq(
                    Box::new(declaration),
                    Box::new(C0Statement::Assign {
                        name: kernel_name,
                        expression,
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
        loop {
            let source_name = self.expect_ident("local name")?;
            let name = self.declare_name(&source_name)?;
            let struct_value_layout =
                if struct_value_candidate && self.peek() != Some(&Token::LBracket) {
                    Some(
                        self.scalar_struct_value_layout(
                            parsed_type
                                .struct_name
                                .as_deref()
                                .expect("plain struct local carries its name"),
                        )?,
                    )
                } else {
                    None
                };
            if let Some(layout) = &struct_value_layout {
                let c_type = struct_value_type(layout);
                let struct_name = parsed_type
                    .struct_name
                    .clone()
                    .expect("plain struct local carries its name");
                self.variable_types.insert(name.clone(), c_type);
                self.variable_structs
                    .insert(name.clone(), struct_name.clone());
                self.variable_struct_values
                    .insert(name.clone(), struct_name.clone());
                let declaration = C0Statement::DeclareStructValue {
                    name: name.clone(),
                    layout: layout.clone(),
                };
                let statement = if self.peek() == Some(&Token::Equal) {
                    self.position += 1;
                    if self.peek() == Some(&Token::LBrace) {
                        let initializer =
                            self.parse_struct_value_initializer(&name, &struct_name)?;
                        C0Statement::Seq(Box::new(declaration), Box::new(initializer))
                    } else if matches!(self.peek(), Some(Token::Ident(_)))
                        && self.peek_next() == Some(&Token::LParen)
                    {
                        let source_name = self.expect_ident("function name")?;
                        let arguments = self.parse_call_arguments(Some(&source_name))?;
                        let call = self.call_assignment_statement(
                            name.clone(),
                            self.resolve_function_name(&source_name),
                            arguments,
                        )?;
                        C0Statement::Seq(Box::new(declaration), Box::new(call))
                    } else {
                        let expression = self.parse_expression_allow_direct_aggregate()?;
                        let copy = self.struct_value_copy_statement(&name, expression)?;
                        C0Statement::Seq(Box::new(declaration), Box::new(copy))
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
            let (mut c_type, array_shape) = self.parse_local_array_shape(&parsed_type)?;
            if parsed_type.is_volatile
                && (array_shape.is_some()
                    || matches!(
                        c_type,
                        C0Type::Int16Array(_)
                            | C0Type::UInt8Array(_)
                            | C0Type::UInt16Array(_)
                            | C0Type::UInt32Array(_)
                            | C0Type::Int64Array(_)
                            | C0Type::UInt64Array(_)
                            | C0Type::Int32Array(_)
                    ))
            {
                return Err(
                    self.error_here("the small volatile model does not support volatile arrays")
                );
            }
            if parsed_type.struct_name.is_some()
                && parsed_type.c_type == C0Type::Int32Pointer
                && array_shape.is_none()
                && self
                    .structs
                    .get(
                        parsed_type
                            .struct_name
                            .as_ref()
                            .expect("struct pointer has a struct name"),
                    )
                    .expect("struct pointer has a declaration")
                    .size_bytes
                    % 4
                    != 0
            {
                // Unaligned struct sizes cannot use the kernel's int32
                // pointer allocation width. Use a byte-addressed local for
                // those allocations; aligned structs retain the historical
                // pointer representation.
                c_type = C0Type::UInt8Pointer;
            }
            self.variable_types.insert(name.clone(), c_type);
            let object_volatile = parsed_type.is_volatile && !c_type.is_pointer();
            let pointee_volatile = parsed_type.is_volatile && c_type.is_scalar_pointer();
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
                if is_plain_struct_type(&parsed_type) && c_type == parsed_type.c_type {
                    return Err(self.error_here("only pointer-to-struct types are supported"));
                }
                if c_type != parsed_type.c_type
                    && !matches!(c_type, C0Type::UInt8Array(_) | C0Type::UInt8Pointer)
                {
                    return Err(self.error_here("local arrays of struct type are not supported"));
                }
                self.variable_structs.insert(
                    name.clone(),
                    parsed_type
                        .struct_name
                        .clone()
                        .expect("struct_name checked above"),
                );
            }
            let declaration = C0Statement::Declare {
                c_type,
                name: name.clone(),
                volatile: object_volatile,
                pointee_volatile,
                constant: object_constant,
                pointee_constant,
            };
            let statement = if self.peek() == Some(&Token::Equal) {
                self.position += 1;
                if matches!(
                    c_type,
                    C0Type::Int32Array(_)
                        | C0Type::UInt8Array(_)
                        | C0Type::Float32Array(_)
                        | C0Type::Float64Array(_)
                ) {
                    let initializer = if let Some(struct_name) = parsed_type.struct_name.as_deref()
                    {
                        let dimensions = array_shape.as_deref().expect(
                            "local struct array initializers retain their declared dimensions",
                        );
                        self.parse_local_struct_array_initializer(&name, struct_name, dimensions)?
                    } else {
                        self.parse_local_array_initializer(&name, c_type, array_shape.as_deref())?
                    };
                    C0Statement::Seq(Box::new(declaration), Box::new(initializer))
                } else if matches!(self.peek(), Some(Token::Ident(_)))
                    && self.peek_next() == Some(&Token::LParen)
                {
                    let call_start = self.position;
                    let source_name = self.expect_ident("function name")?;
                    let arguments = self.parse_call_arguments(Some(&source_name))?;
                    if matches!(self.peek(), Some(Token::Comma | Token::Semicolon)) {
                        let call = self.call_assignment_statement(
                            name.clone(),
                            self.resolve_function_name(&source_name),
                            arguments,
                        )?;
                        C0Statement::Seq(Box::new(declaration), Box::new(call))
                    } else {
                        self.position = call_start;
                        let expression = self.parse_expression()?;
                        self.validate_struct_pointer_assignment(
                            self.variable_structs.get(&name),
                            Some(c_type),
                            &expression,
                        )?;
                        self.reject_discarded_const_pointer(c_type, pointee_constant, &expression)?;
                        C0Statement::Seq(
                            Box::new(declaration),
                            Box::new(C0Statement::Assign { name, expression }),
                        )
                    }
                } else {
                    let expression = self.parse_expression()?;
                    self.validate_struct_pointer_assignment(
                        self.variable_structs.get(&name),
                        Some(c_type),
                        &expression,
                    )?;
                    self.reject_discarded_const_pointer(c_type, pointee_constant, &expression)?;
                    C0Statement::Seq(
                        Box::new(declaration),
                        Box::new(C0Statement::Assign { name, expression }),
                    )
                }
            } else {
                declaration
            };
            declarations.push(statement);
            if self.peek() != Some(&Token::Comma) {
                break;
            }
            self.position += 1;
        }
        self.expect(Token::Semicolon)?;
        Ok(balanced_statement_sequence(declarations).unwrap_or(C0Statement::Skip))
    }

    fn parse_static_local_declaration(&mut self) -> Result<C0Statement, C0SyntaxError> {
        self.expect_ident_spelling("static")?;
        let parsed_type = self.parse_type()?;
        if parsed_type.is_volatile
            && (parsed_type.struct_name.is_some()
                || parsed_type.enum_name.is_some()
                || parsed_type.union_name.is_some()
                || (parsed_type.c_type.is_pointer() && !parsed_type.c_type.is_scalar_pointer()))
        {
            return Err(self.error_here(
                "the sequential volatile model supports scalar objects and pointers to scalar objects",
            ));
        }
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
                || !matches!(
                    parsed_type.c_type,
                    C0Type::Int16
                        | C0Type::Int32
                        | C0Type::UInt8
                        | C0Type::UInt16
                        | C0Type::UInt32
                        | C0Type::Float32
                        | C0Type::Float64
                )
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
                    let length = self.parse_static_array_length(&source_name)?;
                    let initializer = if self.peek() == Some(&Token::Equal) {
                        self.position += 1;
                        self.parse_aggregate_array_initializer(
                            &source_name,
                            struct_name,
                            layout,
                            length,
                        )?
                    } else {
                        Vec::new()
                    };
                    let bytes = length
                        .checked_mul(layout.size_bytes())
                        .expect("validated static aggregate array size");
                    self.variable_types
                        .insert(kernel_name.clone(), C0Type::UInt8Array(bytes));
                    self.variable_array_shapes
                        .insert(kernel_name.clone(), vec![length]);
                    self.variable_structs
                        .insert(kernel_name.clone(), struct_name.clone());
                    if parsed_type.is_constant {
                        self.variable_constants.insert(kernel_name.clone());
                    }
                    self.static_aggregate_arrays.insert(
                        kernel_name.clone(),
                        C0StaticAggregateArray::new(
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
                    .insert(kernel_name.clone(), struct_value_type(layout));
                self.variable_structs
                    .insert(kernel_name.clone(), struct_name.clone());
                if parsed_type.is_constant {
                    self.variable_constants.insert(kernel_name.clone());
                }
                self.static_aggregates.insert(
                    kernel_name.clone(),
                    C0StaticAggregate::new(
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
                let length = self.parse_static_array_length(&source_name)?;
                let initializer = if self.peek() == Some(&Token::Equal) {
                    self.position += 1;
                    self.parse_static_array_initializer(&source_name, parsed_type.c_type, length)?
                } else {
                    vec![zero_initializer(parsed_type.c_type); length as usize]
                };
                self.variable_types.insert(
                    kernel_name.clone(),
                    array_type_for_element(parsed_type.c_type, length)
                        .expect("validated static array element type"),
                );
                if parsed_type.is_constant {
                    self.variable_constants.insert(kernel_name.clone());
                }
                self.static_arrays.insert(
                    kernel_name.clone(),
                    C0StaticArray::new(
                        source_name,
                        kernel_name.clone(),
                        parsed_type.c_type,
                        length,
                        initializer,
                    )
                    .with_constant(parsed_type.is_constant),
                );
            } else {
                self.variable_types
                    .insert(kernel_name.clone(), parsed_type.c_type);
                if parsed_type.is_constant {
                    self.variable_constants.insert(kernel_name.clone());
                }
                if parsed_type.pointee_constant {
                    self.variable_pointee_constants.insert(kernel_name.clone());
                }
                let initializer = if self.peek() == Some(&Token::Equal) {
                    self.position += 1;
                    let initializer = self.parse_expression()?;
                    validate_static_initializer(self, parsed_type.c_type, &initializer)?;
                    initializer
                } else {
                    zero_initializer(parsed_type.c_type)
                };
                self.static_locals.insert(
                    kernel_name.clone(),
                    C0StaticLocal::new(source_name, kernel_name, parsed_type.c_type, initializer)
                        .with_volatile(parsed_type.is_volatile)
                        .with_constant(parsed_type.is_constant),
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
        Ok(C0Statement::Skip)
    }

    fn parse_static_array_length(&mut self, name: &str) -> Result<u32, C0SyntaxError> {
        self.expect(Token::LBracket)?;
        let length = match self.next() {
            Some(Token::Number(number)) => {
                let length = parse_integer_literal_magnitude(&number).map_err(|reason| {
                    self.error_at_previous(format!(
                        "invalid static local array length `{number}`: {reason}"
                    ))
                })?;
                u32::try_from(length).map_err(|_| {
                    self.error_at_previous(format!(
                        "static local array length `{number}` is out of range"
                    ))
                })?
            }
            Some(token) => {
                return Err(self.error_at_previous(format!(
                    "expected positive static local array length, got {}",
                    token.describe()
                )));
            }
            None => {
                return Err(self
                    .error_here("expected positive static local array length, got end of input"));
            }
        };
        if length == 0 {
            return Err(self.error_at_previous(format!(
                "static local array `{name}` must have positive length"
            )));
        }
        self.expect(Token::RBracket)?;
        if self.peek() == Some(&Token::LBracket) {
            return Err(
                self.error_here("multidimensional static local arrays are not supported yet")
            );
        }
        Ok(length)
    }

    fn parse_static_array_initializer(
        &mut self,
        name: &str,
        element_type: C0Type,
        length: u32,
    ) -> Result<Vec<C0Expression>, C0SyntaxError> {
        self.expect(Token::LBrace)?;
        let mut values = Vec::new();
        if self.peek() != Some(&Token::RBrace) {
            loop {
                if values.len() == length as usize {
                    return Err(self.error_here(format!(
                        "too many initializers for static local array `{name}[{length}]`"
                    )));
                }
                let value = self.parse_expression()?;
                validate_static_initializer(self, element_type, &value)?;
                values.push(value);
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
                            "expected `,` or `}}` in static local array `{name}` initializer, got {}",
                            token.describe()
                        )));
                    }
                    None => {
                        return Err(self.error_here(format!(
                            "expected `,` or `}}` in static local array `{name}` initializer, got end of input"
                        )));
                    }
                }
            }
        }
        self.expect(Token::RBrace)?;
        values.resize(length as usize, zero_initializer(element_type));
        Ok(values)
    }

    fn struct_value_copy_statement(
        &mut self,
        target: &str,
        expression: C0Expression,
    ) -> Result<C0Statement, C0SyntaxError> {
        let target_struct = self
            .variable_struct_values
            .get(target)
            .cloned()
            .ok_or_else(|| self.error_here(format!("`{target}` is not a struct value")))?;
        self.aggregate_copy_statement(
            C0Expression::Variable(target.to_string()),
            &target_struct,
            expression,
        )
    }

    fn aggregate_copy_statement(
        &mut self,
        target_pointer: C0Expression,
        target_struct: &str,
        expression: C0Expression,
    ) -> Result<C0Statement, C0SyntaxError> {
        let (prefix, expression) = self.lower_expression_calls(expression)?;
        let copy = self.aggregate_copy_statement_raw(target_pointer, target_struct, expression)?;
        Ok(prepend_statements(prefix, copy))
    }

    fn aggregate_copy_statement_raw(
        &self,
        target_pointer: C0Expression,
        target_struct: &str,
        expression: C0Expression,
    ) -> Result<C0Statement, C0SyntaxError> {
        let (source_pointer, source_struct) = match expression {
            C0Expression::Variable(name) => {
                let source_struct =
                    self.variable_struct_values
                        .get(&name)
                        .cloned()
                        .ok_or_else(|| {
                            self.error_here("aggregate copies require a struct value source")
                        })?;
                (C0Expression::Variable(name), source_struct)
            }
            C0Expression::AggregateAddress {
                pointer,
                struct_name,
            } => (*pointer, struct_name),
            C0Expression::Load(pointer) => {
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
        let mut stores = Vec::new();
        for field in layout.aggregate_fields() {
            let (element_type, element_count) = match field.c_type {
                C0Type::Int16
                | C0Type::Int32
                | C0Type::UInt8
                | C0Type::UInt16
                | C0Type::UInt32
                | C0Type::Int64
                | C0Type::UInt64
                | C0Type::Float32
                | C0Type::Float64 => (field.c_type, 1),
                C0Type::Int32Array(length) => (C0Type::Int32, length),
                C0Type::UInt8Array(length) => (C0Type::UInt8, length),
                C0Type::Float32Array(length) => (C0Type::Float32, length),
                C0Type::Float64Array(length) => (C0Type::Float64, length),
                C0Type::Int32Pointer
                | C0Type::UInt8Pointer
                | C0Type::Float32Pointer
                | C0Type::Float64Pointer
                | C0Type::Int32PointerPointer
                | C0Type::UInt8PointerPointer
                | C0Type::Float32PointerPointer
                | C0Type::Float64PointerPointer => (field.c_type, 1),
                _ => unreachable!("validated struct value field shape"),
            };
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
                stores.push(C0Statement::Store {
                    pointer: target_pointer,
                    value: C0Expression::Field {
                        pointer: Box::new(source_pointer),
                        field_type: element_type,
                        field_struct_name: None,
                        function_pointer_signature: None,
                        array_shape: None,
                    },
                    value_type: Some(element_type),
                });
            }
        }
        Ok(balanced_statement_sequence(stores).unwrap_or(C0Statement::Skip))
    }

    fn parse_for_initializer(&mut self) -> Result<C0Statement, C0SyntaxError> {
        if self.peek() == Some(&Token::Semicolon) {
            return Ok(C0Statement::Skip);
        }
        if self.is_type_start() {
            return self.parse_for_declaration_initializer();
        }

        let mut initializers = vec![self.parse_for_assignment_initializer()?];
        while self.peek() == Some(&Token::Comma) {
            self.position += 1;
            initializers.push(self.parse_for_assignment_initializer()?);
        }
        Ok(balanced_statement_sequence(initializers).unwrap_or(C0Statement::Skip))
    }

    fn parse_for_declaration_initializer(&mut self) -> Result<C0Statement, C0SyntaxError> {
        let parsed_type = self.parse_type()?;
        if parsed_type.union_name.is_some() {
            return Err(self.error_here(
                "tagged union loop locals are not supported; access an active scalar member through a struct pointer",
            ));
        }
        if parsed_type.c_type == C0Type::Void {
            return Err(self.error_here("void for-loop locals are not supported"));
        }
        if parsed_type.enum_name.is_some() {
            return Err(self.error_here(
                "enum local declarations are not supported; use enum values in struct fields",
            ));
        }
        if parsed_type.is_constant {
            return Err(
                self.error_here("const-qualified for-loop locals are not supported in this slice")
            );
        }
        if is_plain_struct_type(&parsed_type) {
            return Err(self.error_here("only pointer-to-struct types are supported"));
        }
        if parsed_type.is_volatile && parsed_type.c_type.is_pointer() {
            return Err(self.error_here(
                "the small volatile model supports only direct scalar integer objects",
            ));
        }
        let mut initializers = Vec::new();
        loop {
            let source_name = self.expect_ident("for-loop local name")?;
            let name = self.declare_name(&source_name)?;
            self.variable_types.insert(name.clone(), parsed_type.c_type);
            let object_volatile = parsed_type.is_volatile && !parsed_type.c_type.is_pointer();
            let pointee_volatile =
                parsed_type.is_volatile && parsed_type.c_type.is_scalar_pointer();
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
            let expression = self.parse_expression()?;
            self.reject_discarded_const_pointer(parsed_type.c_type, pointee_constant, &expression)?;
            initializers.push(C0Statement::Seq(
                Box::new(C0Statement::Declare {
                    c_type: parsed_type.c_type,
                    name: name.clone(),
                    volatile: object_volatile,
                    pointee_volatile,
                    constant: object_constant,
                    pointee_constant,
                }),
                Box::new(C0Statement::Assign { name, expression }),
            ));
            if self.peek() != Some(&Token::Comma) {
                break;
            }
            self.position += 1;
        }
        Ok(balanced_statement_sequence(initializers).unwrap_or(C0Statement::Skip))
    }

    fn parse_for_assignment_initializer(&mut self) -> Result<C0Statement, C0SyntaxError> {
        let Some(Token::Ident(source_name)) = self.next() else {
            return Err(
                self.error_here("expected assignment target in for-loop initializer".to_string())
            );
        };
        let name = self.resolve_name(&source_name);
        if self.variable_is_constant(&name) {
            return Err(self.error_here(format!(
                "cannot assign to const-qualified lvalue `{source_name}`"
            )));
        }
        self.expect(Token::Equal)?;
        let expression = self.parse_expression()?;
        self.validate_function_pointer_assignment(&name, &expression)?;
        Ok(C0Statement::Assign { name, expression })
    }

    fn parse_scalar_update_statement(
        &mut self,
        context: &str,
    ) -> Result<C0Statement, C0SyntaxError> {
        let prefix_operator = match self.peek() {
            Some(Token::PlusPlus | Token::MinusMinus) => self.next(),
            _ => None,
        };
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
        let name = self.resolve_name(&source_name);
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
        if self.variable_struct_values.contains_key(&name) {
            if operator != Token::Equal {
                return Err(self.error_here(format!(
                    "struct value `{name}` only supports whole-value assignment"
                )));
            }
            if matches!(self.peek(), Some(Token::Ident(_)))
                && self.peek_next() == Some(&Token::LParen)
            {
                let source_name = self.expect_ident("function name")?;
                let arguments = self.parse_call_arguments(Some(&source_name))?;
                return self.call_assignment_statement(
                    name,
                    self.resolve_function_name(&source_name),
                    arguments,
                );
            }
            let expression = self.parse_expression_allow_direct_aggregate()?;
            return self.struct_value_copy_statement(&name, expression);
        }
        let expression = match operator {
            Token::Equal => {
                if matches!(self.peek(), Some(Token::Ident(_)))
                    && self.peek_next() == Some(&Token::LParen)
                {
                    let call_start = self.position;
                    let source_name = self.expect_ident("function name")?;
                    let arguments = self.parse_call_arguments(Some(&source_name))?;
                    if self.peek() == Some(&Token::Semicolon) {
                        return self.call_assignment_statement(
                            name,
                            self.resolve_function_name(&source_name),
                            arguments,
                        );
                    }
                    self.position = call_start;
                }
                {
                    let expression = self.parse_expression()?;
                    self.reject_discarded_const_pointer(
                        self.variable_types
                            .get(&name)
                            .copied()
                            .unwrap_or(C0Type::Void),
                        self.variable_pointee_is_constant(&name),
                        &expression,
                    )?;
                    self.validate_function_pointer_assignment(&name, &expression)?;
                    expression
                }
            }
            Token::PlusPlus => C0Expression::Add(
                Box::new(C0Expression::Variable(name.clone())),
                Box::new(C0Expression::Int32Literal(1)),
            ),
            Token::MinusMinus => C0Expression::Subtract(
                Box::new(C0Expression::Variable(name.clone())),
                Box::new(C0Expression::Int32Literal(1)),
            ),
            Token::PlusEqual => C0Expression::Add(
                Box::new(C0Expression::Variable(name.clone())),
                Box::new(self.parse_expression()?),
            ),
            Token::MinusEqual => C0Expression::Subtract(
                Box::new(C0Expression::Variable(name.clone())),
                Box::new(self.parse_expression()?),
            ),
            Token::StarEqual => C0Expression::Multiply(
                Box::new(C0Expression::Variable(name.clone())),
                Box::new(self.parse_expression()?),
            ),
            Token::SlashEqual => C0Expression::Divide(
                Box::new(C0Expression::Variable(name.clone())),
                Box::new(self.parse_expression()?),
            ),
            Token::PercentEqual => C0Expression::Remainder(
                Box::new(C0Expression::Variable(name.clone())),
                Box::new(self.parse_expression()?),
            ),
            Token::ShiftLeftEqual => C0Expression::ShiftLeft(
                Box::new(C0Expression::Variable(name.clone())),
                Box::new(self.parse_expression()?),
            ),
            Token::ShiftRightEqual => C0Expression::ShiftRight(
                Box::new(C0Expression::Variable(name.clone())),
                Box::new(self.parse_expression()?),
            ),
            Token::AmpEqual => C0Expression::BitwiseAnd(
                Box::new(C0Expression::Variable(name.clone())),
                Box::new(self.parse_expression()?),
            ),
            Token::PipeEqual => C0Expression::BitwiseOr(
                Box::new(C0Expression::Variable(name.clone())),
                Box::new(self.parse_expression()?),
            ),
            Token::CaretEqual => C0Expression::BitwiseXor(
                Box::new(C0Expression::Variable(name.clone())),
                Box::new(self.parse_expression()?),
            ),
            token => {
                return Err(self.error_here(format!(
                    "expected scalar update operator in {context}, got {}",
                    token.describe()
                )));
            }
        };
        if operator == Token::Equal {
            self.validate_struct_pointer_assignment(
                self.variable_structs.get(&name),
                self.variable_types.get(&name).copied(),
                &expression,
            )?;
            self.validate_function_pointer_assignment(&name, &expression)?;
        }
        Ok(C0Statement::Assign { name, expression })
    }

    fn parse_update_statement(&mut self, context: &str) -> Result<C0Statement, C0SyntaxError> {
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
    ) -> Result<C0Statement, C0SyntaxError> {
        let target = if self.peek() == Some(&Token::Star) {
            self.position += 1;
            let pointer = self.parse_unary()?;
            self.dereference_expression(pointer)
        } else {
            self.parse_postfix()?
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
            if let C0Expression::AggregateAddress {
                pointer,
                struct_name,
            } = &target
            {
                let value = self.parse_expression_allow_direct_aggregate()?;
                return self.aggregate_copy_statement(pointer.as_ref().clone(), struct_name, value);
            }
            let value = self.parse_expression()?;
            return match target {
                C0Expression::Load(pointer) => {
                    if let Some(struct_name) = self.struct_pointer_pointer_name(&pointer) {
                        self.validate_struct_pointer_value(&struct_name, &value)?;
                    }
                    Ok(C0Statement::Store {
                        pointer: *pointer,
                        value,
                        value_type: None,
                    })
                }
                C0Expression::Field {
                    pointer,
                    field_type,
                    field_struct_name,
                    function_pointer_signature,
                    ..
                } => {
                    if let Some(signature) = function_pointer_signature {
                        self.validate_function_pointer_value(&signature, &value)?;
                    }
                    if let Some(struct_name) = field_struct_name {
                        if matches!(field_type, C0Type::Int32Pointer | C0Type::UInt8Pointer) {
                            self.validate_struct_pointer_value(&struct_name, &value)?;
                        } else if matches!(
                            field_type,
                            C0Type::Int16PointerPointer
                                | C0Type::UInt16PointerPointer
                                | C0Type::Int32PointerPointer
                                | C0Type::UInt8PointerPointer
                                | C0Type::UInt32PointerPointer
                                | C0Type::Int64PointerPointer
                                | C0Type::UInt64PointerPointer
                                | C0Type::Float32PointerPointer
                                | C0Type::Float64PointerPointer
                        ) {
                            self.validate_struct_pointer_pointer_value(&struct_name, &value)?;
                        }
                    }
                    Ok(C0Statement::Store {
                        pointer: *pointer,
                        value,
                        value_type: Some(field_type),
                    })
                }
                C0Expression::AggregateAddress { .. } => unreachable!(
                    "aggregate assignment is handled before scalar memory lvalue matching"
                ),
                C0Expression::UnionAddress { .. } => {
                    Err(self.error_here("assigning to a tagged union value is not supported"))
                }
                C0Expression::UnionField { .. } => {
                    Err(self.error_here("writing tagged union members is not supported"))
                }
                C0Expression::Index(base, index) => Ok(C0Statement::Store {
                    pointer: C0Expression::Add(base, index),
                    value,
                    value_type: None,
                }),
                target => Err(self.error_here(format!(
                    "expected memory lvalue assignment target in {context}, got {target:?}"
                ))),
            };
        }

        if matches!(target, C0Expression::UnionField { .. }) {
            return Err(self.error_here(
                "writing tagged union members is not supported; union accesses are read-only",
            ));
        }

        let increment = matches!(operator, Token::PlusPlus | Token::MinusMinus);
        let operator = match operator {
            Token::PlusPlus | Token::PlusEqual => C0UpdateOperator::Add,
            Token::MinusMinus | Token::MinusEqual => C0UpdateOperator::Subtract,
            Token::StarEqual => C0UpdateOperator::Multiply,
            Token::SlashEqual => C0UpdateOperator::Divide,
            Token::PercentEqual => C0UpdateOperator::Remainder,
            Token::ShiftLeftEqual => C0UpdateOperator::ShiftLeft,
            Token::ShiftRightEqual => C0UpdateOperator::ShiftRight,
            Token::AmpEqual => C0UpdateOperator::BitwiseAnd,
            Token::PipeEqual => C0UpdateOperator::BitwiseOr,
            Token::CaretEqual => C0UpdateOperator::BitwiseXor,
            token => {
                return Err(self.error_here(format!(
                    "expected memory lvalue update operator in {context}, got {}",
                    token.describe()
                )));
            }
        };
        let operand = if increment {
            C0Expression::Int32Literal(1)
        } else {
            self.parse_expression()?
        };
        Ok(C0Statement::Update {
            target,
            operator,
            operand,
        })
    }

    fn prefix_starts_memory_lvalue(&self) -> bool {
        self.peek_n(1) == Some(&Token::Star)
            || matches!(self.peek_n(1), Some(Token::Ident(_)))
                && matches!(self.peek_n(2), Some(Token::LBracket | Token::Arrow))
    }

    fn parse_for_step(&mut self) -> Result<C0Statement, C0SyntaxError> {
        if self.peek() == Some(&Token::RParen) {
            return Ok(C0Statement::Skip);
        }
        let mut steps = vec![self.parse_update_statement("for-loop step")?];
        while self.peek() == Some(&Token::Comma) {
            self.position += 1;
            steps.push(self.parse_update_statement("for-loop step")?);
        }
        Ok(balanced_statement_sequence(steps).unwrap_or(C0Statement::Skip))
    }

    fn call_assignment_statement(
        &self,
        target: String,
        function_name: String,
        arguments: Vec<C0Expression>,
    ) -> Result<C0Statement, C0SyntaxError> {
        if function_name == "realloc" {
            if arguments.len() != 2 {
                return Err(self.error_here(format!(
                    "`realloc` expects two arguments, got {}",
                    arguments.len()
                )));
            }
            return Ok(C0Statement::CallAssign {
                target,
                function_name,
                arguments,
            });
        }
        if !matches!(function_name.as_str(), "malloc" | "calloc") {
            if self.function_declarations.contains_key(&function_name) {
                self.validate_struct_pointer_assignment(
                    self.variable_structs.get(&target),
                    self.variable_types.get(&target).copied(),
                    &C0Expression::Call {
                        function_name: function_name.clone(),
                        arguments: arguments.clone(),
                        position: None,
                    },
                )?;
            }
            return Ok(C0Statement::CallAssign {
                target,
                function_name,
                arguments,
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
                    C0Expression::SizeOfStruct { name, .. } => name == target_struct,
                    C0Expression::SizeOfType {
                        c_type: C0Type::Int32,
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
                    Some(C0Type::UInt8Pointer) => matches!(
                        element_size,
                        C0Expression::Int32Literal(1)
                            | C0Expression::SizeOfType {
                                c_type: C0Type::UInt8,
                                struct_name: None,
                                ..
                            }
                    ),
                    Some(
                        C0Type::Int16Pointer
                        | C0Type::UInt16Pointer
                        | C0Type::Int32Pointer
                        | C0Type::UInt32Pointer
                        | C0Type::Int64Pointer
                        | C0Type::UInt64Pointer
                        | C0Type::Float32Pointer
                        | C0Type::Float64Pointer,
                    ) => {
                        let target_element = self
                            .variable_types
                            .get(&target)
                            .copied()
                            .and_then(C0Type::pointee_type)
                            .expect("data pointer target has a pointee type");
                        matches!(
                            element_size,
                            C0Expression::Int32Literal(bytes)
                                if *bytes == target_element.abi_size_bytes()
                        ) || matches!(
                            element_size,
                            C0Expression::SizeOfType {
                                c_type,
                                struct_name: None,
                                ..
                            } if *c_type == target_element
                        )
                    }
                    Some(
                        C0Type::Int16PointerPointer
                        | C0Type::UInt16PointerPointer
                        | C0Type::Int32PointerPointer
                        | C0Type::UInt8PointerPointer
                        | C0Type::UInt32PointerPointer
                        | C0Type::Int64PointerPointer
                        | C0Type::UInt64PointerPointer
                        | C0Type::Float32PointerPointer
                        | C0Type::Float64PointerPointer,
                    ) => matches!(
                        element_size,
                        C0Expression::Int32Literal(8)
                            | C0Expression::SizeOfType {
                                c_type: C0Type::Int16Pointer
                                    | C0Type::UInt16Pointer
                                    | C0Type::Int32Pointer
                                    | C0Type::UInt8Pointer
                                    | C0Type::UInt32Pointer
                                    | C0Type::Int64Pointer
                                    | C0Type::UInt64Pointer
                                    | C0Type::Float32Pointer
                                    | C0Type::Float64Pointer,
                                struct_name: None,
                                ..
                            }
                    ),
                    _ => matches!(
                        element_size,
                        C0Expression::Int32Literal(4)
                            | C0Expression::SizeOfType {
                                c_type: C0Type::Int32,
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
            C0Expression::Multiply(Box::new(count.clone()), Box::new(element_size.clone()))
        } else {
            let [bytes] = arguments.as_slice() else {
                return Err(self.error_here(format!(
                    "`malloc` expects one byte-count argument, got {}",
                    arguments.len()
                )));
            };
            bytes.clone()
        };
        Ok(C0Statement::HeapAllocate {
            target,
            bytes,
            zeroed,
        })
    }

    fn parse_expression(&mut self) -> Result<C0Expression, C0SyntaxError> {
        let expression = self.parse_conditional()?;
        if self.expression_contains_aggregate(&expression) {
            return Err(self.aggregate_expression_error());
        }
        Ok(expression)
    }

    fn parse_expression_allow_direct_aggregate(&mut self) -> Result<C0Expression, C0SyntaxError> {
        let expression = self.parse_conditional()?;
        if self.expression_contains_aggregate(&expression)
            && self.aggregate_struct_name(&expression).is_none()
        {
            return Err(self.aggregate_expression_error());
        }
        Ok(expression)
    }

    fn aggregate_expression_error(&self) -> C0SyntaxError {
        self.error_here(
            "embedded struct fields are only supported through member access or whole-struct lvalue copies; struct values are not scalar expressions, and tagged union values are not runtime aggregates",
        )
    }

    fn aggregate_struct_name(&self, expression: &C0Expression) -> Option<String> {
        match expression {
            C0Expression::Variable(name) => self.variable_struct_values.get(name).cloned(),
            C0Expression::Call { function_name, .. } => self
                .function_declaration(function_name)
                .and_then(|function| function.return_struct_name.clone()),
            C0Expression::IndirectCall { signature, .. } => signature.return_struct_name.clone(),
            C0Expression::AggregateAddress { struct_name, .. } => Some(struct_name.clone()),
            C0Expression::Field {
                field_type: C0Type::Int32,
                field_struct_name: Some(struct_name),
                ..
            } => Some(struct_name.clone()),
            C0Expression::Field { .. } => None,
            C0Expression::Load(pointer) => self.struct_pointer_name(pointer),
            C0Expression::Conditional {
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
            C0Expression::UnionAddress { .. }
            | C0Expression::UnionField { .. }
            | C0Expression::Void
            | C0Expression::FunctionAddress(_)
            | C0Expression::Int32Literal(_)
            | C0Expression::UInt8Literal(_)
            | C0Expression::UInt32Literal(_)
            | C0Expression::Int64Literal(_)
            | C0Expression::UInt64Literal(_)
            | C0Expression::Float32Literal(_)
            | C0Expression::Float64Literal(_)
            | C0Expression::SizeOfStruct { .. }
            | C0Expression::SizeOfUnion { .. }
            | C0Expression::SizeOfType { .. }
            | C0Expression::Cast { .. }
            | C0Expression::FloatNegate(_)
            | C0Expression::FloatClassification { .. }
            | C0Expression::AddressOf(_)
            | C0Expression::PointerOffsetBytes { .. }
            | C0Expression::LessThan(_, _)
            | C0Expression::LessEqual(_, _)
            | C0Expression::GreaterThan(_, _)
            | C0Expression::GreaterEqual(_, _)
            | C0Expression::Equal(_, _)
            | C0Expression::NotEqual(_, _)
            | C0Expression::Not(_)
            | C0Expression::And(_, _)
            | C0Expression::Or(_, _)
            | C0Expression::Add(_, _)
            | C0Expression::Subtract(_, _)
            | C0Expression::Multiply(_, _)
            | C0Expression::Divide(_, _)
            | C0Expression::Remainder(_, _)
            | C0Expression::ShiftLeft(_, _)
            | C0Expression::ShiftRight(_, _)
            | C0Expression::BitwiseAnd(_, _)
            | C0Expression::BitwiseOr(_, _)
            | C0Expression::BitwiseXor(_, _)
            | C0Expression::BitwiseNot(_)
            | C0Expression::Index(_, _) => None,
        }
    }

    fn expression_contains_aggregate(&self, expression: &C0Expression) -> bool {
        if contains_aggregate_value(expression) || self.aggregate_struct_name(expression).is_some()
        {
            return true;
        }
        match expression {
            C0Expression::Call { .. }
            | C0Expression::IndirectCall { .. }
            | C0Expression::AddressOf(_)
            | C0Expression::Void
            | C0Expression::Variable(_)
            | C0Expression::FunctionAddress(_)
            | C0Expression::Int32Literal(_)
            | C0Expression::UInt8Literal(_)
            | C0Expression::UInt32Literal(_)
            | C0Expression::Int64Literal(_)
            | C0Expression::UInt64Literal(_)
            | C0Expression::Float32Literal(_)
            | C0Expression::Float64Literal(_)
            | C0Expression::SizeOfStruct { .. }
            | C0Expression::SizeOfUnion { .. }
            | C0Expression::SizeOfType { .. }
            | C0Expression::AggregateAddress { .. }
            | C0Expression::UnionAddress { .. }
            | C0Expression::UnionField { .. } => false,
            C0Expression::Cast { expression, .. }
            | C0Expression::FloatNegate(expression)
            | C0Expression::FloatClassification { expression, .. }
            | C0Expression::PointerOffsetBytes {
                pointer: expression,
                ..
            }
            | C0Expression::Not(expression)
            | C0Expression::BitwiseNot(expression)
            | C0Expression::Load(expression) => self.expression_contains_aggregate(expression),
            C0Expression::Conditional {
                condition,
                then_branch,
                else_branch,
            } => {
                self.expression_contains_aggregate(condition)
                    || self.expression_contains_aggregate(then_branch)
                    || self.expression_contains_aggregate(else_branch)
            }
            C0Expression::Field { .. } => false,
            C0Expression::LessThan(left, right)
            | C0Expression::LessEqual(left, right)
            | C0Expression::GreaterThan(left, right)
            | C0Expression::GreaterEqual(left, right)
            | C0Expression::Equal(left, right)
            | C0Expression::NotEqual(left, right)
            | C0Expression::And(left, right)
            | C0Expression::Or(left, right)
            | C0Expression::Add(left, right)
            | C0Expression::Subtract(left, right)
            | C0Expression::Multiply(left, right)
            | C0Expression::Divide(left, right)
            | C0Expression::Remainder(left, right)
            | C0Expression::ShiftLeft(left, right)
            | C0Expression::ShiftRight(left, right)
            | C0Expression::BitwiseAnd(left, right)
            | C0Expression::BitwiseOr(left, right)
            | C0Expression::BitwiseXor(left, right)
            | C0Expression::Index(left, right) => {
                self.expression_contains_aggregate(left)
                    || self.expression_contains_aggregate(right)
            }
        }
    }

    fn fresh_synthesized_call_name(&mut self) -> String {
        loop {
            let name = format!("__click_call_result{}", self.next_synthesized_call);
            self.next_synthesized_call = self.next_synthesized_call.saturating_add(1);
            let already_used = self.variable_types.contains_key(&name)
                || self
                    .scopes
                    .iter()
                    .any(|scope| scope.iter().any(|binding| binding.kernel_name == name));
            if !already_used {
                return name;
            }
        }
    }

    fn fresh_synthesized_aggregate_name(&mut self) -> String {
        loop {
            let name = format!(
                "__click_aggregate_result{}",
                self.next_synthesized_aggregate
            );
            self.next_synthesized_aggregate = self.next_synthesized_aggregate.saturating_add(1);
            let already_used = self.variable_types.contains_key(&name)
                || self
                    .scopes
                    .iter()
                    .any(|scope| scope.iter().any(|binding| binding.kernel_name == name));
            if !already_used {
                return name;
            }
        }
    }

    fn declare_synthesized_aggregate(
        &mut self,
        struct_name: &str,
    ) -> Result<(String, C0StructLayout), C0SyntaxError> {
        let layout = self.structs.get(struct_name).cloned().ok_or_else(|| {
            self.error_here(format!("unknown struct declaration `{struct_name}`"))
        })?;
        let name = self.fresh_synthesized_aggregate_name();
        // This name is a lowering artifact, not a C declaration. Keep its
        // layout metadata in the parser-wide table so later lowering passes
        // can still recognize the generated aggregate expression after the
        // source block that introduced it has closed.
        self.variable_types
            .insert(name.clone(), struct_value_type(&layout));
        self.variable_structs
            .insert(name.clone(), struct_name.to_string());
        self.variable_struct_values
            .insert(name.clone(), struct_name.to_string());
        Ok((name, layout))
    }

    fn fresh_string_literal_name(&mut self, bytes: Vec<u8>) -> String {
        loop {
            let name = format!("__click_string_literal{}", self.next_string_literal);
            self.next_string_literal = self.next_string_literal.saturating_add(1);
            let already_used = self.variable_types.contains_key(&name)
                || self
                    .scopes
                    .iter()
                    .any(|scope| scope.iter().any(|binding| binding.kernel_name == name));
            if already_used {
                continue;
            }
            let length = bytes
                .len()
                .checked_add(1)
                .and_then(|length| u32::try_from(length).ok())
                .expect("validated string literal length fits in u32");
            self.variable_types
                .insert(name.clone(), C0Type::UInt8Array(length));
            self.variable_array_shapes
                .insert(name.clone(), vec![length]);
            self.string_literals
                .push(C0StringLiteral::new(name.clone(), bytes));
            return name;
        }
    }

    fn lower_call_expressions(
        &mut self,
        statement: C0Statement,
    ) -> Result<C0Statement, C0SyntaxError> {
        if !self.statement_contains_lowerable_expression(&statement) {
            return Ok(statement);
        }
        self.lower_statement_calls(statement)
    }

    /// Keep the common no-call path iterative. The parser deliberately
    /// represents long straight-line blocks as deeply nested sequences, so a
    /// recursive lowering walk here would consume the small parser stack even
    /// when there is nothing to lower.
    fn statement_contains_lowerable_expression(&self, statement: &C0Statement) -> bool {
        let mut statements = vec![statement];
        while let Some(statement) = statements.pop() {
            match statement {
                C0Statement::Assign { expression, .. }
                | C0Statement::HeapAllocate {
                    bytes: expression, ..
                }
                | C0Statement::HeapFree {
                    pointer: expression,
                }
                | C0Statement::Return(expression) => {
                    if self.expression_contains_lowerable_expression(expression) {
                        return true;
                    }
                }
                C0Statement::CallAssign { arguments, .. } | C0Statement::Call { arguments, .. } => {
                    if arguments
                        .iter()
                        .any(|expression| self.expression_contains_lowerable_expression(expression))
                    {
                        return true;
                    }
                }
                C0Statement::IndirectCall { .. } => return true,
                C0Statement::Store { pointer, value, .. } => {
                    if self.expression_contains_lowerable_expression(pointer)
                        || self.expression_contains_lowerable_expression(value)
                    {
                        return true;
                    }
                }
                C0Statement::Update {
                    target, operand, ..
                } => {
                    if self.expression_contains_lowerable_expression(target)
                        || self.expression_contains_lowerable_expression(operand)
                    {
                        return true;
                    }
                }
                C0Statement::Seq(first, second) => {
                    statements.push(first);
                    statements.push(second);
                }
                C0Statement::If {
                    condition,
                    then_branch,
                    else_branch,
                } => {
                    if self.expression_contains_lowerable_expression(condition) {
                        return true;
                    }
                    statements.push(then_branch);
                    statements.push(else_branch);
                }
                C0Statement::While { condition, body }
                | C0Statement::DoWhile { condition, body } => {
                    if self.expression_contains_lowerable_expression(condition) {
                        return true;
                    }
                    statements.push(body);
                }
                C0Statement::For {
                    initializer,
                    condition,
                    step,
                    body,
                } => {
                    if self.expression_contains_lowerable_expression(condition) {
                        return true;
                    }
                    statements.push(initializer);
                    statements.push(step);
                    statements.push(body);
                }
                C0Statement::Switch { expression, cases } => {
                    if self.expression_contains_lowerable_expression(expression) {
                        return true;
                    }
                    for case in cases {
                        statements.push(&case.body);
                    }
                }
                C0Statement::Skip
                | C0Statement::Break
                | C0Statement::Continue
                | C0Statement::Declare { .. }
                | C0Statement::DeclareStructValue { .. } => {}
            }
        }
        false
    }

    fn expression_contains_lowerable_expression(&self, expression: &C0Expression) -> bool {
        let mut expressions = vec![expression];
        while let Some(expression) = expressions.pop() {
            if self.aggregate_struct_name(expression).is_some() {
                return true;
            }
            match expression {
                C0Expression::Call { .. } | C0Expression::IndirectCall { .. } => return true,
                C0Expression::Cast { expression, .. }
                | C0Expression::FloatNegate(expression)
                | C0Expression::FloatClassification { expression, .. }
                | C0Expression::AddressOf(expression)
                | C0Expression::PointerOffsetBytes {
                    pointer: expression,
                    ..
                }
                | C0Expression::Not(expression)
                | C0Expression::BitwiseNot(expression)
                | C0Expression::Load(expression) => expressions.push(expression),
                C0Expression::AggregateAddress { pointer, .. }
                | C0Expression::UnionAddress { pointer, .. }
                | C0Expression::Field { pointer, .. }
                | C0Expression::UnionField { pointer, .. } => expressions.push(pointer),
                C0Expression::Conditional {
                    condition,
                    then_branch,
                    else_branch,
                } => {
                    expressions.push(condition);
                    expressions.push(then_branch);
                    expressions.push(else_branch);
                }
                C0Expression::LessThan(left, right)
                | C0Expression::LessEqual(left, right)
                | C0Expression::GreaterThan(left, right)
                | C0Expression::GreaterEqual(left, right)
                | C0Expression::Equal(left, right)
                | C0Expression::NotEqual(left, right)
                | C0Expression::And(left, right)
                | C0Expression::Or(left, right)
                | C0Expression::Add(left, right)
                | C0Expression::Subtract(left, right)
                | C0Expression::Multiply(left, right)
                | C0Expression::Divide(left, right)
                | C0Expression::Remainder(left, right)
                | C0Expression::ShiftLeft(left, right)
                | C0Expression::ShiftRight(left, right)
                | C0Expression::BitwiseAnd(left, right)
                | C0Expression::BitwiseOr(left, right)
                | C0Expression::BitwiseXor(left, right)
                | C0Expression::Index(left, right) => {
                    expressions.push(left);
                    expressions.push(right);
                }
                C0Expression::Void
                | C0Expression::Variable(_)
                | C0Expression::FunctionAddress(_)
                | C0Expression::Int32Literal(_)
                | C0Expression::UInt8Literal(_)
                | C0Expression::UInt32Literal(_)
                | C0Expression::Int64Literal(_)
                | C0Expression::UInt64Literal(_)
                | C0Expression::Float32Literal(_)
                | C0Expression::Float64Literal(_)
                | C0Expression::SizeOfStruct { .. }
                | C0Expression::SizeOfUnion { .. }
                | C0Expression::SizeOfType { .. } => {}
            }
        }
        false
    }

    fn lower_statement_calls(
        &mut self,
        statement: C0Statement,
    ) -> Result<C0Statement, C0SyntaxError> {
        match statement {
            C0Statement::Skip
            | C0Statement::Break
            | C0Statement::Continue
            | C0Statement::Declare { .. }
            | C0Statement::DeclareStructValue { .. } => Ok(statement),
            C0Statement::Assign { name, expression } => {
                let (prefix, expression) = self.lower_expression_calls(expression)?;
                Ok(prepend_statements(
                    prefix,
                    C0Statement::Assign { name, expression },
                ))
            }
            C0Statement::CallAssign {
                target,
                function_name,
                arguments,
            } => {
                let (prefix, arguments) = self.lower_call_arguments(arguments)?;
                Ok(prepend_statements(
                    prefix,
                    C0Statement::CallAssign {
                        target,
                        function_name,
                        arguments,
                    },
                ))
            }
            C0Statement::Call {
                function_name,
                arguments,
            } => {
                let (prefix, arguments) = self.lower_call_arguments(arguments)?;
                Ok(prepend_statements(
                    prefix,
                    C0Statement::Call {
                        function_name,
                        arguments,
                    },
                ))
            }
            C0Statement::IndirectCall {
                function,
                signature,
                arguments,
                position,
            } => {
                let (mut prefix, function) = self.lower_expression_calls(function)?;
                let (argument_prefix, arguments) = self.lower_call_arguments(arguments)?;
                if !prefix.is_empty() && !argument_prefix.is_empty() {
                    return Err(self.error_at_position(
                        position,
                        "multiple unsequenced calls in one expression are not supported",
                    ));
                }
                prefix.extend(argument_prefix);
                let (callback_name, callback_type) =
                    self.declare_synthesized_function_pointer(&signature);
                prefix.push(C0Statement::Declare {
                    c_type: callback_type,
                    name: callback_name.clone(),
                    volatile: false,
                    pointee_volatile: false,
                    constant: false,
                    pointee_constant: false,
                });
                prefix.push(C0Statement::Assign {
                    name: callback_name.clone(),
                    expression: function,
                });
                prefix.push(C0Statement::Call {
                    function_name: callback_name,
                    arguments,
                });
                Ok(balanced_statement_sequence(prefix)
                    .expect("indirect call has a non-empty prefix"))
            }
            C0Statement::HeapAllocate {
                target,
                bytes,
                zeroed,
            } => {
                let (prefix, bytes) = self.lower_expression_calls(bytes)?;
                Ok(prepend_statements(
                    prefix,
                    C0Statement::HeapAllocate {
                        target,
                        bytes,
                        zeroed,
                    },
                ))
            }
            C0Statement::HeapFree { pointer } => {
                let (prefix, pointer) = self.lower_expression_calls(pointer)?;
                Ok(prepend_statements(
                    prefix,
                    C0Statement::HeapFree { pointer },
                ))
            }
            C0Statement::Seq(first, second) => Ok(C0Statement::Seq(
                Box::new(self.lower_statement_calls(*first)?),
                Box::new(self.lower_statement_calls(*second)?),
            )),
            C0Statement::Return(expression) => {
                let (prefix, expression) = self.lower_expression_calls(expression)?;
                Ok(prepend_statements(prefix, C0Statement::Return(expression)))
            }
            C0Statement::Store {
                pointer,
                value,
                value_type,
            } => {
                let (prefix, pointer, value) = self.lower_expression_pair(pointer, value)?;
                Ok(prepend_statements(
                    prefix,
                    C0Statement::Store {
                        pointer,
                        value,
                        value_type,
                    },
                ))
            }
            C0Statement::Update {
                target,
                operator,
                operand,
            } => {
                let (prefix, target, operand) = self.lower_expression_pair(target, operand)?;
                Ok(prepend_statements(
                    prefix,
                    C0Statement::Update {
                        target,
                        operator,
                        operand,
                    },
                ))
            }
            C0Statement::If {
                condition,
                then_branch,
                else_branch,
            } => {
                let (prefix, condition) = self.lower_expression_calls(condition)?;
                let then_branch = self.lower_statement_calls(*then_branch)?;
                let else_branch = self.lower_statement_calls(*else_branch)?;
                Ok(prepend_statements(
                    prefix,
                    C0Statement::If {
                        condition,
                        then_branch: Box::new(then_branch),
                        else_branch: Box::new(else_branch),
                    },
                ))
            }
            C0Statement::While { condition, body } => {
                let (prefix, condition) = self.lower_expression_calls(condition)?;
                let body = self.lower_statement_calls(*body)?;
                if !prefix.is_empty() {
                    let guard = prepend_statements(
                        prefix,
                        C0Statement::If {
                            condition: C0Expression::Not(Box::new(condition)),
                            then_branch: Box::new(C0Statement::Break),
                            else_branch: Box::new(C0Statement::Skip),
                        },
                    );
                    return Ok(C0Statement::While {
                        condition: C0Expression::Int32Literal(1),
                        body: Box::new(C0Statement::Seq(Box::new(guard), Box::new(body))),
                    });
                }
                Ok(C0Statement::While {
                    condition,
                    body: Box::new(body),
                })
            }
            C0Statement::DoWhile { condition, body } => {
                let (prefix, condition) = self.lower_expression_calls(condition)?;
                let body = self.lower_statement_calls(*body)?;
                if prefix.is_empty() {
                    return Ok(C0Statement::DoWhile {
                        condition,
                        body: Box::new(body),
                    });
                }
                // A do-while condition runs after the first body execution,
                // and `continue` must also reach it. Use an unconditional
                // while shell whose tail checks the lowered condition. A
                // continue gets the same call-and-check sequence before
                // returning to the shell head; nested loops keep their own
                // continue targets.
                let body = prepend_condition_check_before_loop_continues(body, &prefix, &condition);
                let condition_check = prepend_statements(
                    prefix,
                    C0Statement::If {
                        condition: C0Expression::Not(Box::new(condition)),
                        then_branch: Box::new(C0Statement::Break),
                        else_branch: Box::new(C0Statement::Skip),
                    },
                );
                Ok(C0Statement::While {
                    condition: C0Expression::Int32Literal(1),
                    body: Box::new(C0Statement::Seq(Box::new(body), Box::new(condition_check))),
                })
            }
            C0Statement::For {
                initializer,
                condition,
                step,
                body,
            } => {
                let (prefix, condition) = self.lower_expression_calls(condition)?;
                let initializer = self.lower_statement_calls(*initializer)?;
                let step = self.lower_statement_calls(*step)?;
                let body = self.lower_statement_calls(*body)?;
                if !prefix.is_empty() {
                    let guard = prepend_statements(
                        prefix,
                        C0Statement::If {
                            condition: C0Expression::Not(Box::new(condition)),
                            then_branch: Box::new(C0Statement::Break),
                            else_branch: Box::new(C0Statement::Skip),
                        },
                    );
                    return Ok(C0Statement::For {
                        initializer: Box::new(initializer),
                        condition: C0Expression::Int32Literal(1),
                        step: Box::new(step),
                        body: Box::new(C0Statement::Seq(Box::new(guard), Box::new(body))),
                    });
                }
                Ok(C0Statement::For {
                    initializer: Box::new(initializer),
                    condition,
                    step: Box::new(step),
                    body: Box::new(body),
                })
            }
            C0Statement::Switch { expression, cases } => {
                let (prefix, expression) = self.lower_expression_calls(expression)?;
                let cases = cases
                    .into_iter()
                    .map(|case| {
                        Ok(C0SwitchCase {
                            value: case.value,
                            body: Box::new(self.lower_statement_calls(*case.body)?),
                        })
                    })
                    .collect::<Result<Vec<_>, C0SyntaxError>>()?;
                Ok(prepend_statements(
                    prefix,
                    C0Statement::Switch { expression, cases },
                ))
            }
        }
    }

    fn lower_call_arguments(
        &mut self,
        arguments: Vec<C0Expression>,
    ) -> Result<(Vec<C0Statement>, Vec<C0Expression>), C0SyntaxError> {
        let mut prefix = Vec::new();
        let mut lowered_arguments = Vec::with_capacity(arguments.len());
        for argument in arguments {
            let argument_position = first_embedded_call_position(&argument);
            let (argument_prefix, argument) = self.lower_expression_calls(argument)?;
            if !prefix.is_empty() && !argument_prefix.is_empty() {
                return Err(self.error_at_position(
                    argument_position,
                    "multiple unsequenced calls in one expression are not supported",
                ));
            }
            prefix.extend(argument_prefix);
            lowered_arguments.push(argument);
        }
        Ok((prefix, lowered_arguments))
    }

    fn lower_expression_pair(
        &mut self,
        left: C0Expression,
        right: C0Expression,
    ) -> Result<(Vec<C0Statement>, C0Expression, C0Expression), C0SyntaxError> {
        let right_position = first_embedded_call_position(&right);
        let (left_prefix, left) = self.lower_expression_calls(left)?;
        let (right_prefix, right) = self.lower_expression_calls(right)?;
        if !left_prefix.is_empty() && !right_prefix.is_empty() {
            return Err(self.error_at_position(
                right_position,
                "multiple unsequenced calls in one expression are not supported",
            ));
        }
        let mut prefix = left_prefix;
        prefix.extend(right_prefix);
        Ok((prefix, left, right))
    }

    fn lower_expression_calls(
        &mut self,
        expression: C0Expression,
    ) -> Result<(Vec<C0Statement>, C0Expression), C0SyntaxError> {
        match expression {
            C0Expression::Call {
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
                    let (target, layout) = self.declare_synthesized_aggregate(&struct_name)?;
                    prefix.push(C0Statement::DeclareStructValue {
                        name: target.clone(),
                        layout,
                    });
                    prefix.push(C0Statement::CallAssign {
                        target: target.clone(),
                        function_name,
                        arguments,
                    });
                    return Ok((prefix, C0Expression::Variable(target)));
                }
                let target = self.fresh_synthesized_call_name();
                if let Some(function) = self.function_declarations.get(&function_name) {
                    if let Some(struct_name) = &function.return_pointer_struct_name {
                        self.variable_types
                            .insert(target.clone(), function.return_type);
                        self.variable_structs
                            .insert(target.clone(), struct_name.clone());
                    }
                } else if let Some(signature) = self.variable_function_pointers.get(&function_name)
                    && let Some(struct_name) = &signature.return_struct_name
                {
                    self.variable_types
                        .insert(target.clone(), signature.return_type);
                    self.variable_structs
                        .insert(target.clone(), struct_name.clone());
                }
                prefix.push(C0Statement::CallAssign {
                    target: target.clone(),
                    function_name,
                    arguments,
                });
                Ok((prefix, C0Expression::Variable(target)))
            }
            C0Expression::IndirectCall {
                function,
                signature,
                arguments,
                position,
            } => self.lower_function_pointer_call(*function, signature, arguments, position),
            C0Expression::Cast {
                expression,
                c_type,
                struct_name,
            } => {
                let (prefix, expression) = self.lower_expression_calls(*expression)?;
                Ok((
                    prefix,
                    C0Expression::Cast {
                        expression: Box::new(expression),
                        c_type,
                        struct_name,
                    },
                ))
            }
            C0Expression::Conditional {
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
                    let (target, layout) = self.declare_synthesized_aggregate(&struct_name)?;
                    let then_copy = self.aggregate_copy_statement_raw(
                        C0Expression::Variable(target.clone()),
                        &struct_name,
                        then_branch,
                    )?;
                    let else_copy = self.aggregate_copy_statement_raw(
                        C0Expression::Variable(target.clone()),
                        &struct_name,
                        else_branch,
                    )?;
                    let then_statement = prepend_statements(then_prefix, then_copy);
                    let else_statement = prepend_statements(else_prefix, else_copy);
                    prefix.push(C0Statement::DeclareStructValue {
                        name: target.clone(),
                        layout,
                    });
                    prefix.push(C0Statement::If {
                        condition,
                        then_branch: Box::new(then_statement),
                        else_branch: Box::new(else_statement),
                    });
                    return Ok((prefix, C0Expression::Variable(target)));
                }
                if then_prefix.is_empty() && else_prefix.is_empty() {
                    return Ok((
                        prefix,
                        C0Expression::Conditional {
                            condition: Box::new(condition),
                            then_branch: Box::new(then_branch),
                            else_branch: Box::new(else_branch),
                        },
                    ));
                }
                let target = self.fresh_synthesized_call_name();
                let then_statement = prepend_statements(
                    then_prefix,
                    C0Statement::Assign {
                        name: target.clone(),
                        expression: then_branch,
                    },
                );
                let else_statement = prepend_statements(
                    else_prefix,
                    C0Statement::Assign {
                        name: target.clone(),
                        expression: else_branch,
                    },
                );
                // A conditional branch may not execute, so the result needs a
                // real stack binding before either arm assigns it. C0's
                // expression calls currently participate in scalar
                // expressions, whose temporary storage uses the int32 ABI
                // slot just like an ordinary scalar result.
                prefix.push(C0Statement::Declare {
                    c_type: C0Type::Int32,
                    name: target.clone(),
                    volatile: false,
                    pointee_volatile: false,
                    constant: false,
                    pointee_constant: false,
                });
                prefix.push(C0Statement::If {
                    condition,
                    then_branch: Box::new(then_statement),
                    else_branch: Box::new(else_statement),
                });
                Ok((prefix, C0Expression::Variable(target)))
            }
            C0Expression::FloatNegate(expression) => {
                let (prefix, expression) = self.lower_expression_calls(*expression)?;
                Ok((prefix, C0Expression::FloatNegate(Box::new(expression))))
            }
            C0Expression::FloatClassification {
                expression,
                classification,
            } => {
                let (prefix, expression) = self.lower_expression_calls(*expression)?;
                Ok((
                    prefix,
                    C0Expression::FloatClassification {
                        expression: Box::new(expression),
                        classification,
                    },
                ))
            }
            C0Expression::AddressOf(expression) => {
                let (prefix, expression) = self.lower_expression_calls(*expression)?;
                Ok((prefix, C0Expression::AddressOf(Box::new(expression))))
            }
            C0Expression::PointerOffsetBytes { pointer, bytes } => {
                let (prefix, pointer) = self.lower_expression_calls(*pointer)?;
                Ok((
                    prefix,
                    C0Expression::PointerOffsetBytes {
                        pointer: Box::new(pointer),
                        bytes,
                    },
                ))
            }
            C0Expression::Not(expression) => {
                let (prefix, expression) = self.lower_expression_calls(*expression)?;
                Ok((prefix, C0Expression::Not(Box::new(expression))))
            }
            C0Expression::BitwiseNot(expression) => {
                let (prefix, expression) = self.lower_expression_calls(*expression)?;
                Ok((prefix, C0Expression::BitwiseNot(Box::new(expression))))
            }
            C0Expression::Load(pointer) => {
                let (prefix, pointer) = self.lower_expression_calls(*pointer)?;
                Ok((prefix, C0Expression::Load(Box::new(pointer))))
            }
            C0Expression::AggregateAddress {
                pointer,
                struct_name,
            } => {
                let (prefix, pointer) = self.lower_expression_calls(*pointer)?;
                Ok((
                    prefix,
                    C0Expression::AggregateAddress {
                        pointer: Box::new(pointer),
                        struct_name,
                    },
                ))
            }
            C0Expression::Field {
                pointer,
                field_type,
                field_struct_name,
                function_pointer_signature,
                array_shape,
            } => {
                let (prefix, pointer) = self.lower_expression_calls(*pointer)?;
                Ok((
                    prefix,
                    C0Expression::Field {
                        pointer: Box::new(pointer),
                        field_type,
                        field_struct_name,
                        function_pointer_signature,
                        array_shape,
                    },
                ))
            }
            C0Expression::UnionField {
                pointer,
                field_type,
                union_name,
            } => {
                let (prefix, pointer) = self.lower_expression_calls(*pointer)?;
                Ok((
                    prefix,
                    C0Expression::UnionField {
                        pointer: Box::new(pointer),
                        field_type,
                        union_name,
                    },
                ))
            }
            C0Expression::LessThan(left, right) => {
                self.lower_binary_calls(*left, *right, C0Expression::LessThan)
            }
            C0Expression::LessEqual(left, right) => {
                self.lower_binary_calls(*left, *right, C0Expression::LessEqual)
            }
            C0Expression::GreaterThan(left, right) => {
                self.lower_binary_calls(*left, *right, C0Expression::GreaterThan)
            }
            C0Expression::GreaterEqual(left, right) => {
                self.lower_binary_calls(*left, *right, C0Expression::GreaterEqual)
            }
            C0Expression::Equal(left, right) => {
                self.lower_binary_calls(*left, *right, C0Expression::Equal)
            }
            C0Expression::NotEqual(left, right) => {
                self.lower_binary_calls(*left, *right, C0Expression::NotEqual)
            }
            C0Expression::Add(left, right) => {
                self.lower_binary_calls(*left, *right, C0Expression::Add)
            }
            C0Expression::Subtract(left, right) => {
                self.lower_binary_calls(*left, *right, C0Expression::Subtract)
            }
            C0Expression::Multiply(left, right) => {
                self.lower_binary_calls(*left, *right, C0Expression::Multiply)
            }
            C0Expression::Divide(left, right) => {
                self.lower_binary_calls(*left, *right, C0Expression::Divide)
            }
            C0Expression::Remainder(left, right) => {
                self.lower_binary_calls(*left, *right, C0Expression::Remainder)
            }
            C0Expression::ShiftLeft(left, right) => {
                self.lower_binary_calls(*left, *right, C0Expression::ShiftLeft)
            }
            C0Expression::ShiftRight(left, right) => {
                self.lower_binary_calls(*left, *right, C0Expression::ShiftRight)
            }
            C0Expression::BitwiseAnd(left, right) => {
                self.lower_binary_calls(*left, *right, C0Expression::BitwiseAnd)
            }
            C0Expression::BitwiseOr(left, right) => {
                self.lower_binary_calls(*left, *right, C0Expression::BitwiseOr)
            }
            C0Expression::BitwiseXor(left, right) => {
                self.lower_binary_calls(*left, *right, C0Expression::BitwiseXor)
            }
            C0Expression::And(left, right) => {
                self.lower_short_circuit_calls(*left, *right, C0Expression::And)
            }
            C0Expression::Or(left, right) => {
                self.lower_short_circuit_calls(*left, *right, C0Expression::Or)
            }
            C0Expression::Index(left, right) => {
                self.lower_binary_calls(*left, *right, C0Expression::Index)
            }
            expression => Ok((Vec::new(), expression)),
        }
    }

    fn lower_function_pointer_call(
        &mut self,
        function: C0Expression,
        signature: C0FunctionPointerSignature,
        arguments: Vec<C0Expression>,
        position: Option<SourcePosition>,
    ) -> Result<(Vec<C0Statement>, C0Expression), C0SyntaxError> {
        let (mut prefix, function) = self.lower_expression_calls(function)?;
        let (argument_prefix, arguments) = self.lower_call_arguments(arguments)?;
        if !prefix.is_empty() && !argument_prefix.is_empty() {
            return Err(self.error_at_position(
                position,
                "multiple unsequenced calls in one expression are not supported",
            ));
        }
        prefix.extend(argument_prefix);

        let (callback_name, callback_type) = self.declare_synthesized_function_pointer(&signature);
        prefix.push(C0Statement::Declare {
            c_type: callback_type,
            name: callback_name.clone(),
            volatile: false,
            pointee_volatile: false,
            constant: false,
            pointee_constant: false,
        });
        prefix.push(C0Statement::Assign {
            name: callback_name.clone(),
            expression: function,
        });
        let (call_prefix, result) = self.lower_expression_calls(C0Expression::Call {
            function_name: callback_name,
            arguments,
            position,
        })?;
        prefix.extend(call_prefix);
        Ok((prefix, result))
    }

    fn declare_synthesized_function_pointer(
        &mut self,
        signature: &C0FunctionPointerSignature,
    ) -> (String, C0Type) {
        let callback_name = self.fresh_synthesized_call_name();
        let callback_type = function_pointer_type(signature);
        self.variable_types
            .insert(callback_name.clone(), callback_type);
        self.variable_function_pointers
            .insert(callback_name.clone(), signature.clone());
        (callback_name, callback_type)
    }

    fn lower_binary_calls(
        &mut self,
        left: C0Expression,
        right: C0Expression,
        constructor: fn(Box<C0Expression>, Box<C0Expression>) -> C0Expression,
    ) -> Result<(Vec<C0Statement>, C0Expression), C0SyntaxError> {
        let (prefix, left, right) = self.lower_expression_pair(left, right)?;
        Ok((prefix, constructor(Box::new(left), Box::new(right))))
    }

    fn lower_short_circuit_calls(
        &mut self,
        left: C0Expression,
        right: C0Expression,
        constructor: fn(Box<C0Expression>, Box<C0Expression>) -> C0Expression,
    ) -> Result<(Vec<C0Statement>, C0Expression), C0SyntaxError> {
        let right_position = first_embedded_call_position(&right);
        let (left_prefix, left) = self.lower_expression_calls(left)?;
        let (right_prefix, right) = self.lower_expression_calls(right)?;
        if !right_prefix.is_empty() {
            return Err(self.error_at_position(
                right_position,
                "calls in the short-circuit right operand are not supported",
            ));
        }
        Ok((left_prefix, constructor(Box::new(left), Box::new(right))))
    }

    fn parse_conditional(&mut self) -> Result<C0Expression, C0SyntaxError> {
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
        let else_branch = self.parse_expression_allow_direct_aggregate()?;
        let then_struct = self.aggregate_struct_name(&then_branch);
        let else_struct = self.aggregate_struct_name(&else_branch);
        if then_struct != else_struct && (then_struct.is_some() || else_struct.is_some()) {
            return Err(
                self.error_here("conditional aggregate branches must have the same struct type")
            );
        }
        Ok(C0Expression::Conditional {
            condition: Box::new(condition),
            then_branch: Box::new(then_branch),
            else_branch: Box::new(else_branch),
        })
    }

    fn parse_call_arguments(
        &mut self,
        function_name: Option<&str>,
    ) -> Result<Vec<C0Expression>, C0SyntaxError> {
        self.expect(Token::LParen)?;
        let mut arguments = Vec::new();
        if self.peek() == Some(&Token::RParen) {
            self.position += 1;
            return Ok(arguments);
        }

        loop {
            let argument_index = arguments.len();
            let expression = self.parse_expression_allow_direct_aggregate()?;
            if let Some((parameter_type, struct_name, function_pointer_signature)) =
                self.call_parameter_metadata(function_name, argument_index)
            {
                if let Some(signature) = function_pointer_signature.as_ref() {
                    self.validate_function_pointer_value(signature, &expression)?;
                } else if let Some(struct_name) = struct_name.as_ref() {
                    self.validate_struct_pointer_assignment(
                        Some(struct_name),
                        Some(parameter_type),
                        &expression,
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
                && parameter.c_type.is_pointer()
                && !parameter.pointee_is_constant()
            {
                self.reject_discarded_const_pointer(
                    parameter.c_type,
                    parameter.pointee_is_constant(),
                    &expression,
                )?;
            }
            if known_scalar_parameter && self.expression_contains_aggregate(&expression) {
                return Err(self.aggregate_expression_error());
            }
            if function_name == Some("free") && self.expression_contains_aggregate(&expression) {
                return Err(self.error_here("`free` requires a pointer, not an aggregate value"));
            }
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

    fn parse_function_pointer_call_arguments(
        &mut self,
        signature: &C0FunctionPointerSignature,
    ) -> Result<Vec<C0Expression>, C0SyntaxError> {
        let arguments = self.parse_call_arguments(None)?;
        for (argument, parameter) in arguments.iter().zip(signature.parameters()) {
            let expected_struct = parameter.struct_name().map(str::to_owned);
            self.validate_struct_pointer_assignment(
                expected_struct.as_ref(),
                Some(parameter.c_type()),
                argument,
            )?;
        }
        Ok(arguments)
    }

    fn call_parameter_metadata(
        &self,
        function_name: Option<&str>,
        argument_index: usize,
    ) -> Option<(C0Type, Option<String>, Option<C0FunctionPointerSignature>)> {
        let function_name = function_name?;
        if let Some(signature) = self.variable_function_pointers.get(function_name) {
            return signature
                .parameters
                .get(argument_index)
                .map(|parameter| (parameter.c_type, parameter.struct_name.clone(), None));
        }
        self.function_declarations
            .get(function_name)
            .and_then(|function| function.parameters.get(argument_index))
            .map(|parameter| {
                (
                    parameter.c_type,
                    parameter.struct_name.clone(),
                    parameter.function_pointer_signature.clone(),
                )
            })
    }

    fn function_pointer_signature(
        &self,
        expression: &C0Expression,
    ) -> Option<C0FunctionPointerSignature> {
        match expression {
            C0Expression::Variable(name) => self.variable_function_pointers.get(name).cloned(),
            C0Expression::FunctionAddress(name) => self
                .function_declarations
                .get(name)
                .map(function_pointer_signature_from_header),
            C0Expression::Conditional {
                then_branch,
                else_branch,
                ..
            } => {
                let then_signature = self.function_pointer_signature(then_branch)?;
                let else_signature = self.function_pointer_signature(else_branch)?;
                (then_signature == else_signature).then_some(then_signature)
            }
            C0Expression::Cast { expression, .. } => self.function_pointer_signature(expression),
            C0Expression::Field {
                function_pointer_signature: Some(signature),
                ..
            } => Some(signature.clone()),
            _ => None,
        }
    }

    fn validate_function_pointer_value(
        &self,
        expected: &C0FunctionPointerSignature,
        expression: &C0Expression,
    ) -> Result<(), C0SyntaxError> {
        if matches!(expression, C0Expression::Int32Literal(0)) {
            return Ok(());
        }
        match self.function_pointer_signature(expression) {
            Some(actual) if actual == *expected => Ok(()),
            Some(actual) => Err(self.error_here(format!(
                "callback signature mismatch: expected {}, got {}",
                describe_function_pointer_signature(expected),
                describe_function_pointer_signature(&actual)
            ))),
            None if matches!(expression, C0Expression::FunctionAddress(_)) => Ok(()),
            None => Err(self.error_here("expected a compatible function pointer")),
        }
    }

    fn validate_function_pointer_assignment(
        &self,
        target: &str,
        expression: &C0Expression,
    ) -> Result<(), C0SyntaxError> {
        let Some(expected) = self.variable_function_pointers.get(target) else {
            return Ok(());
        };
        self.validate_function_pointer_value(expected, expression)
    }

    fn parse_logical_or(&mut self) -> Result<C0Expression, C0SyntaxError> {
        let mut expression = self.parse_logical_and()?;
        loop {
            expression = match self.peek() {
                Some(Token::PipePipe) => {
                    self.position += 1;
                    let right = self.parse_logical_and()?;
                    C0Expression::Or(Box::new(expression), Box::new(right))
                }
                _ => return Ok(expression),
            };
        }
    }

    fn parse_logical_and(&mut self) -> Result<C0Expression, C0SyntaxError> {
        let mut expression = self.parse_bitwise_or()?;
        loop {
            expression = match self.peek() {
                Some(Token::AmpAmp) => {
                    self.position += 1;
                    let right = self.parse_bitwise_or()?;
                    C0Expression::And(Box::new(expression), Box::new(right))
                }
                _ => return Ok(expression),
            };
        }
    }

    fn parse_bitwise_or(&mut self) -> Result<C0Expression, C0SyntaxError> {
        let mut expression = self.parse_bitwise_xor()?;
        while self.peek() == Some(&Token::Pipe) {
            self.position += 1;
            let right = self.parse_bitwise_xor()?;
            expression = C0Expression::BitwiseOr(Box::new(expression), Box::new(right));
        }
        Ok(expression)
    }

    fn parse_bitwise_xor(&mut self) -> Result<C0Expression, C0SyntaxError> {
        let mut expression = self.parse_bitwise_and()?;
        while self.peek() == Some(&Token::Caret) {
            self.position += 1;
            let right = self.parse_bitwise_and()?;
            expression = C0Expression::BitwiseXor(Box::new(expression), Box::new(right));
        }
        Ok(expression)
    }

    fn parse_bitwise_and(&mut self) -> Result<C0Expression, C0SyntaxError> {
        let mut expression = self.parse_equality()?;
        while self.peek() == Some(&Token::Amp) {
            self.position += 1;
            let right = self.parse_equality()?;
            expression = C0Expression::BitwiseAnd(Box::new(expression), Box::new(right));
        }
        Ok(expression)
    }

    /// Equality binds more loosely than the ordered comparisons, as in C
    /// (C11 6.5.8 and 6.5.9): `a == b < c` is `a == (b < c)`.
    fn parse_equality(&mut self) -> Result<C0Expression, C0SyntaxError> {
        let mut expression = self.parse_relational()?;
        loop {
            expression = match self.peek() {
                Some(Token::EqualEqual) => {
                    self.position += 1;
                    let right = self.parse_relational()?;
                    C0Expression::Equal(Box::new(expression), Box::new(right))
                }
                Some(Token::BangEqual) => {
                    self.position += 1;
                    let right = self.parse_relational()?;
                    C0Expression::NotEqual(Box::new(expression), Box::new(right))
                }
                _ => return Ok(expression),
            };
        }
    }

    fn parse_relational(&mut self) -> Result<C0Expression, C0SyntaxError> {
        let mut expression = self.parse_shift()?;
        loop {
            expression = match self.peek() {
                Some(Token::LessThan) => {
                    self.position += 1;
                    let right = self.parse_shift()?;
                    C0Expression::LessThan(Box::new(expression), Box::new(right))
                }
                Some(Token::LessEqual) => {
                    self.position += 1;
                    let right = self.parse_shift()?;
                    C0Expression::LessEqual(Box::new(expression), Box::new(right))
                }
                Some(Token::GreaterThan) => {
                    self.position += 1;
                    let right = self.parse_shift()?;
                    C0Expression::GreaterThan(Box::new(expression), Box::new(right))
                }
                Some(Token::GreaterEqual) => {
                    self.position += 1;
                    let right = self.parse_shift()?;
                    C0Expression::GreaterEqual(Box::new(expression), Box::new(right))
                }
                _ => return Ok(expression),
            };
        }
    }

    fn parse_shift(&mut self) -> Result<C0Expression, C0SyntaxError> {
        let mut expression = self.parse_add()?;
        loop {
            expression = match self.peek() {
                Some(Token::ShiftLeft) => {
                    self.position += 1;
                    let right = self.parse_add()?;
                    C0Expression::ShiftLeft(Box::new(expression), Box::new(right))
                }
                Some(Token::ShiftRight) => {
                    self.position += 1;
                    let right = self.parse_add()?;
                    C0Expression::ShiftRight(Box::new(expression), Box::new(right))
                }
                _ => return Ok(expression),
            };
        }
    }

    fn parse_add(&mut self) -> Result<C0Expression, C0SyntaxError> {
        let mut expression = self.parse_multiply()?;
        loop {
            expression = match self.peek() {
                Some(Token::Plus) => {
                    self.position += 1;
                    let right = self.parse_multiply()?;
                    self.scale_struct_pointer_arithmetic(expression, right, C0Expression::Add)?
                }
                Some(Token::Minus) => {
                    self.position += 1;
                    let right = self.parse_multiply()?;
                    self.scale_struct_pointer_arithmetic(expression, right, C0Expression::Subtract)?
                }
                _ => return Ok(expression),
            };
        }
    }

    fn scale_struct_pointer_arithmetic(
        &self,
        pointer: C0Expression,
        offset: C0Expression,
        constructor: fn(Box<C0Expression>, Box<C0Expression>) -> C0Expression,
    ) -> Result<C0Expression, C0SyntaxError> {
        let Some(struct_name) = self.struct_pointer_name(&pointer) else {
            return Ok(constructor(Box::new(pointer), Box::new(offset)));
        };
        let element_width = self
            .structs
            .get(&struct_name)
            .expect("struct pointer arithmetic has a declaration")
            .size_bytes;
        let byte_pointer = C0Expression::Cast {
            expression: Box::new(pointer),
            c_type: C0Type::UInt8Pointer,
            struct_name: None,
        };
        let byte_offset = C0Expression::Multiply(
            Box::new(offset),
            Box::new(C0Expression::Int32Literal(element_width)),
        );
        Ok(constructor(Box::new(byte_pointer), Box::new(byte_offset)))
    }

    fn parse_multiply(&mut self) -> Result<C0Expression, C0SyntaxError> {
        let mut expression = self.parse_unary()?;
        loop {
            let Some(operator) = self.peek() else {
                break;
            };
            let constructor = match operator {
                Token::Star => C0Expression::Multiply,
                Token::Slash => C0Expression::Divide,
                Token::Percent => C0Expression::Remainder,
                _ => break,
            };
            self.position += 1;
            let right = self.parse_unary()?;
            expression = constructor(Box::new(expression), Box::new(right));
        }
        Ok(expression)
    }

    fn parse_unary(&mut self) -> Result<C0Expression, C0SyntaxError> {
        if self.peek() == Some(&Token::LParen) && self.is_type_start_at(1) {
            self.position += 1;
            let parsed_type = self.parse_type()?;
            self.expect(Token::RParen)?;
            let (c_type, struct_name) = match (
                parsed_type.c_type,
                parsed_type.struct_name,
                parsed_type.union_name,
            ) {
                (
                    C0Type::Int16
                    | C0Type::Int32
                    | C0Type::UInt8
                    | C0Type::UInt16
                    | C0Type::UInt32
                    | C0Type::Int64
                    | C0Type::UInt64,
                    None,
                    None,
                ) => (parsed_type.c_type, None),
                (C0Type::Float32 | C0Type::Float64, None, None) => (parsed_type.c_type, None),
                // An object pointer target: the kernel accepts only a 64-bit
                // integer whose value carries pointer provenance, or zero.
                (c_type, struct_name, None)
                    if c_type.is_pointer() && !matches!(c_type, C0Type::FunctionPointer(_)) =>
                {
                    (c_type, struct_name)
                }
                _ => {
                    return Err(self.error_at_previous(
                        "casts support only modeled scalar integer or floating-point values, or object pointer types",
                    ));
                }
            };
            return Ok(C0Expression::Cast {
                expression: Box::new(self.parse_unary()?),
                c_type,
                struct_name,
            });
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
                let magnitude = parse_integer_literal_magnitude(&number).map_err(|reason| {
                    self.error_here(format!("invalid integer literal `{number}`: {reason}"))
                })?;
                let unsigned_suffix = integer_literal_has_unsigned_suffix(&number);
                let long_suffix = integer_literal_has_long_suffix(&number);
                if unsigned_suffix {
                    if long_suffix || magnitude > u32::MAX as u64 {
                        return Ok(C0Expression::UInt64Literal(0u64.wrapping_sub(magnitude)));
                    }
                    return Ok(C0Expression::UInt32Literal(
                        0u32.wrapping_sub(magnitude as u32),
                    ));
                }
                if magnitude > (i64::MAX as u64) + 1 {
                    return Err(self.error_here(format!(
                        "negative integer literal `-{number}` is out of range"
                    )));
                }
                if !long_suffix && magnitude <= (i32::MAX as u64) + 1 {
                    let value = (-(magnitude as i64) as i32) as u32;
                    return Ok(C0Expression::Int32Literal(value));
                }
                let value = if magnitude == (i64::MAX as u64) + 1 {
                    i64::MIN
                } else {
                    -(magnitude as i64)
                };
                return Ok(C0Expression::Int64Literal(value));
            }
            let expression = self.parse_unary()?;
            if let Some(expression) = negate_float_literal(expression.clone()) {
                return Ok(expression);
            }
            if self.expression_is_float(&expression) {
                return Ok(C0Expression::FloatNegate(Box::new(expression)));
            }
            return Ok(C0Expression::Subtract(
                Box::new(C0Expression::Int32Literal(0)),
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
            if let Some(Token::Ident(name)) = self.peek().cloned()
                && !self.variable_types.contains_key(&self.resolve_name(&name))
            {
                self.position += 1;
                return Ok(C0Expression::FunctionAddress(
                    self.resolve_function_name(&name),
                ));
            }
            let target = self.parse_unary()?;
            return Ok(C0Expression::AddressOf(Box::new(target)));
        }

        if self.peek() == Some(&Token::Bang) {
            self.position += 1;
            return Ok(C0Expression::Not(Box::new(self.parse_unary()?)));
        }

        if self.peek() == Some(&Token::Tilde) {
            self.position += 1;
            return Ok(C0Expression::BitwiseNot(Box::new(self.parse_unary()?)));
        }

        self.parse_postfix()
    }

    fn parse_postfix(&mut self) -> Result<C0Expression, C0SyntaxError> {
        let mut expression = self.parse_primary()?;
        loop {
            match self.peek() {
                Some(Token::LParen) => {
                    let call_position =
                        self.positions.get(self.position.saturating_sub(1)).copied();
                    if let C0Expression::Field {
                        function_pointer_signature: Some(signature),
                        ..
                    } = &expression
                    {
                        let signature = signature.clone();
                        let arguments = self.parse_function_pointer_call_arguments(&signature)?;
                        expression = C0Expression::IndirectCall {
                            function: Box::new(expression),
                            signature,
                            arguments,
                            position: call_position,
                        };
                        continue;
                    }
                    let source_name = match &expression {
                        C0Expression::Variable(name) => name.clone(),
                        _ => {
                            return Err(self.error_here(
                                "function calls currently require an identifier or function pointer",
                            ));
                        }
                    };
                    let arguments = self.parse_call_arguments(Some(&source_name))?;
                    if let Some(result) = parse_float_classification_call(&source_name, &arguments)
                    {
                        expression = result
                            .map_err(|reason| self.error_at_position(call_position, reason))?;
                        continue;
                    }
                    let function_name = self.resolve_function_name(&source_name);
                    expression = C0Expression::Call {
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
                        let offset = flatten_array_indices(indexes, &shape);
                        let stride = C0Expression::Multiply(
                            Box::new(offset),
                            Box::new(C0Expression::Int32Literal(element_width)),
                        );
                        expression = C0Expression::AggregateAddress {
                            pointer: Box::new(C0Expression::Add(
                                Box::new(expression),
                                Box::new(stride),
                            )),
                            struct_name,
                        };
                        continue;
                    }
                    if let Some(shape) = self.scalar_array_field_shape(&expression) {
                        let mut indexes = vec![first_index];
                        while self.peek() == Some(&Token::LBracket) {
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
                        let offset = flatten_array_indices(indexes, &shape);
                        expression = C0Expression::Index(Box::new(expression), Box::new(offset));
                        continue;
                    }
                    let shape = match &expression {
                        C0Expression::Variable(name) => {
                            self.variable_array_shapes.get(name).cloned()
                        }
                        _ => None,
                    };
                    if let Some(shape) = shape {
                        let name = match &expression {
                            C0Expression::Variable(name) => name,
                            _ => unreachable!("array shape belongs to a variable"),
                        };
                        let mut indexes = vec![first_index];
                        while self.peek() == Some(&Token::LBracket) {
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
                        let offset = flatten_array_indices(indexes, &shape);
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
                            C0Expression::Multiply(
                                Box::new(offset),
                                Box::new(C0Expression::Int32Literal(element_width)),
                            )
                        } else {
                            offset
                        };
                        expression = C0Expression::Index(Box::new(expression), Box::new(offset));
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
                                .expect("heap struct pointer has a declaration")
                                .size_bytes;
                            let byte_pointer = C0Expression::Cast {
                                expression: Box::new(expression),
                                c_type: C0Type::UInt8Pointer,
                                struct_name: None,
                            };
                            let offset = C0Expression::Multiply(
                                Box::new(first_index),
                                Box::new(C0Expression::Int32Literal(element_width)),
                            );
                            expression =
                                C0Expression::Index(Box::new(byte_pointer), Box::new(offset));
                            if self.peek() != Some(&Token::Dot) {
                                return Err(self.error_here(
                                    "array of struct values are only supported through field access",
                                ));
                            }
                        } else {
                            expression =
                                C0Expression::Index(Box::new(expression), Box::new(first_index));
                        }
                    }
                }
                Some(Token::Dot) | Some(Token::Arrow) => {
                    let dot = self.peek() == Some(&Token::Dot);
                    let union_base = match &expression {
                        C0Expression::UnionAddress { union_name, .. } => Some(union_name.clone()),
                        _ => None,
                    };
                    self.position += 1;
                    let field_name = self.expect_ident("field name")?;
                    let (
                        pointer,
                        field_type,
                        field_struct_name,
                        field_union_name,
                        function_pointer_signature,
                        array_shape,
                    ) = if dot {
                        let struct_value = matches!(
                            &expression,
                            C0Expression::Variable(name)
                                if self.variable_struct_values.contains_key(name)
                                    || (self.variable_structs.contains_key(name)
                                        && matches!(
                                            self.variable_types.get(name),
                                            Some(C0Type::UInt8Array(_))
                                        ))
                        );
                        if struct_value || matches!(&expression, C0Expression::UnionAddress { .. })
                        {
                            self.resolve_field_access(&expression, &field_name)?
                        } else {
                            self.resolve_array_struct_field_access(&expression, &field_name)?
                        }
                    } else {
                        self.resolve_field_access(&expression, &field_name)?
                    };
                    expression = if let Some(union_name) = union_base {
                        C0Expression::UnionField {
                            pointer: Box::new(pointer),
                            field_type,
                            union_name,
                        }
                    } else {
                        field_expression(
                            pointer,
                            field_type,
                            field_struct_name,
                            field_union_name,
                            function_pointer_signature,
                            array_shape,
                        )
                    };
                }
                _ => return Ok(expression),
            }
        }
    }

    fn struct_array_field_info(
        &self,
        expression: &C0Expression,
    ) -> Option<(String, u32, Vec<u32>)> {
        let C0Expression::Field {
            field_type: C0Type::UInt8Array(_),
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

    fn scalar_array_field_shape(&self, expression: &C0Expression) -> Option<Vec<u32>> {
        let C0Expression::Field {
            field_type: C0Type::Int32Array(_) | C0Type::UInt8Array(_),
            field_struct_name: None,
            array_shape: Some(shape),
            ..
        } = expression
        else {
            return None;
        };
        Some(shape.clone())
    }

    fn expression_is_float(&self, expression: &C0Expression) -> bool {
        match expression {
            C0Expression::Float32Literal(_)
            | C0Expression::Float64Literal(_)
            | C0Expression::FloatNegate(_) => true,
            C0Expression::Variable(name) => matches!(
                self.variable_types.get(name),
                Some(C0Type::Float32 | C0Type::Float64)
            ),
            C0Expression::Cast { c_type, .. } => {
                matches!(c_type, C0Type::Float32 | C0Type::Float64)
            }
            C0Expression::Field { field_type, .. }
            | C0Expression::UnionField { field_type, .. } => {
                matches!(field_type, C0Type::Float32 | C0Type::Float64)
            }
            C0Expression::Load(pointer) => self.expression_pointee_is_float(pointer),
            C0Expression::Index(base, _) => self.expression_pointee_is_float(base),
            C0Expression::Conditional {
                then_branch,
                else_branch,
                ..
            } => self.expression_is_float(then_branch) || self.expression_is_float(else_branch),
            C0Expression::Add(left, right)
            | C0Expression::Subtract(left, right)
            | C0Expression::Multiply(left, right)
            | C0Expression::Divide(left, right) => {
                self.expression_is_float(left) || self.expression_is_float(right)
            }
            C0Expression::Void
            | C0Expression::Call { .. }
            | C0Expression::IndirectCall { .. }
            | C0Expression::FunctionAddress(_)
            | C0Expression::FloatClassification { .. }
            | C0Expression::AddressOf(_)
            | C0Expression::PointerOffsetBytes { .. }
            | C0Expression::Int32Literal(_)
            | C0Expression::UInt8Literal(_)
            | C0Expression::UInt32Literal(_)
            | C0Expression::Int64Literal(_)
            | C0Expression::UInt64Literal(_)
            | C0Expression::SizeOfStruct { .. }
            | C0Expression::SizeOfUnion { .. }
            | C0Expression::SizeOfType { .. }
            | C0Expression::LessThan(_, _)
            | C0Expression::LessEqual(_, _)
            | C0Expression::GreaterThan(_, _)
            | C0Expression::GreaterEqual(_, _)
            | C0Expression::Equal(_, _)
            | C0Expression::NotEqual(_, _)
            | C0Expression::Not(_)
            | C0Expression::And(_, _)
            | C0Expression::Or(_, _)
            | C0Expression::Remainder(_, _)
            | C0Expression::ShiftLeft(_, _)
            | C0Expression::ShiftRight(_, _)
            | C0Expression::BitwiseAnd(_, _)
            | C0Expression::BitwiseOr(_, _)
            | C0Expression::BitwiseXor(_, _)
            | C0Expression::BitwiseNot(_)
            | C0Expression::AggregateAddress { .. }
            | C0Expression::UnionAddress { .. } => false,
        }
    }

    fn expression_pointee_is_float(&self, expression: &C0Expression) -> bool {
        let c_type = match expression {
            C0Expression::Variable(name) => self.variable_types.get(name).copied(),
            C0Expression::Field { field_type, .. }
            | C0Expression::UnionField { field_type, .. } => Some(*field_type),
            C0Expression::Cast { c_type, .. } => Some(*c_type),
            C0Expression::Index(base, _) => {
                return self.expression_pointee_is_float(base);
            }
            _ => None,
        };
        matches!(
            c_type,
            Some(
                C0Type::Float32Pointer
                    | C0Type::Float64Pointer
                    | C0Type::Float32Array(_)
                    | C0Type::Float64Array(_)
            )
        )
    }

    fn struct_pointer_name(&self, expression: &C0Expression) -> Option<String> {
        match expression {
            C0Expression::Variable(name)
                if matches!(
                    self.variable_types.get(name),
                    Some(C0Type::Int32Pointer | C0Type::UInt8Pointer)
                ) =>
            {
                self.variable_structs.get(name).cloned()
            }
            C0Expression::Call { function_name, .. } => self
                .function_declarations
                .get(function_name)
                .map(|function| function.return_pointer_struct_name.clone())
                .or_else(|| {
                    self.variable_function_pointers
                        .get(function_name)
                        .map(|signature| signature.return_struct_name.clone())
                })
                .flatten(),
            C0Expression::IndirectCall { signature, .. } => signature.return_struct_name.clone(),
            C0Expression::Field {
                field_type: C0Type::Int32Pointer | C0Type::UInt8Pointer,
                field_struct_name: Some(struct_name),
                ..
            } => Some(struct_name.clone()),
            C0Expression::Load(pointer) => self.struct_pointer_pointer_name(pointer),
            C0Expression::AddressOf(target) => match target.as_ref() {
                C0Expression::AggregateAddress { struct_name, .. } => Some(struct_name.clone()),
                C0Expression::Variable(name) => self.variable_struct_values.get(name).cloned(),
                _ => None,
            },
            C0Expression::Cast {
                struct_name: Some(struct_name),
                ..
            } => Some(struct_name.clone()),
            // A cast to another pointer type keeps the struct identity of
            // the pointer underneath; a cast to an integer does not, so an
            // `(unsigned long)p + 1` is integer arithmetic, not scaled
            // struct-pointer arithmetic.
            C0Expression::Cast {
                expression, c_type, ..
            } if c_type.is_pointer() => self.struct_pointer_name(expression),
            C0Expression::Add(left, _) | C0Expression::Subtract(left, _) => {
                self.struct_pointer_name(left)
            }
            _ => None,
        }
    }

    fn struct_pointer_pointer_name(&self, expression: &C0Expression) -> Option<String> {
        match expression {
            C0Expression::Variable(name)
                if matches!(
                    self.variable_types.get(name),
                    Some(
                        C0Type::Int16PointerPointer
                            | C0Type::UInt16PointerPointer
                            | C0Type::Int32PointerPointer
                            | C0Type::UInt8PointerPointer
                            | C0Type::UInt32PointerPointer
                            | C0Type::Int64PointerPointer
                            | C0Type::UInt64PointerPointer
                            | C0Type::Float32PointerPointer
                            | C0Type::Float64PointerPointer
                    )
                ) =>
            {
                self.variable_structs.get(name).cloned()
            }
            C0Expression::Call { function_name, .. } => self
                .function_declarations
                .get(function_name)
                .map(|function| function.return_pointer_struct_name.clone())
                .or_else(|| {
                    self.variable_function_pointers
                        .get(function_name)
                        .map(|signature| signature.return_struct_name.clone())
                })
                .flatten(),
            C0Expression::IndirectCall { signature, .. } => signature.return_struct_name.clone(),
            C0Expression::Field {
                field_type:
                    C0Type::Int16PointerPointer
                    | C0Type::UInt16PointerPointer
                    | C0Type::Int32PointerPointer
                    | C0Type::UInt8PointerPointer
                    | C0Type::UInt32PointerPointer
                    | C0Type::Int64PointerPointer
                    | C0Type::UInt64PointerPointer
                    | C0Type::Float32PointerPointer
                    | C0Type::Float64PointerPointer,
                field_struct_name: Some(struct_name),
                ..
            } => Some(struct_name.clone()),
            C0Expression::AddressOf(target) => match target.as_ref() {
                C0Expression::Variable(name)
                    if matches!(
                        self.variable_types.get(name),
                        Some(C0Type::Int32Pointer | C0Type::UInt8Pointer)
                    ) =>
                {
                    self.variable_structs.get(name).cloned()
                }
                C0Expression::Field {
                    field_type: C0Type::Int32Pointer | C0Type::UInt8Pointer,
                    field_struct_name: Some(struct_name),
                    ..
                } => Some(struct_name.clone()),
                C0Expression::Load(_) => self.struct_pointer_name(target),
                _ => None,
            },
            C0Expression::Cast { expression, .. } => self.struct_pointer_pointer_name(expression),
            C0Expression::Add(left, _) | C0Expression::Subtract(left, _) => {
                self.struct_pointer_pointer_name(left)
            }
            _ => None,
        }
    }

    fn validate_struct_pointer_value(
        &self,
        expected_struct: &str,
        expression: &C0Expression,
    ) -> Result<(), C0SyntaxError> {
        if matches!(expression, C0Expression::Int32Literal(0)) {
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
        expression: &C0Expression,
    ) -> Result<(), C0SyntaxError> {
        if matches!(expression, C0Expression::Int32Literal(0)) {
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

    fn validate_struct_pointer_assignment(
        &self,
        expected_struct: Option<&String>,
        target_type: Option<C0Type>,
        expression: &C0Expression,
    ) -> Result<(), C0SyntaxError> {
        let Some(expected_struct) = expected_struct else {
            return Ok(());
        };
        match target_type {
            Some(
                C0Type::Int32Pointer
                | C0Type::UInt8Pointer
                | C0Type::Float32Pointer
                | C0Type::Float64Pointer,
            ) => self.validate_struct_pointer_value(expected_struct, expression),
            Some(
                C0Type::Int16PointerPointer
                | C0Type::UInt16PointerPointer
                | C0Type::Int32PointerPointer
                | C0Type::UInt8PointerPointer
                | C0Type::UInt32PointerPointer
                | C0Type::Int64PointerPointer
                | C0Type::UInt64PointerPointer
                | C0Type::Float32PointerPointer
                | C0Type::Float64PointerPointer,
            ) => self.validate_struct_pointer_pointer_value(expected_struct, expression),
            _ => Ok(()),
        }
    }

    fn dereference_expression(&self, pointer: C0Expression) -> C0Expression {
        if let Some(struct_name) = self.struct_pointer_name(&pointer) {
            C0Expression::AggregateAddress {
                pointer: Box::new(pointer),
                struct_name,
            }
        } else {
            C0Expression::Load(Box::new(pointer))
        }
    }

    fn resolve_field_access(
        &self,
        base: &C0Expression,
        field_name: &str,
    ) -> Result<
        (
            C0Expression,
            C0Type,
            Option<String>,
            Option<String>,
            Option<C0FunctionPointerSignature>,
            Option<Vec<u32>>,
        ),
        C0SyntaxError,
    > {
        let (struct_name, union_name) = match base {
            C0Expression::Variable(base_name) => {
                (self.variable_structs.get(base_name).cloned(), None)
            }
            C0Expression::Field {
                field_struct_name, ..
            } => {
                if self.struct_array_field_info(base).is_some() {
                    return Err(self.error_here(
                        "arrays of embedded structs require an index before field access",
                    ));
                }
                (field_struct_name.clone(), None)
            }
            C0Expression::Load(_) => (self.struct_pointer_name(base), None),
            C0Expression::AggregateAddress { struct_name, .. } => (Some(struct_name.clone()), None),
            C0Expression::UnionAddress { union_name, .. } => (None, Some(union_name)),
            C0Expression::Cast {
                struct_name: Some(struct_name),
                ..
            } => (Some(struct_name.clone()), None),
            _ => (None, None),
        };
        if let Some(struct_name) = struct_name {
            let layout = self.structs.get(&struct_name).ok_or_else(|| {
                self.error_here(format!("unknown struct declaration `{struct_name}`"))
            })?;
            let field = layout.fields.get(field_name).ok_or_else(|| {
                self.error_here(format!(
                    "struct `{struct_name}` has no field `{field_name}`"
                ))
            })?;
            return Ok((
                offset_field_pointer(base.clone(), field.offset_bytes),
                field.c_type,
                field.struct_name.clone(),
                field.union_name.clone(),
                field.function_pointer_signature.clone(),
                field.array_shape.clone(),
            ));
        }
        if let Some(union_name) = union_name {
            let layout = self.unions.get(union_name).ok_or_else(|| {
                self.error_here(format!("unknown union declaration `{union_name}`"))
            })?;
            let field = layout.fields.get(field_name).ok_or_else(|| {
                self.error_here(format!("union `{union_name}` has no member `{field_name}`"))
            })?;
            return Ok((
                offset_field_pointer(base.clone(), field.offset_bytes),
                field.c_type,
                None,
                None,
                None,
                None,
            ));
        }
        Err(self.error_here(format!(
            "cannot access field `{field_name}` through a non-struct-pointer expression"
        )))
    }

    fn resolve_array_struct_field_access(
        &self,
        base: &C0Expression,
        field_name: &str,
    ) -> Result<
        (
            C0Expression,
            C0Type,
            Option<String>,
            Option<String>,
            Option<C0FunctionPointerSignature>,
            Option<Vec<u32>>,
        ),
        C0SyntaxError,
    > {
        let (element_pointer, struct_name) = match base {
            C0Expression::Index(array, index) => {
                let struct_name = match array.as_ref() {
                    C0Expression::Variable(name)
                        if self.variable_array_shapes.contains_key(name) =>
                    {
                        self.variable_structs.get(name).cloned()
                    }
                    C0Expression::Cast {
                        expression, c_type, ..
                    } if *c_type == C0Type::UInt8Pointer
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
                (C0Expression::Add(array.clone(), index.clone()), struct_name)
            }
            C0Expression::AggregateAddress {
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
        Ok((
            offset_field_pointer(element_pointer, field.offset_bytes),
            field.c_type,
            field.struct_name.clone(),
            field.union_name.clone(),
            field.function_pointer_signature.clone(),
            field.array_shape.clone(),
        ))
    }

    fn parse_primary(&mut self) -> Result<C0Expression, C0SyntaxError> {
        if self.peek_ident() == Some("sizeof") && self.peek_next() == Some(&Token::LParen) {
            self.position += 2;
            if self.peek_ident() == Some("struct") {
                self.position += 1;
                let name = self.expect_ident("struct name")?;
                self.expect(Token::RParen)?;
                let bytes = self
                    .structs
                    .get(&name)
                    .ok_or_else(|| self.error_here(format!("unknown struct declaration `{name}`")))?
                    .size_bytes;
                return Ok(C0Expression::SizeOfStruct { name, bytes });
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
                return Ok(C0Expression::SizeOfUnion { name, bytes });
            }
            let parsed_type = self.parse_type()?;
            self.expect(Token::RParen)?;
            if parsed_type.c_type == C0Type::Void {
                return Err(self.error_at_previous("`sizeof(void)` is not supported"));
            }
            if let (C0Type::Int32, Some(name)) = (parsed_type.c_type, &parsed_type.struct_name) {
                let bytes = self
                    .structs
                    .get(name)
                    .ok_or_else(|| self.error_here(format!("unknown struct declaration `{name}`")))?
                    .size_bytes;
                return Ok(C0Expression::SizeOfStruct {
                    name: name.clone(),
                    bytes,
                });
            }
            if let (C0Type::Int32, Some(name)) = (parsed_type.c_type, &parsed_type.union_name) {
                let bytes = self
                    .unions
                    .get(name)
                    .ok_or_else(|| self.error_here(format!("unknown union declaration `{name}`")))?
                    .size_bytes;
                return Ok(C0Expression::SizeOfUnion {
                    name: name.clone(),
                    bytes,
                });
            }
            return Ok(C0Expression::SizeOfType {
                c_type: parsed_type.c_type,
                struct_name: parsed_type.struct_name,
                bytes: parsed_type.c_type.abi_size_bytes(),
            });
        }
        let at = self.error_context();
        match self.next() {
            Some(Token::Ident(name)) => match name.as_str() {
                // These C library-style constants give the value slice a
                // source-level way to exercise exceptional IEEE classes
                // without importing a host-specific math header.
                "INFINITY" => Ok(C0Expression::Float64Literal(0x7ff0_0000_0000_0000)),
                "NAN" => Ok(C0Expression::Float64Literal(0x7ff8_0000_0000_0000)),
                "INFINITYF" => Ok(C0Expression::Float32Literal(0x7f80_0000)),
                "NANF" => Ok(C0Expression::Float32Literal(0x7fc0_0000)),
                _ => match self.enum_constants.get(&name) {
                    Some(value) => Ok(C0Expression::Int32Literal(*value as u32)),
                    None => Ok(C0Expression::Variable(self.resolve_name(&name))),
                },
            },
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
            Some(Token::CharLiteral(value)) => Ok(C0Expression::UInt8Literal(value)),
            Some(Token::StringLiteral(bytes)) => Ok(C0Expression::Variable(
                self.fresh_string_literal_name(bytes),
            )),
            Some(Token::LParen) => {
                let expression = self.parse_expression()?;
                self.expect(Token::RParen)?;
                Ok(expression)
            }
            Some(token) => Err(at.error(format!("expected expression, got {}", token.describe()))),
            None => Err(at.error("expected expression, got end of input")),
        }
    }

    fn expect(&mut self, expected: Token) -> Result<(), C0SyntaxError> {
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

    fn expect_ident(&mut self, label: &str) -> Result<String, C0SyntaxError> {
        let at = self.error_context();
        match self.next() {
            Some(Token::Ident(name)) => Ok(name),
            Some(token) => Err(at.error(format!("expected {label}, got {}", token.describe()))),
            None => Err(at.error(format!("expected {label}, got end of input"))),
        }
    }

    fn expect_ident_spelling(&mut self, expected: &str) -> Result<(), C0SyntaxError> {
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
    fn expect_end(&self, function_name: &str) -> Result<(), C0SyntaxError> {
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
                name == "volatile"
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

fn flatten_array_indices(indexes: Vec<C0Expression>, dimensions: &[u32]) -> C0Expression {
    let mut terms = Vec::with_capacity(indexes.len());
    for (index, expression) in indexes.into_iter().enumerate() {
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
            C0Expression::Multiply(
                Box::new(expression),
                Box::new(C0Expression::Int32Literal(stride)),
            )
        });
    }
    let mut terms = terms.into_iter();
    let mut offset = terms
        .next()
        .expect("a multidimensional access has at least one index");
    for term in terms {
        offset = C0Expression::Add(Box::new(offset), Box::new(term));
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
    if !matches!(
        normalized_suffix.as_str(),
        "" | "u" | "l" | "ll" | "ul" | "lu" | "ull" | "llu"
    ) {
        return Err("unsupported integer-literal suffix");
    }
    u64::from_str_radix(digits, radix).map_err(|_| match radix {
        8 => "digits are not valid for an octal literal or the value is too large",
        16 => "digits are not valid for a hexadecimal literal or the value is too large",
        _ => "the value is too large",
    })
}

fn function_pointer_signature_from_header(header: &C0FunctionHeader) -> C0FunctionPointerSignature {
    C0FunctionPointerSignature::new(
        header.return_type,
        header.return_pointer_struct_name.clone(),
        header
            .parameters
            .iter()
            .map(|parameter| {
                C0FunctionPointerParameter::new(parameter.c_type, parameter.struct_name.clone())
            })
            .collect(),
    )
}

fn function_pointer_type(signature: &C0FunctionPointerSignature) -> C0Type {
    C0Type::FunctionPointer(crate::kernel::CType::function_pointer_signature(
        signature.return_type().to_kernel_type(),
        &signature
            .parameters()
            .iter()
            .map(|parameter| parameter.c_type().to_kernel_type())
            .collect::<Vec<_>>(),
    ))
}

fn describe_function_pointer_signature(signature: &C0FunctionPointerSignature) -> String {
    let parameters = signature
        .parameters
        .iter()
        .map(|parameter| match &parameter.struct_name {
            Some(name) => format!("struct {name}*"),
            None => format!("{:?}", parameter.c_type),
        })
        .collect::<Vec<_>>()
        .join(", ");
    let return_type = match &signature.return_struct_name {
        Some(name) => format!("struct {name}*"),
        None => format!("{:?}", signature.return_type),
    };
    format!("{return_type} ({parameters})")
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

fn parse_integer_literal_expression(literal: &str) -> Result<C0Expression, &'static str> {
    let magnitude = parse_integer_literal_magnitude(literal)?;
    let (digits, suffix) = integer_literal_parts(literal);
    let suffix = suffix.to_ascii_lowercase();
    let is_hex = digits.starts_with("0x") || digits.starts_with("0X");
    let has_long = matches!(suffix.as_str(), "l" | "ll" | "ul" | "lu" | "ull" | "llu");
    let has_unsigned = matches!(suffix.as_str(), "u" | "ul" | "lu" | "ull" | "llu");

    if has_long {
        if has_unsigned {
            return if magnitude <= u64::MAX {
                Ok(C0Expression::UInt64Literal(magnitude))
            } else {
                Err("the value is too large")
            };
        }
        return if magnitude <= i64::MAX as u64 {
            Ok(C0Expression::Int64Literal(magnitude as i64))
        } else if is_hex && magnitude <= u64::MAX {
            Ok(C0Expression::UInt64Literal(magnitude))
        } else {
            Err("the value is too large for a signed integer literal")
        };
    }

    if has_unsigned {
        return if magnitude <= u32::MAX as u64 {
            Ok(C0Expression::UInt32Literal(magnitude as u32))
        } else if magnitude <= u64::MAX {
            Ok(C0Expression::UInt64Literal(magnitude))
        } else {
            Err("the value is too large")
        };
    }

    if is_hex && magnitude > i32::MAX as u64 && magnitude <= u32::MAX as u64 {
        return Ok(C0Expression::UInt32Literal(magnitude as u32));
    }
    if magnitude <= i32::MAX as u64 {
        Ok(C0Expression::Int32Literal(magnitude as u32))
    } else if magnitude <= i64::MAX as u64 {
        Ok(C0Expression::Int64Literal(magnitude as i64))
    } else if is_hex && magnitude <= u64::MAX {
        Ok(C0Expression::UInt64Literal(magnitude))
    } else {
        Err("the value is too large for a signed integer literal")
    }
}

fn is_floating_literal(literal: &str) -> bool {
    !literal.starts_with("0x")
        && !literal.starts_with("0X")
        && literal
            .chars()
            .any(|character| matches!(character, '.' | 'e' | 'E'))
}

fn parse_float_literal_expression(literal: &str) -> Result<C0Expression, &'static str> {
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
            .map(|value| C0Expression::Float64Literal(value.to_bits()))
            .ok_or("value is not a finite binary64 literal"),
        "f" | "F" => number
            .parse::<f32>()
            .ok()
            .filter(|value| value.is_finite())
            .map(|value| C0Expression::Float32Literal(value.to_bits()))
            .ok_or("value is not a finite binary32 literal"),
        "l" | "L" => Err("long double literals are not modeled in C0"),
        _ => Err("unsupported floating-point literal suffix"),
    }
}

fn negate_float_literal(expression: C0Expression) -> Option<C0Expression> {
    match expression {
        C0Expression::Float32Literal(bits) => {
            Some(C0Expression::Float32Literal(bits ^ 0x8000_0000))
        }
        C0Expression::Float64Literal(bits) => {
            Some(C0Expression::Float64Literal(bits ^ 0x8000_0000_0000_0000))
        }
        _ => None,
    }
}

fn parse_float_classification_call(
    function_name: &str,
    arguments: &[C0Expression],
) -> Option<Result<C0Expression, &'static str>> {
    let classification = match function_name {
        "isfinite" => C0FloatClassification::Finite,
        "isinf" => C0FloatClassification::Infinite,
        "iszero" => C0FloatClassification::Zero,
        "issubnormal" => C0FloatClassification::Subnormal,
        "isnan" => C0FloatClassification::Nan,
        _ => return None,
    };
    if arguments.len() != 1 {
        return Some(Err(
            "floating classification predicates require one argument",
        ));
    }
    let result = match &arguments[0] {
        C0Expression::Float32Literal(bits) => {
            classify_float_bits(u64::from(*bits), 8, 23, classification_name(classification))
        }
        C0Expression::Float64Literal(bits) => {
            classify_float_bits(*bits, 11, 52, classification_name(classification))
        }
        _ => {
            return Some(Ok(C0Expression::FloatClassification {
                expression: Box::new(arguments[0].clone()),
                classification,
            }));
        }
    };
    Some(Ok(C0Expression::Int32Literal(u32::from(result))))
}

fn classification_name(classification: C0FloatClassification) -> &'static str {
    match classification {
        C0FloatClassification::Finite => "isfinite",
        C0FloatClassification::Infinite => "isinf",
        C0FloatClassification::Zero => "iszero",
        C0FloatClassification::Subnormal => "issubnormal",
        C0FloatClassification::Nan => "isnan",
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

fn integer_literal_has_unsigned_suffix(literal: &str) -> bool {
    let (_, suffix) = integer_literal_parts(literal);
    suffix
        .chars()
        .any(|character| character.eq_ignore_ascii_case(&'u'))
}

fn integer_literal_has_long_suffix(literal: &str) -> bool {
    let (_, suffix) = integer_literal_parts(literal);
    suffix
        .chars()
        .any(|character| character.eq_ignore_ascii_case(&'l'))
}

fn tokenize(source: &str) -> Result<(Vec<Token>, Vec<SourcePosition>), C0SyntaxError> {
    let chars = source.chars().collect::<Vec<_>>();
    let char_positions = character_positions(source);
    let mut tokens = Vec::new();
    let mut positions = Vec::new();
    let mut index = 0;

    while index < chars.len() {
        let ch = chars[index];
        let position = char_positions[index];
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
            if index + 1 == chars.len() {
                return Err(C0SyntaxError::at(position, "unterminated block comment"));
            }
            index += 2;
            continue;
        }

        if ch == '.' && chars.get(index + 1) == Some(&'.') && chars.get(index + 2) == Some(&'.') {
            return Err(C0SyntaxError::at(
                position,
                "variadic parameter lists (`...`) are not supported in C0",
            ));
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

        if ch.is_ascii_digit() {
            let start = index;
            if ch == '0' && matches!(chars.get(index + 1), Some('x') | Some('X')) {
                index += 2;
                while index < chars.len() && chars[index].is_ascii_hexdigit() {
                    index += 1;
                }
                if matches!(chars.get(index), Some('.' | 'p' | 'P')) {
                    return Err(C0SyntaxError::at(
                        position,
                        "hexadecimal floating-point literals are not supported in C0",
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
            let (value, next_index) =
                parse_char_literal(&chars, index).map_err(|error| error.with_position(position))?;
            tokens.push(Token::CharLiteral(value));
            positions.push(position);
            index = next_index;
            continue;
        }

        if ch == '"' {
            let (value, next_index) = parse_string_literal(&chars, index)
                .map_err(|error| error.with_position(position))?;
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
                return Err(C0SyntaxError::at(
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

fn balanced_statement_sequence(mut statements: Vec<C0Statement>) -> Option<C0Statement> {
    while statements.len() > 1 {
        let mut next_level = Vec::with_capacity(statements.len().div_ceil(2));
        let mut iter = statements.into_iter();
        while let Some(first) = iter.next() {
            next_level.push(match iter.next() {
                Some(second) => C0Statement::Seq(Box::new(first), Box::new(second)),
                None => first,
            });
        }
        statements = next_level;
    }
    statements.pop()
}

fn prepend_statements(prefix: Vec<C0Statement>, statement: C0Statement) -> C0Statement {
    if prefix.is_empty() {
        return statement;
    }
    let mut statements = prefix;
    statements.push(statement);
    balanced_statement_sequence(statements).expect("the statement prefix is non-empty")
}

/// Run a lowered loop-condition prefix and condition check before each
/// `continue` that targets the current loop. Nested loops consume their own
/// `continue` statements, while a `switch` does not introduce a continue
/// target and is traversed.
fn prepend_condition_check_before_loop_continues(
    statement: C0Statement,
    prefix: &[C0Statement],
    loop_condition: &C0Expression,
) -> C0Statement {
    match statement {
        C0Statement::Continue => prepend_statements(
            prefix.to_vec(),
            C0Statement::If {
                condition: C0Expression::Not(Box::new(loop_condition.clone())),
                then_branch: Box::new(C0Statement::Break),
                else_branch: Box::new(C0Statement::Continue),
            },
        ),
        C0Statement::Seq(first, second) => C0Statement::Seq(
            Box::new(prepend_condition_check_before_loop_continues(
                *first,
                prefix,
                loop_condition,
            )),
            Box::new(prepend_condition_check_before_loop_continues(
                *second,
                prefix,
                loop_condition,
            )),
        ),
        C0Statement::If {
            condition: if_condition,
            then_branch,
            else_branch,
        } => C0Statement::If {
            condition: if_condition.clone(),
            then_branch: Box::new(prepend_condition_check_before_loop_continues(
                *then_branch,
                prefix,
                loop_condition,
            )),
            else_branch: Box::new(prepend_condition_check_before_loop_continues(
                *else_branch,
                prefix,
                loop_condition,
            )),
        },
        C0Statement::Switch { expression, cases } => C0Statement::Switch {
            expression,
            cases: cases
                .into_iter()
                .map(|case| C0SwitchCase {
                    value: case.value,
                    body: Box::new(prepend_condition_check_before_loop_continues(
                        *case.body,
                        prefix,
                        loop_condition,
                    )),
                })
                .collect(),
        },
        statement @ (C0Statement::While { .. }
        | C0Statement::DoWhile { .. }
        | C0Statement::For { .. }
        | C0Statement::Skip
        | C0Statement::Break
        | C0Statement::Declare { .. }
        | C0Statement::DeclareStructValue { .. }
        | C0Statement::Assign { .. }
        | C0Statement::CallAssign { .. }
        | C0Statement::Call { .. }
        | C0Statement::IndirectCall { .. }
        | C0Statement::HeapAllocate { .. }
        | C0Statement::HeapFree { .. }
        | C0Statement::Return(_)
        | C0Statement::Store { .. }
        | C0Statement::Update { .. }) => statement,
    }
}

fn first_embedded_call_position(expression: &C0Expression) -> Option<SourcePosition> {
    match expression {
        C0Expression::Call {
            position,
            arguments,
            ..
        } => position.or_else(|| arguments.iter().find_map(first_embedded_call_position)),
        C0Expression::IndirectCall {
            function,
            position,
            arguments,
            ..
        } => position
            .or_else(|| first_embedded_call_position(function))
            .or_else(|| arguments.iter().find_map(first_embedded_call_position)),
        C0Expression::Cast { expression, .. }
        | C0Expression::FloatNegate(expression)
        | C0Expression::FloatClassification { expression, .. }
        | C0Expression::AddressOf(expression)
        | C0Expression::PointerOffsetBytes {
            pointer: expression,
            ..
        }
        | C0Expression::Not(expression)
        | C0Expression::BitwiseNot(expression)
        | C0Expression::Load(expression) => first_embedded_call_position(expression),
        C0Expression::AggregateAddress { pointer, .. }
        | C0Expression::Field { pointer, .. }
        | C0Expression::UnionField { pointer, .. }
        | C0Expression::UnionAddress { pointer, .. } => first_embedded_call_position(pointer),
        C0Expression::Conditional {
            condition,
            then_branch,
            else_branch,
        } => first_embedded_call_position(condition)
            .or_else(|| first_embedded_call_position(then_branch))
            .or_else(|| first_embedded_call_position(else_branch)),
        C0Expression::LessThan(left, right)
        | C0Expression::LessEqual(left, right)
        | C0Expression::GreaterThan(left, right)
        | C0Expression::GreaterEqual(left, right)
        | C0Expression::Equal(left, right)
        | C0Expression::NotEqual(left, right)
        | C0Expression::And(left, right)
        | C0Expression::Or(left, right)
        | C0Expression::Add(left, right)
        | C0Expression::Subtract(left, right)
        | C0Expression::Multiply(left, right)
        | C0Expression::Divide(left, right)
        | C0Expression::Remainder(left, right)
        | C0Expression::ShiftLeft(left, right)
        | C0Expression::ShiftRight(left, right)
        | C0Expression::BitwiseAnd(left, right)
        | C0Expression::BitwiseOr(left, right)
        | C0Expression::BitwiseXor(left, right)
        | C0Expression::Index(left, right) => {
            first_embedded_call_position(left).or_else(|| first_embedded_call_position(right))
        }
        C0Expression::Void
        | C0Expression::Variable(_)
        | C0Expression::FunctionAddress(_)
        | C0Expression::Int32Literal(_)
        | C0Expression::UInt8Literal(_)
        | C0Expression::UInt32Literal(_)
        | C0Expression::Int64Literal(_)
        | C0Expression::UInt64Literal(_)
        | C0Expression::Float32Literal(_)
        | C0Expression::Float64Literal(_)
        | C0Expression::SizeOfStruct { .. }
        | C0Expression::SizeOfUnion { .. }
        | C0Expression::SizeOfType { .. } => None,
    }
}

fn parse_char_literal(chars: &[char], start: usize) -> Result<(u8, usize), C0SyntaxError> {
    let Some(first) = chars.get(start + 1).copied() else {
        return Err(C0SyntaxError::new("unterminated character literal"));
    };
    let (value, end) = if first == '\\' {
        let Some(escaped) = chars.get(start + 2).copied() else {
            return Err(C0SyntaxError::new("unterminated character literal"));
        };
        let value = match escaped {
            'n' => b'\n',
            'r' => b'\r',
            't' => b'\t',
            '0' => b'\0',
            '\\' => b'\\',
            '\'' => b'\'',
            '"' => b'"',
            other => {
                return Err(C0SyntaxError::new(format!(
                    "unsupported character escape `\\{other}`"
                )));
            }
        };
        (value, start + 3)
    } else {
        if !first.is_ascii() {
            return Err(C0SyntaxError::new(
                "only ASCII character literals are supported",
            ));
        }
        (first as u8, start + 2)
    };

    if chars.get(end) != Some(&'\'') {
        return Err(C0SyntaxError::new(
            "character literals must contain exactly one byte",
        ));
    }

    Ok((value, end + 1))
}

fn parse_string_literal(chars: &[char], start: usize) -> Result<(Vec<u8>, usize), C0SyntaxError> {
    let mut value = Vec::new();
    let mut index = start + 1;
    while let Some(ch) = chars.get(index).copied() {
        match ch {
            '"' => return Ok((value, index + 1)),
            '\\' => {
                let Some(escaped) = chars.get(index + 1).copied() else {
                    return Err(C0SyntaxError::new("unterminated string literal"));
                };
                let byte = match escaped {
                    'n' => b'\n',
                    'r' => b'\r',
                    't' => b'\t',
                    '0' => b'\0',
                    '\\' => b'\\',
                    '\'' => b'\'',
                    '"' => b'"',
                    other => {
                        return Err(C0SyntaxError::new(format!(
                            "unsupported string escape `\\{other}`"
                        )));
                    }
                };
                value.push(byte);
                index += 2;
            }
            '\n' | '\r' => {
                return Err(C0SyntaxError::new(
                    "string literals may not contain an unescaped newline",
                ));
            }
            other if other.is_ascii() => {
                value.push(other as u8);
                index += 1;
            }
            _ => {
                return Err(C0SyntaxError::new(
                    "only ASCII string literals are supported",
                ));
            }
        }
    }
    Err(C0SyntaxError::new("unterminated string literal"))
}

fn is_ident_start(ch: char) -> bool {
    ch.is_ascii_alphabetic() || ch == '_'
}

fn is_ident_continue(ch: char) -> bool {
    ch.is_ascii_alphanumeric() || ch == '_'
}
