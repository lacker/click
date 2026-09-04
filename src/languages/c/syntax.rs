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
    "expression.null-pointer",
    "expression.address-of",
    "expression.cast",
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
    name: String,
    parameters: Vec<C0Parameter>,
    body: C0Statement,
    structs: BTreeMap<String, C0StructLayout>,
    enums: BTreeMap<String, C0EnumDefinition>,
    unions: BTreeMap<String, C0UnionLayout>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct C0Parameter {
    c_type: C0Type,
    name: String,
    struct_name: Option<String>,
    struct_layout: Option<C0StructLayout>,
    /// The ABI width of one element when the source parameter was declared as
    /// an array of structs. The public C0 type remains the compatible
    /// struct-pointer placeholder, while the kernel uses byte addressing for
    /// the lowered indexed field accesses.
    array_element_width: Option<u32>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct ParsedType {
    c_type: C0Type,
    struct_name: Option<String>,
    enum_name: Option<String>,
    union_name: Option<String>,
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
    /// The ABI width of one element when this is an inline array of embedded
    /// structs. The public C0 type remains a byte-array placeholder, while
    /// member selection uses this metadata to preserve struct indexing.
    array_element_width: Option<u32>,
    /// The fixed dimensions of an inline array of embedded structs, in C's
    /// declared order. The shape is retained so multidimensional indexing can
    /// be flattened with the correct row-major stride.
    array_shape: Option<Vec<u32>>,
    offset_bytes: u32,
    byte_width: u32,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum C0Type {
    Void,
    Int16,
    Int32,
    UInt8,
    UInt16,
    UInt32,
    Int32Pointer,
    UInt8Pointer,
    Int32PointerPointer,
    UInt8PointerPointer,
    /// A callback signature identified by a stable, structural signature key.
    /// The key is shared with the kernel type and is deliberately opaque to
    /// ordinary C expressions: function pointers are callable, not objects.
    FunctionPointer(u64),
    Int32Array(u32),
    UInt8Array(u32),
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
            (Self::Lp64, C0Type::Int16) => (2, 2),
            (Self::Lp64, C0Type::Int32) => (4, 4),
            (Self::Lp64, C0Type::UInt8) => (1, 1),
            (Self::Lp64, C0Type::UInt16) => (2, 2),
            (Self::Lp64, C0Type::UInt32) => (4, 4),
            (
                Self::Lp64,
                C0Type::Int32Pointer
                | C0Type::UInt8Pointer
                | C0Type::Int32PointerPointer
                | C0Type::UInt8PointerPointer,
            ) => (8, 8),
            (Self::Lp64, C0Type::FunctionPointer(_)) => (8, 8),
            (Self::Lp64, C0Type::Int32Array(length)) => (length.saturating_mul(4), 4),
            (Self::Lp64, C0Type::UInt8Array(length)) => (length, 1),
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
    FunctionAddress(String),
    Cast {
        expression: Box<C0Expression>,
        c_type: C0Type,
    },
    Conditional {
        condition: Box<C0Expression>,
        then_branch: Box<C0Expression>,
        else_branch: Box<C0Expression>,
    },
    AddressOf(Box<C0Expression>),
    PointerOffsetBytes {
        pointer: Box<C0Expression>,
        bytes: u32,
    },
    Int32Literal(u32),
    UInt8Literal(u8),
    UInt32Literal(u32),
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
            name,
            parameters,
            body: C0Statement::Skip,
            structs: BTreeMap::new(),
            enums: BTreeMap::new(),
            unions: BTreeMap::new(),
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
        if let Some(name) = &self.return_struct_name {
            let layout = self
                .structs
                .get(name)
                .expect("struct return has a parsed layout")
                .to_kernel_aggregate_layout();
            function = function.with_return_aggregate_layout(layout);
        }
        function
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
            struct_name,
            struct_layout: None,
            array_element_width: None,
        }
    }

    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn c_type(&self) -> C0Type {
        self.c_type
    }

    pub fn struct_name(&self) -> Option<&str> {
        self.struct_name.as_deref()
    }

    pub fn struct_layout(&self) -> Option<&C0StructLayout> {
        self.struct_layout.as_ref()
    }

    pub fn array_element_width(&self) -> Option<u32> {
        self.array_element_width
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
            );
        }
        let c_type = self
            .array_element_width
            .map(|_| crate::kernel::CType::UInt8Pointer)
            .unwrap_or_else(|| self.c_type.to_kernel_type());
        crate::kernel::c_parameter(self.name.clone(), c_type)
    }
}

impl C0Type {
    pub fn is_pointer(self) -> bool {
        matches!(
            self,
            Self::Int32Pointer
                | Self::UInt8Pointer
                | Self::Int32PointerPointer
                | Self::UInt8PointerPointer
                | Self::FunctionPointer(_)
        )
    }

    pub fn pointee_type(self) -> Option<Self> {
        match self {
            Self::Int32Pointer | Self::Int32Array(_) => Some(Self::Int32),
            Self::UInt8Pointer | Self::UInt8Array(_) => Some(Self::UInt8),
            Self::Int32PointerPointer => Some(Self::Int32Pointer),
            Self::UInt8PointerPointer => Some(Self::UInt8Pointer),
            Self::Void
            | Self::Int16
            | Self::Int32
            | Self::UInt8
            | Self::UInt16
            | Self::UInt32
            | Self::FunctionPointer(_) => None,
        }
    }

    pub fn to_kernel_type(self) -> crate::kernel::CType {
        match self {
            Self::Void => crate::kernel::CType::Void,
            Self::Int16 => crate::kernel::CType::Int16,
            Self::Int32 => crate::kernel::CType::Int32,
            Self::UInt8 => crate::kernel::CType::UInt8,
            Self::UInt16 => crate::kernel::CType::UInt16,
            Self::UInt32 => crate::kernel::CType::UInt32,
            Self::Int32Pointer => crate::kernel::CType::Int32Pointer,
            Self::UInt8Pointer => crate::kernel::CType::UInt8Pointer,
            Self::Int32PointerPointer => crate::kernel::CType::Int32PointerPointer,
            Self::UInt8PointerPointer => crate::kernel::CType::UInt8PointerPointer,
            Self::FunctionPointer(signature) => crate::kernel::CType::FunctionPointer(signature),
            Self::Int32Array(length) => crate::kernel::CType::Int32Array(length),
            Self::UInt8Array(length) => crate::kernel::CType::UInt8Array(length),
        }
    }
}

impl C0Statement {
    pub fn to_kernel_statement(&self) -> crate::kernel::CStatement {
        match self {
            Self::Skip => crate::kernel::c_skip(),
            Self::Break => crate::kernel::c_break(),
            Self::Continue => crate::kernel::c_continue(),
            Self::Declare { c_type, name } => {
                crate::kernel::c_declare(name.clone(), c_type.to_kernel_type())
            }
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
            Self::FunctionAddress(name) => crate::kernel::c_function_address(name.clone()),
            Self::Cast { expression, c_type } => {
                crate::kernel::c_cast(expression.to_kernel_expression(), c_type.to_kernel_type())
            }
            Self::Conditional {
                condition,
                then_branch,
                else_branch,
            } => crate::kernel::c_conditional(
                condition.to_kernel_expression(),
                then_branch.to_kernel_expression(),
                else_branch.to_kernel_expression(),
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
        | C0Statement::HeapAllocate { .. }
        | C0Statement::HeapFree { .. }
        | C0Statement::Return(_)
        | C0Statement::Store { .. }
        | C0Statement::Update { .. } => Ok(()),
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

fn flatten_aggregate_fields(
    fields: &BTreeMap<String, C0StructField>,
    structs: &BTreeMap<String, C0StructLayout>,
) -> Vec<C0AggregateField> {
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
        ) && let [length] = shape
        {
            let nested_layout = structs
                .get(nested_name)
                .expect("embedded struct array field has a parsed layout");
            for index in 0..*length {
                let element_offset = field
                    .offset_bytes
                    .checked_add(
                        index
                            .checked_mul(element_width)
                            .expect("validated embedded struct array field offset"),
                    )
                    .expect("validated embedded struct array field offset");
                append_nested_fields(
                    &mut aggregate_fields,
                    &format!("{field_name}[{index}]"),
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
        C0Expression::Call { arguments, .. } => arguments.iter().any(contains_aggregate_value),
        C0Expression::AddressOf(_) => false,
        C0Expression::Cast { expression, .. }
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
            | "unsigned"
            | "signed"
            | "char"
            | "short"
            | "long"
            | "size_t"
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
            other => format!("`{}`", other.form()),
        }
    }

    fn form(&self) -> &'static str {
        match self {
            Self::Ident(_) | Self::Number(_) | Self::CharLiteral(_) => "",
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
    loop_contexts: Vec<CLoopContext>,
    function_declarations: BTreeMap<String, C0FunctionHeader>,
    defined_functions: BTreeSet<String>,
    abi: CAbi,
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
    name: String,
    parameters: Vec<C0Parameter>,
}

fn function_headers_compatible(left: &C0FunctionHeader, right: &C0FunctionHeader) -> bool {
    left.return_type == right.return_type
        && left.return_struct_name == right.return_struct_name
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
            unions: BTreeMap::new(),
            scopes: Vec::new(),
            next_scoped_name: 0,
            next_synthesized_call: 0,
            loop_contexts: Vec::new(),
            function_declarations: BTreeMap::new(),
            defined_functions: BTreeSet::new(),
            abi,
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
        }
    }

    fn resolve_name(&self, source_name: &str) -> String {
        self.scopes
            .iter()
            .rev()
            .flat_map(|scope| scope.iter().rev())
            .find(|binding| binding.source_name == source_name)
            .map(|binding| binding.kernel_name.clone())
            .unwrap_or_else(|| source_name.to_string())
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
                && field
                    .array_shape
                    .as_deref()
                    .is_some_and(|shape| shape.len() == 1)
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
                        | C0Type::Int32Array(_)
                        | C0Type::UInt8Array(_)
                        | C0Type::Int32Pointer
                        | C0Type::UInt8Pointer
                        | C0Type::Int32PointerPointer
                        | C0Type::UInt8PointerPointer
                )
            {
                return Err(self.error_here(format!(
                    "struct-by-value currently supports int16, int32, uint8, uint16, named enum fields, fixed scalar arrays, one-dimensional embedded-struct arrays, data-pointer fields, and embedded struct fields; `struct {struct_name}` contains a function pointer, an unsupported embedded-struct array, or a union field"
                )));
            }
        }
        Ok(layout)
    }

    fn is_type_start(&self) -> bool {
        self.peek_ident()
            .is_some_and(|name| is_builtin_type_start(name) || self.typedefs.contains_key(name))
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
        let function = self.parse_function_definition()?;
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
            if !self.is_type_start() {
                return Err(self.error_here(format!(
                    "expected function declaration, got {}",
                    self.peek()
                        .map(Token::describe)
                        .unwrap_or_else(|| "end of input".to_string())
                )));
            }
            let header = self.parse_function_header()?;
            if self.peek() == Some(&Token::LBrace) {
                if is_extern {
                    return Err(self.error_here(
                        "`extern` function definitions are not supported; use `extern` only for prototypes",
                    ));
                }
                functions.push(self.finish_function_definition(header)?);
            } else {
                if self.peek() != Some(&Token::Semicolon) {
                    return Err(self.error_here(format!(
                        "expected function body or `;` after `{}`",
                        header.name
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
        self.parse_declarations()?;
        while self.peek().is_some() {
            if self.peek_ident() == Some("extern") {
                self.position += 1;
            }
            if !self.is_type_start() {
                return Err(self.error_here(format!(
                    "expected a header declaration, got {}",
                    self.peek()
                        .map(Token::describe)
                        .unwrap_or_else(|| "end of input".to_string())
                )));
            }
            let header = self.parse_function_header()?;
            if self.peek() != Some(&Token::Semicolon) {
                self.pop_scope();
                return Err(self.error_here(format!(
                    "function definitions are not allowed in headers; `{}` has a body",
                    header.name
                )));
            }
            self.pop_scope();
            self.expect(Token::Semicolon)?;
            self.register_function_declaration(&header, false)?;
            self.parse_declarations()?;
        }
        Ok(())
    }

    fn parse_function_definition(&mut self) -> Result<C0Function, C0SyntaxError> {
        let header = self.parse_function_header()?;
        self.register_function_declaration(&header, true)?;
        if self.peek() != Some(&Token::LBrace) {
            return Err(self.error_here(format!("expected function body after `{}`", header.name)));
        }
        self.finish_function_definition(header)
    }

    fn finish_function_definition(
        &mut self,
        header: C0FunctionHeader,
    ) -> Result<C0Function, C0SyntaxError> {
        let mut body = self.parse_block_statement()?;
        body = self.lower_call_expressions(body)?;
        self.pop_scope();
        validate_function_returns(&body, header.return_type)?;
        if header.return_type == C0Type::Void {
            body = C0Statement::Seq(
                Box::new(body),
                Box::new(C0Statement::Return(C0Expression::Void)),
            );
        }

        Ok(C0Function {
            return_type: header.return_type,
            return_struct_name: header.return_struct_name,
            name: header.name,
            parameters: header.parameters,
            body,
            structs: self.structs.clone(),
            enums: self.enums.clone(),
            unions: self.unions.clone(),
        })
    }

    fn parse_function_header(&mut self) -> Result<C0FunctionHeader, C0SyntaxError> {
        let parsed_return_type = self.parse_type()?;
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
        let name = self.expect_ident("function name")?;
        self.expect(Token::LParen)?;
        self.push_scope();
        let parameters = self.parse_parameters()?;
        self.expect(Token::RParen)?;
        Ok(C0FunctionHeader {
            return_type,
            return_struct_name,
            name,
            parameters,
        })
    }

    fn register_function_declaration(
        &mut self,
        header: &C0FunctionHeader,
        definition: bool,
    ) -> Result<(), C0SyntaxError> {
        if let Some(previous) = self.function_declarations.get(&header.name) {
            if !function_headers_compatible(previous, header) {
                return Err(self.error_here(format!(
                    "conflicting declarations for function `{}`",
                    header.name
                )));
            }
        } else {
            self.function_declarations
                .insert(header.name.clone(), header.clone());
        }
        if definition && !self.defined_functions.insert(header.name.clone()) {
            return Err(self.error_here(format!("duplicate function definition `{}`", header.name)));
        }
        Ok(())
    }

    fn parse_declarations(&mut self) -> Result<(), C0SyntaxError> {
        while self.peek().is_some() {
            if self.peek_ident() == Some("typedef") {
                self.parse_typedef_declaration()?;
            } else if self.peek_ident() == Some("struct") && self.peek_n(2) == Some(&Token::LBrace)
            {
                self.parse_struct_declaration()?;
            } else if self.peek_ident() == Some("enum") && self.peek_n(2) == Some(&Token::LBrace) {
                self.parse_enum_declaration()?;
            } else if self.peek_ident() == Some("union") && self.peek_n(2) == Some(&Token::LBrace) {
                self.parse_union_declaration()?;
            } else {
                break;
            }
        }
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
        let c_type = if self.peek() == Some(&Token::LBracket) {
            if base_type.struct_name.is_some()
                || !matches!(base_type.c_type, C0Type::Int32 | C0Type::UInt8)
            {
                return Err(self.error_here(
                    "inline struct arrays currently support only int32 and uint8 elements",
                ));
            }
            self.position += 1;
            let length = match self.next() {
                Some(Token::Number(number)) => {
                    let length = parse_integer_literal_magnitude(&number).map_err(|reason| {
                        self.error_here(format!("invalid struct array length `{number}`: {reason}"))
                    })?;
                    let length = u32::try_from(length).map_err(|_| {
                        self.error_here(format!("struct array length `{number}` is out of range"))
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
                    return Err(self.error_here("expected struct array length, got end of input"));
                }
            };
            self.expect(Token::RBracket)?;
            if self.peek() == Some(&Token::LBracket) {
                return Err(
                    self.error_here("multidimensional inline arrays in structs are not supported")
                );
            }
            match base_type.c_type {
                C0Type::Int32 => C0Type::Int32Array(length),
                C0Type::UInt8 => C0Type::UInt8Array(length),
                _ => unreachable!("validated scalar struct array element type"),
            }
        } else {
            base_type.c_type
        };

        if !matches!(
            c_type,
            C0Type::Int16
                | C0Type::Int32
                | C0Type::UInt8
                | C0Type::UInt16
                | C0Type::Int32Pointer
                | C0Type::UInt8Pointer
                | C0Type::Int32PointerPointer
                | C0Type::UInt8PointerPointer
                | C0Type::Int32Array(_)
                | C0Type::UInt8Array(_)
        ) {
            return Err(self.error_here(format!(
                "struct `{struct_name}` fields currently support int16, int32, uint8, uint16, enum, fixed scalar arrays, and pointer fields",
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
            None,
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
            if let Some((name, c_type)) =
                self.parse_function_pointer_declarator(parsed_type.c_type)?
            {
                let kernel_name = self.declare_name(&name)?;
                self.variable_types.insert(kernel_name.clone(), c_type);
                parameters.push(C0Parameter {
                    c_type,
                    name: kernel_name,
                    struct_layout: None,
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
            let struct_array =
                parsed_type.struct_name.is_some() && self.peek() == Some(&Token::LBracket);
            let struct_value = is_plain_struct_type(&parsed_type) && !struct_array;
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
            let c_type = struct_value_layout
                .as_ref()
                .map(struct_value_type)
                .unwrap_or(self.parse_parameter_array_suffix(parsed_type.c_type)?);
            self.variable_types.insert(kernel_name.clone(), c_type);
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
                        struct_layout: struct_value_layout,
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
                        struct_layout: self.structs.get(&struct_name_value).cloned(),
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
                struct_layout: struct_name
                    .as_ref()
                    .and_then(|name| self.structs.get(name))
                    .cloned(),
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
            },
            Some(Token::Ident(name)) => self.parse_named_type(name)?,
            Some(token) => {
                return Err(self.error_at_previous(format!(
                    "expected type `void`, `int32`/`int`, `uint8`/`unsigned char`, `enum`, or `struct`, got {}",
                    token.describe()
                )));
            }
            None => {
                return Err(self.error_here(
                    "expected type `void`, `int32`/`int`, `uint8`/`unsigned char`, `enum`, or `struct`, got end of input",
                ));
            }
        };

        let mut c_type = parsed.c_type;
        while self.peek() == Some(&Token::Star) {
            self.position += 1;
            c_type = match c_type {
                C0Type::Int16 | C0Type::UInt16 => {
                    return Err(self.error_at_previous(
                        "pointers to 16-bit integer values are not supported yet",
                    ));
                }
                C0Type::Int32 => C0Type::Int32Pointer,
                C0Type::UInt8 => C0Type::UInt8Pointer,
                C0Type::UInt32 => {
                    return Err(
                        self.error_at_previous("pointers to uint32 values are not supported yet")
                    );
                }
                C0Type::Int32Pointer => C0Type::Int32PointerPointer,
                C0Type::UInt8Pointer => C0Type::UInt8PointerPointer,
                C0Type::Void => return Err(self.error_at_previous("`void *` is not supported yet")),
                C0Type::Int32PointerPointer | C0Type::UInt8PointerPointer => {
                    return Err(
                        self.error_at_previous("pointer depth beyond `**` is not supported")
                    );
                }
                C0Type::Int32Array(_) | C0Type::UInt8Array(_) => {
                    return Err(self.error_at_previous("pointer-to-array types are not supported"));
                }
                C0Type::FunctionPointer(_) => {
                    return Err(
                        self.error_at_previous("pointers to function pointers are not supported")
                    );
                }
            };
            if parsed.struct_name.is_some() && c_type != C0Type::Int32Pointer {
                return Err(
                    self.error_at_previous("pointer depth beyond `struct S*` is not supported")
                );
            }
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
        })
    }

    /// Parses the parenthesized declarator in `int32 (*callback)(int32)`.
    /// The pointed-to signature is structural, so names in the nested
    /// parameter list are intentionally ignored.
    fn parse_function_pointer_declarator(
        &mut self,
        return_type: C0Type,
    ) -> Result<Option<(String, C0Type)>, C0SyntaxError> {
        if self.peek() != Some(&Token::LParen) {
            return Ok(None);
        }
        self.position += 1;
        self.expect(Token::Star)?;
        let name = self.expect_ident("function-pointer name")?;
        self.expect(Token::RParen)?;
        self.expect(Token::LParen)?;
        let mut parameter_types = Vec::new();
        if self.peek() != Some(&Token::RParen) {
            loop {
                let parsed_type = self.parse_type()?;
                if parsed_type.struct_name.is_some() || parsed_type.c_type == C0Type::Void {
                    return Err(self.error_here(
                        "function-pointer parameters must use modeled non-struct types",
                    ));
                }
                let parameter_type = self.parse_parameter_array_suffix(parsed_type.c_type)?;
                parameter_types.push(parameter_type);
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
        if parameter_types.len() > 13 {
            return Err(
                self.error_here("function-pointer signatures support at most 13 parameters")
            );
        }
        let parameter_types = parameter_types
            .iter()
            .copied()
            .map(C0Type::to_kernel_type)
            .collect::<Vec<_>>();
        let signature = crate::kernel::CType::function_pointer_signature(
            return_type.to_kernel_type(),
            &parameter_types,
        );
        if signature == 0 {
            return Err(
                self.error_here("function-pointer signature uses an unsupported modeled type")
            );
        }
        Ok(Some((name, C0Type::FunctionPointer(signature))))
    }

    fn parse_named_type(&mut self, name: String) -> Result<ParsedType, C0SyntaxError> {
        let c_type = match name.as_str() {
            "void" => C0Type::Void,
            "int16" | "short" | "int16_t" => C0Type::Int16,
            "int32" | "int" | "int32_t" => C0Type::Int32,
            "uint8" | "uint8_t" => C0Type::UInt8,
            "uint16" | "uint16_t" => C0Type::UInt16,
            "uint32" | "uint32_t" => C0Type::UInt32,
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
            "long" | "size_t" | "int64_t" | "uint64_t" => {
                return Err(self.error_at_previous(format!(
                    "unsupported integer width `{name}`: see the integer-types issue"
                )));
            }
            "float" | "double" => {
                return Err(self.error_at_previous(format!(
                    "unsupported C type `{name}`: floating-point values are not modeled in C0"
                )));
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
        })
    }

    fn parse_parameter_array_suffix(&mut self, c_type: C0Type) -> Result<C0Type, C0SyntaxError> {
        if self.peek() != Some(&Token::LBracket) {
            return Ok(c_type);
        }
        let pointer_type = match c_type {
            C0Type::Int32 => C0Type::Int32Pointer,
            C0Type::UInt8 => C0Type::UInt8Pointer,
            C0Type::Int32Pointer => C0Type::Int32PointerPointer,
            C0Type::UInt8Pointer => C0Type::UInt8PointerPointer,
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
                C0Type::Int32 => (C0Type::Int32Array, 4u32, "int32".to_string(), false),
                C0Type::UInt8 => (C0Type::UInt8Array, 1u32, "uint8".to_string(), false),
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
        self.pop_scope();

        Ok(balanced_statement_sequence(statements).unwrap_or(C0Statement::Skip))
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
                let statement = self.parse_memory_lvalue_statement("statement", None)?;
                self.expect(Token::Semicolon)?;
                Ok(statement)
            }
            Some(Token::Ident(_)) if self.peek_next() == Some(&Token::Dot) => {
                let statement = self.parse_memory_lvalue_statement("statement", None)?;
                self.expect(Token::Semicolon)?;
                Ok(statement)
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
                    } else {
                        self.parse_expression()?
                    };
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
                        let arguments = self.parse_call_arguments()?;
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
                        let function_name = self.expect_ident("function name")?;
                        if matches!(function_name.as_str(), "malloc" | "calloc" | "realloc") {
                            return Err(
                                self.error_here("the allocation result may not be discarded")
                            );
                        }
                        let arguments = self.parse_call_arguments()?;
                        self.expect(Token::Semicolon)?;
                        Ok(C0Statement::Call {
                            function_name,
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
            _ => unreachable!("array initializer called for a scalar type"),
        };
        let mut values = Vec::new();
        let dimensions = array_shape
            .map(ToOwned::to_owned)
            .unwrap_or_else(|| vec![length]);
        self.parse_array_initializer_level(name, &dimensions, 0, &mut values)?;

        let mut stores = Vec::with_capacity(length as usize);
        for index in 0..length {
            let value = values
                .get(index as usize)
                .cloned()
                .unwrap_or(C0Expression::Int32Literal(0));
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

    fn parse_array_initializer_level(
        &mut self,
        name: &str,
        dimensions: &[u32],
        depth: usize,
        values: &mut Vec<C0Expression>,
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
                    self.parse_array_initializer_level(name, dimensions, depth + 1, values)?;
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
            values.push(C0Expression::Int32Literal(0));
        }
        Ok(())
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
        if self.peek() == Some(&Token::LParen) {
            let Some((name, c_type)) =
                self.parse_function_pointer_declarator(parsed_type.c_type)?
            else {
                unreachable!("function-pointer declarator starts with a parenthesis");
            };
            let kernel_name = self.declare_name(&name)?;
            self.variable_types.insert(kernel_name.clone(), c_type);
            let declaration = C0Statement::Declare {
                c_type,
                name: kernel_name.clone(),
            };
            let statement = if self.peek() == Some(&Token::Equal) {
                self.position += 1;
                let expression = self.parse_expression()?;
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
                    .insert(name.clone(), struct_name);
                let declaration = C0Statement::DeclareStructValue {
                    name: name.clone(),
                    layout: layout.clone(),
                };
                let statement = if self.peek() == Some(&Token::Equal) {
                    self.position += 1;
                    if matches!(self.peek(), Some(Token::Ident(_)))
                        && self.peek_next() == Some(&Token::LParen)
                    {
                        let function_name = self.expect_ident("function name")?;
                        let arguments = self.parse_call_arguments()?;
                        let call =
                            self.call_assignment_statement(name.clone(), function_name, arguments)?;
                        C0Statement::Seq(Box::new(declaration), Box::new(call))
                    } else {
                        let expression = self.parse_expression()?;
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
            };
            let statement = if self.peek() == Some(&Token::Equal) {
                self.position += 1;
                if matches!(c_type, C0Type::Int32Array(_) | C0Type::UInt8Array(_)) {
                    if parsed_type.struct_name.is_some() {
                        return Err(self.error_here(
                            "local array initializers for struct arrays are not supported",
                        ));
                    }
                    let initializer =
                        self.parse_local_array_initializer(&name, c_type, array_shape.as_deref())?;
                    C0Statement::Seq(Box::new(declaration), Box::new(initializer))
                } else if matches!(self.peek(), Some(Token::Ident(_)))
                    && self.peek_next() == Some(&Token::LParen)
                {
                    let call_start = self.position;
                    let function_name = self.expect_ident("function name")?;
                    let arguments = self.parse_call_arguments()?;
                    if matches!(self.peek(), Some(Token::Comma | Token::Semicolon)) {
                        let call =
                            self.call_assignment_statement(name.clone(), function_name, arguments)?;
                        C0Statement::Seq(Box::new(declaration), Box::new(call))
                    } else {
                        self.position = call_start;
                        let expression = self.parse_expression()?;
                        C0Statement::Seq(
                            Box::new(declaration),
                            Box::new(C0Statement::Assign { name, expression }),
                        )
                    }
                } else {
                    let expression = self.parse_expression()?;
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

    fn struct_value_copy_statement(
        &self,
        target: &str,
        expression: C0Expression,
    ) -> Result<C0Statement, C0SyntaxError> {
        let source = match expression {
            C0Expression::Variable(name) => name,
            _ => {
                return Err(self.error_here(
                    "struct value initialization and assignment require another struct value",
                ));
            }
        };
        let target_struct = self
            .variable_struct_values
            .get(target)
            .ok_or_else(|| self.error_here(format!("`{target}` is not a struct value")))?;
        let source_struct = self
            .variable_struct_values
            .get(&source)
            .ok_or_else(|| self.error_here("struct value copies require a struct value source"))?;
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
                C0Type::Int16 | C0Type::Int32 | C0Type::UInt8 | C0Type::UInt16 => (field.c_type, 1),
                C0Type::Int32Array(length) => (C0Type::Int32, length),
                C0Type::UInt8Array(length) => (C0Type::UInt8, length),
                C0Type::Int32Pointer
                | C0Type::UInt8Pointer
                | C0Type::Int32PointerPointer
                | C0Type::UInt8PointerPointer => (field.c_type, 1),
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
                let target_pointer = offset_field_pointer(
                    C0Expression::Variable(target.to_string()),
                    element_offset,
                );
                let source_pointer =
                    offset_field_pointer(C0Expression::Variable(source.clone()), element_offset);
                stores.push(C0Statement::Store {
                    pointer: target_pointer,
                    value: C0Expression::Field {
                        pointer: Box::new(source_pointer),
                        field_type: element_type,
                        field_struct_name: None,
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
        if is_plain_struct_type(&parsed_type) {
            return Err(self.error_here("only pointer-to-struct types are supported"));
        }
        let mut initializers = Vec::new();
        loop {
            let source_name = self.expect_ident("for-loop local name")?;
            let name = self.declare_name(&source_name)?;
            self.variable_types.insert(name.clone(), parsed_type.c_type);
            if self.peek() != Some(&Token::Equal) {
                return Err(self.error_here("for-loop declarations require an initializer"));
            }
            self.position += 1;
            let expression = self.parse_expression()?;
            initializers.push(C0Statement::Seq(
                Box::new(C0Statement::Declare {
                    c_type: parsed_type.c_type,
                    name: name.clone(),
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
        self.expect(Token::Equal)?;
        let expression = self.parse_expression()?;
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
                let function_name = self.expect_ident("function name")?;
                let arguments = self.parse_call_arguments()?;
                return self.call_assignment_statement(name, function_name, arguments);
            }
            let expression = self.parse_expression()?;
            return self.struct_value_copy_statement(&name, expression);
        }
        let expression = match operator {
            Token::Equal => {
                if matches!(self.peek(), Some(Token::Ident(_)))
                    && self.peek_next() == Some(&Token::LParen)
                {
                    let call_start = self.position;
                    let function_name = self.expect_ident("function name")?;
                    let arguments = self.parse_call_arguments()?;
                    if self.peek() == Some(&Token::Semicolon) {
                        return self.call_assignment_statement(name, function_name, arguments);
                    }
                    self.position = call_start;
                }
                self.parse_expression()?
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
            C0Expression::Load(Box::new(self.parse_unary()?))
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
        if operator == Token::Equal {
            let value = self.parse_expression()?;
            return match target {
                C0Expression::Load(pointer) => Ok(C0Statement::Store {
                    pointer: *pointer,
                    value,
                    value_type: None,
                }),
                C0Expression::Field {
                    pointer,
                    field_type,
                    ..
                } => Ok(C0Statement::Store {
                    pointer: *pointer,
                    value,
                    value_type: Some(field_type),
                }),
                C0Expression::AggregateAddress { .. } => {
                    Err(self.error_here("assigning to an embedded struct value is not supported"))
                }
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
                    Some(C0Type::Int32PointerPointer) => matches!(
                        element_size,
                        C0Expression::Int32Literal(8)
                            | C0Expression::SizeOfType {
                                c_type: C0Type::Int32Pointer,
                                struct_name: None,
                                ..
                            }
                    ),
                    Some(C0Type::UInt8PointerPointer) => matches!(
                        element_size,
                        C0Expression::Int32Literal(8)
                            | C0Expression::SizeOfType {
                                c_type: C0Type::UInt8Pointer,
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
        if contains_aggregate_value(&expression) {
            return Err(self.error_here(
                "embedded struct fields are only supported through member access; struct values are not supported, and tagged union values are not runtime aggregates",
            ));
        }
        Ok(expression)
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

    fn lower_call_expressions(
        &mut self,
        statement: C0Statement,
    ) -> Result<C0Statement, C0SyntaxError> {
        if !statement_contains_embedded_call(&statement) {
            return Ok(statement);
        }
        self.lower_statement_calls(statement)
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
                let target = self.fresh_synthesized_call_name();
                prefix.push(C0Statement::CallAssign {
                    target: target.clone(),
                    function_name,
                    arguments,
                });
                Ok((prefix, C0Expression::Variable(target)))
            }
            C0Expression::Cast { expression, c_type } => {
                let (prefix, expression) = self.lower_expression_calls(*expression)?;
                Ok((
                    prefix,
                    C0Expression::Cast {
                        expression: Box::new(expression),
                        c_type,
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
                });
                prefix.push(C0Statement::If {
                    condition,
                    then_branch: Box::new(then_statement),
                    else_branch: Box::new(else_statement),
                });
                Ok((prefix, C0Expression::Variable(target)))
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
                array_shape,
            } => {
                let (prefix, pointer) = self.lower_expression_calls(*pointer)?;
                Ok((
                    prefix,
                    C0Expression::Field {
                        pointer: Box::new(pointer),
                        field_type,
                        field_struct_name,
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
        self.position += 1;
        let then_branch = self.parse_expression()?;
        self.expect(Token::Colon)?;
        let else_branch = self.parse_conditional()?;
        Ok(C0Expression::Conditional {
            condition: Box::new(condition),
            then_branch: Box::new(then_branch),
            else_branch: Box::new(else_branch),
        })
    }

    fn parse_call_arguments(&mut self) -> Result<Vec<C0Expression>, C0SyntaxError> {
        self.expect(Token::LParen)?;
        let mut arguments = Vec::new();
        if self.peek() == Some(&Token::RParen) {
            self.position += 1;
            return Ok(arguments);
        }

        loop {
            arguments.push(self.parse_expression()?);
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
            let c_type = match (
                parsed_type.c_type,
                parsed_type.struct_name,
                parsed_type.union_name,
            ) {
                (
                    C0Type::Int16 | C0Type::Int32 | C0Type::UInt8 | C0Type::UInt16 | C0Type::UInt32,
                    None,
                    None,
                ) => parsed_type.c_type,
                _ => {
                    return Err(self.error_at_previous(
                        "casts currently support only `int16`, `int32`, `uint8`, `uint16`, and `uint32` scalar values",
                    ));
                }
            };
            return Ok(C0Expression::Cast {
                expression: Box::new(self.parse_unary()?),
                c_type,
            });
        }

        if self.peek() == Some(&Token::Plus) {
            self.position += 1;
            return self.parse_unary();
        }
        if self.peek() == Some(&Token::Minus) {
            self.position += 1;
            if let Some(Token::Number(number)) = self.peek().cloned() {
                self.position += 1;
                let magnitude = parse_integer_literal_magnitude(&number).map_err(|reason| {
                    self.error_here(format!("invalid integer literal `{number}`: {reason}"))
                })?;
                if magnitude > (i32::MAX as u64) + 1 {
                    return Err(self.error_here(format!(
                        "negative int32 literal `-{number}` is out of range"
                    )));
                }
                let value = (-(magnitude as i64) as i32) as u32;
                return Ok(C0Expression::Int32Literal(value));
            }
            return Ok(C0Expression::Subtract(
                Box::new(C0Expression::Int32Literal(0)),
                Box::new(self.parse_unary()?),
            ));
        }

        if self.peek() == Some(&Token::Star) {
            self.position += 1;
            return Ok(C0Expression::Load(Box::new(self.parse_unary()?)));
        }

        if self.peek() == Some(&Token::Amp) {
            self.position += 1;
            if let Some(Token::Ident(name)) = self.peek().cloned()
                && !self.variable_types.contains_key(&self.resolve_name(&name))
            {
                self.position += 1;
                return Ok(C0Expression::FunctionAddress(name));
            }
            return Ok(C0Expression::AddressOf(Box::new(self.parse_unary()?)));
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
                    let function_name = match &expression {
                        C0Expression::Variable(name) => name.clone(),
                        _ => {
                            return Err(self.error_here(
                                "function calls currently require an identifier or function pointer",
                            ));
                        }
                    };
                    let arguments = self.parse_call_arguments()?;
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
                    let (pointer, field_type, field_struct_name, field_union_name, array_shape) =
                        if dot {
                            let struct_value = matches!(
                                &expression,
                                C0Expression::Variable(name)
                                    if self.variable_struct_values.contains_key(name)
                            );
                            if struct_value
                                || matches!(&expression, C0Expression::UnionAddress { .. })
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
            C0Expression::Field {
                field_type: C0Type::Int32Pointer,
                field_struct_name: Some(struct_name),
                ..
            } => Some(struct_name.clone()),
            _ => None,
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
            Option<Vec<u32>>,
        ),
        C0SyntaxError,
    > {
        let (struct_name, union_name) = match base {
            C0Expression::Variable(base_name) => (self.variable_structs.get(base_name), None),
            C0Expression::Field {
                field_struct_name, ..
            } => {
                if self.struct_array_field_info(base).is_some() {
                    return Err(self.error_here(
                        "arrays of embedded structs require an index before field access",
                    ));
                }
                (field_struct_name.as_ref(), None)
            }
            C0Expression::AggregateAddress { struct_name, .. } => (Some(struct_name), None),
            C0Expression::UnionAddress { union_name, .. } => (None, Some(union_name)),
            _ => (None, None),
        };
        if let Some(struct_name) = struct_name {
            let layout = self.structs.get(struct_name).ok_or_else(|| {
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
                    C0Expression::Cast { expression, c_type }
                        if *c_type == C0Type::UInt8Pointer
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
            Some(Token::Ident(name)) => match self.enum_constants.get(&name) {
                Some(value) => Ok(C0Expression::Int32Literal(*value as u32)),
                None => Ok(C0Expression::Variable(self.resolve_name(&name))),
            },
            Some(Token::Number(number)) => {
                let value = parse_integer_literal_magnitude(&number).map_err(|reason| {
                    at.error(format!("invalid integer literal `{number}`: {reason}"))
                })?;
                if value <= i32::MAX as u64 {
                    Ok(C0Expression::Int32Literal(value as u32))
                } else if integer_literal_has_unsigned_suffix(&number) && value <= u32::MAX as u64 {
                    Ok(C0Expression::UInt32Literal(value as u32))
                } else {
                    Err(at.error(format!("int32 literal `{number}` is out of range")))
                }
            }
            Some(Token::CharLiteral(value)) => Ok(C0Expression::UInt8Literal(value)),
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

    fn is_type_start_at(&self, offset: usize) -> bool {
        match self.peek_n(offset) {
            Some(Token::Ident(name)) => {
                is_builtin_type_start(name) || self.typedefs.contains_key(name)
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
    let suffix_start = if literal.starts_with("0x") || literal.starts_with("0X") {
        literal[2..]
            .find(|character: char| !character.is_ascii_hexdigit())
            .map_or(literal.len(), |offset| offset + 2)
    } else {
        literal
            .find(|character: char| character.is_ascii_alphabetic())
            .unwrap_or(literal.len())
    };
    let (digits, suffix) = literal.split_at(suffix_start);

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

fn integer_literal_has_unsigned_suffix(literal: &str) -> bool {
    literal
        .chars()
        .skip_while(|character| {
            character.is_ascii_hexdigit() || *character == 'x' || *character == 'X'
        })
        .any(|character| character.eq_ignore_ascii_case(&'u'))
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
            } else {
                index += 1;
                while index < chars.len() && chars[index].is_ascii_digit() {
                    index += 1;
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
        | C0Statement::HeapAllocate { .. }
        | C0Statement::HeapFree { .. }
        | C0Statement::Return(_)
        | C0Statement::Store { .. }
        | C0Statement::Update { .. }) => statement,
    }
}

fn statement_contains_embedded_call(statement: &C0Statement) -> bool {
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
                if expression_contains_embedded_call(expression) {
                    return true;
                }
            }
            C0Statement::CallAssign { arguments, .. } | C0Statement::Call { arguments, .. } => {
                if arguments.iter().any(expression_contains_embedded_call) {
                    return true;
                }
            }
            C0Statement::Store { pointer, value, .. } => {
                if expression_contains_embedded_call(pointer)
                    || expression_contains_embedded_call(value)
                {
                    return true;
                }
            }
            C0Statement::Update {
                target, operand, ..
            } => {
                if expression_contains_embedded_call(target)
                    || expression_contains_embedded_call(operand)
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
                if expression_contains_embedded_call(condition) {
                    return true;
                }
                statements.push(then_branch);
                statements.push(else_branch);
            }
            C0Statement::While { condition, body } | C0Statement::DoWhile { condition, body } => {
                if expression_contains_embedded_call(condition) {
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
                if expression_contains_embedded_call(condition) {
                    return true;
                }
                statements.push(initializer);
                statements.push(step);
                statements.push(body);
            }
            C0Statement::Switch { expression, cases } => {
                if expression_contains_embedded_call(expression) {
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

fn first_embedded_call_position(expression: &C0Expression) -> Option<SourcePosition> {
    match expression {
        C0Expression::Call {
            position,
            arguments,
            ..
        } => position.or_else(|| arguments.iter().find_map(first_embedded_call_position)),
        C0Expression::Cast { expression, .. }
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
        | C0Expression::SizeOfStruct { .. }
        | C0Expression::SizeOfUnion { .. }
        | C0Expression::SizeOfType { .. } => None,
    }
}

fn expression_contains_embedded_call(expression: &C0Expression) -> bool {
    let mut expressions = vec![expression];
    while let Some(expression) = expressions.pop() {
        match expression {
            C0Expression::Call { .. } => return true,
            C0Expression::Cast { expression, .. }
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
            | C0Expression::SizeOfStruct { .. }
            | C0Expression::SizeOfUnion { .. }
            | C0Expression::SizeOfType { .. } => {}
        }
    }
    false
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

fn is_ident_start(ch: char) -> bool {
    ch.is_ascii_alphabetic() || ch == '_'
}

fn is_ident_continue(ch: char) -> bool {
    ch.is_ascii_alphanumeric() || ch == '_'
}
