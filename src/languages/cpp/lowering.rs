//! Direct lowering from the pinned C++ semantic artifact to kernel execution.
//!
//! This adapter consumes Clang's already-typed nodes. It does not print C++ as
//! C, invoke the C parser, or infer types from source spellings. The first
//! slice represents `int&` and `const int&` as address-valued kernel parameters;
//! every C++ lvalue-to-rvalue conversion becomes a typed load through that
//! address and assignment writes the referent without reseating the reference.
//! Function-body scalar locals use the kernel's ordinary declaration,
//! assignment, and call-result statements.

use std::collections::BTreeMap;

use super::{
    CppBinaryOperator, CppCallArgument, CppExpression, CppFunction, CppInitializer, CppPlace,
    CppPlaceReference, CppStatement, CppType, PreparedCppImport,
};
use crate::kernel::{
    CExpression, CFunction, CStatement, CType, LoadSourceId, LoadSourceOwnerId, c_add, c_assign,
    c_call, c_call_assign, c_declare, c_function, c_if, c_int32_literal, c_parameter, c_return,
    c_seq, c_skip, c_typed_load_with_source, c_typed_store, c_variable,
};

/// One kernel function together with the immutable semantic artifact that
/// produced it. Keeping the source artifact attached retains Clang declaration
/// identities and spans even though they are not part of kernel equality.
#[derive(Clone, Debug)]
pub struct LoweredCppFunction {
    source: PreparedCppImport,
    function: CFunction,
    reachable_functions: Vec<CFunction>,
}

impl LoweredCppFunction {
    pub fn source(&self) -> &PreparedCppImport {
        &self.source
    }

    pub fn source_function(&self) -> &CppFunction {
        &self.source.export().function
    }

    pub fn kernel_function(&self) -> &CFunction {
        &self.function
    }

    pub fn reachable_kernel_functions(&self) -> &[CFunction] {
        &self.reachable_functions
    }
}

/// Lowers the first pinned C++ import slice directly to the kernel's checked
/// execution vocabulary.
pub fn lower_import(import: &PreparedCppImport) -> Result<LoweredCppFunction, String> {
    let function = lower_function(import, &import.export().function)?;
    let reachable_functions = import
        .export()
        .reachable_functions
        .iter()
        .map(|source| lower_function(import, source))
        .collect::<Result<Vec<_>, _>>()?;
    Ok(LoweredCppFunction {
        source: import.clone(),
        function,
        reachable_functions,
    })
}

fn lower_function(import: &PreparedCppImport, source: &CppFunction) -> Result<CFunction, String> {
    let places = source
        .parameters
        .iter()
        .chain(source.body.iter().filter_map(|statement| match statement {
            CppStatement::Declare { local, .. } => Some(local),
            _ => None,
        }))
        .map(|parameter| (parameter.declaration_id.as_str(), parameter))
        .collect::<BTreeMap<_, _>>();
    let parameters = source
        .parameters
        .iter()
        .map(lower_parameter)
        .collect::<Result<Vec<_>, _>>()?;
    let mut context = LoweringContext {
        source_unit: import.logical_source(),
        function_name: &source.name,
        places,
        next_load_occurrence: 0,
    };
    let body = context.lower_sequence(&source.body)?;
    Ok(c_function(
        CType::Int32,
        source.name.clone(),
        parameters,
        body,
    ))
}

fn lower_parameter(parameter: &CppPlace) -> Result<crate::kernel::CParameter, String> {
    match &parameter.value_type {
        CppType::Boolean {
            bits: 8,
            is_const: false,
        } => Ok(c_parameter(parameter.name.clone(), CType::Bool)),
        CppType::LvalueReference { pointee }
            if is_mutable_int32(pointee) || is_const_int32(pointee) =>
        {
            Ok(c_parameter(parameter.name.clone(), CType::Int32Pointer)
                .with_pointee_constant(is_const_int32(pointee)))
        }
        _ => Err(format!(
            "C++ parameter `{}` is outside direct by-value `bool`, `int&`, and `const int&` lowering",
            parameter.name
        )),
    }
}

struct LoweringContext<'a> {
    source_unit: &'a str,
    function_name: &'a str,
    places: BTreeMap<&'a str, &'a CppPlace>,
    next_load_occurrence: u32,
}

impl LoweringContext<'_> {
    fn lower_sequence(&mut self, statements: &[CppStatement]) -> Result<CStatement, String> {
        let mut statements = statements
            .iter()
            .map(|statement| self.lower_statement(statement));
        let Some(first) = statements.next() else {
            return Ok(c_skip());
        };
        let first = first?;
        statements.try_fold(first, |body, statement| {
            statement.map(|statement| c_seq(body, statement))
        })
    }

    fn lower_statement(&mut self, statement: &CppStatement) -> Result<CStatement, String> {
        match statement {
            CppStatement::Declare {
                local, initializer, ..
            } => {
                let declaration = c_declare(local.name.clone(), CType::Int32);
                let initialization = match initializer {
                    CppInitializer::Value { value } => {
                        c_assign(local.name.clone(), self.lower_expression(value)?)
                    }
                    CppInitializer::Call {
                        callee, arguments, ..
                    } => c_call_assign(
                        local.name.clone(),
                        callee.name.clone(),
                        self.lower_call_arguments(arguments)?,
                    ),
                };
                Ok(c_seq(declaration, initialization))
            }
            CppStatement::Assign { target, value, .. } => {
                let target_is_local =
                    matches!(self.place(target)?.value_type, CppType::Integer { .. });
                let value = self.lower_expression(value)?;
                if target_is_local {
                    Ok(c_assign(target.name.clone(), value))
                } else {
                    Ok(c_typed_store(
                        self.lower_place(target)?,
                        value,
                        CType::Int32,
                    ))
                }
            }
            CppStatement::Return { value, .. } => Ok(c_return(self.lower_expression(value)?)),
            CppStatement::If {
                condition,
                then_branch,
                else_branch,
                ..
            } => {
                let condition = self.lower_expression(condition)?;
                let then_branch = self.lower_sequence(then_branch)?;
                let else_branch = self.lower_sequence(else_branch)?;
                Ok(c_if(condition, then_branch, else_branch))
            }
            CppStatement::Call {
                callee, arguments, ..
            } => Ok(c_call(
                callee.name.clone(),
                self.lower_call_arguments(arguments)?,
            )),
        }
    }

    fn lower_call_arguments(
        &mut self,
        arguments: &[CppCallArgument],
    ) -> Result<Vec<CExpression>, String> {
        arguments
            .iter()
            .map(|argument| self.lower_call_argument(argument))
            .collect()
    }

    fn lower_call_argument(&mut self, argument: &CppCallArgument) -> Result<CExpression, String> {
        match argument {
            CppCallArgument::Value { value } => self.lower_expression(value),
            CppCallArgument::Reference { place } => self.lower_place(place),
        }
    }

    fn lower_expression(&mut self, expression: &CppExpression) -> Result<CExpression, String> {
        match expression {
            CppExpression::IntegerLiteral {
                value, value_type, ..
            } if is_mutable_int32(value_type) => {
                let value = value
                    .parse::<i32>()
                    .map_err(|_| format!("unsupported C++ integer literal `{value}`"))?;
                Ok(c_int32_literal(value as u32))
            }
            CppExpression::IntegerLiteral { .. } => {
                Err("C++ integer literal is outside direct `int` lowering".into())
            }
            CppExpression::Load {
                place, value_type, ..
            } => match (&self.place(place)?.value_type, value_type) {
                (
                    CppType::Boolean {
                        bits: 8,
                        is_const: false,
                    },
                    CppType::Boolean {
                        bits: 8,
                        is_const: false,
                    },
                ) => Ok(c_variable(place.name.clone())),
                (CppType::Integer { .. }, CppType::Integer { .. })
                    if is_mutable_int32(&self.place(place)?.value_type)
                        && is_mutable_int32(value_type) =>
                {
                    Ok(c_variable(place.name.clone()))
                }
                (CppType::LvalueReference { pointee }, value_type)
                    if (is_mutable_int32(pointee) || is_const_int32(pointee))
                        && is_mutable_int32(value_type) =>
                {
                    let pointer = self.lower_place(place)?;
                    let occurrence = self.next_load_occurrence;
                    self.next_load_occurrence = self
                        .next_load_occurrence
                        .checked_add(1)
                        .ok_or_else(|| "C++ load occurrence capacity exceeded".to_string())?;
                    Ok(c_typed_load_with_source(
                        pointer,
                        CType::Int32,
                        Some(LoadSourceId {
                            owner: LoadSourceOwnerId {
                                source_unit: self.source_unit.into(),
                                function: self.function_name.into(),
                            },
                            occurrence,
                        }),
                    ))
                }
                _ => Err("C++ load is outside direct bool/reference lowering".into()),
            },
            CppExpression::Binary {
                operator: CppBinaryOperator::Add,
                left,
                right,
                value_type,
                ..
            } if is_mutable_int32(value_type) => {
                let left = self.lower_expression(left)?;
                let right = self.lower_expression(right)?;
                Ok(c_add(left, right))
            }
            CppExpression::Binary { .. } => {
                Err("C++ binary expression is outside direct `int` lowering".into())
            }
        }
    }

    fn lower_place(&self, place: &CppPlaceReference) -> Result<CExpression, String> {
        self.place(place)?;
        Ok(c_variable(place.name.clone()))
    }

    fn place(&self, place: &CppPlaceReference) -> Result<&CppPlace, String> {
        let Some(parameter) = self.places.get(place.declaration_id.as_str()) else {
            return Err(format!(
                "C++ lowering found unknown declaration `{}`",
                place.declaration_id
            ));
        };
        if parameter.name != place.name {
            return Err(format!(
                "C++ declaration `{}` is named `{}`, not `{}`",
                place.declaration_id, parameter.name, place.name
            ));
        }
        Ok(parameter)
    }
}

fn is_mutable_int32(value_type: &CppType) -> bool {
    matches!(
        value_type,
        CppType::Integer {
            bits: 32,
            signed: true,
            is_const: false,
        }
    )
}

fn is_const_int32(value_type: &CppType) -> bool {
    matches!(
        value_type,
        CppType::Integer {
            bits: 32,
            signed: true,
            is_const: true,
        }
    )
}
