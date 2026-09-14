use std::collections::BTreeMap;

use serde::{Deserialize, Serialize};

pub(crate) const EXPORT_SCHEMA: u32 = 2;
pub(crate) const LANGUAGE: &str = "c++";
pub(crate) const STANDARD: &str = "c++20";
pub(crate) const TARGET: &str = "x86_64-unknown-linux-gnu";
pub(crate) const CLANG_VERSION: &str = "19.1.7";

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct CppExport {
    pub schema: u32,
    pub language: String,
    pub profile: CppProfile,
    pub logical_source: String,
    pub function: CppFunction,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct CppProfile {
    pub frontend: String,
    pub frontend_version: String,
    pub standard: String,
    pub target: String,
    pub exceptions: bool,
    pub rtti: bool,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct CppFunction {
    pub declaration_id: String,
    pub name: String,
    pub return_type: CppType,
    pub parameters: Vec<CppPlace>,
    pub is_noexcept: bool,
    pub span: CppSpan,
    pub body: Vec<CppStatement>,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(tag = "kind", rename_all = "snake_case", deny_unknown_fields)]
pub enum CppType {
    Boolean {
        bits: u32,
        is_const: bool,
    },
    Integer {
        bits: u32,
        signed: bool,
        is_const: bool,
    },
    LvalueReference {
        pointee: Box<CppType>,
    },
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct CppPlace {
    pub declaration_id: String,
    pub name: String,
    pub value_type: CppType,
    pub span: CppSpan,
}

#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum CppBinaryOperator {
    Add,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(tag = "kind", rename_all = "snake_case", deny_unknown_fields)]
pub enum CppExpression {
    IntegerLiteral {
        value: String,
        value_type: CppType,
        span: CppSpan,
    },
    Load {
        place: CppPlaceReference,
        value_type: CppType,
        span: CppSpan,
    },
    Binary {
        operator: CppBinaryOperator,
        left: Box<CppExpression>,
        right: Box<CppExpression>,
        value_type: CppType,
        span: CppSpan,
    },
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct CppPlaceReference {
    pub declaration_id: String,
    pub name: String,
    pub span: CppSpan,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(tag = "kind", rename_all = "snake_case", deny_unknown_fields)]
pub enum CppStatement {
    Assign {
        target: CppPlaceReference,
        value: CppExpression,
        span: CppSpan,
    },
    Return {
        value: CppExpression,
        span: CppSpan,
    },
    If {
        condition: CppExpression,
        then_branch: Vec<CppStatement>,
        else_branch: Vec<CppStatement>,
        span: CppSpan,
    },
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct CppSpan {
    pub file: String,
    pub start_line: u32,
    pub start_column: u32,
    pub end_line: u32,
    pub end_column: u32,
}

impl CppExport {
    pub(crate) fn validate(&self, logical_source: &str, function: &str) -> Result<(), String> {
        if self.schema != EXPORT_SCHEMA {
            return Err(format!(
                "unsupported C++ exporter schema {}; expected {EXPORT_SCHEMA}",
                self.schema
            ));
        }
        if self.language != LANGUAGE
            || self.profile.frontend != "clang"
            || self.profile.standard != STANDARD
            || self.profile.target != TARGET
            || self.profile.exceptions
            || self.profile.rtti
        {
            return Err(format!(
                "C++ export profile must be Clang {STANDARD} for {TARGET} with exceptions and RTTI disabled"
            ));
        }
        if !self.profile.frontend_version.contains(CLANG_VERSION) {
            return Err(format!(
                "C++ export used `{}`; expected Clang {CLANG_VERSION}",
                self.profile.frontend_version
            ));
        }
        if self.logical_source != logical_source {
            return Err(format!(
                "C++ export names logical source `{}` instead of `{logical_source}`",
                self.logical_source
            ));
        }
        self.function.validate(function, logical_source)
    }
}

impl CppFunction {
    fn validate(&self, expected_name: &str, logical_source: &str) -> Result<(), String> {
        if self.name != expected_name || self.declaration_id.is_empty() {
            return Err(format!(
                "C++ export resolved `{}` instead of selected function `{expected_name}`",
                self.name
            ));
        }
        require_int32(&self.return_type, false, "function return type")?;
        if !self.is_noexcept {
            return Err(format!(
                "selected C++ function `{expected_name}` must be explicitly non-throwing"
            ));
        }
        self.span.validate(logical_source)?;
        let mut places = BTreeMap::new();
        for parameter in &self.parameters {
            parameter.span.validate(logical_source)?;
            if parameter.declaration_id.is_empty() || parameter.name.is_empty() {
                return Err("C++ parameter is missing declaration identity".into());
            }
            match &parameter.value_type {
                CppType::Boolean { .. } => {
                    require_bool(&parameter.value_type, false, "by-value parameter")?;
                }
                CppType::LvalueReference { pointee } => {
                    require_int32(pointee, true, "reference pointee")?;
                }
                _ => {
                    return Err(
                        "the supported C++ parameters are by-value `bool`, `int&`, and `const int&`"
                            .into(),
                    );
                }
            }
            if places
                .insert(
                    parameter.declaration_id.clone(),
                    (parameter.name.clone(), parameter.value_type.clone()),
                )
                .is_some()
            {
                return Err(format!(
                    "duplicate C++ parameter declaration identity `{}`",
                    parameter.declaration_id
                ));
            }
        }
        if self.body.is_empty() {
            return Err("supported C++ function has no executable statements".into());
        }
        for statement in &self.body {
            statement.validate(&places, logical_source)?;
        }
        if !sequence_always_returns(&self.body) {
            return Err(
                "supported non-void C++ function can reach the end without returning".into(),
            );
        }
        Ok(())
    }
}

impl CppStatement {
    fn validate(
        &self,
        places: &BTreeMap<String, (String, CppType)>,
        logical_source: &str,
    ) -> Result<(), String> {
        match self {
            Self::Assign {
                target,
                value,
                span,
            } => {
                span.validate(logical_source)?;
                let target_type = validate_place_reference(target, places, logical_source)?;
                match target_type {
                    CppType::LvalueReference { pointee } => {
                        require_int32(pointee, false, "assignment target")?;
                    }
                    _ => return Err("C++ assignment target is not a mutable reference".into()),
                }
                value.validate(places, logical_source)?;
                require_int32(value.value_type(), false, "assignment value")
            }
            Self::Return { value, span } => {
                span.validate(logical_source)?;
                value.validate(places, logical_source)?;
                require_int32(value.value_type(), false, "return value")
            }
            Self::If {
                condition,
                then_branch,
                else_branch,
                span,
            } => {
                span.validate(logical_source)?;
                condition.validate(places, logical_source)?;
                require_bool(condition.value_type(), false, "if condition")?;
                for statement in then_branch.iter().chain(else_branch) {
                    statement.validate(places, logical_source)?;
                }
                Ok(())
            }
        }
    }
}

impl CppExpression {
    fn value_type(&self) -> &CppType {
        match self {
            Self::IntegerLiteral { value_type, .. }
            | Self::Load { value_type, .. }
            | Self::Binary { value_type, .. } => value_type,
        }
    }

    fn validate(
        &self,
        places: &BTreeMap<String, (String, CppType)>,
        logical_source: &str,
    ) -> Result<(), String> {
        match self {
            Self::IntegerLiteral {
                value,
                value_type,
                span,
            } => {
                value
                    .parse::<i32>()
                    .map_err(|_| format!("unsupported C++ integer literal `{value}`"))?;
                require_int32(value_type, false, "integer literal type")?;
                span.validate(logical_source)
            }
            Self::Load {
                place,
                value_type,
                span,
            } => {
                span.validate(logical_source)?;
                let place_type = validate_place_reference(place, places, logical_source)?;
                match place_type {
                    CppType::LvalueReference { pointee } => {
                        require_int32(pointee, true, "loaded reference pointee")?;
                        require_int32(value_type, false, "loaded value type")
                    }
                    CppType::Boolean { .. } => {
                        require_bool(place_type, false, "loaded parameter")?;
                        require_bool(value_type, false, "loaded value type")
                    }
                    _ => Err("C++ load does not name a supported parameter".into()),
                }
            }
            Self::Binary {
                left,
                right,
                value_type,
                span,
                ..
            } => {
                require_int32(value_type, false, "binary result type")?;
                span.validate(logical_source)?;
                left.validate(places, logical_source)?;
                right.validate(places, logical_source)?;
                require_int32(left.value_type(), false, "binary left operand")?;
                require_int32(right.value_type(), false, "binary right operand")
            }
        }
    }
}

fn sequence_always_returns(statements: &[CppStatement]) -> bool {
    statements.iter().any(CppStatement::always_returns)
}

impl CppStatement {
    fn always_returns(&self) -> bool {
        match self {
            Self::Return { .. } => true,
            Self::If {
                then_branch,
                else_branch,
                ..
            } => sequence_always_returns(then_branch) && sequence_always_returns(else_branch),
            Self::Assign { .. } => false,
        }
    }
}

impl CppSpan {
    fn validate(&self, logical_source: &str) -> Result<(), String> {
        if self.file != logical_source
            || self.start_line == 0
            || self.start_column == 0
            || self.end_line == 0
            || self.end_column == 0
            || (self.end_line, self.end_column) < (self.start_line, self.start_column)
        {
            return Err(format!("invalid C++ source span in `{}`", self.file));
        }
        Ok(())
    }
}

fn validate_place_reference<'a>(
    reference: &CppPlaceReference,
    places: &'a BTreeMap<String, (String, CppType)>,
    logical_source: &str,
) -> Result<&'a CppType, String> {
    reference.span.validate(logical_source)?;
    let Some((name, value_type)) = places.get(&reference.declaration_id) else {
        return Err(format!(
            "C++ expression refers to unknown declaration `{}`",
            reference.declaration_id
        ));
    };
    if name != &reference.name {
        return Err(format!(
            "C++ declaration `{}` is named `{name}`, not `{}`",
            reference.declaration_id, reference.name
        ));
    }
    Ok(value_type)
}

fn require_int32(value: &CppType, allow_const: bool, label: &str) -> Result<(), String> {
    match value {
        CppType::Integer {
            bits: 32,
            signed: true,
            is_const,
        } if allow_const || !is_const => Ok(()),
        _ => Err(format!("{label} is outside the first C++ `int` slice")),
    }
}

fn require_bool(value: &CppType, allow_const: bool, label: &str) -> Result<(), String> {
    match value {
        CppType::Boolean { bits: 8, is_const } if allow_const || !is_const => Ok(()),
        _ => Err(format!("{label} is outside the supported C++ `bool` slice")),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn schema_refuses_unknown_fields() {
        let input = br#"{"schema":1,"surprise":1}"#;
        let error = serde_json::from_slice::<CppExport>(input).unwrap_err();
        assert!(error.to_string().contains("unknown field"));
    }
}
