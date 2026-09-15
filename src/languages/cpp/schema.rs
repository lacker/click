use std::collections::BTreeMap;

use serde::{Deserialize, Serialize};

pub(crate) const EXPORT_SCHEMA: u32 = 9;
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
    pub records: Vec<CppRecord>,
    pub function: CppFunction,
    pub reachable_functions: Vec<CppFunction>,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct CppRecord {
    pub declaration_id: String,
    pub name: String,
    pub size_bytes: u32,
    pub alignment_bytes: u32,
    pub fields: Vec<CppField>,
    pub destructor: Option<CppFunctionReference>,
    pub span: CppSpan,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct CppField {
    pub declaration_id: String,
    pub name: String,
    pub value_type: CppType,
    pub offset_bytes: u32,
    pub size_bytes: u32,
    pub span: CppSpan,
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
    pub function_kind: CppFunctionKind,
    pub return_type: CppType,
    pub parameters: Vec<CppPlace>,
    pub is_noexcept: bool,
    pub span: CppSpan,
    pub body: Vec<CppStatement>,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(tag = "kind", rename_all = "snake_case", deny_unknown_fields)]
pub enum CppFunctionKind {
    Free,
    Constructor {
        record_declaration_id: String,
        record_name: String,
    },
    Destructor {
        record_declaration_id: String,
        record_name: String,
    },
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(tag = "kind", rename_all = "snake_case", deny_unknown_fields)]
pub enum CppType {
    Void,
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
    Pointer {
        pointee: Box<CppType>,
    },
    Record {
        declaration_id: String,
        name: String,
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
    AddressOf {
        place: CppPlaceReference,
        value_type: CppType,
        span: CppSpan,
    },
    Dereference {
        pointer: Box<CppExpression>,
        value_type: CppType,
        span: CppSpan,
    },
    MemberLoad {
        object: CppPlaceReference,
        field: CppFieldReference,
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
#[serde(deny_unknown_fields)]
pub struct CppFunctionReference {
    pub declaration_id: String,
    pub name: String,
    pub span: CppSpan,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct CppFieldReference {
    pub record_declaration_id: String,
    pub declaration_id: String,
    pub name: String,
    pub span: CppSpan,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct CppFieldInitializer {
    pub field: CppFieldReference,
    pub value: CppExpression,
    pub span: CppSpan,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(tag = "kind", rename_all = "snake_case", deny_unknown_fields)]
pub enum CppCleanup {
    Destructor {
        object: CppPlaceReference,
        callee: CppFunctionReference,
        span: CppSpan,
    },
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(tag = "kind", rename_all = "snake_case", deny_unknown_fields)]
pub enum CppCallArgument {
    Value { value: CppExpression },
    Reference { place: CppPlaceReference },
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(tag = "kind", rename_all = "snake_case", deny_unknown_fields)]
pub enum CppInitializer {
    Value {
        value: CppExpression,
    },
    Call {
        callee: CppFunctionReference,
        arguments: Vec<CppCallArgument>,
        span: CppSpan,
    },
    Aggregate {
        fields: Vec<CppFieldInitializer>,
        span: CppSpan,
    },
    Constructor {
        callee: CppFunctionReference,
        arguments: Vec<CppCallArgument>,
        span: CppSpan,
    },
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(tag = "kind", rename_all = "snake_case", deny_unknown_fields)]
pub enum CppStatement {
    Declare {
        local: CppPlace,
        initializer: CppInitializer,
        span: CppSpan,
    },
    Assign {
        target: CppPlaceReference,
        value: CppExpression,
        span: CppSpan,
    },
    Store {
        pointer: CppExpression,
        value: CppExpression,
        span: CppSpan,
    },
    MemberStore {
        object: CppPlaceReference,
        field: CppFieldReference,
        value: CppExpression,
        span: CppSpan,
    },
    Return {
        value: CppExpression,
        cleanups: Vec<CppCleanup>,
        span: CppSpan,
    },
    If {
        condition: CppExpression,
        then_branch: Vec<CppStatement>,
        else_branch: Vec<CppStatement>,
        span: CppSpan,
    },
    Call {
        callee: CppFunctionReference,
        arguments: Vec<CppCallArgument>,
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
        if self.function.name != function {
            return Err(format!(
                "C++ export resolved `{}` instead of selected function `{function}`",
                self.function.name
            ));
        }
        if !matches!(self.function.function_kind, CppFunctionKind::Free) {
            return Err("the selected C++ declaration must be a free function".into());
        }

        if self.records.len() > 1 {
            return Err("the first C++ object slice supports exactly one record type".into());
        }
        let mut records = BTreeMap::new();
        for record in &self.records {
            record.validate(logical_source)?;
            if records
                .insert(record.declaration_id.clone(), record)
                .is_some()
            {
                return Err(format!(
                    "duplicate C++ record declaration identity `{}`",
                    record.declaration_id
                ));
            }
        }

        let mut functions = BTreeMap::new();
        let mut names = BTreeMap::new();
        for source in std::iter::once(&self.function).chain(&self.reachable_functions) {
            source.validate(logical_source, &records)?;
            if functions
                .insert(source.declaration_id.clone(), source)
                .is_some()
            {
                return Err(format!(
                    "duplicate C++ function declaration identity `{}`",
                    source.declaration_id
                ));
            }
            if let Some(previous) = names.insert(source.name.clone(), source.declaration_id.clone())
            {
                return Err(format!(
                    "reachable C++ functions `{previous}` and `{}` share unsupported overloaded name `{}`",
                    source.declaration_id, source.name
                ));
            }
        }

        for record in &self.records {
            let Some(destructor) = &record.destructor else {
                continue;
            };
            let target = functions.get(&destructor.declaration_id).ok_or_else(|| {
                format!(
                    "C++ record `{}` refers to missing destructor definition `{}`",
                    record.name, destructor.declaration_id
                )
            })?;
            if target.name != destructor.name {
                return Err(format!(
                    "C++ destructor declaration `{}` is named `{}`, not `{}`",
                    destructor.declaration_id, target.name, destructor.name
                ));
            }
            if !matches!(
                &target.function_kind,
                CppFunctionKind::Destructor {
                    record_declaration_id,
                    record_name,
                } if record_declaration_id == &record.declaration_id
                    && record_name == &record.name
            ) {
                return Err(format!(
                    "C++ record `{}` has a mismatched destructor declaration",
                    record.name
                ));
            }
        }

        let mut visiting = Vec::new();
        let mut visited = std::collections::BTreeSet::new();
        validate_reachable_calls(
            &self.function.declaration_id,
            &functions,
            &mut visiting,
            &mut visited,
            logical_source,
        )?;
        if visited.len() != functions.len() {
            return Err(
                "C++ export contains a function outside the selected function's reachable graph"
                    .into(),
            );
        }
        Ok(())
    }
}

impl CppRecord {
    fn validate(&self, logical_source: &str) -> Result<(), String> {
        if self.declaration_id.is_empty() || self.name.is_empty() {
            return Err("C++ record is missing declaration identity".into());
        }
        self.span.validate(logical_source)?;
        if let Some(destructor) = &self.destructor {
            if destructor.declaration_id.is_empty() || destructor.name.is_empty() {
                return Err(format!(
                    "C++ record `{}` has an unidentified destructor",
                    self.name
                ));
            }
            destructor.span.validate(logical_source)?;
        }
        if self.fields.is_empty()
            || self.alignment_bytes == 0
            || !self.alignment_bytes.is_power_of_two()
            || self.size_bytes == 0
            || !self.size_bytes.is_multiple_of(self.alignment_bytes)
        {
            return Err(format!("C++ record `{}` has an invalid layout", self.name));
        }
        let mut identities = std::collections::BTreeSet::new();
        let mut names = std::collections::BTreeSet::new();
        let mut previous_end = 0u32;
        for field in &self.fields {
            field.span.validate(logical_source)?;
            if field.declaration_id.is_empty() || field.name.is_empty() {
                return Err(format!(
                    "C++ record `{}` has an unidentified field",
                    self.name
                ));
            }
            if !identities.insert(field.declaration_id.clone()) || !names.insert(field.name.clone())
            {
                return Err(format!("C++ record `{}` has a duplicate field", self.name));
            }
            let (size, alignment) = match &field.value_type {
                CppType::Integer { .. } => {
                    require_int32(&field.value_type, false, "record field")?;
                    (4, 4)
                }
                CppType::Pointer { pointee } => {
                    require_int32(pointee, false, "record pointer field")?;
                    (8, 8)
                }
                _ => {
                    return Err(format!(
                        "C++ record field `{}.{}` is outside the `int`/`int*` slice",
                        self.name, field.name
                    ));
                }
            };
            let end = field
                .offset_bytes
                .checked_add(field.size_bytes)
                .ok_or_else(|| format!("C++ record `{}` field layout overflows", self.name))?;
            if field.size_bytes != size
                || field.offset_bytes % alignment != 0
                || field.offset_bytes < previous_end
                || end > self.size_bytes
            {
                return Err(format!(
                    "C++ record field `{}.{}` has an invalid layout",
                    self.name, field.name
                ));
            }
            previous_end = end;
        }
        Ok(())
    }
}

impl CppFunction {
    fn place_type(&self, declaration_id: &str) -> Option<&CppType> {
        self.parameters
            .iter()
            .chain(self.body.iter().filter_map(|statement| match statement {
                CppStatement::Declare { local, .. } => Some(local),
                _ => None,
            }))
            .find(|place| place.declaration_id == declaration_id)
            .map(|place| &place.value_type)
    }

    fn validate(
        &self,
        logical_source: &str,
        records: &BTreeMap<String, &CppRecord>,
    ) -> Result<(), String> {
        if self.name.is_empty() || self.declaration_id.is_empty() {
            return Err("C++ function is missing declaration identity".into());
        }
        match &self.function_kind {
            CppFunctionKind::Free => {
                require_int32(&self.return_type, false, "function return type")?;
            }
            CppFunctionKind::Constructor {
                record_declaration_id,
                record_name,
            }
            | CppFunctionKind::Destructor {
                record_declaration_id,
                record_name,
            } => {
                if self.return_type != CppType::Void {
                    return Err(format!(
                        "C++ object operation `{}` must have void artifact return type",
                        self.name
                    ));
                }
                validate_record_reference(records, record_declaration_id, record_name)?;
            }
        }
        if !self.is_noexcept {
            return Err(format!(
                "C++ function `{}` must be explicitly non-throwing",
                self.name
            ));
        }
        self.span.validate(logical_source)?;
        let mut places = BTreeMap::new();
        let mut names = std::collections::BTreeSet::new();
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
                    if let CppType::Record {
                        declaration_id,
                        name,
                    } = pointee.as_ref()
                    {
                        validate_record_reference(records, declaration_id, name)?;
                    } else {
                        require_int32(pointee, true, "reference pointee")?;
                    }
                }
                CppType::Pointer { pointee } => {
                    require_int32(pointee, false, "pointer pointee")?;
                }
                _ => {
                    return Err(
                        "the supported C++ parameters are by-value `bool`, `int&`, `const int&`, `int*`, and one simple record reference"
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
            if !names.insert(parameter.name.clone()) {
                return Err(format!("duplicate C++ parameter name `{}`", parameter.name));
            }
        }
        if let CppFunctionKind::Constructor {
            record_declaration_id,
            record_name,
        }
        | CppFunctionKind::Destructor {
            record_declaration_id,
            record_name,
        } = &self.function_kind
        {
            let Some(self_parameter) = self.parameters.first() else {
                return Err(format!(
                    "C++ object operation `{}` is missing its explicit object parameter",
                    self.name
                ));
            };
            if self_parameter.name != "self"
                || !matches!(
                    &self_parameter.value_type,
                    CppType::LvalueReference { pointee }
                        if matches!(
                            pointee.as_ref(),
                            CppType::Record { declaration_id, name }
                                if declaration_id == record_declaration_id && name == record_name
                        )
                )
            {
                return Err(format!(
                    "C++ object operation `{}` has an invalid explicit object parameter",
                    self.name
                ));
            }
            if matches!(self.function_kind, CppFunctionKind::Destructor { .. })
                && self.parameters.len() != 1
            {
                return Err(format!(
                    "C++ destructor `{}` cannot have explicit parameters",
                    self.name
                ));
            }
        }
        if let CppFunctionKind::Constructor {
            record_declaration_id,
            record_name,
        } = &self.function_kind
        {
            let self_parameter = &self.parameters[0];
            let record = validate_record_reference(records, record_declaration_id, record_name)?;
            if self.body.len() < record.fields.len() {
                return Err(format!(
                    "C++ constructor `{}` does not initialize every field",
                    self.name
                ));
            }
            for (statement, expected_field) in self.body.iter().zip(&record.fields) {
                let CppStatement::MemberStore {
                    object,
                    field,
                    value,
                    ..
                } = statement
                else {
                    return Err(format!(
                        "C++ constructor `{}` must begin with member initialization in declaration order",
                        self.name
                    ));
                };
                if object.declaration_id != self_parameter.declaration_id
                    || object.name != self_parameter.name
                    || field.record_declaration_id != *record_declaration_id
                    || field.declaration_id != expected_field.declaration_id
                    || field.name != expected_field.name
                    || value.references_place(&self_parameter.declaration_id)
                {
                    return Err(format!(
                        "C++ constructor `{}` has an invalid initializer for field `{}`",
                        self.name, expected_field.name
                    ));
                }
            }
        }
        if self.body.is_empty() {
            return Err("supported C++ function has no executable statements".into());
        }
        let mut aggregate_locals = 0;
        let mut destructible_local = None;
        for statement in &self.body {
            if let CppStatement::Declare {
                local,
                initializer,
                span,
            } = statement
            {
                span.validate(logical_source)?;
                local.span.validate(logical_source)?;
                if local.declaration_id.is_empty() || local.name.is_empty() {
                    return Err("C++ local is missing declaration identity".into());
                }
                match &local.value_type {
                    CppType::Integer { .. } => {
                        require_int32(&local.value_type, false, "automatic local")?;
                    }
                    CppType::Record {
                        declaration_id,
                        name,
                    } => {
                        let record = validate_record_reference(records, declaration_id, name)?;
                        aggregate_locals += 1;
                        if aggregate_locals > 1 {
                            return Err(format!(
                                "C++ function `{}` declares more than one aggregate local",
                                self.name
                            ));
                        }
                        if record.destructor.is_some() {
                            if !matches!(initializer, CppInitializer::Constructor { .. }) {
                                return Err(format!(
                                    "C++ local `{}` with nontrivial destruction requires direct constructor initialization",
                                    local.name
                                ));
                            }
                            destructible_local = Some(local.clone());
                        }
                    }
                    _ => {
                        return Err(
                            "the supported automatic C++ local must be mutable `int` or one simple aggregate object"
                                .into(),
                        );
                    }
                }
                initializer.validate_for_local(
                    &local.value_type,
                    &places,
                    records,
                    logical_source,
                )?;
                if places
                    .insert(
                        local.declaration_id.clone(),
                        (local.name.clone(), local.value_type.clone()),
                    )
                    .is_some()
                {
                    return Err(format!(
                        "duplicate C++ local declaration identity `{}`",
                        local.declaration_id
                    ));
                }
                if !names.insert(local.name.clone()) {
                    return Err(format!(
                        "C++ local `{}` shadows another supported place",
                        local.name
                    ));
                }
            } else {
                statement.validate(&places, records, logical_source)?;
            }
        }
        if let Some(local) = destructible_local {
            let Some(CppStatement::Return { .. }) = self.body.last() else {
                return Err(format!(
                    "C++ function `{}` with automatic destruction requires one final return",
                    self.name
                ));
            };
            validate_return_cleanups(&self.body, &self.name, &local)?;
        } else if sequence_contains_cleanup(&self.body) {
            return Err(format!(
                "C++ function `{}` has cleanup without a constructed automatic object",
                self.name
            ));
        }
        match &self.function_kind {
            CppFunctionKind::Free if !sequence_always_returns(&self.body) => {
                return Err(
                    "supported non-void C++ function can reach the end without returning".into(),
                );
            }
            CppFunctionKind::Constructor { .. } | CppFunctionKind::Destructor { .. }
                if sequence_contains_return(&self.body) =>
            {
                return Err(
                    "supported C++ constructor/destructor body cannot contain a return statement"
                        .into(),
                );
            }
            _ => {}
        }
        Ok(())
    }
}

impl CppStatement {
    fn validate(
        &self,
        places: &BTreeMap<String, (String, CppType)>,
        records: &BTreeMap<String, &CppRecord>,
        logical_source: &str,
    ) -> Result<(), String> {
        match self {
            Self::Declare { .. } => {
                Err("automatic C++ locals are currently supported only in the function body".into())
            }
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
                    CppType::Integer { .. } => {
                        require_int32(target_type, false, "assignment target")?;
                    }
                    _ => {
                        return Err(
                            "C++ assignment target is not a mutable reference or local".into()
                        );
                    }
                }
                value.validate(places, records, logical_source)?;
                require_int32(value.value_type(), false, "assignment value")
            }
            Self::Store {
                pointer,
                value,
                span,
            } => {
                span.validate(logical_source)?;
                pointer.validate(places, records, logical_source)?;
                require_mutable_int32_pointer(pointer.value_type(), "store pointer")?;
                value.validate(places, records, logical_source)?;
                require_int32(value.value_type(), false, "stored value")
            }
            Self::MemberStore {
                object,
                field,
                value,
                span,
            } => {
                span.validate(logical_source)?;
                let field_type =
                    validate_member_reference(object, field, places, records, logical_source)?;
                value.validate(places, records, logical_source)?;
                if value.value_type() != field_type {
                    return Err(format!(
                        "C++ member store to `{}` has a mismatched value type",
                        field.name
                    ));
                }
                Ok(())
            }
            Self::Return {
                value,
                cleanups,
                span,
            } => {
                span.validate(logical_source)?;
                value.validate(places, records, logical_source)?;
                require_int32(value.value_type(), false, "return value")?;
                for cleanup in cleanups {
                    cleanup.validate(places, records, logical_source)?;
                }
                Ok(())
            }
            Self::If {
                condition,
                then_branch,
                else_branch,
                span,
            } => {
                span.validate(logical_source)?;
                condition.validate(places, records, logical_source)?;
                require_bool(condition.value_type(), false, "if condition")?;
                for statement in then_branch.iter().chain(else_branch) {
                    statement.validate(places, records, logical_source)?;
                }
                Ok(())
            }
            Self::Call {
                callee,
                arguments,
                span,
            } => validate_call(callee, arguments, span, places, records, logical_source),
        }
    }
}

impl CppCleanup {
    fn validate(
        &self,
        places: &BTreeMap<String, (String, CppType)>,
        records: &BTreeMap<String, &CppRecord>,
        logical_source: &str,
    ) -> Result<(), String> {
        match self {
            Self::Destructor {
                object,
                callee,
                span,
            } => {
                span.validate(logical_source)?;
                callee.span.validate(logical_source)?;
                let CppType::Record {
                    declaration_id,
                    name,
                } = validate_place_reference(object, places, logical_source)?
                else {
                    return Err("C++ destructor cleanup must name a record object".into());
                };
                let record = validate_record_reference(records, declaration_id, name)?;
                let Some(destructor) = &record.destructor else {
                    return Err(format!(
                        "C++ cleanup names trivially destructible record `{}`",
                        record.name
                    ));
                };
                if destructor.declaration_id != callee.declaration_id
                    || destructor.name != callee.name
                {
                    return Err(format!(
                        "C++ cleanup for `{}` names the wrong destructor",
                        object.name
                    ));
                }
                Ok(())
            }
        }
    }
}

impl CppInitializer {
    fn validate_for_local(
        &self,
        local_type: &CppType,
        places: &BTreeMap<String, (String, CppType)>,
        records: &BTreeMap<String, &CppRecord>,
        logical_source: &str,
    ) -> Result<(), String> {
        match (self, local_type) {
            (Self::Value { value }, CppType::Integer { .. }) => {
                value.validate(places, records, logical_source)?;
                require_int32(value.value_type(), false, "local initializer")
            }
            (
                Self::Call {
                    callee,
                    arguments,
                    span,
                },
                CppType::Integer { .. },
            ) => validate_call(callee, arguments, span, places, records, logical_source),
            (
                Self::Aggregate { fields, span },
                CppType::Record {
                    declaration_id,
                    name,
                },
            ) => {
                span.validate(logical_source)?;
                let record = validate_record_reference(records, declaration_id, name)?;
                if fields.len() != record.fields.len() {
                    return Err(format!(
                        "C++ aggregate initializer for `{name}` must initialize every field"
                    ));
                }
                for (initializer, expected) in fields.iter().zip(&record.fields) {
                    initializer.span.validate(logical_source)?;
                    initializer.field.span.validate(logical_source)?;
                    if initializer.field.record_declaration_id != *declaration_id
                        || initializer.field.declaration_id != expected.declaration_id
                        || initializer.field.name != expected.name
                    {
                        return Err(format!(
                            "C++ aggregate initializer for `{name}` does not follow declaration order"
                        ));
                    }
                    initializer
                        .value
                        .validate(places, records, logical_source)?;
                    if initializer.value.value_type() != &expected.value_type {
                        return Err(format!(
                            "C++ aggregate initializer for `{}.{}` has a mismatched value type",
                            name, expected.name
                        ));
                    }
                }
                Ok(())
            }
            (
                Self::Constructor {
                    callee,
                    arguments,
                    span,
                },
                CppType::Record { .. },
            ) => validate_call(callee, arguments, span, places, records, logical_source),
            (Self::Aggregate { .. }, _) => {
                Err("C++ aggregate initializer requires a supported record local".into())
            }
            (Self::Constructor { .. }, _) => {
                Err("C++ constructor initializer requires a supported record local".into())
            }
            (_, CppType::Record { .. }) => Err(
                "C++ record local requires direct aggregate or constructor initialization".into(),
            ),
            _ => Err("unsupported C++ local initializer".into()),
        }
    }
}

fn validate_call(
    callee: &CppFunctionReference,
    arguments: &[CppCallArgument],
    span: &CppSpan,
    places: &BTreeMap<String, (String, CppType)>,
    records: &BTreeMap<String, &CppRecord>,
    logical_source: &str,
) -> Result<(), String> {
    span.validate(logical_source)?;
    callee.span.validate(logical_source)?;
    if callee.declaration_id.is_empty() || callee.name.is_empty() {
        return Err("C++ call is missing resolved declaration identity".into());
    }
    for argument in arguments {
        argument.validate(places, records, logical_source)?;
    }
    Ok(())
}

impl CppCallArgument {
    fn validate(
        &self,
        places: &BTreeMap<String, (String, CppType)>,
        records: &BTreeMap<String, &CppRecord>,
        logical_source: &str,
    ) -> Result<(), String> {
        match self {
            Self::Value { value } => value.validate(places, records, logical_source),
            Self::Reference { place } => {
                let value_type = validate_place_reference(place, places, logical_source)?;
                match value_type {
                    CppType::LvalueReference { pointee } => {
                        require_int32(pointee, true, "call reference argument")
                    }
                    _ => Err("C++ reference argument does not name a supported reference".into()),
                }
            }
        }
    }
}

impl CppExpression {
    pub(crate) fn value_type(&self) -> &CppType {
        match self {
            Self::IntegerLiteral { value_type, .. }
            | Self::Load { value_type, .. }
            | Self::AddressOf { value_type, .. }
            | Self::Dereference { value_type, .. }
            | Self::MemberLoad { value_type, .. }
            | Self::Binary { value_type, .. } => value_type,
        }
    }

    fn references_place(&self, declaration_id: &str) -> bool {
        match self {
            Self::IntegerLiteral { .. } => false,
            Self::Load { place, .. } | Self::AddressOf { place, .. } => {
                place.declaration_id == declaration_id
            }
            Self::Dereference { pointer, .. } => pointer.references_place(declaration_id),
            Self::MemberLoad { object, .. } => object.declaration_id == declaration_id,
            Self::Binary { left, right, .. } => {
                left.references_place(declaration_id) || right.references_place(declaration_id)
            }
        }
    }

    fn validate(
        &self,
        places: &BTreeMap<String, (String, CppType)>,
        records: &BTreeMap<String, &CppRecord>,
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
                    CppType::Integer { .. } => {
                        require_int32(place_type, false, "loaded local")?;
                        require_int32(value_type, false, "loaded value type")
                    }
                    CppType::Pointer { .. } => {
                        require_mutable_int32_pointer(place_type, "loaded pointer parameter")?;
                        require_mutable_int32_pointer(value_type, "loaded pointer value type")
                    }
                    CppType::Record { .. } => {
                        Err("C++ record values cannot be loaded or copied".into())
                    }
                    CppType::Void => Err("C++ void values cannot be loaded".into()),
                }
            }
            Self::AddressOf {
                place,
                value_type,
                span,
            } => {
                span.validate(logical_source)?;
                let place_type = validate_place_reference(place, places, logical_source)?;
                match place_type {
                    CppType::LvalueReference { pointee } => {
                        require_int32(pointee, false, "addressed reference pointee")?;
                    }
                    _ => {
                        return Err(
                            "supported C++ address-of must name a mutable `int&` parameter".into(),
                        );
                    }
                }
                require_mutable_int32_pointer(value_type, "address-of result type")
            }
            Self::Dereference {
                pointer,
                value_type,
                span,
            } => {
                span.validate(logical_source)?;
                pointer.validate(places, records, logical_source)?;
                require_mutable_int32_pointer(pointer.value_type(), "dereference operand")?;
                require_int32(value_type, false, "dereference result type")
            }
            Self::MemberLoad {
                object,
                field,
                value_type,
                span,
            } => {
                span.validate(logical_source)?;
                let field_type =
                    validate_member_reference(object, field, places, records, logical_source)?;
                if value_type != field_type {
                    return Err(format!(
                        "C++ member load of `{}` has a mismatched value type",
                        field.name
                    ));
                }
                Ok(())
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
                left.validate(places, records, logical_source)?;
                right.validate(places, records, logical_source)?;
                require_int32(left.value_type(), false, "binary left operand")?;
                require_int32(right.value_type(), false, "binary right operand")
            }
        }
    }
}

fn sequence_always_returns(statements: &[CppStatement]) -> bool {
    statements.iter().any(CppStatement::always_returns)
}

fn sequence_contains_return(statements: &[CppStatement]) -> bool {
    statements.iter().any(|statement| match statement {
        CppStatement::Return { .. } => true,
        CppStatement::If {
            then_branch,
            else_branch,
            ..
        } => sequence_contains_return(then_branch) || sequence_contains_return(else_branch),
        _ => false,
    })
}

fn sequence_contains_cleanup(statements: &[CppStatement]) -> bool {
    statements.iter().any(|statement| match statement {
        CppStatement::Return { cleanups, .. } => !cleanups.is_empty(),
        CppStatement::If {
            then_branch,
            else_branch,
            ..
        } => sequence_contains_cleanup(then_branch) || sequence_contains_cleanup(else_branch),
        _ => false,
    })
}

fn validate_return_cleanups(
    statements: &[CppStatement],
    function_name: &str,
    local: &CppPlace,
) -> Result<(), String> {
    for statement in statements {
        match statement {
            CppStatement::Return { cleanups, .. } => {
                if !matches!(
                    cleanups.as_slice(),
                    [CppCleanup::Destructor { object, .. }]
                        if object.declaration_id == local.declaration_id
                            && object.name == local.name
                ) {
                    return Err(format!(
                        "C++ return from `{function_name}` must destroy local `{}` exactly once",
                        local.name
                    ));
                }
            }
            CppStatement::If {
                then_branch,
                else_branch,
                ..
            } => {
                validate_return_cleanups(then_branch, function_name, local)?;
                validate_return_cleanups(else_branch, function_name, local)?;
            }
            CppStatement::Declare { .. }
            | CppStatement::Assign { .. }
            | CppStatement::Store { .. }
            | CppStatement::MemberStore { .. }
            | CppStatement::Call { .. } => {}
        }
    }
    Ok(())
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
            Self::Declare { .. }
            | Self::Assign { .. }
            | Self::Store { .. }
            | Self::MemberStore { .. }
            | Self::Call { .. } => false,
        }
    }
}

fn validate_reachable_calls(
    declaration_id: &str,
    functions: &BTreeMap<String, &CppFunction>,
    visiting: &mut Vec<String>,
    visited: &mut std::collections::BTreeSet<String>,
    logical_source: &str,
) -> Result<(), String> {
    if visited.contains(declaration_id) {
        return Ok(());
    }
    if let Some(start) = visiting.iter().position(|active| active == declaration_id) {
        let mut cycle = visiting[start..]
            .iter()
            .filter_map(|identity| {
                functions
                    .get(identity)
                    .map(|function| function.name.as_str())
            })
            .collect::<Vec<_>>();
        cycle.push(
            functions
                .get(declaration_id)
                .map_or("<unknown>", |function| function.name.as_str()),
        );
        return Err(format!(
            "recursive C++ calls are outside the supported slice: {}",
            cycle.join(" -> ")
        ));
    }
    let function = functions.get(declaration_id).ok_or_else(|| {
        format!("C++ reachable graph refers to missing declaration `{declaration_id}`")
    })?;
    visiting.push(declaration_id.to_string());
    let mut calls = Vec::new();
    collect_calls(&function.body, &mut calls);
    for call in calls {
        let (callee, arguments) = match &call {
            CollectedCall::Ordinary { callee, arguments }
            | CollectedCall::Constructor {
                callee, arguments, ..
            } => (*callee, *arguments),
            CollectedCall::Destructor { callee, .. } => (*callee, &[][..]),
        };
        callee.span.validate(logical_source)?;
        let target = functions.get(&callee.declaration_id).ok_or_else(|| {
            format!(
                "C++ call to `{}` refers to missing reachable definition `{}`",
                callee.name, callee.declaration_id
            )
        })?;
        if target.name != callee.name {
            return Err(format!(
                "C++ declaration `{}` is named `{}`, not `{}`",
                callee.declaration_id, target.name, callee.name
            ));
        }
        match call {
            CollectedCall::Ordinary { .. } => {
                if !matches!(target.function_kind, CppFunctionKind::Free) {
                    return Err(format!(
                        "ordinary C++ call from `{}` cannot invoke object operation `{}`",
                        function.name, target.name
                    ));
                }
                validate_call_arguments(
                    function,
                    target.name.as_str(),
                    &target.parameters,
                    arguments,
                )?;
            }
            CollectedCall::Constructor { local, .. } => {
                let CppFunctionKind::Constructor {
                    record_declaration_id,
                    record_name,
                } = &target.function_kind
                else {
                    return Err(format!(
                        "C++ local `{}` construction refers to non-constructor `{}`",
                        local.name, target.name
                    ));
                };
                if !matches!(
                    &local.value_type,
                    CppType::Record { declaration_id, name }
                        if declaration_id == record_declaration_id && name == record_name
                ) {
                    return Err(format!(
                        "C++ constructor `{}` does not construct local `{}`",
                        target.name, local.name
                    ));
                }
                let Some((_, explicit_parameters)) = target.parameters.split_first() else {
                    return Err(format!(
                        "C++ constructor `{}` is missing its object parameter",
                        target.name
                    ));
                };
                validate_call_arguments(
                    function,
                    target.name.as_str(),
                    explicit_parameters,
                    arguments,
                )?;
            }
            CollectedCall::Destructor { object, .. } => {
                let CppFunctionKind::Destructor {
                    record_declaration_id,
                    record_name,
                } = &target.function_kind
                else {
                    return Err(format!(
                        "C++ cleanup for `{}` refers to non-destructor `{}`",
                        object.name, target.name
                    ));
                };
                if !matches!(
                    function.place_type(&object.declaration_id),
                    Some(CppType::Record { declaration_id, name })
                        if declaration_id == record_declaration_id && name == record_name
                ) {
                    return Err(format!(
                        "C++ destructor `{}` does not destroy object `{}`",
                        target.name, object.name
                    ));
                }
                if target.parameters.len() != 1 {
                    return Err(format!(
                        "C++ destructor `{}` has an invalid object interface",
                        target.name
                    ));
                }
            }
        }
        validate_reachable_calls(
            &callee.declaration_id,
            functions,
            visiting,
            visited,
            logical_source,
        )?;
    }
    visiting.pop();
    visited.insert(declaration_id.to_string());
    Ok(())
}

enum CollectedCall<'a> {
    Ordinary {
        callee: &'a CppFunctionReference,
        arguments: &'a [CppCallArgument],
    },
    Constructor {
        local: &'a CppPlace,
        callee: &'a CppFunctionReference,
        arguments: &'a [CppCallArgument],
    },
    Destructor {
        object: &'a CppPlaceReference,
        callee: &'a CppFunctionReference,
    },
}

fn collect_calls<'a>(statements: &'a [CppStatement], calls: &mut Vec<CollectedCall<'a>>) {
    for statement in statements {
        match statement {
            CppStatement::Declare {
                initializer:
                    CppInitializer::Call {
                        callee, arguments, ..
                    },
                ..
            } => calls.push(CollectedCall::Ordinary { callee, arguments }),
            CppStatement::Declare {
                local,
                initializer:
                    CppInitializer::Constructor {
                        callee, arguments, ..
                    },
                ..
            } => calls.push(CollectedCall::Constructor {
                local,
                callee,
                arguments,
            }),
            CppStatement::Declare { .. } => {}
            CppStatement::Call {
                callee, arguments, ..
            } => calls.push(CollectedCall::Ordinary { callee, arguments }),
            CppStatement::If {
                then_branch,
                else_branch,
                ..
            } => {
                collect_calls(then_branch, calls);
                collect_calls(else_branch, calls);
            }
            CppStatement::Return { cleanups, .. } => {
                for cleanup in cleanups {
                    let CppCleanup::Destructor { object, callee, .. } = cleanup;
                    calls.push(CollectedCall::Destructor { object, callee });
                }
            }
            CppStatement::Assign { .. }
            | CppStatement::Store { .. }
            | CppStatement::MemberStore { .. } => {}
        }
    }
}

fn validate_call_arguments(
    caller: &CppFunction,
    callee_name: &str,
    parameters: &[CppPlace],
    arguments: &[CppCallArgument],
) -> Result<(), String> {
    if arguments.len() != parameters.len() {
        return Err(format!(
            "C++ call from `{}` to `{}` has {} arguments for {} parameters",
            caller.name,
            callee_name,
            arguments.len(),
            parameters.len()
        ));
    }
    for (index, (argument, parameter)) in arguments.iter().zip(parameters).enumerate() {
        let compatible = match (argument, &parameter.value_type) {
            (
                CppCallArgument::Value { value },
                CppType::Boolean {
                    bits: 8,
                    is_const: false,
                },
            ) => matches!(
                value.value_type(),
                CppType::Boolean {
                    bits: 8,
                    is_const: false,
                }
            ),
            (
                CppCallArgument::Reference { place },
                CppType::LvalueReference { pointee: expected },
            ) => {
                let actual = caller
                    .parameters
                    .iter()
                    .find(|candidate| candidate.declaration_id == place.declaration_id)
                    .map(|candidate| &candidate.value_type);
                match (actual, expected.as_ref()) {
                    (
                        Some(CppType::LvalueReference { pointee: actual }),
                        CppType::Integer {
                            bits: 32,
                            signed: true,
                            is_const: expected_const,
                        },
                    ) => matches!(
                        actual.as_ref(),
                        CppType::Integer {
                            bits: 32,
                            signed: true,
                            is_const: actual_const,
                        } if *expected_const || !*actual_const
                    ),
                    _ => false,
                }
            }
            (CppCallArgument::Value { value }, CppType::Pointer { pointee }) => {
                require_int32(pointee, false, "call pointer parameter").is_ok()
                    && require_mutable_int32_pointer(value.value_type(), "call pointer argument")
                        .is_ok()
            }
            _ => false,
        };
        if !compatible {
            return Err(format!(
                "C++ call from `{}` to `{}` has unsupported argument {} for parameter `{}`",
                caller.name,
                callee_name,
                index + 1,
                parameter.name
            ));
        }
    }
    Ok(())
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

fn validate_record_reference<'a>(
    records: &'a BTreeMap<String, &CppRecord>,
    declaration_id: &str,
    name: &str,
) -> Result<&'a CppRecord, String> {
    let record = records.get(declaration_id).ok_or_else(|| {
        format!("C++ type refers to unknown record declaration `{declaration_id}`")
    })?;
    if record.name != name {
        return Err(format!(
            "C++ record declaration `{declaration_id}` is named `{}`, not `{name}`",
            record.name
        ));
    }
    Ok(record)
}

fn validate_member_reference<'a>(
    object: &CppPlaceReference,
    field: &CppFieldReference,
    places: &'a BTreeMap<String, (String, CppType)>,
    records: &'a BTreeMap<String, &CppRecord>,
    logical_source: &str,
) -> Result<&'a CppType, String> {
    field.span.validate(logical_source)?;
    if field.declaration_id.is_empty()
        || field.record_declaration_id.is_empty()
        || field.name.is_empty()
    {
        return Err("C++ member reference is missing declaration identity".into());
    }
    let object_type = validate_place_reference(object, places, logical_source)?;
    let record_type = match object_type {
        CppType::LvalueReference { pointee } => pointee.as_ref(),
        CppType::Record { .. } => object_type,
        _ => return Err("C++ member access requires a supported record object".into()),
    };
    let CppType::Record {
        declaration_id,
        name,
    } = record_type
    else {
        return Err("C++ member access requires a supported record object".into());
    };
    if declaration_id != &field.record_declaration_id {
        return Err(format!(
            "C++ field `{}` belongs to the wrong record declaration",
            field.name
        ));
    }
    let record = validate_record_reference(records, declaration_id, name)?;
    let resolved = record
        .fields
        .iter()
        .find(|candidate| candidate.declaration_id == field.declaration_id)
        .ok_or_else(|| {
            format!(
                "C++ member access refers to unknown field declaration `{}`",
                field.declaration_id
            )
        })?;
    if resolved.name != field.name {
        return Err(format!(
            "C++ field declaration `{}` is named `{}`, not `{}`",
            field.declaration_id, resolved.name, field.name
        ));
    }
    Ok(&resolved.value_type)
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

fn require_mutable_int32_pointer(value: &CppType, label: &str) -> Result<(), String> {
    match value {
        CppType::Pointer { pointee } => require_int32(pointee, false, label),
        _ => Err(format!(
            "{label} is outside the supported C++ mutable `int*` slice"
        )),
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
