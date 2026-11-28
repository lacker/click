//! Direct lowering from the pinned C++ semantic artifact to kernel execution.
//!
//! This adapter consumes Clang's already-typed nodes. It does not print C++ as
//! C, invoke the C parser, or infer types from source spellings. The first
//! slice represents `int&` and `const int&` as address-valued kernel parameters;
//! every C++ lvalue-to-rvalue conversion becomes a typed load through that
//! address and assignment writes the referent without reseating the reference.
//! Mutable `int*` parameters remain distinct from references in the semantic
//! artifact, while both reuse the kernel's checked address and memory rules.
//! Function-body scalar locals use the kernel's ordinary declaration,
//! assignment, and call-result statements.

use super::lifetime::{LifetimePlan, LifetimeState};
use super::names::ResolvedNames;
use super::scalar::{self, Scalar, ScalarKind};
use std::collections::{BTreeMap, BTreeSet};

use super::{
    CppBinaryOperator, CppCallArgument, CppCleanup, CppCondition, CppConstant,
    CppExceptionBehavior, CppExpression, CppFieldReference, CppFunction, CppFunctionKind,
    CppInitializer, CppPlace, CppPlaceReference, CppStatement, CppType, PreparedCppImport,
};
use crate::kernel::{
    AggregateLayout, BindingName, LoadSourceId, LoadSourceOwnerId, LocalBindingId, LocalFunctionId,
    ProgramExpression, ProgramFunction, ProgramStatement, ProgramType, int32,
    program_allocate_aggregate_destination, program_assign, program_call, program_call_construct,
    program_copy_aggregate, program_declare, program_declare_aggregate,
    program_declare_initialized, program_declare_with_all_qualifiers,
    program_end_automatic_lifetimes, program_function, program_if, program_parameter,
    program_return, program_seq, program_skip, program_try_catch_int32, program_typed_store,
    program_unwind_cleanup,
};

/// One kernel function together with the immutable semantic artifact that
/// produced it. Keeping the source artifact attached retains Clang declaration
/// identities and spans even though they are not part of kernel equality.
#[derive(Clone, Debug)]
pub struct LoweredCppFunction {
    source: PreparedCppImport,
    names: ResolvedNames,
    /// The selected functions, in selection order.
    functions: Vec<ProgramFunction>,
    reachable_functions: Vec<ProgramFunction>,
    execution: std::sync::Arc<crate::languages::PreparedExecution>,
}

impl LoweredCppFunction {
    /// Shared verifier key for a resolved Clang declaration identity. Write
    /// a C++ path and signature when naming the declaration in a proof head.
    pub fn contract_name(&self, declaration_id: &str) -> Option<&str> {
        self.names.get(declaration_id)
    }

    pub(crate) fn prepared_execution(&self) -> std::sync::Arc<crate::languages::PreparedExecution> {
        self.execution.clone()
    }
    pub fn contract_functions(&self) -> &[crate::languages::interface::ImportedFunction] {
        &self.execution.functions
    }

    pub fn record_layouts(&self) -> &BTreeMap<String, crate::languages::interface::RecordLayout> {
        &self.execution.layouts
    }

    pub fn source(&self) -> &PreparedCppImport {
        &self.source
    }

    /// The first selected function's artifact.
    pub fn source_function(&self) -> &CppFunction {
        &self.source.export().functions[0]
    }

    /// The first selected function, lowered.
    pub fn kernel_function(&self) -> &ProgramFunction {
        &self.functions[0]
    }

    pub fn reachable_kernel_functions(&self) -> &[ProgramFunction] {
        &self.reachable_functions
    }
}

/// Normalize the pinned C++ artifact into checked execution and its prepared
/// contract-facing metadata.
pub fn lower_import(import: &PreparedCppImport) -> Result<LoweredCppFunction, String> {
    // Each function is named by its C++ path, which an artifact locked
    // before paths were exported does not carry.
    let lambda_paths = super::schema::lambda_paths(import.export())?;
    let paths = import
        .export()
        .functions
        .iter()
        .chain(&import.export().reachable_functions)
        .map(|function| {
            if function.path.is_empty() {
                return Err(format!(
                    "C++ artifact names `{}` without its C++ path; refresh it with `click capture`",
                    function.name
                ));
            }
            Ok((
                function.declaration_id.as_str(),
                lambda_paths
                    .get(function.declaration_id.as_str())
                    .cloned()
                    .unwrap_or_else(|| super::names::path_name(&function.path)),
            ))
        })
        .collect::<Result<Vec<_>, String>>()?;
    let names = ResolvedNames::new(paths.iter().map(|(id, name)| (*id, name.as_str())))?;
    // Build immutable inventories once; every function borrows the same indexes.
    let layouts = super::interface::prepare_layouts(import)?;
    let records = super::schema::RecordIndex::new(
        import
            .export()
            .records
            .iter()
            .map(|record| {
                crate::instrumentation::record_deterministic_work(1);
                (record.declaration_id.clone(), record)
            })
            .collect::<BTreeMap<_, _>>(),
    )
    .with_symbolic_layouts(&layouts);
    let constants = import
        .export()
        .constants
        .iter()
        .map(|constant| {
            crate::instrumentation::record_deterministic_work(1);
            (constant.declaration_id.as_str(), constant)
        })
        .collect::<BTreeMap<_, _>>();
    let polymorphism = Polymorphism::new(import, &records);
    let functions = import
        .export()
        .functions
        .iter()
        .map(|source| {
            lower_function(
                import,
                source,
                &names,
                &records,
                &constants,
                &layouts,
                &polymorphism,
            )
        })
        .collect::<Result<Vec<_>, _>>()?;
    let reachable_functions = import
        .export()
        .reachable_functions
        .iter()
        .map(|source| {
            lower_function(
                import,
                source,
                &names,
                &records,
                &constants,
                &layouts,
                &polymorphism,
            )
        })
        .collect::<Result<Vec<_>, _>>()?;
    let (library_contracts, library_models) =
        super::standard_library::contracts(import.export(), &names)?;
    // An overload's head at its shared path selects it by signature.
    let mut overload_paths = BTreeMap::new();
    for (id, path) in &paths {
        crate::instrumentation::record_deterministic_work(1);
        let name = names.require(id)?;
        if name != path {
            overload_paths.insert(name.to_string(), path.clone());
        }
    }
    let mut execution = super::interface::prepare(
        import,
        &functions,
        &reachable_functions,
        layouts,
        library_contracts,
        polymorphism.coercions.into_inner(),
        &polymorphism.dispatches.into_inner(),
        &polymorphism.receiver_calls.into_inner(),
        overload_paths,
    )?;
    execution.library_models = library_models;
    Ok(LoweredCppFunction {
        execution: std::sync::Arc::new(execution),
        names,
        source: import.clone(),
        functions,
        reachable_functions,
    })
}

fn lower_function(
    import: &PreparedCppImport,
    source: &CppFunction,
    names: &ResolvedNames,
    records: &super::schema::RecordIndex<'_>,
    constants: &BTreeMap<&str, &CppConstant>,
    layouts: &BTreeMap<String, crate::languages::interface::RecordLayout>,
    polymorphism: &Polymorphism<'_>,
) -> Result<ProgramFunction, String> {
    let mut declared_places = Vec::new();
    collect_declared_places(&source.body, &mut declared_places);
    let places = source
        .parameters
        .iter()
        .chain(declared_places)
        .map(|parameter| (parameter.declaration_id.as_str(), parameter))
        .collect::<BTreeMap<_, _>>();
    let receiver = source.receiver().map(|place| place.declaration_id.as_str());
    // Reference parameters and locals both carry the address of the referent.
    let reference_parameters = places
        .values()
        .filter(|place| matches!(place.value_type, CppType::LvalueReference { .. }))
        .map(|place| place.declaration_id.as_str())
        .filter(|id| Some(*id) != receiver)
        .collect::<BTreeSet<_>>();
    let function_name = names.require(&source.declaration_id)?;
    let owner = LocalFunctionId::new(
        Some(import.logical_source().to_owned()),
        function_name.to_owned(),
    );
    let parameters = source
        .parameters
        .iter()
        .enumerate()
        .map(|(index, parameter)| {
            if receiver == Some(parameter.declaration_id.as_str()) {
                return lower_parameter(parameter, layouts, RECEIVER_NAME.into());
            }
            let binding = if source.axiom.is_some() && parameter.name.is_empty() {
                let ordinal = u32::try_from(index).map_err(|_| "too many C++ parameters")?;
                BindingName::from(LocalBindingId::new(owner.clone(), true, ordinal, None))
            } else {
                BindingName::from(parameter.name.as_str())
            };
            let binding = if matches!(parameter.value_type, CppType::LvalueReference { .. }) {
                BindingName::reference_carrier(binding)
            } else {
                binding
            };
            lower_parameter(parameter, layouts, binding)
        })
        .collect::<Result<Vec<_>, String>>()?;
    let mut context = LoweringContext {
        receiver,
        reference_parameters,
        source_unit: import.logical_source(),
        function_name,
        names,
        temporary_owner: owner,
        next_temporary: 0,
        next_result_step: std::cell::Cell::new(0),
        places,
        records,
        constants,
        layouts,
        next_load_occurrence: 0,
        unwind_cleanups: matches!(
            import.export().exception_behavior,
            CppExceptionBehavior::ScalarInt32
        ),
        pending_coercions: Vec::new(),
        direct_receiver: None,
        polymorphism,
    };
    let lifetimes = LifetimePlan::for_lowering(&source.body, context.records)?;
    let body = context.lower_sequence_with_lifetimes(
        &source.body,
        &lifetimes,
        &mut LifetimeState::default(),
        0,
    )?;
    let return_type = match &source.function_kind {
        CppFunctionKind::Constructor { .. } | CppFunctionKind::Destructor { .. } => {
            ProgramType::Void
        }
        _ if source.return_type == CppType::Void => ProgramType::Void,
        _ if matches!(source.return_type, CppType::Record { .. }) => ProgramType::Int32Pointer,
        _ => cpp_return_scalar_type(&source.return_type)?,
    };
    // Falling off a void function is a return. Keep that semantic exit in
    // the lowered body, as the C frontend does, so an explicit call-outcome
    // split has a continuation even when the call is the last source statement.
    let body = if return_type == ProgramType::Void {
        program_seq(
            body,
            program_return(ProgramExpression::Value(crate::kernel::ProgramValue::Void)),
        )
    } else {
        body
    };
    let return_constant = scalar::returns_constant_element(&source.return_type);
    let mut function = program_function(return_type, function_name.to_owned(), parameters, body)
        .with_return_pointee_constant(return_constant);
    if let CppFunctionKind::Constructor { record_name, .. } = &source.function_kind {
        function = function.with_construction_parameter(0, context.record_layout(record_name)?);
    }
    if let CppType::Record { name, .. } = &source.return_type {
        function = if super::construction::is_construction_return(source) {
            function.with_construction_return(context.record_layout(name)?)
        } else {
            function.with_return_aggregate_layout(context.record_layout(name)?)
        };
    }
    Ok(function)
}

/// The name a sidecar gives a member function's receiver: the pointer
/// `this`, as in C++.
pub(super) const RECEIVER_NAME: &str = "this";

/// Whether a declared local is a reference, which a proof names by its
/// referent as it names a reference parameter.
pub(super) fn is_reference_local(local: &CppPlace) -> bool {
    matches!(local.value_type, CppType::LvalueReference { .. })
}

fn lower_parameter(
    parameter: &CppPlace,
    layouts: &BTreeMap<String, crate::languages::interface::RecordLayout>,
    binding: BindingName,
) -> Result<crate::kernel::ProgramParameter, String> {
    let lowered = lower_parameter_value(parameter, layouts, binding)?;
    // A reference or pointer to a symbolic record designates its whole
    // object, `sizeof` bytes, as a Rust reference to one does.
    let pointee = match &parameter.value_type {
        CppType::LvalueReference { pointee } => match pointee.as_ref() {
            CppType::Record { name, .. } => Some(name.as_str()),
            _ => None,
        },
        pointer @ CppType::Pointer { .. } => scalar::record_pointee(pointer).map(|(_, name)| name),
        _ => None,
    };
    Ok(
        match pointee
            .and_then(|name| layouts.get(name))
            .map(|layout| layout.size())
        {
            Some(size @ crate::kernel::LayoutSize::Of(_)) => {
                lowered.with_fixed_reference_bounds(size)
            }
            _ => lowered,
        },
    )
}

/// The declared type of a C++ local the lowering binds by its spelling, as
/// a parameter of its type is typed: none for a reference, which its carrier
/// binds, or for a struct value, which has no scalar value.
pub(super) fn spelled_local_type(
    local: &CppPlace,
    layouts: &BTreeMap<String, crate::languages::interface::RecordLayout>,
) -> Option<ProgramType> {
    if matches!(
        local.value_type,
        CppType::LvalueReference { .. } | CppType::Record { .. }
    ) {
        return None;
    }
    lower_parameter_value(local, layouts, local.name.as_str().into())
        .ok()
        .map(|parameter| parameter.program_type())
}

fn lower_parameter_value(
    parameter: &CppPlace,
    layouts: &BTreeMap<String, crate::languages::interface::RecordLayout>,
    binding: BindingName,
) -> Result<crate::kernel::ProgramParameter, String> {
    match &parameter.value_type {
        CppType::Record {
            name,
            is_const: false,
            ..
        } => {
            let layout = layouts
                .get(name)
                .ok_or("C++ record parameter has no checked layout")?;
            Ok(crate::kernel::program_parameter_with_aggregate_layout(
                binding.clone(),
                ProgramType::UInt8Pointer,
                layout.to_kernel_aggregate_layout(),
            ))
        }
        CppType::Integer { .. } | CppType::Enumeration { .. } | CppType::Parameter { .. } => {
            Ok(program_parameter(
                binding.clone(),
                cpp_scalar_kernel_type(&parameter.value_type)?,
            ))
        }
        CppType::Boolean {
            bits: 8,
            is_const: false,
        } => Ok(program_parameter(binding.clone(), ProgramType::Bool)),
        CppType::LvalueReference { .. }
            if scalar::reference_element(&parameter.value_type).is_some() =>
        {
            let element = scalar::reference_element(&parameter.value_type).unwrap();
            Ok(
                program_parameter(binding.clone(), element_pointer_type(element)?)
                    .with_pointee_constant(element.is_const),
            )
        }
        CppType::LvalueReference { pointee } if is_const_int64(pointee) => Ok(program_parameter(
            binding.clone(),
            ProgramType::Int64Pointer,
        )
        .with_pointee_constant(true)),
        CppType::LvalueReference { pointee }
            if let CppType::Record { name, is_const, .. } = pointee.as_ref() =>
        {
            let carrier_type = if layouts.contains_key(name) {
                ProgramType::Int32Pointer
            } else {
                ProgramType::VoidPointer
            };
            Ok(program_parameter(binding, carrier_type).with_pointee_constant(*is_const))
        }
        CppType::FunctionPointer { .. } => Ok(program_parameter(
            binding.clone(),
            super::interface::function_pointer_signature(&parameter.value_type)?
                .pointer_type()
                .to_kernel_type(),
        )),
        pointer @ CppType::Pointer { .. }
            if let Some((_, name)) = scalar::record_pointee(pointer) =>
        {
            let carrier_type = if layouts.contains_key(name) {
                ProgramType::Int32Pointer
            } else {
                ProgramType::VoidPointer
            };
            Ok(program_parameter(binding, carrier_type))
        }
        pointer if let Some(is_const) = scalar::void_pointer(pointer) => {
            Ok(program_parameter(binding.clone(), ProgramType::VoidPointer)
                .with_pointee_constant(is_const))
        }
        CppType::Pointer { pointee } if Scalar::pointer_element(pointee, true).is_some() => {
            Ok(program_parameter(
                binding.clone(),
                Scalar::pointer_element(pointee, true)
                    .unwrap()
                    .kind
                    .pointer_kernel_type()
                    .unwrap(),
            )
            .with_pointee_constant(scalar::returns_constant_element(&parameter.value_type)))
        }
        _ => Err(format!(
            "C++ parameter `{}` is outside native scalar/reference/pointer and trivial record-value lowering",
            parameter.name
        )),
    }
}

// An empty evaluation prefix does not introduce a synthetic execution step.
fn evaluate_then(prefix: ProgramStatement, continuation: ProgramStatement) -> ProgramStatement {
    if matches!(prefix, ProgramStatement::Skip) {
        continuation
    } else {
        program_seq(prefix, continuation)
    }
}

/// A source scalar evaluation, independent of its initializer/return context.
/// Artifact wrappers retain their source role; every call uses this normalizer.
enum ScalarInput<'a> {
    Value(&'a CppExpression),
    Call {
        callee: &'a super::CppFunctionReference,
        arguments: &'a [CppCallArgument],
        value_type: &'a CppType,
        conversions: &'a [super::CppScalarConversion],
    },
}

struct ScalarEvaluation {
    prefix: ProgramStatement,
    value: ProgramExpression,
    value_type: ProgramType,
    may_throw: bool,
}

struct LoweringContext<'a> {
    /// Declarations of the reference parameters, whose carrying pointers are
    /// represented by a typed reference-carrier binding.
    reference_parameters: std::collections::BTreeSet<&'a str>,
    /// The declaration of the receiver, which is named [`RECEIVER_NAME`].
    receiver: Option<&'a str>,
    source_unit: &'a str,
    function_name: &'a str,
    names: &'a ResolvedNames,
    places: BTreeMap<&'a str, &'a CppPlace>,
    records: &'a super::schema::RecordIndex<'a>,
    constants: &'a BTreeMap<&'a str, &'a CppConstant>,
    layouts: &'a BTreeMap<String, crate::languages::interface::RecordLayout>,
    next_load_occurrence: u32,
    temporary_owner: LocalFunctionId,
    next_temporary: u32,
    next_result_step: std::cell::Cell<u32>,
    unwind_cleanups: bool,
    /// The packs the call being lowered needs, with their unpacks and the
    /// derived class's address: one for each reference argument that
    /// converts a derived class reference to a polymorphic base.
    pending_coercions: Vec<(usize, crate::kernel::CppBindingContract, ProgramExpression)>,
    /// The receiver of the call being lowered when it converts to a base
    /// whose method runs as itself, on memory: it is not packed.
    direct_receiver: Option<CppPlaceReference>,
    polymorphism: &'a Polymorphism<'a>,
}

/// What lowering each function shares about the program's polymorphic
/// classes.
struct Polymorphism<'a> {
    functions: BTreeMap<&'a str, &'a CppFunction>,
    /// The polymorphic classes another polymorphic class derives from: a
    /// reference to one may stand for an object of a derived class.
    open: BTreeSet<&'a str>,
    /// The polymorphic classes that derive from a polymorphic class.
    derived: BTreeSet<&'a str>,
    /// Every conversion of a derived class reference to a polymorphic base
    /// the program makes, by derived and base record.
    coercions: std::cell::RefCell<BTreeSet<crate::kernel::CppObjectConversion>>,
    /// Methods the program calls through their virtual interface.
    dispatches: std::cell::RefCell<BTreeSet<String>>,
    /// Each function's calls of methods on a receiver that may be an object
    /// of a derived class, by its importer name: the function called, and
    /// the reference parameter the receiver is, or `None` for `this`.
    receiver_calls:
        std::cell::RefCell<BTreeMap<String, Vec<crate::languages::interface::CppReceiverCall>>>,
}

impl<'a> Polymorphism<'a> {
    fn new(import: &'a PreparedCppImport, records: &super::schema::RecordIndex<'a>) -> Self {
        let functions = import
            .export()
            .functions
            .iter()
            .chain(&import.export().reachable_functions)
            .map(|function| (function.declaration_id.as_str(), function))
            .collect();
        let mut open = BTreeSet::new();
        let mut derived = BTreeSet::new();
        for record in import
            .export()
            .records
            .iter()
            .filter(|record| record.polymorphic)
        {
            crate::instrumentation::record_deterministic_work(1);
            if let Some(CppType::Record {
                declaration_id,
                name,
                ..
            }) = record.base.as_ref().map(|base| &base.value_type)
                && records
                    .get(declaration_id)
                    .is_some_and(|base| base.polymorphic)
            {
                open.insert(name.as_str());
                derived.insert(record.name.as_str());
            }
        }
        Self {
            functions,
            open,
            derived,
            coercions: std::cell::RefCell::default(),
            dispatches: std::cell::RefCell::default(),
            receiver_calls: std::cell::RefCell::default(),
        }
    }
}

fn value_step(
    step: u32,
    expression: ProgramExpression,
    value_type: ProgramType,
) -> ProgramStatement {
    ProgramStatement::StepValue {
        aggregate_layout: None,
        steps: vec![step],
        expression,
        value_type: Some(value_type),
        pointee_constant: false,
    }
}

fn value_result(step: u32) -> ProgramExpression {
    ProgramExpression::StepResult {
        step,
        origin: crate::kernel::StepOrigin::Value("scalar evaluation"),
        ends: true,
    }
}

impl LoweringContext<'_> {
    fn result_step(&self) -> u32 {
        let step = self.next_result_step.get();
        self.next_result_step.set(
            step.checked_add(1)
                .expect("too many value steps in one function"),
        );
        crate::instrumentation::record_deterministic_work(1);
        step
    }

    fn retain_value(
        &self,
        expression: ProgramExpression,
        value_type: ProgramType,
    ) -> (ProgramStatement, ProgramExpression) {
        let step = self.result_step();
        (value_step(step, expression, value_type), value_result(step))
    }

    /// `call`, after the packs its arguments need and before their unpacks:
    /// the callee holds the base class's object the derived class's memory
    /// stands for, which the sidecar may declare.
    fn coerced(&mut self, call: ProgramStatement) -> ProgramStatement {
        self.coerced_call(call, false)
    }

    fn coerced_call(&mut self, call: ProgramStatement, has_receiver: bool) -> ProgramStatement {
        use crate::kernel::{
            ReferenceBindingOperation, ReferenceBindingSlot, ReferenceBindingSource,
        };
        let coercions = std::mem::take(&mut self.pending_coercions);
        // The only multi-step call passed here is a call followed by the
        // assignment of its result. Both count as regions of the binding.
        let call_regions = match &call {
            ProgramStatement::Seq(statements) => statements.len(),
            _ => 1,
        };
        let mut statement = call;
        for (index, (position, contract, address)) in coercions.iter().enumerate().rev() {
            crate::instrumentation::record_deterministic_work(1);
            let remaining = coercions.len() - index;
            let slot = if has_receiver && *position == 0 {
                ReferenceBindingSlot::Receiver
            } else {
                ReferenceBindingSlot::Argument(position - usize::from(has_receiver))
            };
            let transition = |contract, source| ProgramStatement::Call {
                function_name: String::new(),
                arguments: vec![address.clone()],
                callee: None,
                dispatch: crate::kernel::CallDispatch::Direct,
                reference_binding: Some(std::sync::Arc::new(ReferenceBindingOperation {
                    contract: crate::kernel::ReferenceBindingContract::Cpp(contract),
                    source,
                })),
            };
            let acquire = transition(
                contract.clone(),
                Some(ReferenceBindingSource {
                    slot,
                    call_offset: remaining,
                    release_offset: remaining + call_regions + remaining - 1,
                }),
            );
            let release = transition(contract.release(), None);
            statement = program_seq(acquire, program_seq(statement, release));
        }
        statement
    }

    fn call_has_receiver(&self, callee: &super::CppFunctionReference) -> bool {
        self.polymorphism
            .functions
            .get(callee.declaration_id.as_str())
            .is_some_and(|function| function.receiver().is_some())
    }

    /// Records the pack a reference argument needs when its place ends in
    /// base projections to a polymorphic class.
    fn note_object_coercion(
        &mut self,
        place: &super::CppPlaceReference,
        position: usize,
    ) -> Result<(), String> {
        let trailing = place
            .projections
            .iter()
            .rev()
            .take_while(|projection| {
                matches!(projection, super::schema::CppProjection::Base { .. })
            })
            .count();
        if trailing == 0 {
            return Ok(());
        }
        let super::schema::CppProjection::Base { base } = place.projections.last().unwrap() else {
            unreachable!("a trailing base projection");
        };
        if !self
            .records
            .get(&base.base_declaration_id)
            .is_some_and(|record| record.polymorphic)
        {
            return Ok(());
        }
        let root = self.place(place)?;
        let derived_path = &place.projections[..place.projections.len() - trailing];
        let (derived_type, _) = self.records.resolve_path(&root.value_type, derived_path)?;
        let CppType::Record { name: derived, .. } = derived_type else {
            return Err("C++ base conversion starts from a non-record place".into());
        };
        let derived = derived.clone();
        // A reference to a class another derives from already holds the
        // object of whichever class it refers to.
        if self.polymorphism.open.contains(derived.as_str()) && !self.is_exact(place)? {
            return Ok(());
        }
        let mut derived_place = place.clone();
        derived_place.projections.truncate(derived_path.len());
        let address = crate::kernel::program_expression::cast(
            self.lower_place(&derived_place)?,
            ProgramType::Int32Pointer,
        );
        self.record_binding(position, &derived, &base.base_name, base.is_const, address);
        Ok(())
    }

    fn record_binding(
        &mut self,
        position: usize,
        derived: &str,
        base: &str,
        shared: bool,
        address: ProgramExpression,
    ) {
        use crate::kernel::{CppBindingContract, CppObjectConversion, ReferenceBindingKind};
        let conversion = CppObjectConversion::new(derived, base);
        self.polymorphism
            .coercions
            .borrow_mut()
            .insert(conversion.clone());
        self.pending_coercions.push((
            position,
            CppBindingContract {
                conversion,
                kind: ReferenceBindingKind::acquire(shared),
            },
            address,
        ));
    }

    /// Whether `place`, before any base edges it ends in, is a complete
    /// object whose class is the one it is declared with: a field, or a
    /// local or by-value parameter, never a referent or the receiver.
    fn is_exact(&self, place: &CppPlaceReference) -> Result<bool, String> {
        if place
            .projections
            .iter()
            .rev()
            .find(|projection| !matches!(projection, super::schema::CppProjection::Base { .. }))
            .is_some()
        {
            return Ok(true);
        }
        let root = self.place(place)?;
        let id = place.declaration_id.as_str();
        Ok(self.receiver != Some(id)
            && !self.reference_parameters.contains(id)
            && matches!(root.value_type, CppType::Record { .. }))
    }

    /// The function a call runs, and the packs its exact arguments need. A
    /// complete object of an open class passed by reference becomes the
    /// object a reference to its class holds. A call that dispatches through
    /// a reference to an open class's method that overrides another runs
    /// whichever override the object's class selects, using the method's
    /// virtual interface.
    fn call_target(
        &mut self,
        callee: &super::CppFunctionReference,
        arguments: &[CppCallArgument],
    ) -> Result<(String, crate::kernel::CallDispatch), String> {
        use crate::kernel::CallDispatch;
        self.direct_receiver = None;
        let name = self.callee_name(callee)?;
        let Some(function) = (!callee.through_pointer)
            .then(|| {
                self.polymorphism
                    .functions
                    .get(callee.declaration_id.as_str())
            })
            .flatten()
            .copied()
        else {
            return Ok((name, CallDispatch::Direct));
        };
        let receiver = function.receiver();
        for (position, (argument, parameter)) in
            arguments.iter().zip(&function.parameters).enumerate()
        {
            let CppCallArgument::Reference { place } = argument else {
                continue;
            };
            let CppType::LvalueReference { pointee } = &parameter.value_type else {
                continue;
            };
            let CppType::Record {
                name: class,
                is_const,
                ..
            } = pointee.as_ref()
            else {
                continue;
            };
            if receiver.is_some_and(|receiver| std::ptr::eq(receiver, parameter))
                || !self.polymorphism.open.contains(class.as_str())
                || place.projections.last().is_some_and(|projection| {
                    matches!(projection, super::schema::CppProjection::Base { .. })
                })
                || !self.is_exact(place)?
            {
                continue;
            }
            crate::instrumentation::record_deterministic_work(1);
            let address = crate::kernel::program_expression::cast(
                self.lower_place(place)?,
                ProgramType::Int32Pointer,
            );
            self.record_binding(position, class, class, *is_const, address);
        }
        let Some(CppType::LvalueReference { pointee }) =
            receiver.map(|parameter| &parameter.value_type)
        else {
            return Ok((name, CallDispatch::Direct));
        };
        let CppType::Record { name: class, .. } = pointee.as_ref() else {
            return Ok((name, CallDispatch::Direct));
        };
        let Some(CppCallArgument::Reference { place }) = arguments.first() else {
            return Ok((name, CallDispatch::Direct));
        };
        let exact = self.is_exact(place)?;
        let dispatches = function.virtual_method.as_ref().is_some_and(|method| {
            !callee.qualified
                && !method.overrides.is_empty()
                && self.polymorphism.open.contains(class.as_str())
        }) && !exact;
        let dispatch = if dispatches {
            self.polymorphism
                .dispatches
                .borrow_mut()
                .insert(name.clone());
            CallDispatch::CppVirtual
        } else {
            CallDispatch::Direct
        };
        if !exact && self.polymorphism.derived.contains(class.as_str()) {
            let id = place.declaration_id.as_str();
            let holder = (self.receiver != Some(id)).then(|| place.name.clone());
            self.polymorphism
                .receiver_calls
                .borrow_mut()
                .entry(self.function_name.to_string())
                .or_default()
                .push(crate::languages::interface::CppReceiverCall {
                    method: name.clone(),
                    dispatch,
                    holder,
                });
        }
        if !dispatches {
            // A method of a class with a polymorphic base, called as itself,
            // runs on that class's part of a derived object, which its
            // contract states as memory.
            if self.polymorphism.derived.contains(class.as_str())
                && place.projections.last().is_some_and(|projection| {
                    matches!(projection, super::schema::CppProjection::Base { .. })
                })
            {
                self.direct_receiver = Some(place.clone());
            }
        }
        Ok((name, dispatch))
    }

    fn lower_statement(&mut self, statement: &CppStatement) -> Result<ProgramStatement, String> {
        match statement {
            CppStatement::TrivialCopy { target, source, .. } => {
                let root = self.place(target)?;
                let (CppType::Record { name, .. }, _) = self
                    .records
                    .resolve_path(&root.value_type, &target.projections)?
                else {
                    return Err("C++ trivial copy requires a record target".into());
                };
                Ok(program_copy_aggregate(
                    self.lower_place(target)?,
                    self.lower_place(source)?,
                    self.record_layout(name)?,
                ))
            }
            CppStatement::Declare {
                local, initializer, ..
            } => match (&local.value_type, initializer) {
                (
                    CppType::Integer { .. } | CppType::Enumeration { .. },
                    CppInitializer::Uninitialized,
                ) => Ok(program_declare(
                    local.name.clone(),
                    cpp_scalar_kernel_type(&local.value_type)?,
                )),
                (CppType::LvalueReference { .. }, CppInitializer::Value { value }) => {
                    let address = self.lower_expression(value)?;
                    let carrier = BindingName::reference_carrier(local.name.as_str());
                    let (pointer_type, constant) = match &local.value_type {
                        CppType::LvalueReference { pointee }
                            if matches!(pointee.as_ref(), CppType::Record { .. }) =>
                        {
                            (
                                ProgramType::Int32Pointer,
                                matches!(pointee.as_ref(), CppType::Record { is_const: true, .. }),
                            )
                        }
                        _ => {
                            let element = scalar::reference_element(&local.value_type)
                                .ok_or("unsupported C++ reference local")?;
                            (element_pointer_type(element)?, element.is_const)
                        }
                    };
                    Ok(program_seq(
                        program_declare_with_all_qualifiers(
                            carrier.clone(),
                            pointer_type,
                            false,
                            false,
                            false,
                            constant,
                        ),
                        program_assign(carrier, address),
                    ))
                }
                (
                    CppType::Integer { .. } | CppType::Enumeration { .. } | CppType::Pointer { .. },
                    CppInitializer::Value { value },
                ) => {
                    let evaluation = self.normalize_scalar(ScalarInput::Value(value))?;
                    Ok(evaluate_then(
                        evaluation.prefix,
                        program_declare_initialized(
                            local.name.clone(),
                            evaluation.value_type,
                            evaluation.value,
                            false,
                            false,
                            Scalar::of(&local.value_type).is_some_and(|scalar| scalar.is_const),
                            scalar::returns_constant_element(&local.value_type),
                        ),
                    ))
                }
                (
                    CppType::Integer { .. }
                    | CppType::Enumeration { .. }
                    | CppType::Pointer { .. }
                    | CppType::LvalueReference { .. },
                    CppInitializer::Call {
                        callee,
                        arguments,
                        conversions,
                        ..
                    },
                ) => {
                    let raw_type = conversions
                        .first()
                        .map_or(&local.value_type, |cast| &cast.source_type);
                    let raw_value_type = scalar::scalar_value_type(raw_type);
                    let raw_type = &raw_value_type;
                    // A reference bound to a call's result is carried by a
                    // pointer named for the address it holds.
                    let name = if is_reference_local(local) {
                        BindingName::reference_carrier(local.name.as_str())
                    } else {
                        local.name.clone().into()
                    };
                    let evaluation = self.normalize_scalar_into(
                        ScalarInput::Call {
                            callee,
                            arguments,
                            value_type: raw_type,
                            conversions,
                        },
                        (conversions.is_empty()
                            && !Scalar::of(&local.value_type)
                                .is_some_and(|scalar| scalar.is_const))
                        .then_some(name.clone()),
                    )?;
                    let constant =
                        Scalar::of(&local.value_type).is_some_and(|scalar| scalar.is_const);
                    if conversions.is_empty() && !constant {
                        return Ok(evaluation.prefix);
                    }
                    Ok(evaluate_then(
                        evaluation.prefix,
                        program_declare_initialized(
                            name,
                            cpp_return_scalar_type(&scalar::scalar_value_type(&local.value_type))?,
                            evaluation.value,
                            false,
                            false,
                            constant,
                            scalar::returns_constant_element(&local.value_type),
                        ),
                    ))
                }
                (
                    CppType::Record { name, .. },
                    CppInitializer::ConstructionCall {
                        callee, arguments, ..
                    },
                ) => {
                    let layout = self.record_layout(name)?;
                    let (prefix, actual, prepared) = self.normalize_arguments(callee, arguments)?;
                    Ok(evaluate_then(
                        prefix,
                        program_seq(
                            program_allocate_aggregate_destination(local.name.clone(), layout),
                            end_prepared_arguments(
                                self.coerced(program_call_construct(
                                    local.name.clone(),
                                    self.callee_name(callee)?,
                                    actual,
                                )),
                                prepared,
                            ),
                        ),
                    ))
                }
                (
                    CppType::Record {
                        declaration_id,
                        name,
                        ..
                    },
                    CppInitializer::Aggregate { fields, .. },
                ) => {
                    let record = self.records.get(declaration_id.as_str()).ok_or_else(|| {
                        format!("C++ lowering found unknown record declaration `{declaration_id}`")
                    })?;
                    if record.name != *name || fields.len() != record.fields.len() {
                        return Err(format!(
                            "C++ aggregate initializer for `{name}` disagrees with its record"
                        ));
                    }
                    let layout = self.record_layout(&record.name)?;
                    let members = record
                        .fields
                        .iter()
                        .map(|field| {
                            Ok((
                                field.declaration_id.clone(),
                                self.records.field_offset(record, field)?,
                                cpp_scalar_kernel_type(&field.value_type)?,
                            ))
                        })
                        .collect::<Result<Vec<_>, String>>()?;
                    let mut result = program_declare_aggregate(local.name.clone(), layout);
                    for (initializer, (declaration_id, offset, value_type)) in
                        fields.iter().zip(members)
                    {
                        if initializer.field.declaration_id != declaration_id {
                            return Err(format!(
                                "C++ aggregate initializer for `{name}` is out of declaration order"
                            ));
                        }
                        let pointer = crate::kernel::program_expression::pointer_offset_bytes(
                            crate::kernel::program_expression::variable(local.name.clone()),
                            offset,
                        );
                        let value = self.lower_expression(&initializer.value)?;
                        result =
                            program_seq(result, program_typed_store(pointer, value, value_type));
                    }
                    Ok(result)
                }
                (
                    CppType::Record {
                        declaration_id,
                        name,
                        ..
                    },
                    CppInitializer::Constructor {
                        callee, arguments, ..
                    },
                ) => {
                    let record = self.records.get(declaration_id.as_str()).ok_or_else(|| {
                        format!("C++ lowering found unknown record declaration `{declaration_id}`")
                    })?;
                    if record.name != *name {
                        return Err(format!(
                            "C++ constructor initializer for `{name}` disagrees with its record"
                        ));
                    }
                    let layout = self.record_layout(&record.name)?;
                    let mut lowered_arguments = vec![crate::kernel::program_expression::cast(
                        crate::kernel::program_expression::variable(local.name.clone()),
                        ProgramType::Int32Pointer,
                    )];
                    lowered_arguments.extend(self.lower_call_arguments(arguments)?);
                    Ok(program_seq(
                        program_allocate_aggregate_destination(local.name.clone(), layout),
                        self.coerced(program_call(self.callee_name(callee)?, lowered_arguments)),
                    ))
                }
                // A local of an abstract type argument holds a copied value.
                (CppType::Parameter { .. }, CppInitializer::Value { value }) => {
                    let evaluation = self.normalize_scalar(ScalarInput::Value(value))?;
                    Ok(evaluate_then(
                        evaluation.prefix,
                        program_declare_initialized(
                            local.name.clone(),
                            cpp_scalar_kernel_type(&scalar::scalar_value_type(&local.value_type))?,
                            evaluation.value,
                            false,
                            false,
                            false,
                            false,
                        ),
                    ))
                }
                // A function-pointer local holds `&f` or another pointer.
                (CppType::FunctionPointer { .. }, CppInitializer::Value { value }) => {
                    Ok(program_declare_initialized(
                        local.name.clone(),
                        super::interface::function_pointer_signature(&local.value_type)?
                            .pointer_type()
                            .to_kernel_type(),
                        self.lower_expression(value)?,
                        false,
                        false,
                        false,
                        false,
                    ))
                }
                _ => Err(format!(
                    "C++ local `{}` has an initializer outside direct lowering",
                    local.name
                )),
            },
            CppStatement::Assign { target, value, .. } => {
                let target_is_local = matches!(
                    self.place(target)?.value_type,
                    CppType::Integer { .. } | CppType::Enumeration { .. } | CppType::Pointer { .. }
                );
                let evaluation = self.normalize_scalar(ScalarInput::Value(value))?;
                let assignment = if target_is_local {
                    program_assign(target.name.clone(), evaluation.value)
                } else {
                    // A reference to a value of an abstract type stores a
                    // value of that type.
                    let element = match scalar::reference_element(&self.place(target)?.value_type) {
                        Some(Scalar {
                            kind: kind @ ScalarKind::Parameter(_),
                            ..
                        }) => kind.kernel_type(),
                        _ => ProgramType::Int32,
                    };
                    program_typed_store(self.lower_place(target)?, evaluation.value, element)
                };
                Ok(evaluate_then(evaluation.prefix, assignment))
            }
            CppStatement::NewObject {
                target,
                record,
                fields,
                ..
            } => {
                let CppType::Record {
                    declaration_id,
                    name,
                    ..
                } = record
                else {
                    return Err("C++ `new` allocates a record".into());
                };
                let source = self.records.get(declaration_id.as_str()).ok_or_else(|| {
                    format!("C++ lowering found unknown record declaration `{declaration_id}`")
                })?;
                if source.name != *name || fields.len() != source.fields.len() {
                    return Err(format!(
                        "C++ `new` initializer for `{name}` disagrees with its record"
                    ));
                }
                let class = self
                    .layouts
                    .get(name.as_str())
                    .and_then(|layout| layout.class())
                    .map(|class| {
                        (
                            crate::kernel::effective_type::CAccessClass::Struct(class.clone()),
                            source.size_bytes,
                            source.alignment_bytes,
                        )
                    });
                // A symbolic record's allocation is its `sizeof` bytes, a
                // 64-bit size.
                let bytes = match self.layouts.get(name.as_str()).map(|layout| layout.size()) {
                    Some(size @ crate::kernel::LayoutSize::Of(_)) => {
                        ProgramExpression::Value(crate::kernel::ProgramValue::UInt64(size.term()))
                    }
                    _ => crate::kernel::program_expression::int32_literal(source.size_bytes),
                };
                // The allocation comes first and each field's value after it,
                // as C++17 sequences a new-expression.
                let object = self.fresh_temporary(ProgramType::Int32Pointer)?;
                let mut result = program_seq(
                    program_declare(object.clone(), ProgramType::Int32Pointer),
                    ProgramStatement::HeapAllocate {
                        target: (object.clone()),
                        bytes,
                        zeroed: false,
                        object_type: class,
                        ends_program_on_failure: true,
                    },
                );
                for (initializer, field) in fields.iter().zip(&source.fields) {
                    if initializer.field.declaration_id != field.declaration_id {
                        return Err(format!(
                            "C++ `new` initializer for `{name}` is out of declaration order"
                        ));
                    }
                    let pointer = crate::kernel::program_expression::pointer_offset_bytes(
                        crate::kernel::program_expression::variable(object.clone()),
                        self.records.field_offset(source, field)?,
                    );
                    let value = self.lower_expression(&initializer.value)?;
                    result = program_seq(
                        result,
                        program_typed_store(
                            pointer,
                            value,
                            cpp_scalar_kernel_type(&field.value_type)?,
                        ),
                    );
                }
                let assignment = if target.projections.is_empty() {
                    program_assign(
                        self.variable_name(target),
                        crate::kernel::program_expression::variable(object),
                    )
                } else {
                    program_typed_store(
                        self.lower_place(target)?,
                        crate::kernel::program_expression::variable(object),
                        ProgramType::Int32Pointer,
                    )
                };
                Ok(program_seq(result, assignment))
            }
            CppStatement::DeleteObject { pointer, .. } => Ok(crate::kernel::program_heap_free(
                self.lower_expression(pointer)?,
            )),
            CppStatement::Store { pointer, value, .. } => Ok(program_typed_store(
                self.lower_expression(pointer)?,
                self.lower_expression(value)?,
                cpp_scalar_kernel_type(value.value_type())?,
            )),
            CppStatement::MemberConstruct {
                object,
                field,
                callee,
                arguments,
                ..
            } => {
                let place = self.place(object)?;
                let (_, offset) = self.records.resolve_path(
                    &place.value_type,
                    object
                        .projections
                        .iter()
                        .map(super::schema::CppProjection::as_ref)
                        .chain(std::iter::once(super::schema::ProjectionRef::Field(field))),
                )?;
                let destination = crate::kernel::program_expression::cast(
                    crate::kernel::program_expression::pointer_offset_bytes(
                        crate::kernel::program_expression::variable(self.variable_name(object)),
                        offset,
                    ),
                    ProgramType::Int32Pointer,
                );
                let mut lowered = vec![destination];
                lowered.extend(self.lower_call_arguments(arguments)?);
                Ok(self.coerced(program_call(self.callee_name(callee)?, lowered)))
            }
            CppStatement::BaseDestruct {
                object,
                base,
                callee,
                ..
            } => {
                // The base subobject's address: the base destructor runs on
                // it after the class's own destructor body.
                let place = self.place(object)?;
                let (_, offset) = self.records.resolve_path(
                    &place.value_type,
                    object
                        .projections
                        .iter()
                        .map(super::schema::CppProjection::as_ref)
                        .chain(std::iter::once(super::schema::ProjectionRef::Base(base))),
                )?;
                Ok(program_call(
                    self.callee_name(callee)?,
                    vec![crate::kernel::program_expression::cast(
                        crate::kernel::program_expression::pointer_offset_bytes(
                            crate::kernel::program_expression::variable(self.variable_name(object)),
                            offset,
                        ),
                        ProgramType::Int32Pointer,
                    )],
                ))
            }
            CppStatement::BaseConstruct {
                object,
                base,
                callee,
                arguments,
                ..
            } => {
                // The base subobject's address: the base constructor runs on
                // it, before the class's own members.
                let place = self.place(object)?;
                let (_, offset) = self.records.resolve_path(
                    &place.value_type,
                    object
                        .projections
                        .iter()
                        .map(super::schema::CppProjection::as_ref)
                        .chain(std::iter::once(super::schema::ProjectionRef::Base(base))),
                )?;
                let destination = crate::kernel::program_expression::cast(
                    crate::kernel::program_expression::pointer_offset_bytes(
                        crate::kernel::program_expression::variable(self.variable_name(object)),
                        offset,
                    ),
                    ProgramType::Int32Pointer,
                );
                let mut lowered = vec![destination];
                lowered.extend(self.lower_call_arguments(arguments)?);
                Ok(self.coerced(program_call(self.callee_name(callee)?, lowered)))
            }
            CppStatement::MemberStore {
                object,
                field,
                value,
                ..
            } => {
                let (pointer, value_type, pointee_constant) =
                    self.lower_member_pointer(object, field)?;
                let evaluation = self.normalize_scalar(ScalarInput::Value(value))?;
                Ok(evaluate_then(
                    evaluation.prefix,
                    crate::kernel::program_qualified_typed_store(
                        pointer,
                        evaluation.value,
                        value_type,
                        None,
                        pointee_constant,
                        false,
                    ),
                ))
            }
            CppStatement::Unreachable { span } => Ok(crate::kernel::program_labeled_assert(
                crate::kernel::program_expression::cast(
                    ProgramExpression::Value(int32(0)),
                    ProgramType::Bool,
                ),
                format!(
                    "C++ __builtin_unreachable at {}:{}:{}",
                    span.file, span.start_line, span.start_column
                ),
            )),
            CppStatement::Assume { condition, span } => Ok(crate::kernel::program_labeled_assert(
                self.lower_expression(condition)?,
                format!(
                    "C++ __builtin_assume at {}:{}:{}",
                    span.file, span.start_line, span.start_column
                ),
            )),
            CppStatement::LibraryAssert {
                condition,
                contract,
                span,
                ..
            } => Ok(crate::kernel::program_labeled_assert(
                self.lower_expression(condition)?,
                format!(
                    "C++ assumed library contract `{}` [{} sha256:{}]{} at {}:{}:{}",
                    contract.function,
                    contract.header,
                    contract.sha256,
                    contract
                        .literal_constructor
                        .as_ref()
                        .map(|pin| format!(
                            "; literal constructor `{}` [{} sha256:{}]",
                            pin.function, pin.header, pin.sha256
                        ))
                        .unwrap_or_default(),
                    span.file,
                    span.start_line,
                    span.start_column
                ),
            )),
            CppStatement::AssignConstructionCall { .. }
            | CppStatement::ReturnConstruct { .. }
            | CppStatement::ReturnAggregateCall { .. }
            | CppStatement::ReturnRecord { .. }
            | CppStatement::Return { .. }
            | CppStatement::ReturnVoid { .. }
            | CppStatement::ReturnCall { .. }
            | CppStatement::Throw { .. }
            | CppStatement::ThrowIosFailure { .. }
            | CppStatement::ThrowAggregate { .. }
            | CppStatement::TryCatchInt32 { .. }
            | CppStatement::Scope { .. }
            | CppStatement::If { .. }
            | CppStatement::While { .. } => {
                Err("C++ control flow requires lifetime-aware lowering".into())
            }
            CppStatement::Call {
                callee, arguments, ..
            } => {
                let (target, dispatch) = self.call_target(callee, arguments)?;
                let parameter_names = self.callee_parameter_names(callee);
                let (prefix, arguments, mut temporaries) =
                    self.normalize_temporary_arguments_for(arguments, &parameter_names, true)?;
                temporaries.reverse();
                let operation = self.coerced_call(
                    ProgramStatement::Call {
                        function_name: target,
                        arguments,
                        dispatch,
                        callee: None,
                        reference_binding: None,
                    },
                    self.call_has_receiver(callee),
                );
                let operation = if temporaries.is_empty() {
                    operation
                } else {
                    program_seq(
                        operation,
                        program_end_automatic_lifetimes(temporaries.into_iter().collect()),
                    )
                };
                Ok(evaluate_then(prefix, operation))
            }
            CppStatement::CallStore {
                callee,
                arguments,
                value_type,
                field,
                compound_operator,
                value,
                ..
            } => {
                let (stored_type, offset) = if let Some(field) = field {
                    let (field_type, offset) =
                        self.records.resolve_returned_field(value_type, field)?;
                    (cpp_scalar_kernel_type(field_type)?, Some(offset))
                } else {
                    let element = scalar::reference_element(value_type)
                        .ok_or("unsupported C++ call store referent")?;
                    (element.kind.kernel_type(), None)
                };
                // C++17 sequences the right operand before the call.
                let expression = self.lower_expression(value)?;
                let (read, operand) = self.retain_value(expression, stored_type);
                let evaluation = self.normalize_scalar(ScalarInput::Call {
                    callee,
                    arguments,
                    value_type,
                    conversions: &[],
                })?;
                let pointer = match offset {
                    Some(offset) => crate::kernel::program_expression::pointer_offset_bytes(
                        evaluation.value,
                        offset,
                    ),
                    None => evaluation.value,
                };
                let value = match compound_operator {
                    Some(operator) => {
                        use super::CppCompoundAssignment;
                        use crate::kernel::program_expression::{add, subtract};

                        let previous = self.lower_typed_load(pointer.clone(), stored_type)?;
                        match operator {
                            CppCompoundAssignment::Add => add(previous, operand),
                            CppCompoundAssignment::Subtract => subtract(previous, operand),
                        }
                    }
                    None => operand,
                };
                Ok(evaluate_then(
                    read,
                    evaluate_then(
                        evaluation.prefix,
                        program_typed_store(pointer, value, stored_type),
                    ),
                ))
            }
        }
    }

    /// Each sequence starts with the objects live on entry. Construction adds
    /// an object only after its initializer; lexical exits restore a cursor.
    fn lower_sequence_with_lifetimes<'p>(
        &mut self,
        statements: &[CppStatement],
        plan: &'p LifetimePlan,
        state: &mut LifetimeState<'p>,
        unwind_base: usize,
    ) -> Result<ProgramStatement, String> {
        let mut lowered = None;
        for statement in statements {
            let current =
                self.lower_statement_with_lifetimes(statement, plan, state, unwind_base)?;
            lowered = Some(match lowered {
                Some(previous) => program_seq(previous, current),
                None => current,
            });
            plan.constructed(statement, state);
        }
        Ok(lowered.unwrap_or_else(program_skip))
    }

    fn lower_statement_with_lifetimes<'p>(
        &mut self,
        statement: &CppStatement,
        plan: &'p LifetimePlan,
        state: &mut LifetimeState<'p>,
        unwind_base: usize,
    ) -> Result<ProgramStatement, String> {
        match statement {
            CppStatement::AssignConstructionCall {
                target,
                callee,
                arguments,
                ..
            } => {
                let Some(CppType::Record { name, .. }) =
                    plan.full_expression_temporary_type(statement)
                else {
                    return Err(
                        "C++ construction assignment is missing its RHS lifetime event".into(),
                    );
                };
                let layout = self.record_layout(name)?;
                let (prefix, actual, prepared) = self.normalize_arguments(callee, arguments)?;
                let temporary = self.fresh_aggregate_capture(name)?;
                let (materialize, address) = self.retain_materialized(&temporary);
                // The RHS is a separate object: the live LHS may be read by
                // the factory and cannot serve as unwritten construction storage.
                Ok(evaluate_then(
                    prefix,
                    program_seq(
                        program_allocate_aggregate_destination(temporary.clone(), layout.clone()),
                        program_seq(
                            end_prepared_arguments(
                                self.coerced(program_call_construct(
                                    temporary.clone(),
                                    self.callee_name(callee)?,
                                    actual,
                                )),
                                prepared,
                            ),
                            program_seq(
                                program_seq(
                                    materialize,
                                    program_copy_aggregate(
                                        self.lower_place(target)?,
                                        address,
                                        layout,
                                    ),
                                ),
                                program_end_automatic_lifetimes(vec![(temporary)]),
                            ),
                        ),
                    ),
                ))
            }
            CppStatement::ReturnConstruct {
                callee, arguments, ..
            } => {
                let (prefix, arguments, prepared) = self.normalize_arguments(callee, arguments)?;
                let mut actual = vec![crate::kernel::program_expression::cast(
                    crate::kernel::program_expression::variable(crate::kernel::CONTRACT_RESULT),
                    ProgramType::Int32Pointer,
                )];
                actual.extend(arguments);
                Ok(evaluate_then(
                    prefix,
                    program_seq(
                        end_prepared_arguments(
                            self.coerced(program_call(self.callee_name(callee)?, actual)),
                            prepared,
                        ),
                        program_return(crate::kernel::program_expression::variable(
                            crate::kernel::CONTRACT_RESULT,
                        )),
                    ),
                ))
            }
            CppStatement::ReturnAggregateCall {
                callee, arguments, ..
            } => {
                let (prefix, arguments, prepared) = self.normalize_arguments(callee, arguments)?;
                Ok(evaluate_then(
                    prefix,
                    program_seq(
                        end_prepared_arguments(
                            self.coerced(program_call_construct(
                                crate::kernel::CONTRACT_RESULT,
                                self.callee_name(callee)?,
                                arguments,
                            )),
                            prepared,
                        ),
                        program_return(crate::kernel::program_expression::variable(
                            crate::kernel::CONTRACT_RESULT,
                        )),
                    ),
                ))
            }
            CppStatement::ReturnRecord {
                source, value_type, ..
            } => {
                let CppType::Record { name, .. } = value_type else {
                    return Err("C++ record return has no nominal record type".into());
                };
                let layout = self.record_layout(name)?;
                let capture = self.fresh_aggregate_capture(name)?;
                let (materialize, address) = self.retain_materialized(&capture);
                let mut result = program_seq(
                    program_declare_aggregate(capture.clone(), layout.clone()),
                    program_copy_aggregate(
                        crate::kernel::program_expression::variable(capture.clone()),
                        self.lower_place(source)?,
                        layout,
                    ),
                );
                result = program_seq(result, materialize);
                for cleanup in state.exit(0) {
                    result = program_seq(result, self.lower_cleanup(cleanup)?);
                }
                Ok(program_seq(result, program_return(address)))
            }
            CppStatement::ReturnVoid { .. } => {
                let cleanups = self.lower_cleanups(&state.exit(0).collect::<Vec<_>>())?;
                Ok(evaluate_then(
                    cleanups,
                    program_return(ProgramExpression::Value(crate::kernel::ProgramValue::Void)),
                ))
            }
            CppStatement::Return { value, .. } => {
                let evaluation = self.normalize_scalar(ScalarInput::Value(value))?;
                self.lower_scalar_return(evaluation, &state.exit(0).collect::<Vec<_>>(), &[])
            }
            CppStatement::ReturnCall {
                callee,
                arguments,
                value_type,
                conversions,
                ..
            } => {
                let evaluation = self.normalize_scalar(ScalarInput::Call {
                    callee,
                    arguments,
                    value_type: conversions
                        .first()
                        .map_or(value_type, |cast| &cast.source_type),
                    conversions,
                })?;
                self.lower_scalar_return(
                    evaluation,
                    &state.exit(0).collect::<Vec<_>>(),
                    &state.exit(unwind_base).collect::<Vec<_>>(),
                )
            }
            CppStatement::ThrowAggregate {
                value_type, fields, ..
            } => {
                let CppType::Record { name, .. } = value_type else {
                    unreachable!("checked aggregate exception")
                };
                let mut operation = self.lower_throwing_statement(
                    ProgramStatement::ThrowOpaque(super::names::opaque_exception_type(name)),
                    state.exit(unwind_base),
                )?;
                // Braced aggregate initialization is sequenced left to right.
                // Discarding an opaque field never discards its reads or UB checks.
                let initializers = fields
                    .iter()
                    .map(|field| self.lower_expression(&field.value))
                    .collect::<Result<Vec<_>, _>>()?;
                for expression in initializers.into_iter().rev() {
                    operation = program_seq(
                        ProgramStatement::StepValue {
                            aggregate_layout: None,
                            steps: Vec::new(),
                            expression,
                            value_type: None,
                            pointee_constant: false,
                        },
                        operation,
                    );
                }
                Ok(operation)
            }
            CppStatement::ThrowIosFailure { .. } => self.lower_throwing_statement(
                ProgramStatement::ThrowOpaque(crate::kernel::TypeParameterName::intern(
                    "std::ios_base::failure",
                )),
                state.exit(unwind_base),
            ),
            CppStatement::Throw { value, .. } => {
                let throw = ProgramStatement::Throw(self.lower_expression(value)?);
                self.lower_throwing_statement(throw, state.exit(unwind_base))
            }
            CppStatement::If {
                condition,
                then_branch,
                else_branch,
                ..
            } => {
                let evaluation = self.normalize_scalar(match condition {
                    CppCondition::Expression(value) => ScalarInput::Value(value),
                    CppCondition::Call { call } => ScalarInput::Call {
                        callee: &call.callee,
                        arguments: &call.arguments,
                        value_type: &call.value_type,
                        conversions: &[],
                    },
                })?;
                let prefix = if evaluation.may_throw {
                    self.lower_throwing_statement(evaluation.prefix, state.exit(unwind_base))?
                } else {
                    evaluation.prefix
                };
                let mark = state.mark();
                let then_branch =
                    self.lower_sequence_with_lifetimes(then_branch, plan, state, unwind_base)?;
                state.restore(mark);
                let else_branch =
                    self.lower_sequence_with_lifetimes(else_branch, plan, state, unwind_base)?;
                state.restore(mark);
                Ok(evaluate_then(
                    prefix,
                    program_if(evaluation.value, then_branch, else_branch),
                ))
            }
            CppStatement::While {
                condition, body, ..
            } => {
                // The condition is evaluated before each iteration, so it is
                // one expression with nothing to capture first.
                let evaluation = self.normalize_scalar(ScalarInput::Value(condition))?;
                if evaluation.may_throw || !matches!(evaluation.prefix, ProgramStatement::Skip) {
                    return Err("a C++ while condition must evaluate without a call".into());
                }
                let mark = state.mark();
                let body = self.lower_sequence_with_lifetimes(body, plan, state, unwind_base)?;
                state.restore(mark);
                Ok(crate::kernel::program_while(
                    evaluation.value,
                    Vec::new(),
                    body,
                ))
            }
            CppStatement::TryCatchInt32 {
                try_body,
                binding,
                handler,
                ..
            } => {
                let mark = state.mark();
                let try_body = self.lower_sequence_with_lifetimes(try_body, plan, state, mark)?;
                state.restore(mark);
                let handler =
                    self.lower_sequence_with_lifetimes(handler, plan, state, unwind_base)?;
                state.restore(mark);
                Ok(program_try_catch_int32(
                    try_body,
                    binding.name.clone(),
                    handler,
                ))
            }
            CppStatement::Scope { body, .. } => {
                let mark = state.mark();
                let mut result =
                    self.lower_sequence_with_lifetimes(body, plan, state, unwind_base)?;
                for cleanup in state.exit(mark) {
                    result = program_seq(result, self.lower_cleanup(cleanup)?);
                }
                state.restore(mark);
                Ok(result)
            }
            CppStatement::Declare {
                initializer: CppInitializer::Call { .. },
                ..
            }
            | CppStatement::Call { .. }
            | CppStatement::CallStore { .. } => {
                let operation = self.lower_statement(statement)?;
                self.lower_throwing_statement(operation, state.exit(unwind_base))
            }
            _ => self.lower_statement(statement),
        }
    }

    /// A statement that may exit by throwing, with the destructors of the
    /// objects live around it to run if it does.
    fn lower_throwing_statement<'p>(
        &mut self,
        statement: ProgramStatement,
        cleanups: impl Iterator<Item = &'p CppCleanup>,
    ) -> Result<ProgramStatement, String> {
        let cleanups = cleanups.collect::<Vec<_>>();
        if cleanups.is_empty() {
            return Ok(statement);
        }
        Ok(program_unwind_cleanup(
            statement,
            self.lower_cleanups(&cleanups)?,
        ))
    }

    /// The destructors to run, in order, as one statement.
    fn lower_cleanups(&mut self, cleanups: &[&CppCleanup]) -> Result<ProgramStatement, String> {
        let mut lowered = program_skip();
        for cleanup in cleanups {
            lowered = program_seq(lowered, self.lower_cleanup(cleanup)?);
        }
        Ok(lowered)
    }

    /// Normalize evaluation into explicit statements followed by a pure value.
    /// The validated C++ ordering policy is shared by every scalar call context.
    fn normalize_scalar(&mut self, input: ScalarInput<'_>) -> Result<ScalarEvaluation, String> {
        self.normalize_scalar_into(input, None)
    }

    /// Use an existing source destination when the caller needs no temporary.
    fn normalize_scalar_into(
        &mut self,
        input: ScalarInput<'_>,
        destination: Option<BindingName>,
    ) -> Result<ScalarEvaluation, String> {
        match input {
            ScalarInput::Value(value) if expression_contains_observer(value) => {
                self.normalize_expression(value)
            }
            ScalarInput::Value(value) => Ok(ScalarEvaluation {
                prefix: program_skip(),
                value: self.lower_expression(value)?,
                value_type: cpp_return_scalar_type(value.value_type())?,
                may_throw: false,
            }),
            ScalarInput::Call {
                callee,
                arguments,
                value_type,
                conversions,
            } => {
                let (target, dispatch) = self.call_target(callee, arguments)?;
                let parameter_names = self.callee_parameter_names(callee);
                let (prefix, arguments, temporaries) = self.normalize_temporary_arguments_for(
                    arguments,
                    &parameter_names,
                    arguments.iter().any(CppCallArgument::is_opaque_copy),
                )?;
                // Keep the callee's own type until the source conversion
                // reads the value, including reference loads.
                let capture_type = cpp_return_scalar_type(value_type)?;
                let (mut call, raw) =
                    crate::kernel::program_call_value(self.result_step(), target, arguments);
                let ProgramStatement::CallResult {
                    result_type,
                    result_pointee_constant,
                    dispatch: call_dispatch,
                    ..
                } = &mut call
                else {
                    unreachable!("a value-producing call")
                };
                let pointee_constant = scalar::returns_constant_element(value_type);
                *call_dispatch = dispatch;
                *result_type = Some(capture_type);
                *result_pointee_constant = pointee_constant;
                let (operation, mut value) =
                    if let Some(name) = destination.filter(|_| conversions.is_empty()) {
                        (
                            program_seq(
                                program_declare_with_all_qualifiers(
                                    name.clone(),
                                    capture_type,
                                    false,
                                    false,
                                    false,
                                    pointee_constant,
                                ),
                                self.coerced_call(
                                    program_seq(call, program_assign(name.clone(), raw)),
                                    self.call_has_receiver(callee),
                                ),
                            ),
                            crate::kernel::program_expression::variable(name),
                        )
                    } else {
                        (self.coerced_call(call, self.call_has_receiver(callee)), raw)
                    };
                let operation = if temporaries.is_empty() {
                    operation
                } else {
                    program_seq(
                        operation,
                        program_end_automatic_lifetimes(temporaries.into_iter().rev().collect()),
                    )
                };
                let mut result_type = capture_type;
                for conversion in conversions {
                    if conversion.cast_kind == super::CppScalarCastKind::ReferenceLoad {
                        let element = scalar::reference_element(&conversion.source_type)
                            .ok_or("unsupported C++ reference load")?;
                        result_type = element.kind.kernel_type();
                        value = self.lower_typed_load(value, result_type)?;
                        continue;
                    }
                    if matches!(conversion.value_type, CppType::Pointer { .. }) {
                        result_type = cpp_return_scalar_type(&conversion.value_type)?;
                        if conversion.cast_kind == super::CppScalarCastKind::BytePointerCast {
                            value = crate::kernel::program_expression::cast(value, result_type);
                        }
                        continue;
                    }
                    let source = Scalar::mutable_kind(&conversion.source_type)
                        .ok_or("unsupported C++ call conversion operand")?;
                    let target = Scalar::mutable_kind(&conversion.value_type)
                        .ok_or("unsupported C++ call conversion result")?;
                    if source != target {
                        value = scalar::convert(value, source, target);
                    }
                    result_type = target.kernel_type();
                }
                Ok(ScalarEvaluation {
                    prefix: evaluate_then(prefix, operation),
                    value,
                    value_type: result_type,
                    may_throw: true,
                })
            }
        }
    }

    /// The arguments of a call to `callee` whose full expression holds no
    /// other temporaries, with the prepared parameter objects of its
    /// by-value record copies; the caller ends those once the call returns.
    fn normalize_arguments(
        &mut self,
        callee: &super::CppFunctionReference,
        arguments: &[CppCallArgument],
    ) -> Result<(ProgramStatement, Vec<ProgramExpression>, Vec<BindingName>), String> {
        let parameter_names = self.callee_parameter_names(callee);
        self.normalize_temporary_arguments_for(arguments, &parameter_names, false)
    }

    /// The parameter names of `callee`, by position, when it is a known
    /// function: what a prepared by-value argument is passed as.
    fn callee_parameter_names(&self, callee: &super::CppFunctionReference) -> Vec<String> {
        (!callee.through_pointer)
            .then(|| {
                self.polymorphism
                    .functions
                    .get(callee.declaration_id.as_str())
            })
            .flatten()
            .map(|function| {
                function
                    .parameters
                    .iter()
                    .map(|parameter| parameter.name.clone())
                    .collect()
            })
            .unwrap_or_default()
    }

    fn normalize_temporary_arguments_for(
        &mut self,
        arguments: &[CppCallArgument],
        parameter_names: &[String],
        allow_temporaries: bool,
    ) -> Result<(ProgramStatement, Vec<ProgramExpression>, Vec<BindingName>), String> {
        let mut temporaries = Vec::new();
        let mut evaluation = program_skip();
        let has_nested = arguments
            .iter()
            .any(|argument| matches!(argument, CppCallArgument::Call { .. }));
        // Check and state field reads before a nested call can throw. Scalar
        // isolation keeps their values invariant in every argument order.
        let mut retained_states = Vec::with_capacity(arguments.len());
        for argument in arguments {
            let retained_state = if let CppCallArgument::Value { value } = argument {
                if has_nested && super::schema::field_scalar_argument(value) {
                    let value_type = cpp_return_scalar_type(value.value_type())?;
                    let expression = self.lower_expression(value)?;
                    let (read, captured) = self.retain_value(expression, value_type);
                    evaluation = evaluate_then(evaluation, read);
                    Some(captured)
                } else {
                    None
                }
            } else {
                None
            };
            retained_states.push(retained_state);
        }
        let mut lowered = Vec::with_capacity(arguments.len());
        for (position, (argument, retained_state)) in
            arguments.iter().zip(retained_states).enumerate()
        {
            let parameter_name = parameter_names
                .get(position)
                .filter(|name| !name.is_empty());
            crate::instrumentation::record_deterministic_work(1);
            if let Some(retained_state) = retained_state {
                lowered.push(retained_state);
            } else if let CppCallArgument::Value {
                value:
                    CppExpression::ClosureInstance {
                        function, captures, ..
                    },
            } = argument
            {
                // A lambda made for a `std::function` argument is the value
                // its instance function returns for the captured values.
                let mut values = Vec::with_capacity(captures.len());
                for value in captures {
                    values.push(self.lower_expression(value)?);
                }
                let closure = self.names.require(&function.declaration_id)?;
                let (call, returned) = crate::kernel::program_create_closure(
                    self.result_step(),
                    closure.to_owned(),
                    values,
                    None,
                );
                evaluation = evaluate_then(evaluation, call);
                lowered.push(returned);
            } else if let CppCallArgument::RecordCopy {
                place,
                value_type: CppType::Record { name, .. },
                ..
            } = argument
            {
                // The trivial copy into the callee's parameter object is a
                // region of its own before the call, as C's is: the call
                // receives the initialized object, which ends with the full
                // expression.
                let layout = self.record_layout(name)?;
                let capture = self.fresh_prepared_argument(name, parameter_name)?;
                let source = crate::kernel::program_expression::cast(
                    self.lower_place(place)?,
                    ProgramType::UInt8Pointer,
                );
                evaluation = evaluate_then(
                    evaluation,
                    program_seq(
                        program_allocate_aggregate_destination(capture.clone(), layout.clone()),
                        crate::kernel::program_copy_aggregate(
                            crate::kernel::program_expression::variable(capture.clone()),
                            source,
                            layout,
                        ),
                    ),
                );
                lowered.push(crate::kernel::program_expression::cast(
                    crate::kernel::program_expression::variable(capture.clone()),
                    ProgramType::UInt8Pointer,
                ));
                temporaries.push(capture);
            } else if matches!(
                argument,
                CppCallArgument::Construct { .. }
                    | CppCallArgument::Call {
                        value_type: CppType::Record { .. },
                        ..
                    }
            ) {
                if !allow_temporaries {
                    return Err(
                        "C++ record temporaries require a statement-call full expression".into(),
                    );
                }
                let (callee, arguments, value_type, constructor) = match argument {
                    CppCallArgument::Construct {
                        callee,
                        arguments,
                        value_type,
                        ..
                    } => (callee, arguments, value_type, true),
                    CppCallArgument::Call {
                        callee,
                        arguments,
                        value_type,
                        ..
                    } => (callee, arguments, value_type, false),
                    _ => unreachable!(),
                };
                let CppType::Record { name, .. } = value_type else {
                    unreachable!()
                };
                let layout = self.record_layout(name)?;
                // The prvalue initializes the callee's parameter object directly.
                let capture = self.fresh_prepared_argument(name, parameter_name)?;
                let inner_parameter_names = self.callee_parameter_names(callee);
                let (prefix, mut actual, inner_temporaries) = self
                    .normalize_temporary_arguments_for(arguments, &inner_parameter_names, true)?;
                temporaries.extend(inner_temporaries);
                evaluation = evaluate_then(evaluation, prefix);
                let operation = if constructor {
                    actual.insert(
                        0,
                        crate::kernel::program_expression::cast(
                            crate::kernel::program_expression::variable(capture.clone()),
                            ProgramType::Int32Pointer,
                        ),
                    );
                    program_call(self.callee_name(callee)?, actual)
                } else {
                    program_call_construct(capture.clone(), self.callee_name(callee)?, actual)
                };
                evaluation = evaluate_then(
                    evaluation,
                    program_seq(
                        program_allocate_aggregate_destination(capture.clone(), layout),
                        self.coerced(operation),
                    ),
                );
                // Preserve the materialization point for proofs. The call's
                // source layout also needs the prepared binding itself.
                let (materialize, _) = self.retain_materialized(&capture);
                evaluation = evaluate_then(evaluation, materialize);
                lowered.push(crate::kernel::program_expression::cast(
                    crate::kernel::program_expression::variable(capture.clone()),
                    ProgramType::UInt8Pointer,
                ));
                temporaries.push(capture);
            } else if let CppCallArgument::Call {
                callee,
                arguments,
                value_type,
                ..
            } = argument
            {
                let inner = self.normalize_scalar(ScalarInput::Call {
                    callee,
                    arguments,
                    value_type,
                    conversions: &[],
                })?;
                evaluation = evaluate_then(evaluation, inner.prefix);
                lowered.push(inner.value);
            } else if let CppCallArgument::Value { value } = argument
                && !has_nested
                && expression_contains_observer(value)
            {
                let inner = self.normalize_scalar(ScalarInput::Value(value))?;
                evaluation = evaluate_then(evaluation, inner.prefix);
                lowered.push(inner.value);
            } else {
                // Remaining siblings are stable and total across the call.
                lowered.push(self.lower_call_argument(argument, position)?);
            }
        }
        Ok((evaluation, lowered, temporaries))
    }

    fn lower_scalar_return(
        &mut self,
        evaluation: ScalarEvaluation,
        cleanups: &[&CppCleanup],
        unwind_cleanups: &[&CppCleanup],
    ) -> Result<ProgramStatement, String> {
        if cleanups.is_empty() {
            return Ok(evaluate_then(
                evaluation.prefix,
                program_return(evaluation.value),
            ));
        }
        // Evaluate the return expression before any destructor can change
        // its operands. A throwing call runs only the exceptional cleanups.
        let (capture, value) = self.retain_value(evaluation.value, evaluation.value_type);
        let mut prefix = evaluate_then(evaluation.prefix, capture);
        if evaluation.may_throw && self.unwind_cleanups && !unwind_cleanups.is_empty() {
            prefix = program_unwind_cleanup(prefix, self.lower_cleanups(unwind_cleanups)?);
        }
        for cleanup in cleanups {
            prefix = program_seq(prefix, self.lower_cleanup(cleanup)?);
        }
        Ok(program_seq(prefix, program_return(value)))
    }

    fn normalize_expression(
        &mut self,
        expression: &CppExpression,
    ) -> Result<ScalarEvaluation, String> {
        let value_type = cpp_return_scalar_type(expression.value_type())?;
        let (prefix, value, may_throw) = match expression {
            CppExpression::ObserverCall {
                callee,
                arguments,
                value_type: result_type,
                returned_member,
                reference_load,
                ..
            } => {
                let Some(member) = returned_member else {
                    let mut evaluation = self.normalize_scalar(ScalarInput::Call {
                        callee,
                        arguments,
                        value_type: reference_load.as_deref().unwrap_or(result_type),
                        conversions: &[],
                    })?;
                    if reference_load.is_some() {
                        // Read the referent at this operand's evaluation point.
                        // Later comparisons and branch proofs use the captured
                        // scalar, including when a succeeding call has its own
                        // result and program point.
                        let load = self.lower_typed_load(evaluation.value, value_type)?;
                        let (capture, value) = self.retain_value(load, value_type);
                        evaluation.prefix = evaluate_then(evaluation.prefix, capture);
                        evaluation.value = value;
                        evaluation.value_type = value_type;
                    }
                    // Call graph validation requires every observer to be noexcept.
                    evaluation.may_throw = false;
                    return Ok(evaluation);
                };
                let (field_type, offset) = self
                    .records
                    .resolve_returned_field(&member.reference_type, &member.field)?;
                let pointee_constant = scalar::returns_constant_element(field_type);
                let evaluation = self.normalize_scalar(ScalarInput::Call {
                    callee,
                    arguments,
                    value_type: &member.reference_type,
                    conversions: &[],
                })?;
                let pointer = crate::kernel::program_expression::pointer_offset_bytes(
                    evaluation.value,
                    offset,
                );
                (
                    evaluation.prefix,
                    self.lower_qualified_typed_load(pointer, value_type, pointee_constant)?,
                    false,
                )
            }
            CppExpression::LogicalNot { value, .. } => {
                let input = self.normalize_expression(value)?;
                (
                    input.prefix,
                    crate::kernel::program_expression::cast(
                        crate::kernel::program_expression::not(input.value),
                        ProgramType::Bool,
                    ),
                    input.may_throw,
                )
            }
            CppExpression::PointerQualification { value, .. } => {
                let input = self.normalize_expression(value)?;
                (input.prefix, input.value, input.may_throw)
            }
            CppExpression::VoidPointerCast {
                value, value_type, ..
            } => {
                let input = self.normalize_expression(value)?;
                (
                    input.prefix,
                    erase_pointer_type(input.value, value_type),
                    input.may_throw,
                )
            }
            CppExpression::BytePointerCast { value, .. } => {
                let input = self.normalize_expression(value)?;
                (
                    input.prefix,
                    crate::kernel::program_expression::cast(input.value, ProgramType::UInt8Pointer),
                    input.may_throw,
                )
            }
            CppExpression::IntegralCast {
                value, value_type, ..
            }
            | CppExpression::EnumCast {
                value, value_type, ..
            } => {
                let input = self.normalize_expression(value)?;
                let source = Scalar::mutable_kind(value.value_type())
                    .ok_or("unsupported observer cast operand")?;
                let target =
                    Scalar::mutable_kind(value_type).ok_or("unsupported observer cast result")?;
                (
                    input.prefix,
                    scalar::convert(input.value, source, target),
                    input.may_throw,
                )
            }
            CppExpression::ReferenceBinding {
                address,
                value_type,
                ..
            } => {
                let input = self.normalize_expression(address)?;
                let value = self.reference_binding_address(input.value, address, value_type)?;
                (input.prefix, value, input.may_throw)
            }
            // The load has the pointee's type, as `lower_expression`'s
            // dereference has: `*pick(p)` through `unsigned char*` reads one
            // byte, not an `int`.
            CppExpression::Dereference {
                pointer,
                value_type,
                ..
            } if is_native_object_pointer(pointer.value_type()) => {
                let input = self.normalize_expression(pointer)?;
                let value =
                    self.lower_typed_load(input.value, cpp_scalar_kernel_type(value_type)?)?;
                (input.prefix, value, input.may_throw)
            }
            CppExpression::Dereference { .. } => {
                return Err("C++ dereference is outside mutable `int*` lowering".into());
            }
            CppExpression::Binary {
                operator,
                left,
                right,
                value_type,
                ..
            } => {
                let lhs = self.normalize_expression(left)?;
                let rhs = self.normalize_expression(right)?;
                if *operator == CppBinaryOperator::LogicalAnd {
                    let step = self.result_step();
                    let prefix = evaluate_then(
                        lhs.prefix,
                        program_if(
                            lhs.value,
                            evaluate_then(
                                rhs.prefix,
                                value_step(step, rhs.value, ProgramType::Bool),
                            ),
                            value_step(
                                step,
                                crate::kernel::program_expression::cast(
                                    ProgramExpression::Value(int32(0)),
                                    ProgramType::Bool,
                                ),
                                ProgramType::Bool,
                            ),
                        ),
                    );
                    return Ok(ScalarEvaluation {
                        prefix,
                        value: value_result(step),
                        value_type: ProgramType::Bool,
                        may_throw: lhs.may_throw || rhs.may_throw,
                    });
                }
                let value = lower_binary_value(*operator, lhs.value, rhs.value, value_type);
                (
                    evaluate_then(lhs.prefix, rhs.prefix),
                    value,
                    lhs.may_throw || rhs.may_throw,
                )
            }
            _ => (program_skip(), self.lower_expression(expression)?, false),
        };
        Ok(ScalarEvaluation {
            prefix,
            value,
            value_type,
            may_throw,
        })
    }

    fn fresh_temporary(&mut self, program_type: ProgramType) -> Result<BindingName, String> {
        self.fresh_temporary_with(program_type, false)
    }

    fn fresh_temporary_with(
        &mut self,
        program_type: ProgramType,
        prepared_argument: bool,
    ) -> Result<BindingName, String> {
        let ordinal = self.next_temporary;
        self.next_temporary = ordinal
            .checked_add(1)
            .ok_or("C++ temporary ordinal overflow")?;
        crate::instrumentation::record_deterministic_work(1);
        let owner = self.temporary_owner.clone();
        let id = if prepared_argument {
            LocalBindingId::prepared_argument(owner, ordinal)
        } else {
            LocalBindingId::temporary(owner, ordinal)
        };
        id.initialize_program_type(program_type);
        Ok(id.into())
    }

    /// Publish the address after construction or copying has completed.
    /// The full expression still owns the storage and retires it separately.
    fn retain_materialized(&self, binding: &BindingName) -> (ProgramStatement, ProgramExpression) {
        self.retain_value(
            crate::kernel::program_expression::variable(binding.clone()),
            ProgramType::UInt8Pointer,
        )
    }

    fn fresh_aggregate_capture(&mut self, record: &str) -> Result<BindingName, String> {
        self.fresh_aggregate_capture_with(record, false)
    }

    /// The object a call receives as its by-value parameter, named for that
    /// parameter when the callee is known.
    fn fresh_prepared_argument(
        &mut self,
        record: &str,
        parameter: Option<&String>,
    ) -> Result<BindingName, String> {
        let Some(parameter) = parameter else {
            return self.fresh_aggregate_capture_with(record, true);
        };
        let ordinal = self.next_temporary;
        self.next_temporary = ordinal
            .checked_add(1)
            .ok_or("C++ temporary ordinal overflow")?;
        crate::instrumentation::record_deterministic_work(1);
        let id =
            LocalBindingId::prepared_argument_for(self.temporary_owner.clone(), ordinal, parameter);
        id.initialize_program_type(ProgramType::Int32Pointer);
        id.initialize_struct_name(record);
        Ok(id.into())
    }

    fn fresh_aggregate_capture_with(
        &mut self,
        record: &str,
        prepared_argument: bool,
    ) -> Result<BindingName, String> {
        let binding = self.fresh_temporary_with(ProgramType::Int32Pointer, prepared_argument)?;
        binding
            .local_id()
            .expect("temporary identity")
            .initialize_struct_name(record);
        Ok(binding)
    }

    fn lower_call_arguments(
        &mut self,
        arguments: &[CppCallArgument],
    ) -> Result<Vec<ProgramExpression>, String> {
        arguments
            .iter()
            .enumerate()
            .map(|(position, argument)| self.lower_call_argument(argument, position))
            .collect()
    }

    fn lower_cleanup(&self, cleanup: &CppCleanup) -> Result<ProgramStatement, String> {
        let CppCleanup::Destructor { object, callee, .. } = cleanup;
        Ok(program_seq(
            program_call(
                self.callee_name(callee)?,
                vec![crate::kernel::program_expression::cast(
                    self.lower_place(object)?,
                    ProgramType::Int32Pointer,
                )],
            ),
            // A completed automatic destructor also ends its object's
            // storage lifetime. Raw aliases must not keep that storage live.
            program_end_automatic_lifetimes(vec![object.name.clone().into()]),
        ))
    }

    fn lower_call_argument(
        &mut self,
        argument: &CppCallArgument,
        position: usize,
    ) -> Result<ProgramExpression, String> {
        match argument {
            CppCallArgument::RecordCopy { place, .. } => {
                Ok(crate::kernel::program_expression::cast(
                    self.lower_place(place)?,
                    ProgramType::UInt8Pointer,
                ))
            }
            CppCallArgument::Value { value } => self.lower_expression(value),
            CppCallArgument::Reference { place } => {
                if self.direct_receiver.as_ref() == Some(place) {
                    self.direct_receiver = None;
                } else {
                    self.note_object_coercion(place, position)?;
                }
                let root = self.place(place)?;
                // A scalar local bound to a native reference: its address.
                if place.projections.is_empty()
                    && matches!(root.value_type, CppType::Integer { .. })
                {
                    return Ok(ProgramExpression::AddressOf(Box::new(
                        crate::kernel::program_expression::variable(self.variable_name(place)),
                    )));
                }
                let address = self.lower_place(place)?;
                // Binding a reference to a scalar field selects the same
                // member bounds as taking its address. This checks storage
                // without loading the field value.
                if !place.projections.is_empty() {
                    let (value_type, _) = self
                        .records
                        .resolve_path(&root.value_type, &place.projections)?;
                    if matches!(value_type, CppType::Record { .. }) {
                        // Keep each declared receiver projection, even when a
                        // zero-offset child's address equals its parent's.
                        // Expansion follows these explicit edges by index.
                        let mut address =
                            crate::kernel::program_expression::variable(self.variable_name(place));
                        let mut parent = &root.value_type;
                        for projection in &place.projections {
                            let (child, offset) = self
                                .records
                                .resolve_path(parent, std::iter::once(projection.as_ref()))?;
                            address = crate::kernel::program_expression::pointer_offset_bytes(
                                address, offset,
                            );
                            if let CppType::Record { name, is_const, .. } = child {
                                address = ProgramExpression::Cast {
                                    expression: Box::new(address),
                                    target_type: ProgramType::Int32Pointer,
                                    integer_mode: crate::kernel::IntegerCastMode::Standard,
                                    pointee_struct: Some(name.clone()),
                                    pointee_struct_size: None,
                                    pointee_volatile: false,
                                    pointee_constant: *is_const,
                                    explicit_qualification: false,
                                };
                            }
                            parent = child;
                        }
                        return Ok(address);
                    }
                    if let Some(element) = Scalar::pointer_element(value_type, true) {
                        let member_type = element.kind.kernel_type();
                        return Ok(crate::kernel::program_expression::checked_object_address(
                            crate::kernel::program_expression::typed_load(
                                ProgramExpression::Subobject {
                                    pointer: Box::new(address),
                                    width: member_type.byte_width(),
                                },
                                member_type,
                            ),
                        ));
                    }
                }
                if !matches!(root.value_type, CppType::Record { .. }) {
                    return Ok(address);
                }
                // Automatic aggregates use byte-addressed storage. Calls
                // need the reference's pointee representation, as constructor
                // and destructor receivers already do.
                let (value_type, _) = self
                    .records
                    .resolve_path(&root.value_type, &place.projections)?;
                let pointer_type = match value_type {
                    CppType::Record { .. } | CppType::Integer { bits: 32, .. } => {
                        ProgramType::Int32Pointer
                    }
                    CppType::Integer { bits: 64, .. } => ProgramType::Int64Pointer,
                    _ => {
                        return Err(
                            "C++ reference place has no supported pointer representation".into(),
                        );
                    }
                };
                Ok(crate::kernel::program_expression::cast(
                    address,
                    pointer_type,
                ))
            }
            CppCallArgument::Call { .. } | CppCallArgument::Construct { .. } => {
                Err("nested C++ call bypassed argument evaluation normalization".into())
            }
        }
    }

    fn lower_expression(
        &mut self,
        expression: &CppExpression,
    ) -> Result<ProgramExpression, String> {
        match expression {
            CppExpression::RuntimeConstantEvaluation { .. } => {
                Ok(crate::kernel::program_expression::cast(
                    ProgramExpression::Value(int32(0)),
                    ProgramType::Bool,
                ))
            }
            CppExpression::LogicalNot { value, .. } => Ok(crate::kernel::program_expression::cast(
                crate::kernel::program_expression::not(self.lower_expression(value)?),
                ProgramType::Bool,
            )),

            CppExpression::ObserverCall { .. } => Err(
                "C++ expression observers are supported in normalized scalar values only".into(),
            ),
            CppExpression::FunctionAddress { function, .. } => {
                Ok(crate::kernel::program_expression::function_address(
                    self.names.require(&function.declaration_id)?,
                ))
            }
            CppExpression::ClosureInstance { .. } => {
                Err("a C++ closure creation is evaluated only as a call argument".into())
            }
            CppExpression::NullPointer { value_type, .. } => {
                Ok(crate::kernel::program_expression::cast(
                    ProgramExpression::Value(int32(0)),
                    cpp_scalar_kernel_type(value_type)?,
                ))
            }
            CppExpression::IntegerLiteral {
                value, value_type, ..
            }
            | CppExpression::CompilerConstant {
                value, value_type, ..
            } => Scalar::mutable_kind(value_type)
                .and_then(|kind| kind.parse_literal(value))
                .map(|literal| literal.kernel_expression())
                .ok_or_else(|| format!("unsupported C++ integer constant `{value}`")),
            CppExpression::ConstantReference {
                constant,
                value_type,
                ..
            } => {
                let resolved = self
                    .constants
                    .get(constant.declaration_id.as_str())
                    .ok_or_else(|| {
                        format!(
                            "C++ lowering found unknown constant declaration `{}`",
                            constant.declaration_id
                        )
                    })?;
                if resolved.name != constant.name {
                    return Err(format!(
                        "C++ constant declaration `{}` changed name during lowering",
                        constant.declaration_id
                    ));
                }
                Scalar::mutable_kind(value_type)
                    .and_then(|kind| kind.parse_literal(&resolved.evaluated_value))
                    .map(|literal| literal.kernel_expression())
                    .ok_or_else(|| {
                        format!(
                            "C++ constant `{}` has unsupported evaluated value `{}`",
                            resolved.name, resolved.evaluated_value
                        )
                    })
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
                ) => Ok(crate::kernel::program_expression::variable(
                    self.variable_name(place),
                )),
                (
                    CppType::Integer { .. } | CppType::Enumeration { .. },
                    CppType::Integer { .. } | CppType::Enumeration { .. },
                ) if cpp_scalar_kernel_type(&scalar::scalar_value_type(
                    &self.place(place)?.value_type,
                ))? == cpp_scalar_kernel_type(value_type)? =>
                {
                    Ok(crate::kernel::program_expression::variable(
                        self.variable_name(place),
                    ))
                }
                (
                    CppType::Pointer { pointee },
                    CppType::Pointer {
                        pointee: value_pointee,
                    },
                ) if Scalar::pointer_element(pointee, true).is_some()
                    && scalar::same_scalar_type(pointee, value_pointee) =>
                {
                    Ok(crate::kernel::program_expression::variable(
                        self.variable_name(place),
                    ))
                }
                (pointer @ CppType::Pointer { .. }, value_type)
                    if scalar::record_pointee(pointer).is_some() && pointer == value_type =>
                {
                    Ok(crate::kernel::program_expression::variable(
                        self.variable_name(place),
                    ))
                }
                // A function-pointer variable read to pass it on.
                (CppType::FunctionPointer { .. }, CppType::FunctionPointer { .. }) => Ok(
                    crate::kernel::program_expression::variable(self.variable_name(place)),
                ),
                // A value of an abstract type argument, copied whole.
                (CppType::Parameter { name, .. }, CppType::Parameter { name: value, .. })
                    if name == value =>
                {
                    Ok(crate::kernel::program_expression::variable(
                        self.variable_name(place),
                    ))
                }
                (reference @ CppType::LvalueReference { .. }, _)
                    if scalar::reference_element(reference).is_some() =>
                {
                    let element = scalar::reference_element(reference).unwrap();
                    let pointer = self.lower_place(place)?;
                    let occurrence = self.next_load_occurrence;
                    self.next_load_occurrence = self
                        .next_load_occurrence
                        .checked_add(1)
                        .ok_or_else(|| "C++ load occurrence capacity exceeded".to_string())?;
                    Ok(crate::kernel::program_expression::typed_load_with_source(
                        pointer,
                        element.kind.kernel_type(),
                        Some(LoadSourceId {
                            owner: LoadSourceOwnerId {
                                source_unit: self.source_unit.into(),
                                function: self.function_name.into(),
                            },
                            occurrence,
                            reference_access: None,
                        }),
                    ))
                }
                (CppType::LvalueReference { pointee }, value_type)
                    if is_const_int64(pointee) && is_mutable_int64(value_type) =>
                {
                    let pointer = self.lower_place(place)?;
                    self.lower_typed_load(pointer, ProgramType::Int64)
                }
                _ => Err("C++ load is outside direct bool/reference lowering".into()),
            },
            CppExpression::AddressOf {
                place, value_type, ..
            } if scalar::record_referent(value_type).is_some() => {
                let (_, name, constant) = scalar::record_referent(value_type).unwrap();
                let pointer = self.lower_place(place)?;
                let address = if place.projections.is_empty() {
                    pointer
                } else {
                    ProgramExpression::Subobject {
                        pointer: Box::new(pointer),
                        width: self.record_layout(name)?.size().bytes().ok_or(
                            "C++ subobject of a symbolic record is outside the supported slice",
                        )?,
                    }
                };
                Ok(
                    crate::kernel::program_expression::cast_with_pointee_qualifiers(
                        address,
                        ProgramType::Int32Pointer,
                        false,
                        constant,
                    ),
                )
            }
            CppExpression::AddressOf {
                place, value_type, ..
            } if !place.projections.is_empty() => {
                // Address formation checks storage, not a read of the field value.
                // The member is its own subobject (C++ [basic.compound]): the
                // pointer may not reach a sibling member at an adjacent address.
                let CppType::Pointer { pointee } = value_type else {
                    unreachable!("validated field address")
                };
                let member_type = Scalar::pointer_element(pointee, true)
                    .unwrap()
                    .kind
                    .kernel_type();
                Ok(crate::kernel::program_expression::checked_object_address(
                    crate::kernel::program_expression::typed_load(
                        ProgramExpression::Subobject {
                            pointer: Box::new(self.lower_place(place)?),
                            width: member_type.byte_width(),
                        },
                        member_type,
                    ),
                ))
            }
            CppExpression::AddressOf {
                place, value_type, ..
            } => match (&self.place(place)?.value_type, value_type) {
                (CppType::LvalueReference { pointee }, CppType::Pointer { pointee: result })
                    if Scalar::pointer_element(pointee, true).is_some()
                        && scalar::same_scalar_type(pointee, result) =>
                {
                    Ok(crate::kernel::program_expression::variable(
                        self.variable_name(place),
                    ))
                }
                (
                    CppType::Integer { .. } | CppType::Enumeration { .. },
                    CppType::Pointer { pointee },
                ) if Scalar::pointer_element(pointee, true).is_some() => {
                    Ok(ProgramExpression::AddressOf(Box::new(
                        crate::kernel::program_expression::variable(self.variable_name(place)),
                    )))
                }
                _ => Err("C++ address-of is outside integer reference lowering".into()),
            },
            CppExpression::ReferenceBinding {
                address,
                value_type,
                ..
            } => {
                let pointer = self.lower_expression(address)?;
                self.reference_binding_address(pointer, address, value_type)
            }
            CppExpression::Dereference {
                pointer,
                value_type,
                ..
            } if is_native_object_pointer(pointer.value_type()) => {
                let address = self.lower_expression(pointer)?;
                self.lower_typed_load(address, cpp_scalar_kernel_type(value_type)?)
            }
            CppExpression::Dereference { .. } => {
                Err("C++ dereference is outside mutable `int*` lowering".into())
            }
            CppExpression::MemberLoad {
                object,
                field,
                value_type,
                ..
            } => {
                let (pointer, field_type, pointee_constant) =
                    self.lower_member_pointer(object, field)?;
                if cpp_scalar_kernel_type(value_type)? != field_type {
                    return Err(format!(
                        "C++ member `{}` load type disagrees with its record field",
                        field.name
                    ));
                }
                self.lower_qualified_typed_load(pointer, field_type, pointee_constant)
            }
            CppExpression::PointerQualification { value, .. } => self.lower_expression(value),
            CppExpression::VoidPointerCast {
                value, value_type, ..
            } => Ok(erase_pointer_type(
                self.lower_expression(value)?,
                value_type,
            )),
            CppExpression::BytePointerCast { value, .. } => {
                Ok(crate::kernel::program_expression::cast(
                    self.lower_expression(value)?,
                    ProgramType::UInt8Pointer,
                ))
            }
            CppExpression::IntegralCast {
                value, value_type, ..
            }
            | CppExpression::EnumCast {
                value, value_type, ..
            } => {
                let source = Scalar::mutable_kind(value.value_type())
                    .ok_or_else(|| "unsupported C++ integral cast operand".to_string())?;
                let target = Scalar::mutable_kind(value_type)
                    .ok_or_else(|| "unsupported C++ integral cast result".to_string())?;
                Ok(scalar::convert(
                    self.lower_expression(value)?,
                    source,
                    target,
                ))
            }
            CppExpression::Binary {
                operator,
                left,
                right,
                value_type,
                ..
            } => {
                let left = self.lower_expression(left)?;
                let right = self.lower_expression(right)?;
                Ok(lower_binary_value(*operator, left, right, value_type))
            }
        }
    }

    fn reference_binding_address(
        &self,
        pointer: ProgramExpression,
        address: &CppExpression,
        value_type: &CppType,
    ) -> Result<ProgramExpression, String> {
        if matches!(address, CppExpression::AddressOf { .. }) {
            return Ok(pointer);
        }
        let (pointer, element) = if let Some((_, name, _)) = scalar::record_referent(value_type) {
            // The byte-array lvalue denotes the complete record footprint.
            // Checked address formation validates it without reading fields.
            let bytes = self
                .record_layout(name)?
                .size()
                .bytes()
                .ok_or("C++ byte view of a symbolic record is outside the supported slice")?;
            // The array lvalue checks the whole footprint without selecting
            // a new subobject. Keep the source pointer's designation/bounds.
            (pointer, ProgramType::UInt8Array(bytes))
        } else {
            (pointer, ProgramType::Int32)
        };
        let checked = crate::kernel::program_expression::checked_object_address(
            crate::kernel::program_expression::typed_load(pointer, element),
        );
        Ok(if matches!(element, ProgramType::UInt8Array(_)) {
            crate::kernel::program_expression::cast_with_pointee_qualifiers(
                checked,
                ProgramType::Int32Pointer,
                false,
                matches!(value_type, CppType::LvalueReference { pointee } if matches!(pointee.as_ref(), CppType::Record { is_const: true, .. })),
            )
        } else {
            checked
        })
    }

    fn record_layout(&self, name: &str) -> Result<AggregateLayout, String> {
        self.layouts
            .get(name)
            .map(crate::languages::interface::RecordLayout::to_kernel_aggregate_layout)
            .ok_or_else(|| format!("C++ lowering found no checked layout for `{name}`"))
    }

    fn lower_place(&self, place: &CppPlaceReference) -> Result<ProgramExpression, String> {
        let root = self.place(place)?;
        let (_, offset) = self
            .records
            .resolve_path(&root.value_type, &place.projections)?;
        Ok(crate::kernel::program_expression::pointer_offset_bytes(
            crate::kernel::program_expression::variable(self.variable_name(place)),
            offset,
        ))
    }

    fn lower_typed_load(
        &mut self,
        pointer: ProgramExpression,
        value_type: ProgramType,
    ) -> Result<ProgramExpression, String> {
        self.lower_qualified_typed_load(pointer, value_type, false)
    }

    fn lower_qualified_typed_load(
        &mut self,
        pointer: ProgramExpression,
        value_type: ProgramType,
        pointee_constant: bool,
    ) -> Result<ProgramExpression, String> {
        let occurrence = self.next_load_occurrence;
        self.next_load_occurrence = self
            .next_load_occurrence
            .checked_add(1)
            .ok_or_else(|| "C++ load occurrence capacity exceeded".to_string())?;
        Ok(
            crate::kernel::program_expression::qualified_typed_load_with_source(
                pointer,
                value_type,
                pointee_constant,
                None,
                Some(LoadSourceId {
                    owner: LoadSourceOwnerId {
                        source_unit: self.source_unit.into(),
                        function: self.function_name.into(),
                    },
                    occurrence,
                    reference_access: None,
                }),
            ),
        )
    }

    fn lower_member_pointer(
        &self,
        object: &CppPlaceReference,
        field: &CppFieldReference,
    ) -> Result<(ProgramExpression, ProgramType, bool), String> {
        let place = self.place(object)?;
        let (value_type, offset) = self.records.resolve_path(
            &place.value_type,
            object
                .projections
                .iter()
                .map(super::schema::CppProjection::as_ref)
                .chain(std::iter::once(super::schema::ProjectionRef::Field(field))),
        )?;
        Ok((
            crate::kernel::program_expression::pointer_offset_bytes(
                crate::kernel::program_expression::variable(self.variable_name(object)),
                offset,
            ),
            cpp_scalar_kernel_type(value_type)?,
            scalar::returns_constant_element(value_type),
        ))
    }

    /// The kernel name a call invokes: the function's, or, for a call
    /// through a function pointer, the variable that holds it.
    fn callee_name(&self, callee: &super::CppFunctionReference) -> Result<String, String> {
        if !callee.through_pointer {
            return Ok(self.names.require(&callee.declaration_id)?.to_owned());
        }
        let place = self
            .places
            .get(callee.declaration_id.as_str())
            .ok_or_else(|| {
                format!(
                    "C++ lowering found unknown function pointer `{}`",
                    callee.name
                )
            })?;
        if place.name != callee.name || !matches!(place.value_type, CppType::FunctionPointer { .. })
        {
            return Err(format!(
                "C++ call target `{}` is not a function pointer",
                callee.name
            ));
        }
        Ok(place.name.clone())
    }

    /// The kernel variable a place reference reads: the place's own name,
    /// or the carrier of a reference parameter.
    fn variable_name(&self, place: &CppPlaceReference) -> BindingName {
        if self.receiver == Some(place.declaration_id.as_str()) {
            RECEIVER_NAME.into()
        } else if self
            .reference_parameters
            .contains(place.declaration_id.as_str())
        {
            BindingName::reference_carrier(place.name.as_str())
        } else {
            place.name.clone().into()
        }
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
fn collect_declared_places<'a>(statements: &'a [CppStatement], places: &mut Vec<&'a CppPlace>) {
    for statement in statements {
        match statement {
            CppStatement::Declare { local, .. } => places.push(local),
            CppStatement::Scope { body, .. } => collect_declared_places(body, places),
            CppStatement::TryCatchInt32 {
                try_body,
                binding,
                handler,
                ..
            } => {
                collect_declared_places(try_body, places);
                places.push(binding);
                collect_declared_places(handler, places);
            }
            CppStatement::If {
                then_branch,
                else_branch,
                ..
            } => {
                collect_declared_places(then_branch, places);
                collect_declared_places(else_branch, places);
            }
            CppStatement::While { body, .. } => collect_declared_places(body, places),
            _ => {}
        }
    }
}

fn expression_contains_observer(expression: &CppExpression) -> bool {
    crate::instrumentation::record_deterministic_work(1);
    match expression {
        CppExpression::ObserverCall { .. } => true,
        CppExpression::LogicalNot { value, .. }
        | CppExpression::IntegralCast { value, .. }
        | CppExpression::EnumCast { value, .. }
        | CppExpression::PointerQualification { value, .. }
        | CppExpression::VoidPointerCast { value, .. }
        | CppExpression::BytePointerCast { value, .. }
        | CppExpression::ReferenceBinding { address: value, .. }
        | CppExpression::Dereference { pointer: value, .. } => expression_contains_observer(value),
        CppExpression::Binary { left, right, .. } => {
            expression_contains_observer(left) || expression_contains_observer(right)
        }
        _ => false,
    }
}

fn lower_binary_value(
    operator: CppBinaryOperator,
    left: ProgramExpression,
    right: ProgramExpression,
    value_type: &CppType,
) -> ProgramExpression {
    let expression = match operator {
        CppBinaryOperator::Add => crate::kernel::program_expression::add(left, right),
        CppBinaryOperator::Subtract => crate::kernel::program_expression::subtract(left, right),
        CppBinaryOperator::Multiply => crate::kernel::program_expression::multiply(left, right),
        CppBinaryOperator::Divide => crate::kernel::program_expression::divide(left, right),
        CppBinaryOperator::Remainder => crate::kernel::program_expression::remainder(left, right),
        CppBinaryOperator::Equal => crate::kernel::program_expression::equal(left, right),
        CppBinaryOperator::NotEqual => crate::kernel::program_expression::not_equal(left, right),
        CppBinaryOperator::LessThan => crate::kernel::program_expression::less_than(left, right),
        CppBinaryOperator::GreaterThan => {
            crate::kernel::program_expression::greater_than(left, right)
        }
        CppBinaryOperator::LessEqual => crate::kernel::program_expression::less_equal(left, right),
        CppBinaryOperator::GreaterEqual => {
            crate::kernel::program_expression::greater_equal(left, right)
        }
        CppBinaryOperator::LogicalAnd => crate::kernel::program_expression::and(left, right),
    };
    if is_mutable_bool(value_type) {
        crate::kernel::program_expression::cast(expression, ProgramType::Bool)
    } else {
        expression
    }
}

fn cpp_return_scalar_type(value_type: &CppType) -> Result<ProgramType, String> {
    if scalar::void_pointer(value_type).is_some() {
        return Ok(ProgramType::VoidPointer);
    }
    if scalar::record_pointee(value_type).is_some()
        || matches!(value_type, CppType::LvalueReference { .. })
            && scalar::record_referent(value_type).is_some()
    {
        return Ok(ProgramType::Int32Pointer);
    }
    if let CppType::Pointer { pointee } = value_type {
        return Scalar::pointer_element(pointee, true)
            .and_then(|scalar| scalar.kind.pointer_kernel_type())
            .ok_or_else(|| "unsupported native C++ pointer result".into());
    }
    if let Some(element) = scalar::reference_element(value_type) {
        return element_pointer_type(element);
    }
    Scalar::mutable_kind(value_type)
        .map(ScalarKind::kernel_type)
        .ok_or_else(|| "unsupported C++ scalar kernel type".into())
}

fn erase_pointer_type(expression: ProgramExpression, value_type: &CppType) -> ProgramExpression {
    ProgramExpression::Cast {
        expression: Box::new(expression),
        target_type: ProgramType::VoidPointer,
        integer_mode: crate::kernel::IntegerCastMode::PointerCoercion,
        pointee_struct: None,
        pointee_struct_size: None,
        pointee_volatile: false,
        pointee_constant: scalar::returns_constant_element(value_type),
        explicit_qualification: false,
    }
}

/// The pointer that carries a native reference to `element`.
fn element_pointer_type(element: Scalar) -> Result<ProgramType, String> {
    element
        .kind
        .pointer_kernel_type()
        .ok_or_else(|| "unsupported native C++ reference element".into())
}

fn cpp_scalar_kernel_type(value_type: &CppType) -> Result<ProgramType, String> {
    if let Some(kind) = Scalar::mutable_kind(value_type)
        .filter(|kind| kind.is_integer() || matches!(kind, ScalarKind::Parameter(_)))
    {
        Ok(kind.kernel_type())
    } else if is_native_object_pointer(value_type) || scalar::void_pointer(value_type).is_some() {
        cpp_return_scalar_type(value_type)
    } else if scalar::record_pointee(value_type).is_some() {
        Ok(ProgramType::Int32Pointer)
    } else {
        Err("unsupported C++ scalar kernel type".into())
    }
}

fn is_mutable_bool(value_type: &CppType) -> bool {
    Scalar::is(value_type, ScalarKind::Bool, false)
}
fn is_mutable_int64(value_type: &CppType) -> bool {
    Scalar::is(value_type, ScalarKind::Int64, false)
}
fn is_const_int64(value_type: &CppType) -> bool {
    Scalar::is(value_type, ScalarKind::Int64, true)
}

fn is_native_object_pointer(value_type: &CppType) -> bool {
    matches!(value_type, CppType::Pointer { pointee } if Scalar::pointer_element(pointee, true).is_some())
}

/// `call`, then the end of the prepared parameter objects it received.
fn end_prepared_arguments(call: ProgramStatement, prepared: Vec<BindingName>) -> ProgramStatement {
    if prepared.is_empty() {
        call
    } else {
        program_seq(
            call,
            program_end_automatic_lifetimes(prepared.into_iter().rev().collect()),
        )
    }
}
