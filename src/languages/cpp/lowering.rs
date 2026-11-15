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
    AggregateLayout, LoadSourceId, LoadSourceOwnerId, ProgramExpression, ProgramFunction,
    ProgramStatement, ProgramType, int32, program_allocate_aggregate_destination, program_assign,
    program_call, program_call_construct, program_copy_aggregate, program_declare,
    program_declare_aggregate, program_declare_initialized, program_declare_with_all_qualifiers,
    program_end_automatic_lifetimes, program_function, program_if, program_parameter,
    program_return, program_seq, program_skip, program_try_catch_int32,
    program_try_catch_int32_with_cleanup, program_typed_store,
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
    /// Proof-facing name for a resolved Clang declaration identity.
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

    /// Every selected function, lowered, in selection order.
    pub fn kernel_functions(&self) -> &[ProgramFunction] {
        &self.functions
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
    let paths = import
        .export()
        .functions
        .iter()
        .chain(&import.export().reachable_functions)
        .map(|function| {
            if function.path.is_empty() {
                return Err(format!(
                    "C++ artifact names `{}` without its C++ path; refresh it with `click import lock`",
                    function.name
                ));
            }
            Ok((
                function.declaration_id.as_str(),
                super::names::path_name(&function.path),
            ))
        })
        .collect::<Result<Vec<_>, String>>()?;
    let names = ResolvedNames::new(paths.iter().map(|(id, name)| (*id, name.as_str())))?;
    // Build immutable inventories once; every function borrows the same indexes.
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
    );
    let constants = import
        .export()
        .constants
        .iter()
        .map(|constant| {
            crate::instrumentation::record_deterministic_work(1);
            (constant.declaration_id.as_str(), constant)
        })
        .collect::<BTreeMap<_, _>>();
    let layouts = super::interface::prepare_layouts(import)?;
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
    let mut execution = super::interface::prepare(
        import,
        &functions,
        &reachable_functions,
        layouts,
        library_contracts,
        &polymorphism.coercions.into_inner(),
        &polymorphism.dispatches.into_inner(),
        &polymorphism.receiver_calls.into_inner(),
    )?;
    execution.library_models = library_models;
    // An overload's head at its shared path selects it by signature.
    for (id, path) in &paths {
        crate::instrumentation::record_deterministic_work(1);
        let name = names.require(id)?;
        if name != path {
            execution
                .overload_paths
                .insert(name.to_string(), path.clone());
        }
    }
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
    let reference_parameters = source
        .parameters
        .iter()
        .enumerate()
        .filter(|(index, parameter)| is_reference_parameter(*index, parameter))
        .map(|(_, parameter)| parameter.declaration_id.as_str())
        // A local of reference type is carried the same way: the pointer is
        // named for the address it holds, and the local's own name is the
        // referent a proof reads.
        .chain(
            places
                .values()
                .filter(|place| is_reference_local(place))
                .map(|place| place.declaration_id.as_str()),
        )
        .collect::<std::collections::BTreeSet<_>>();
    let parameters = source
        .parameters
        .iter()
        .enumerate()
        .map(|(index, parameter)| {
            if is_receiver(index, parameter) {
                let mut receiver = parameter.clone();
                receiver.name = RECEIVER_NAME.to_string();
                return lower_parameter(&receiver, layouts);
            }
            if !is_reference_parameter(index, parameter) {
                return lower_parameter(parameter, layouts);
            }
            let mut carrier = parameter.clone();
            carrier.name = reference_carrier_name(&parameter.name);
            lower_parameter(&carrier, layouts)
        })
        .collect::<Result<Vec<_>, String>>()?;
    let mut context = LoweringContext {
        receiver: source
            .parameters
            .first()
            .filter(|parameter| is_receiver(0, parameter))
            .map(|parameter| parameter.declaration_id.as_str()),
        reference_parameters,
        source_unit: import.logical_source(),
        function_name: names.require(&source.declaration_id)?,
        names,
        source_names: places.values().map(|place| place.name.as_str()).collect(),
        next_call_capture: 0,
        next_call_result: std::cell::Cell::new(0),
        places,
        records,
        constants,
        layouts,
        next_load_occurrence: 0,
        return_capture_name: return_capture_name(source),
        nested_capture_name: fresh_internal_name(source, "__click_cpp_nested_value"),
        unwind_exception_name: fresh_internal_name(source, "__click_cpp_unwind_exception"),
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
    let return_constant = scalar::returns_constant_element(&source.return_type);
    let mut function = program_function(
        return_type,
        names.require(&source.declaration_id)?.to_owned(),
        parameters,
        body,
    )
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

pub(super) use crate::languages::c::syntax::reference_carrier_name;

/// The name a sidecar gives a member function's receiver: the pointer
/// `this`, as in C++.
pub(super) const RECEIVER_NAME: &str = "this";

/// Whether a parameter is a member function's receiver. The exporter
/// delivers it first, as a reference named `self`.
pub(super) fn is_receiver(index: usize, parameter: &CppPlace) -> bool {
    index == 0 && parameter.name == "self"
}

/// Whether a declared local is a reference, which a proof names by its
/// referent as it names a reference parameter.
pub(super) fn is_reference_local(local: &CppPlace) -> bool {
    matches!(local.value_type, CppType::LvalueReference { .. })
}

/// Whether a parameter is a reference the sidecar names by its referent. A
/// receiver also arrives as a reference; it is the pointer `this`.
pub(super) fn is_reference_parameter(index: usize, parameter: &CppPlace) -> bool {
    matches!(parameter.value_type, CppType::LvalueReference { .. })
        && !is_receiver(index, parameter)
}

fn lower_parameter(
    parameter: &CppPlace,
    layouts: &BTreeMap<String, crate::languages::interface::RecordLayout>,
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
                parameter.name.clone(),
                ProgramType::UInt8Pointer,
                layout.to_kernel_aggregate_layout(),
            ))
        }
        CppType::Integer { .. } | CppType::Enumeration { .. } | CppType::Parameter { .. } => {
            Ok(program_parameter(
                parameter.name.clone(),
                cpp_scalar_kernel_type(&parameter.value_type)?,
            ))
        }
        CppType::Boolean {
            bits: 8,
            is_const: false,
        } => Ok(program_parameter(parameter.name.clone(), ProgramType::Bool)),
        CppType::LvalueReference { .. }
            if scalar::reference_element(&parameter.value_type).is_some() =>
        {
            let element = scalar::reference_element(&parameter.value_type).unwrap();
            Ok(
                program_parameter(parameter.name.clone(), element_pointer_type(element)?)
                    .with_pointee_constant(element.is_const),
            )
        }
        CppType::LvalueReference { pointee } if is_const_int64(pointee) => Ok(program_parameter(
            parameter.name.clone(),
            ProgramType::Int64Pointer,
        )
        .with_pointee_constant(true)),
        CppType::LvalueReference { pointee }
            if matches!(pointee.as_ref(), CppType::Record { .. }) =>
        {
            Ok(
                program_parameter(parameter.name.clone(), ProgramType::Int32Pointer)
                    .with_pointee_constant(matches!(
                        pointee.as_ref(),
                        CppType::Record { is_const: true, .. }
                    )),
            )
        }
        CppType::FunctionPointer { .. } => Ok(program_parameter(
            parameter.name.clone(),
            super::interface::function_pointer_signature(&parameter.value_type)?
                .pointer_type()
                .to_kernel_type(),
        )),
        pointer @ CppType::Pointer { .. } if scalar::record_pointee(pointer).is_some() => Ok(
            program_parameter(parameter.name.clone(), ProgramType::Int32Pointer),
        ),
        CppType::Pointer { pointee } if Scalar::pointer_element(pointee, false).is_some() => {
            Ok(program_parameter(
                parameter.name.clone(),
                Scalar::pointer_element(pointee, false)
                    .unwrap()
                    .kind
                    .pointer_kernel_type()
                    .unwrap(),
            ))
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
    /// named by [`reference_carrier_name`].
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
    return_capture_name: String,
    nested_capture_name: String,
    source_names: std::collections::BTreeSet<&'a str>,
    next_call_capture: u64,
    next_call_result: std::cell::Cell<u32>,
    unwind_exception_name: String,
    unwind_cleanups: bool,
    /// The packs the call being lowered needs, with their unpacks and the
    /// derived class's address: one for each reference argument that
    /// converts a derived class reference to a polymorphic base.
    pending_coercions: Vec<(String, String, ProgramExpression)>,
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
    coercions: std::cell::RefCell<BTreeSet<(String, String)>>,
    /// Every dispatch the program makes through a reference to an open
    /// class's method that overrides another, by the name of the function
    /// it calls, with the method's importer name.
    dispatches: std::cell::RefCell<BTreeMap<String, String>>,
    /// Each function's calls of methods on a receiver that may be an object
    /// of a derived class, by its importer name: the function called, and
    /// the reference parameter the receiver is, or `None` for `this`.
    receiver_calls: std::cell::RefCell<BTreeMap<String, Vec<(String, Option<String>)>>>,
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

impl LoweringContext<'_> {
    fn call_then_assign(
        &self,
        target: impl Into<String>,
        function: impl Into<String>,
        arguments: Vec<ProgramExpression>,
    ) -> ProgramStatement {
        let id = self.next_call_result.get();
        self.next_call_result
            .set(id.checked_add(1).expect("too many calls in one function"));
        let (call, value) = crate::kernel::program_call_value(id, function, arguments);
        program_seq(call, program_assign(target, value))
    }

    /// `call`, after the packs its arguments need and before their unpacks:
    /// the callee holds the base class's object the derived class's memory
    /// stands for, which the sidecar may declare.
    fn coerced(&mut self, call: ProgramStatement) -> ProgramStatement {
        let coercions = std::mem::take(&mut self.pending_coercions);
        let mut statement = call;
        for (pack, unpack, address) in coercions.iter().rev() {
            crate::instrumentation::record_deterministic_work(1);
            statement = program_seq(
                program_call(pack.clone(), vec![address.clone()]),
                program_seq(
                    statement,
                    program_call(unpack.clone(), vec![address.clone()]),
                ),
            );
        }
        statement
    }

    /// Records the pack a reference argument needs when its place ends in
    /// base projections to a polymorphic class.
    fn note_object_coercion(&mut self, place: &super::CppPlaceReference) -> Result<(), String> {
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
        let (pack, unpack) = if base.is_const {
            (
                crate::languages::cpp::names::object_const_pack_name(&derived, &base.base_name),
                crate::languages::cpp::names::object_const_unpack_name(&derived, &base.base_name),
            )
        } else {
            (
                crate::languages::cpp::names::object_pack_name(&derived, &base.base_name),
                crate::languages::cpp::names::object_unpack_name(&derived, &base.base_name),
            )
        };
        self.pending_coercions.push((pack, unpack, address));
        self.polymorphism
            .coercions
            .borrow_mut()
            .insert((derived, base.base_name.clone()));
        Ok(())
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
    /// whichever override the object's class selects, which the function
    /// named for that dispatch stands for.
    fn call_name(
        &mut self,
        callee: &super::CppFunctionReference,
        arguments: &[CppCallArgument],
    ) -> Result<String, String> {
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
            return Ok(name);
        };
        for (index, (argument, parameter)) in arguments.iter().zip(&function.parameters).enumerate()
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
            if is_receiver(index, parameter)
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
            let (pack, unpack) = if *is_const {
                (
                    crate::languages::cpp::names::object_const_pack_name(class, class),
                    crate::languages::cpp::names::object_const_unpack_name(class, class),
                )
            } else {
                (
                    crate::languages::cpp::names::object_pack_name(class, class),
                    crate::languages::cpp::names::object_unpack_name(class, class),
                )
            };
            self.pending_coercions.push((pack, unpack, address));
            self.polymorphism
                .coercions
                .borrow_mut()
                .insert((class.clone(), class.clone()));
        }
        let receiver = function
            .parameters
            .first()
            .filter(|parameter| is_receiver(0, parameter));
        let Some(CppType::LvalueReference { pointee }) =
            receiver.map(|parameter| &parameter.value_type)
        else {
            return Ok(name);
        };
        let CppType::Record { name: class, .. } = pointee.as_ref() else {
            return Ok(name);
        };
        let Some(CppCallArgument::Reference { place }) = arguments.first() else {
            return Ok(name);
        };
        let exact = self.is_exact(place)?;
        let dispatches = function.virtual_method.as_ref().is_some_and(|method| {
            !callee.qualified
                && !method.overrides.is_empty()
                && self.polymorphism.open.contains(class.as_str())
        }) && !exact;
        if !exact && self.polymorphism.derived.contains(class.as_str()) {
            let id = place.declaration_id.as_str();
            let holder = (self.receiver != Some(id)).then(|| place.name.clone());
            let target = if dispatches {
                crate::languages::cpp::names::object_dispatch_name(
                    class,
                    function
                        .path
                        .last()
                        .map_or(callee.name.as_str(), String::as_str),
                )
            } else {
                name.clone()
            };
            self.polymorphism
                .receiver_calls
                .borrow_mut()
                .entry(self.function_name.to_string())
                .or_default()
                .push((target, holder));
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
            return Ok(name);
        }
        let method_name = function
            .path
            .last()
            .map_or(callee.name.as_str(), String::as_str);
        let dispatch = crate::languages::cpp::names::object_dispatch_name(class, method_name);
        self.polymorphism
            .dispatches
            .borrow_mut()
            .insert(dispatch.clone(), name);
        Ok(dispatch)
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
                    let carrier = reference_carrier_name(&local.name);
                    let element = scalar::reference_element(&local.value_type)
                        .ok_or("unsupported C++ reference local")?;
                    Ok(program_seq(
                        program_declare_with_all_qualifiers(
                            carrier.clone(),
                            element_pointer_type(element)?,
                            false,
                            false,
                            false,
                            element.is_const,
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
                            false,
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
                        reference_carrier_name(&local.name)
                    } else {
                        local.name.clone()
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
                        .then_some(name.as_str()),
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
                            false,
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
                    let (prefix, actual) = self.normalize_arguments(arguments)?;
                    Ok(evaluate_then(
                        prefix,
                        program_seq(
                            program_allocate_aggregate_destination(local.name.clone(), layout),
                            self.coerced(program_call_construct(
                                local.name.clone(),
                                self.callee_name(callee)?,
                                actual,
                            )),
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
                                field.offset_bytes,
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
                // The allocation comes first and each field's value after it,
                // as C++17 sequences a new-expression.
                let object = self.fresh_call_capture()?;
                let mut result = program_seq(
                    program_declare(object.clone(), ProgramType::Int32Pointer),
                    ProgramStatement::HeapAllocate {
                        target: object.clone(),
                        bytes: crate::kernel::program_expression::int32_literal(source.size_bytes),
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
                        field.offset_bytes,
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
                let (pointer, value_type) = self.lower_member_pointer(object, field)?;
                let evaluation = self.normalize_scalar(ScalarInput::Value(value))?;
                Ok(evaluate_then(
                    evaluation.prefix,
                    program_typed_store(pointer, evaluation.value, value_type),
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
            | CppStatement::ReturnCall { .. }
            | CppStatement::Throw { .. }
            | CppStatement::TryCatchInt32 { .. }
            | CppStatement::Scope { .. }
            | CppStatement::If { .. }
            | CppStatement::While { .. } => {
                Err("C++ control flow requires lifetime-aware lowering".into())
            }
            CppStatement::Call {
                callee, arguments, ..
            } => {
                let target = self.call_name(callee, arguments)?;
                let (prefix, arguments) = self.normalize_arguments(arguments)?;
                Ok(evaluate_then(
                    prefix,
                    self.coerced(program_call(target, arguments)),
                ))
            }
            CppStatement::CallStore {
                callee,
                arguments,
                value_type,
                value,
                ..
            } => {
                let element = scalar::reference_element(value_type)
                    .ok_or("unsupported C++ call store referent")?;
                let element_type = element.kind.kernel_type();
                // The right operand is read first; the call then yields the
                // referent's address.
                let stored = self.fresh_call_capture()?;
                let read = program_seq(
                    program_declare(stored.clone(), element_type),
                    program_assign(stored.clone(), self.lower_expression(value)?),
                );
                let target = self.call_name(callee, arguments)?;
                let (prefix, arguments) = self.normalize_arguments(arguments)?;
                let address = self.fresh_call_capture()?;
                Ok(program_seq(
                    read,
                    evaluate_then(
                        prefix,
                        program_seq(
                            program_seq(
                                program_declare(address.clone(), element_pointer_type(element)?),
                                self.coerced(self.call_then_assign(
                                    address.clone(),
                                    target,
                                    arguments,
                                )),
                            ),
                            program_typed_store(
                                crate::kernel::program_expression::variable(address),
                                crate::kernel::program_expression::variable(stored),
                                element_type,
                            ),
                        ),
                    ),
                ))
            }
        }
    }

    /// Capture the result before destruction. A throwing return call takes the
    /// same cleanup chain on its exceptional edge and never produces a return.
    fn lower_captured_return(
        &mut self,
        mut evaluation: ProgramStatement,
        value_type: ProgramType,
        cleanups: &[&CppCleanup],
        unwind_cleanups: &[&CppCleanup],
        can_throw: bool,
    ) -> Result<ProgramStatement, String> {
        let capture = self.return_capture_name.clone();
        if can_throw && self.unwind_cleanups && !unwind_cleanups.is_empty() {
            let binding = self.unwind_exception_name.clone();
            let mut handler = program_skip();
            for cleanup in unwind_cleanups {
                handler = program_seq(handler, self.lower_cleanup(cleanup)?);
            }
            handler = program_seq(
                handler,
                ProgramStatement::Throw(crate::kernel::program_expression::variable(
                    binding.clone(),
                )),
            );
            evaluation = program_try_catch_int32_with_cleanup(evaluation, binding, handler, true);
        }
        let mut result = program_seq(program_declare(capture.clone(), value_type), evaluation);
        for cleanup in cleanups {
            result = program_seq(result, self.lower_cleanup(cleanup)?);
        }
        Ok(program_seq(
            result,
            program_return(crate::kernel::program_expression::variable(capture)),
        ))
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
                let (prefix, actual) = self.normalize_arguments(arguments)?;
                let temporary = self.fresh_aggregate_capture()?;
                // The RHS is a separate object: the live LHS may be read by
                // the factory and cannot serve as unwritten construction storage.
                Ok(evaluate_then(
                    prefix,
                    program_seq(
                        program_allocate_aggregate_destination(temporary.clone(), layout.clone()),
                        program_seq(
                            self.coerced(program_call_construct(
                                temporary.clone(),
                                self.callee_name(callee)?,
                                actual,
                            )),
                            program_seq(
                                program_copy_aggregate(
                                    self.lower_place(target)?,
                                    crate::kernel::program_expression::variable(temporary.clone()),
                                    layout,
                                ),
                                program_end_automatic_lifetimes(vec![temporary]),
                            ),
                        ),
                    ),
                ))
            }
            CppStatement::ReturnConstruct {
                callee, arguments, ..
            } => {
                let (prefix, arguments) = self.normalize_arguments(arguments)?;
                let mut actual = vec![crate::kernel::program_expression::cast(
                    crate::kernel::program_expression::variable(
                        crate::kernel::C_CONTRACT_RESULT_NAME,
                    ),
                    ProgramType::Int32Pointer,
                )];
                actual.extend(arguments);
                Ok(evaluate_then(
                    prefix,
                    program_seq(
                        self.coerced(program_call(self.callee_name(callee)?, actual)),
                        program_return(crate::kernel::program_expression::variable(
                            crate::kernel::C_CONTRACT_RESULT_NAME,
                        )),
                    ),
                ))
            }
            CppStatement::ReturnAggregateCall {
                callee, arguments, ..
            } => {
                let (prefix, arguments) = self.normalize_arguments(arguments)?;
                Ok(evaluate_then(
                    prefix,
                    program_seq(
                        self.coerced(program_call_construct(
                            crate::kernel::C_CONTRACT_RESULT_NAME,
                            self.callee_name(callee)?,
                            arguments,
                        )),
                        program_return(crate::kernel::program_expression::variable(
                            crate::kernel::C_CONTRACT_RESULT_NAME,
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
                let capture = self.return_capture_name.clone();
                let mut result = program_seq(
                    program_declare_aggregate(capture.clone(), layout.clone()),
                    program_copy_aggregate(
                        crate::kernel::program_expression::variable(capture.clone()),
                        self.lower_place(source)?,
                        layout,
                    ),
                );
                for cleanup in state.exit(0) {
                    result = program_seq(result, self.lower_cleanup(cleanup)?);
                }
                Ok(program_seq(
                    result,
                    program_return(crate::kernel::program_expression::variable(capture)),
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

    fn lower_throwing_statement<'p>(
        &mut self,
        statement: ProgramStatement,
        mut cleanups: impl Iterator<Item = &'p CppCleanup>,
    ) -> Result<ProgramStatement, String> {
        let Some(first) = cleanups.next() else {
            return Ok(statement);
        };
        let binding = self.unwind_exception_name.clone();
        let mut handler = program_seq(program_skip(), self.lower_cleanup(first)?);
        for cleanup in cleanups {
            handler = program_seq(handler, self.lower_cleanup(cleanup)?);
        }
        handler = program_seq(
            handler,
            ProgramStatement::Throw(crate::kernel::program_expression::variable(binding.clone())),
        );
        Ok(program_try_catch_int32_with_cleanup(
            statement, binding, handler, true,
        ))
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
        destination: Option<&str>,
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
                let target = self.call_name(callee, arguments)?;
                let (prefix, arguments) = self.normalize_arguments(arguments)?;
                // A converted result always has a callee-typed temporary.
                let capture = match destination.filter(|_| conversions.is_empty()) {
                    Some(name) => name.to_owned(),
                    None => self.fresh_call_capture()?,
                };
                let capture_type = cpp_return_scalar_type(value_type)?;
                let mut value = crate::kernel::program_expression::variable(capture.clone());
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
                    prefix: evaluate_then(
                        prefix,
                        program_seq(
                            program_declare_with_all_qualifiers(
                                capture.clone(),
                                capture_type,
                                false,
                                false,
                                false,
                                scalar::returns_constant_element(value_type),
                            ),
                            self.coerced(self.call_then_assign(capture.clone(), target, arguments)),
                        ),
                    ),
                    value,
                    value_type: result_type,
                    may_throw: true,
                })
            }
        }
    }

    fn normalize_arguments(
        &mut self,
        arguments: &[CppCallArgument],
    ) -> Result<(ProgramStatement, Vec<ProgramExpression>), String> {
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
                    let capture = self.fresh_call_capture()?;
                    let expression = self.lower_expression(value)?;
                    evaluation = evaluate_then(
                        evaluation,
                        program_seq(
                            program_declare(
                                capture.clone(),
                                cpp_return_scalar_type(value.value_type())?,
                            ),
                            program_assign(capture.clone(), expression),
                        ),
                    );
                    Some(crate::kernel::program_expression::variable(capture))
                } else {
                    None
                }
            } else {
                None
            };
            retained_states.push(retained_state);
        }
        let mut lowered = Vec::with_capacity(arguments.len());
        for (argument, retained_state) in arguments.iter().zip(retained_states) {
            crate::instrumentation::record_deterministic_work(1);
            if let Some(retained_state) = retained_state {
                lowered.push(retained_state);
            } else if let CppCallArgument::Value {
                value:
                    CppExpression::ClosureInstance {
                        function,
                        captures,
                        value_type,
                        ..
                    },
            } = argument
            {
                // A lambda made for a `std::function` argument is the value
                // its instance function returns for the captured values.
                let capture = self.fresh_call_capture()?;
                let mut values = Vec::with_capacity(captures.len());
                for value in captures {
                    values.push(self.lower_expression(value)?);
                }
                let closure = self.names.require(&function.declaration_id)?;
                evaluation = evaluate_then(
                    evaluation,
                    program_seq(
                        program_declare(
                            capture.clone(),
                            super::interface::function_pointer_signature(value_type)?
                                .pointer_type()
                                .to_kernel_type(),
                        ),
                        self.call_then_assign(
                            capture.clone(),
                            crate::languages::rust::names::closure_instance_name(closure),
                            values,
                        ),
                    ),
                );
                lowered.push(crate::kernel::program_expression::variable(capture));
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
                lowered.push(self.lower_call_argument(argument)?);
            }
        }
        Ok((evaluation, lowered))
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
        let capture = self.return_capture_name.clone();
        self.lower_captured_return(
            evaluate_then(evaluation.prefix, program_assign(capture, evaluation.value)),
            evaluation.value_type,
            cleanups,
            unwind_cleanups,
            evaluation.may_throw,
        )
    }

    fn normalize_expression(
        &mut self,
        expression: &CppExpression,
    ) -> Result<ScalarEvaluation, String> {
        let value_type = if scalar::record_pointee(expression.value_type()).is_some() {
            ProgramType::Int32Pointer
        } else if let CppType::Pointer { pointee } = expression.value_type() {
            Scalar::pointer_element(pointee, true)
                .and_then(|scalar| scalar.kind.pointer_kernel_type())
                .ok_or("unsupported native pointer expression")?
        } else {
            cpp_return_scalar_type(expression.value_type())?
        };
        let (prefix, value, may_throw) = match expression {
            CppExpression::ObserverCall {
                callee,
                arguments,
                value_type,
                ..
            } => {
                if self.unwind_cleanups {
                    return Err("C++ expression observers currently require the normal-only exception profile".into());
                }
                return self.normalize_scalar(ScalarInput::Call {
                    callee,
                    arguments,
                    value_type,
                    conversions: &[],
                });
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
            CppExpression::ReferenceBinding { address, .. } => {
                let input = self.normalize_expression(address)?;
                let value = if matches!(address.as_ref(), CppExpression::AddressOf { .. }) {
                    input.value
                } else {
                    crate::kernel::program_expression::checked_object_address(
                        crate::kernel::program_expression::typed_load(
                            input.value,
                            ProgramType::Int32,
                        ),
                    )
                };
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
                    let capture = self.fresh_call_capture()?;
                    let prefix = evaluate_then(
                        lhs.prefix,
                        program_seq(
                            program_declare(capture.clone(), ProgramType::Bool),
                            program_if(
                                lhs.value,
                                evaluate_then(
                                    rhs.prefix,
                                    program_assign(capture.clone(), rhs.value),
                                ),
                                program_assign(
                                    capture.clone(),
                                    crate::kernel::program_expression::cast(
                                        ProgramExpression::Value(int32(0)),
                                        ProgramType::Bool,
                                    ),
                                ),
                            ),
                        ),
                    );
                    return Ok(ScalarEvaluation {
                        prefix,
                        value: crate::kernel::program_expression::variable(capture),
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

    fn fresh_call_capture(&mut self) -> Result<String, String> {
        self.fresh_capture(self.nested_capture_name.clone())
    }

    fn fresh_aggregate_capture(&mut self) -> Result<String, String> {
        // Materialized objects have addressable storage. Keep their names
        // separate from scalar call captures: addressability is summarized
        // across functions by name, so an aggregate temporary in one function
        // must not obscure a scalar capture's nonescaping storage in another.
        self.fresh_capture(format!("{}_aggregate", self.nested_capture_name))
    }

    fn fresh_capture(&mut self, prefix: String) -> Result<String, String> {
        let mut capture = format!("{prefix}_{}", self.next_call_capture);
        self.next_call_capture = self
            .next_call_capture
            .checked_add(1)
            .ok_or("C++ nested call capture counter overflow")?;
        loop {
            crate::instrumentation::record_deterministic_work(1);
            if !self.source_names.contains(capture.as_str()) {
                break;
            }
            capture.push('_');
        }
        Ok(capture)
    }

    fn lower_call_arguments(
        &mut self,
        arguments: &[CppCallArgument],
    ) -> Result<Vec<ProgramExpression>, String> {
        arguments
            .iter()
            .map(|argument| self.lower_call_argument(argument))
            .collect()
    }

    fn lower_cleanup(&self, cleanup: &CppCleanup) -> Result<ProgramStatement, String> {
        let CppCleanup::Destructor { object, callee, .. } = cleanup;
        Ok(program_call(
            self.callee_name(callee)?,
            vec![crate::kernel::program_expression::cast(
                self.lower_place(object)?,
                ProgramType::Int32Pointer,
            )],
        ))
    }

    fn lower_call_argument(
        &mut self,
        argument: &CppCallArgument,
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
                    self.note_object_coercion(place)?;
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
            CppCallArgument::Call { .. } => {
                Err("nested C++ call bypassed scalar evaluation normalization".into())
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
                ) if Scalar::pointer_element(pointee, false).is_some()
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
            CppExpression::ReferenceBinding { address, .. } => {
                let pointer = self.lower_expression(address)?;
                if matches!(address.as_ref(), CppExpression::AddressOf { .. }) {
                    // An existing reference parameter already denotes its referent.
                    Ok(pointer)
                } else {
                    Ok(crate::kernel::program_expression::checked_object_address(
                        crate::kernel::program_expression::typed_load(pointer, ProgramType::Int32),
                    ))
                }
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
                let (pointer, field_type) = self.lower_member_pointer(object, field)?;
                if cpp_scalar_kernel_type(value_type)? != field_type {
                    return Err(format!(
                        "C++ member `{}` load type disagrees with its record field",
                        field.name
                    ));
                }
                self.lower_typed_load(pointer, field_type)
            }
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
        let occurrence = self.next_load_occurrence;
        self.next_load_occurrence = self
            .next_load_occurrence
            .checked_add(1)
            .ok_or_else(|| "C++ load occurrence capacity exceeded".to_string())?;
        Ok(crate::kernel::program_expression::typed_load_with_source(
            pointer,
            value_type,
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

    fn lower_member_pointer(
        &self,
        object: &CppPlaceReference,
        field: &CppFieldReference,
    ) -> Result<(ProgramExpression, ProgramType), String> {
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
    fn variable_name(&self, place: &CppPlaceReference) -> String {
        if self.receiver == Some(place.declaration_id.as_str()) {
            RECEIVER_NAME.to_string()
        } else if self
            .reference_parameters
            .contains(place.declaration_id.as_str())
        {
            reference_carrier_name(&place.name)
        } else {
            place.name.clone()
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
fn return_capture_name(function: &CppFunction) -> String {
    fresh_internal_name(function, "__click_cpp_return_value")
}

fn fresh_internal_name(function: &CppFunction, base: &str) -> String {
    let mut declared_places = Vec::new();
    collect_declared_places(&function.body, &mut declared_places);
    let names = function
        .parameters
        .iter()
        .chain(declared_places)
        .map(|place| place.name.as_str())
        .collect::<std::collections::BTreeSet<_>>();
    if !names.contains(base) {
        return base.to_string();
    }
    for suffix in 1u64.. {
        let candidate = format!("{base}_{suffix}");
        if !names.contains(candidate.as_str()) {
            return candidate;
        }
    }
    unreachable!("an unbounded suffix space contains an unused internal name")
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
    if scalar::record_pointee(value_type).is_some() {
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
    } else if is_native_object_pointer(value_type) {
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
    matches!(value_type, CppType::Pointer { pointee } if Scalar::pointer_element(pointee, false).is_some())
}
