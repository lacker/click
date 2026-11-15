//! A declared exclusive resource assertion without an owned occurrence.
//!
//! A description retains the resource family, evaluated parameters, and field
//! schema. It contains no instance identity, observed field values, or proof
//! of ownership. Consumers must check an owned instance separately.

use super::{
    AlgebraicValue, PureFactContext, ResourceArguments, ResourceFieldSchema, ResourceInstance,
    Variable,
};
use std::sync::Arc;

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct ResourceDescription(Arc<ResourceDescriptionData>);

#[derive(Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
struct ResourceDescriptionData {
    family: String,
    /// Full family arity for R(anchor, _, ...); only the anchor is captured.
    population_arity: Option<usize>,
    arguments: ResourceArguments,
    schema: ResourceFieldSchema,
    resource_arguments: Arc<[ResourceReference]>,
}

/// An observation-free reference to a particular resource. Copying a reference
/// does not copy ownership and cannot recover the referenced instance's fields.
/// Unlike a description, the reference distinguishes different occurrences of
/// the same assertion.
#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct ResourceReference {
    identity: Variable,
    description: ResourceDescription,
}

impl ResourceReference {
    pub fn from_instance(instance: &ResourceInstance) -> Self {
        Self {
            identity: instance.identity(),
            description: ResourceDescription::from_instance(instance),
        }
    }

    pub fn identity(&self) -> Variable {
        self.identity
    }

    pub fn description(&self) -> &ResourceDescription {
        &self.description
    }

    /// Transform captured value arguments while preserving reference identities
    /// and schemas. Shared description nodes are transformed once per argument
    /// list; this visits no observed model fields and grants no custody.
    pub(in crate::kernel) fn map_captured_values(
        references: &[Self],
        mut map: impl FnMut(&AlgebraicValue) -> AlgebraicValue,
    ) -> Arc<[Self]> {
        let mut mapped = std::collections::BTreeMap::<usize, ResourceDescription>::new();
        let mut pending = references
            .iter()
            .rev()
            .map(|reference| (&reference.description, false))
            .collect::<Vec<_>>();
        while let Some((description, expanded)) = pending.pop() {
            let key = Arc::as_ptr(&description.0) as usize;
            if mapped.contains_key(&key) {
                continue;
            }
            if !expanded {
                pending.push((description, true));
                pending.extend(
                    description
                        .resource_arguments()
                        .iter()
                        .rev()
                        .map(|reference| (&reference.description, false)),
                );
                continue;
            }
            let arguments = description.arguments().iter().map(&mut map).collect();
            let resource_arguments = description
                .resource_arguments()
                .iter()
                .map(|reference| Self {
                    identity: reference.identity,
                    description: mapped[&(Arc::as_ptr(&reference.description.0) as usize)].clone(),
                })
                .collect::<Vec<_>>()
                .into();
            mapped.insert(
                key,
                ResourceDescription(Arc::new(ResourceDescriptionData {
                    family: description.family().into(),
                    population_arity: description.population_arity(),
                    arguments,
                    schema: description.schema().clone(),
                    resource_arguments,
                })),
            );
        }
        references
            .iter()
            .map(|reference| Self {
                identity: reference.identity,
                description: mapped[&(Arc::as_ptr(&reference.description.0) as usize)].clone(),
            })
            .collect::<Vec<_>>()
            .into()
    }

    /// Visit captured values, including nested references, once per shared
    /// description. Occurrence identities and model observations are not values.
    pub(in crate::kernel) fn visit_captured_values(
        references: &[Self],
        mut visit: impl FnMut(&AlgebraicValue),
    ) {
        let mut seen = std::collections::BTreeSet::new();
        let mut pending = references.iter().collect::<Vec<_>>();
        while let Some(reference) = pending.pop() {
            let description = &reference.description;
            if !seen.insert(Arc::as_ptr(&description.0) as usize) {
                continue;
            }
            for argument in description.arguments() {
                visit(argument);
            }
            pending.extend(description.resource_arguments());
        }
    }

    pub fn matches_instance(
        &self,
        instance: &ResourceInstance,
        assumptions: &PureFactContext,
    ) -> bool {
        self.identity == instance.identity()
            && self.description.matches_instance(instance, assumptions)
    }
}

impl ResourceDescription {
    /// A resource type has no owned occurrence or observed field values.
    pub fn new(family: String, arguments: ResourceArguments, schema: ResourceFieldSchema) -> Self {
        Self(Arc::new(ResourceDescriptionData {
            family,
            population_arity: None,
            arguments,
            schema,
            resource_arguments: Arc::from([]),
        }))
    }

    pub(crate) fn map_values(&self, map: impl FnMut(&AlgebraicValue) -> AlgebraicValue) -> Self {
        let reference = ResourceReference {
            identity: Variable(0),
            description: self.clone(),
        };
        ResourceReference::map_captured_values(&[reference], map)[0]
            .description
            .clone()
    }

    pub(crate) fn visit_values(&self, visit: impl FnMut(&AlgebraicValue)) {
        let reference = ResourceReference {
            identity: Variable(0),
            description: self.clone(),
        };
        ResourceReference::visit_captured_values(&[reference], visit);
    }

    /// Describe a checked exclusive instance without retaining its binder or
    /// the values observed in its fields.
    pub fn from_instance(instance: &ResourceInstance) -> Self {
        Self(Arc::new(ResourceDescriptionData {
            family: instance.name.clone(),
            population_arity: None,
            arguments: instance.arguments.clone(),
            schema: instance.schema.clone(),
            resource_arguments: instance.resource_arguments.clone(),
        }))
    }

    pub fn family(&self) -> &str {
        &self.0.family
    }

    /// A population pattern grants no ownership of any particular member.
    pub fn with_population_arity(self, arity: usize) -> Result<Self, &'static str> {
        if arity < 2
            || self.arguments().len() != 1
            || !matches!(
                self.arguments()[0],
                AlgebraicValue::Program(super::ProgramValue::Pointer(_))
            )
            || !self.resource_arguments().is_empty()
        {
            return Err("population authority supports R(anchor, _, ...) scopes");
        }
        Ok(Self(Arc::new(ResourceDescriptionData {
            family: self.0.family.clone(),
            arguments: self.0.arguments.clone(),
            schema: self.0.schema.clone(),
            resource_arguments: self.0.resource_arguments.clone(),
            population_arity: Some(arity),
        })))
    }

    pub fn population_arity(&self) -> Option<usize> {
        self.0.population_arity
    }

    pub fn arguments(&self) -> &[AlgebraicValue] {
        &self.0.arguments
    }

    pub fn schema(&self) -> &ResourceFieldSchema {
        &self.0.schema
    }

    pub fn resource_arguments(&self) -> &[ResourceReference] {
        &self.0.resource_arguments
    }

    /// Check the full description without requiring an earlier occurrence or
    /// earlier observations. Argument equality uses the same checked relation
    /// as ordinary resource contracts. This supplies no ownership evidence.
    pub fn matches_instance(
        &self,
        instance: &ResourceInstance,
        assumptions: &PureFactContext,
    ) -> bool {
        self.population_arity().is_none()
            && self.family() == instance.name()
            && self.schema() == instance.schema()
            && self.resource_arguments() == instance.resource_arguments()
            && self.arguments().len() == instance.arguments().len()
            && self
                .arguments()
                .iter()
                .zip(instance.arguments())
                .all(|(left, right)| {
                    left == right
                        || super::resource_arguments_proven_equal(left, right, assumptions)
                })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::{ProgramType, ResourceFieldType, Variable, int32};
    use std::collections::BTreeSet;
    use std::hash::{Hash, Hasher};

    fn instance(identity: u64, family: &str, argument: u32, observed: u32) -> ResourceInstance {
        ResourceInstance::new(
            Variable(identity),
            family.into(),
            vec![int32(argument).into()].into(),
            ResourceFieldSchema::new(vec![(
                "value".into(),
                ResourceFieldType::Program(ProgramType::Int32),
            )])
            .unwrap(),
            vec![int32(observed).into()].into(),
        )
        .unwrap()
    }

    fn hash(description: &ResourceDescription) -> u64 {
        let mut hasher = std::collections::hash_map::DefaultHasher::new();
        description.hash(&mut hasher);
        hasher.finish()
    }

    #[test]
    fn captured_value_traversal_visits_shared_descriptions_once() {
        for size in [16, 64, 256, 1024] {
            let reference = ResourceReference::from_instance(&instance(1, "cell", 7, 9));
            let references = vec![reference; size];
            let mut visited = 0;
            ResourceReference::visit_captured_values(&references, |_| visited += 1);
            assert_eq!(visited, 1);
            let mut mapped = 0;
            let result = ResourceReference::map_captured_values(&references, |value| {
                mapped += 1;
                value.clone()
            });
            assert_eq!(mapped, 1);
            assert_eq!(result.as_ref(), references.as_slice());
        }
    }

    #[test]
    fn description_has_exact_family_arguments_and_schema_without_observations() {
        let first = instance(1, "state", 7, 10);
        let later = instance(2, "state", 7, 20);
        let description = ResourceDescription::from_instance(&first);
        assert_eq!(description, ResourceDescription::from_instance(&later));
        assert_eq!(
            hash(&description),
            hash(&ResourceDescription::from_instance(&later))
        );
        assert_eq!(description.family(), "state");
        assert_eq!(description.arguments(), first.arguments());
        assert_eq!(description.schema(), first.schema());
        assert_ne!(
            description,
            ResourceDescription::from_instance(&instance(3, "other", 7, 10))
        );
        assert_ne!(
            description,
            ResourceDescription::from_instance(&instance(3, "state", 8, 10))
        );
        let mut different_schema = later;
        different_schema.schema = ResourceFieldSchema::new(vec![(
            "other".into(),
            ResourceFieldType::Program(ProgramType::Int32),
        )])
        .unwrap();
        assert_ne!(
            description,
            ResourceDescription::from_instance(&different_schema)
        );
        assert_eq!(
            BTreeSet::from([
                description.clone(),
                ResourceDescription::from_instance(&different_schema)
            ])
            .len(),
            2
        );
    }

    #[test]
    fn resource_reference_keeps_identity_but_forgets_observed_fields() {
        let before = instance(1, "cell", 7, 10);
        let after = instance(1, "cell", 7, 20);
        let other = instance(2, "cell", 7, 10);
        let reference = ResourceReference::from_instance(&before);
        assert_eq!(reference, ResourceReference::from_instance(&after));
        assert_ne!(reference, ResourceReference::from_instance(&other));
        assert!(reference.matches_instance(&after, &PureFactContext::new()));
        assert!(!reference.matches_instance(&other, &PureFactContext::new()));
    }

    #[test]
    fn contract_identity_includes_resource_arguments() {
        use crate::kernel::{
            ResourceAccessMode, ResourceFamily, ResourceSpec, ResourceStateSource,
            ResourceTransferRole,
        };
        let spec = ResourceSpec::declared(
            ResourceFamily::Composite,
            ResourceAccessMode::Own,
            "wrapper".into(),
            vec![],
            vec![],
            ResourceTransferRole::Borrow,
            ResourceStateSource::Current,
        )
        .unwrap();
        let first = spec.clone().with_resource_arguments(vec![Variable(1)]);
        let second = spec.with_resource_arguments(vec![Variable(2)]);
        assert!(
            ResourceSpec::quantified(
                crate::kernel::ProgramExpression::Value(int32(1)),
                first.clone(),
                ResourceTransferRole::Borrow,
                ResourceStateSource::Current,
            )
            .is_err()
        );
        assert_ne!(first, second);
        assert_eq!(BTreeSet::from([first.clone(), second.clone()]).len(), 2);
        assert_eq!(std::collections::HashSet::from([first, second]).len(), 2);
    }

    #[test]
    fn containing_a_reference_does_not_own_its_target() {
        use crate::kernel::{Resource, ResourceContext, ResourceFact};
        let target = instance(1, "cell", 7, 10);
        let wrapper = instance(2, "wrapper", 7, 0)
            .with_resource_arguments(vec![ResourceReference::from_instance(&target)]);
        let context = ResourceContext::new()
            .try_compose_with_fact(
                ResourceFact::own(Resource::Instance(wrapper)),
                &PureFactContext::new(),
            )
            .unwrap();
        assert!(context.owned_instance(target.identity()).is_none());
    }

    #[test]
    fn descriptions_and_ownership_matching_do_not_erase_resource_arguments() {
        use crate::kernel::{Resource, ResourceContext, ResourceFact};
        let target = instance(1, "cell", 7, 10);
        let other_target = instance(2, "cell", 7, 10);
        let wrapper = instance(3, "wrapper", 7, 0)
            .with_resource_arguments(vec![ResourceReference::from_instance(&target)]);
        let wrong = instance(3, "wrapper", 7, 0)
            .with_resource_arguments(vec![ResourceReference::from_instance(&other_target)]);
        let assumptions = PureFactContext::new();
        assert!(
            !ResourceDescription::from_instance(&wrapper).matches_instance(&wrong, &assumptions)
        );
        assert!(!crate::kernel::memory_provenance::resources_directly_match(
            &Resource::Instance(wrapper.clone()),
            &Resource::Instance(wrong.clone()),
            &assumptions,
        ));
        let context = ResourceContext::new()
            .try_compose_with_fact(ResourceFact::own(Resource::Instance(wrapper)), &assumptions)
            .unwrap();
        assert!(
            context
                .without_fact_incrementally(
                    &ResourceFact::own(Resource::Instance(wrong)),
                    &assumptions,
                )
                .is_none()
        );
    }

    #[cfg(test)]
    mod scaling_tests {
        include!("../scaling_tests/kernel/resource_description/tests.rs");
    }
}
