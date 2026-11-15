//! Report-local disambiguation; never retained by checking or error capture.
use super::*;
use crate::kernel::MemoryRange;

const MAX_RANGES: usize = 64;

#[derive(Clone, Default)]
pub(super) struct RangeCollisions {
    entries: Vec<(String, MemoryRange, Option<usize>)>,
    collecting: bool,
    limited: bool,
}

impl RangeCollisions {
    pub(super) fn observe(&mut self, text: &str, range: &MemoryRange) -> Option<String> {
        if let Some((_, _, label)) = self
            .entries
            .iter()
            .find(|(spelling, value, _)| spelling == text && value == range)
        {
            return label.map(|id| format!(" [range {}]", alphabetic_label(id)));
        }
        if self.collecting {
            if self.entries.len() < MAX_RANGES {
                self.entries.push((text.to_owned(), range.clone(), None));
            } else {
                self.limited = true;
            }
        }
        None
    }

    fn finish(&mut self) -> bool {
        self.collecting = false;
        let mut next = 0;
        for index in 0..self.entries.len() {
            if self.entries.iter().enumerate().any(|(other, entry)| {
                other != index
                    && entry.0 == self.entries[index].0
                    && entry.1.base() == self.entries[index].1.base()
                    && entry.1.bound_terms() == self.entries[index].1.bound_terms()
                    && entry.1.element_width() == self.entries[index].1.element_width()
                    && entry.1.kind() == self.entries[index].1.kind()
            }) {
                self.entries[index].2 = Some(next);
                next += 1;
            }
        }
        next != 0
    }
}

impl MemoryStateLabels {
    pub(crate) fn begin_range_collision_detection(&mut self) {
        self.range_collisions = Some(RangeCollisions {
            collecting: true,
            ..Default::default()
        });
    }

    pub(crate) fn finish_range_collision_detection(&mut self) -> bool {
        self.range_collisions
            .as_mut()
            .is_some_and(RangeCollisions::finish)
    }

    pub(crate) fn end_range_collision_detection(&mut self) {
        self.range_collisions = None;
    }

    fn range_object_identity(&mut self, pointer: &Pointer) -> String {
        if let Some((parameters, arguments)) = self.naming.as_deref() {
            for (parameter, argument) in parameters.iter().zip(arguments).take(128) {
                if let crate::kernel::ProgramExpression::Value(
                    crate::kernel::ProgramValue::Pointer(value),
                ) = argument
                    && value.designation() == pointer
                {
                    return format!("parameter `{}`", parameter.name());
                }
            }
        }
        self.legend_pointer(pointer)
    }

    pub(crate) fn range_collision_legend(&mut self) -> String {
        let Some(collisions) = self.range_collisions.clone() else {
            return String::new();
        };
        let mut result = String::new();
        for (_, range, label) in collisions.entries {
            let Some(label) = label else { continue };
            if result.is_empty() {
                result.push_str(
                    "\n  range identities (same printed footprint, different internal identities):",
                );
            }
            let (designation, opaque, known) = range.diagnostic_pointer_metadata();
            let designation = self.range_object_identity(designation);
            let bounds = match (known, opaque) {
                (true, None) => "known object extent".to_owned(),
                (true, Some(origin)) => format!(
                    "known extent; retained extent identity = {}",
                    self.range_object_identity(origin)
                ),
                (false, Some(origin)) => {
                    format!("opaque extent from {}", self.range_object_identity(origin))
                }
                (false, None) => "unknown extent".to_owned(),
            };
            // Keep the legend bounded even for large symbolic pointer terms.
            let bounded = |text: String| {
                let prefix = text.chars().take(400).collect::<String>();
                if prefix.len() < text.len() {
                    format!("{prefix}…")
                } else {
                    prefix
                }
            };
            result.push_str(&format!(
                "\n    range {}: object identity = {}; bounds = {}",
                alphabetic_label(label),
                bounded(designation),
                bounded(bounds)
            ));
        }
        if collisions.limited {
            result.push_str("\n  range identity comparison limited to the first 64 distinct displayed representations");
        }
        result
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::{PointerBlock, PointerValue, ProgramType};

    fn range(origin: u64) -> MemoryRange {
        let base = Pointer::symbolic(Variable(987_800));
        let value = PointerValue::new(
            Pointer::symbolic(Variable(origin)),
            ProgramType::Int32Pointer,
        )
        .with_address(base);
        MemoryRange::from_pointer_value(&value, 0u32.into(), 1u32.into(), 4)
    }

    #[test]
    fn equal_ranges_and_different_spellings_do_not_get_labels() {
        let mut collisions = RangeCollisions {
            collecting: true,
            ..Default::default()
        };
        let one = range(987_801);
        collisions.observe("memory(p)", &one);
        collisions.observe("memory(p)", &one.clone());
        collisions.observe("memory(q)", &range(987_802));
        assert!(!collisions.finish());
        assert_eq!(collisions.entries.len(), 2);
        assert_eq!(collisions.observe("memory(p)", &one), None);
    }

    #[test]
    fn collision_labels_are_shared_and_collection_is_capped() {
        let mut labels = MemoryStateLabels::default();
        assert!(labels.range_collisions.is_none());
        labels.begin_range_collision_detection();
        for index in 0..100 {
            labels
                .range_collisions
                .as_mut()
                .unwrap()
                .observe("memory(p)", &range(987_801 + index));
        }
        assert_eq!(
            labels.range_collisions.as_ref().unwrap().entries.len(),
            MAX_RANGES
        );
        assert!(labels.finish_range_collision_detection());
        let collisions = labels.range_collisions.as_mut().unwrap();
        assert_eq!(
            collisions.observe("memory(p)", &range(987_801)),
            Some(" [range A]".into())
        );
        assert_eq!(
            collisions.observe("memory(p)", &range(987_802)),
            Some(" [range B]".into())
        );
        assert!(
            labels
                .range_collision_legend()
                .contains("limited to the first 64")
        );
        labels.end_range_collision_detection();
        assert!(labels.range_collisions.is_none());
    }

    #[test]
    fn ordinary_rendering_does_not_collect_collisions() {
        let mut labels = MemoryStateLabels::default();
        for origin in 987_801..987_805 {
            let fact = ResourceFact::View(Resource::Memory(range(origin)));
            let text = render_resource_fact_labeled(&fact, &mut labels);
            assert!(!text.contains("[range "));
            assert!(labels.range_collisions.is_none());
        }
        // Keep a concrete object in the metadata coverage too.
        let value = PointerValue::new(
            Pointer {
                block: PointerBlock::Concrete("global:table".into()),
                offset: PointerOffsetTerm::Constant(0),
            },
            ProgramType::Int32Pointer,
        );
        let range = MemoryRange::from_pointer_value(&value, 0u32.into(), 1u32.into(), 4);
        assert!(range.diagnostic_pointer_metadata().2);
    }
}
