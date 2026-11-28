//! Boolean pure-call production retains numeric operands and exact opaque
//! descriptors. Compatibility readers borrow a single selected call adapter.
use super::*;

impl KernelTermImport {
    pub(crate) fn boolean_call(&mut self, application: &SharedPureApplication) -> KernelTerm {
        if self.exact_field_inputs {
            // A stored Boolean call must reproduce each producer's argument
            // descriptor, including the distinction between a boxed and shared word.
            let arguments = (0..application.arguments().len())
                .map(|index| KernelTerm::written_call_argument(application, index))
                .collect();
            return KernelTerm::checked_call(
                KernelType::Bool,
                application.name().into(),
                arguments,
            );
        }
        self.boolean_call_with_retained(application, &[])
    }

    pub(crate) fn boolean_call_with_retained(
        &mut self,
        application: &SharedPureApplication,
        retained: &[Option<KernelTerm>],
    ) -> KernelTerm {
        let arguments = application
            .arguments()
            .iter()
            .enumerate()
            .map(|(index, _)| {
                retained
                    .get(index)
                    .and_then(Clone::clone)
                    .unwrap_or_else(|| {
                        if let Some(root) = application.common_argument(index) {
                            root
                        } else {
                            KernelTerm::written_call_argument(application, index)
                        }
                    })
            })
            .collect();
        KernelTerm::checked_call(KernelType::Bool, application.name().into(), arguments)
    }
}
impl KernelTerm {
    pub(crate) fn boolean_call_machine_argument(&self) -> Option<SharedMachineIntegerTerm> {
        let KernelType::Program(ty) = self.ty() else {
            return None;
        };
        let format = MachineIntegerType::from_program_type(*ty)?;
        if self.requires_native_argument_input() || self.written_argument().is_some() {
            return None;
        }
        Some(MachineOperandView::Shared(self).retain(format))
    }

    pub(crate) fn old_boolean_call(&self) -> Option<&OldConditionTerm> {
        if self.ty() != &KernelType::Bool {
            return None;
        }
        let KernelTermNode::Call { name, arguments } = self.node() else {
            return None;
        };
        let OldMachineTerm::BoolCast { value, .. } = self.0.machine_leaf.get_or_init(|| {
            let mut export = KernelTermExport::default();
            let arguments = arguments
                .iter()
                .map(|argument| {
                    if let Some(machine) = argument.boolean_call_machine_argument() {
                        PureFunctionArgument::SharedMachine(machine)
                    } else {
                        export.argument(argument).expect("Boolean call argument")
                    }
                })
                .collect();
            OldMachineTerm::BoolCast {
                to: MachineIntegerType::UInt8,
                value: Box::new(OldConditionTerm::BoolApplication(
                    SharedPureApplication::intern(name.clone(), arguments),
                )),
            }
        }) else {
            unreachable!("Boolean call descriptor");
        };
        Some(value)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn boolean_calls_preserve_exact_descriptors_and_semantic_identity() {
        let _session = crate::kernel::VerificationSession::enter();
        // Two producers of one logical pointer: distinct handles.
        let pointer = || {
            Pointer::new(
                Address::symbolic(Variable(999401)),
                ProgramType::Int32Pointer,
            )
        };
        let applications = [pointer(), pointer()].map(|pointer| {
            SharedPureApplication::intern(
                "boolean_exact_arguments".into(),
                vec![PureFunctionArgument::Value(ProgramValue::Pointer(pointer))],
            )
        });
        assert_eq!(applications[0], applications[1]);
        let roots = applications
            .each_ref()
            .map(|application| KernelTermImport::default().boolean_call(application));
        assert_ne!(roots[0], roots[1]);
        assert!(
            BooleanOperandView::Shared(&roots[0])
                .syntax_equal(BooleanOperandView::Shared(&roots[1]))
        );
        for (root, application) in roots.iter().zip(&applications) {
            assert_eq!(
                format!("{:?}", KernelTermExport::condition(root).unwrap()),
                format!(
                    "{:?}",
                    OldConditionTerm::BoolApplication(application.clone())
                )
            );
            assert!(std::ptr::eq(
                root.old_boolean_call().unwrap(),
                root.old_boolean_call().unwrap()
            ));
        }
        let stored = applications.each_ref().map(|application| {
            StoredConditionTerm::from(OldConditionTerm::BoolApplication(application.clone()))
        });
        assert_eq!(stored[0], stored[1]);
        for (condition, application) in stored.iter().zip(&applications) {
            let root = condition.root().expect("stored Boolean call");
            let KernelTermNode::Call { arguments, .. } = root.node() else {
                panic!("expected call")
            };
            assert!(std::ptr::eq(
                arguments[0].written_argument().unwrap(),
                &application.arguments()[0]
            ));
        }
        let observed = roots.map(|guard| {
            SharedMachineIntegerTerm::observe_shared(
                MachineIntegerType::Int32,
                KernelTerm::machine_if_shared(
                    MachineIntegerType::Int32,
                    [
                        guard,
                        KernelTermImport::default()
                            .machine(MachineIntegerType::Int32, &OldMachineTerm::constant(1)),
                        KernelTermImport::default()
                            .machine(MachineIntegerType::Int32, &OldMachineTerm::constant(0)),
                    ],
                ),
            )
            .unwrap()
        });
        assert_eq!(observed[0], observed[1]);
    }
}

#[cfg(test)]
mod scaling_tests {
    include!("../../../../scaling_tests/kernel/primitives/kernel_term/boolean/call.rs");
}
