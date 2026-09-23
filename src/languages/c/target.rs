//! Concrete implementation choices for the supported C subset.
//!
//! These are target assumptions, not properties of ISO C or LP64 in general.
//! The Linux kernel builds with `-funsigned-char`; we initially model its
//! x86-64 data layout. This does not claim support for every kernel compiler
//! option, extension, or execution behavior.

use super::syntax::CAbi;
use crate::kernel::ByteOrder;

#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
pub enum CTarget {
    X86_64LinuxKernel,
    /// C11/POSIX user space with the same LP64 and unsigned-char layout, but
    /// without the Linux kernel's `__KERNEL__` predefine.
    X86_64LinuxUserspace,
}

impl CTarget {
    pub const SUPPORTED: Self = Self::X86_64LinuxKernel;

    /// Every selectable target, in the order a diagnostic lists them.
    pub const ALL: &'static [Self] = &[Self::X86_64LinuxKernel, Self::X86_64LinuxUserspace];

    pub const fn name(self) -> &'static str {
        match self {
            Self::X86_64LinuxKernel => "x86_64-linux-kernel",
            Self::X86_64LinuxUserspace => "x86_64-linux-userspace",
        }
    }

    /// Resolves the spelling used by a sidecar's `target` directive.
    pub fn from_name(name: &str) -> Option<Self> {
        Self::ALL
            .iter()
            .copied()
            .find(|target| target.name() == name)
    }

    /// The accepted directive spellings, for an unknown-target diagnostic.
    pub fn accepted_names() -> String {
        Self::ALL
            .iter()
            .map(|target| format!("`{}`", target.name()))
            .collect::<Vec<_>>()
            .join(", ")
    }

    pub const fn abi(self) -> CAbi {
        match self {
            Self::X86_64LinuxKernel | Self::X86_64LinuxUserspace => CAbi::Lp64,
        }
    }

    pub const fn char_bits(self) -> u32 {
        match self {
            Self::X86_64LinuxKernel | Self::X86_64LinuxUserspace => 8,
        }
    }

    /// The order the kernel's byte view of integer cells follows. Both
    /// selectable targets are x86-64, which is little-endian, matching the
    /// `__BYTE_ORDER__` predefine below.
    pub const fn byte_order(self) -> ByteOrder {
        match self {
            Self::X86_64LinuxKernel | Self::X86_64LinuxUserspace => ByteOrder::Little,
        }
    }

    pub const fn plain_char_is_signed(self) -> bool {
        match self {
            Self::X86_64LinuxKernel | Self::X86_64LinuxUserspace => false,
        }
    }

    /// Modeled target/build predefines, independent of compiler version.
    /// Compiler-specific feature/version macros are not synthesized.
    pub const fn predefined_macros(self) -> &'static [(&'static str, &'static str)] {
        match self {
            Self::X86_64LinuxKernel => &[
                ("__CHAR_UNSIGNED__", "1"),
                ("__CHAR_BIT__", "8"),
                ("__SIZEOF_POINTER__", "8"),
                ("__SIZEOF_LONG__", "8"),
                ("__SIZEOF_INT__", "4"),
                ("__SIZEOF_SHORT__", "2"),
                ("__SIZEOF_LONG_LONG__", "8"),
                ("__LP64__", "1"),
                ("_LP64", "1"),
                ("__x86_64__", "1"),
                ("__x86_64", "1"),
                ("__amd64__", "1"),
                ("__amd64", "1"),
                ("__linux__", "1"),
                ("__linux", "1"),
                ("linux", "1"),
                ("__unix__", "1"),
                ("__unix", "1"),
                ("unix", "1"),
                ("__KERNEL__", "1"),
                ("__BYTE_ORDER__", "1234"),
                ("__ORDER_LITTLE_ENDIAN__", "1234"),
                ("__ORDER_BIG_ENDIAN__", "4321"),
            ],
            Self::X86_64LinuxUserspace => &[
                ("__CHAR_UNSIGNED__", "1"),
                ("__CHAR_BIT__", "8"),
                ("__SIZEOF_POINTER__", "8"),
                ("__SIZEOF_LONG__", "8"),
                ("__SIZEOF_INT__", "4"),
                ("__SIZEOF_SHORT__", "2"),
                ("__SIZEOF_LONG_LONG__", "8"),
                ("__LP64__", "1"),
                ("_LP64", "1"),
                ("__x86_64__", "1"),
                ("__x86_64", "1"),
                ("__amd64__", "1"),
                ("__amd64", "1"),
                ("__linux__", "1"),
                ("__linux", "1"),
                ("linux", "1"),
                ("__unix__", "1"),
                ("__unix", "1"),
                ("unix", "1"),
                ("__BYTE_ORDER__", "1234"),
                ("__ORDER_LITTLE_ENDIAN__", "1234"),
                ("__ORDER_BIG_ENDIAN__", "4321"),
            ],
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn supported_target_matches_kernel_char_and_data_model() {
        let target = CTarget::SUPPORTED;
        assert_eq!(target.name(), "x86_64-linux-kernel");
        assert_eq!(target.abi(), CAbi::SUPPORTED);
        assert_eq!(target.char_bits(), 8);
        assert!(!target.plain_char_is_signed());
    }

    #[test]
    fn every_target_byte_order_matches_its_byte_order_predefine() {
        for target in CTarget::ALL {
            let predefined = target
                .predefined_macros()
                .iter()
                .find(|(name, _)| *name == "__BYTE_ORDER__")
                .map(|(_, value)| *value);
            let expected = match target.byte_order() {
                ByteOrder::Little => "1234",
                ByteOrder::Big => "4321",
            };
            assert_eq!(predefined, Some(expected), "{}", target.name());
        }
    }

    #[test]
    fn verified_theorems_expose_the_concrete_target() {
        let theorems = crate::surface::verify_c0_sources(
            "verifying \"a.c\"; int answer() { ensures result == 1; } by { execute(); simp(); }",
            &[("a.c", "int answer(void) { return 1; }")],
        )
        .unwrap();
        assert!(!theorems.is_empty());
        assert!(
            theorems
                .iter()
                .all(|theorem| theorem.target() == CTarget::SUPPORTED)
        );
    }

    #[test]
    fn userspace_profile_never_injects_kernel_predefines() {
        let target = CTarget::X86_64LinuxUserspace;
        assert_eq!(target.abi(), CAbi::Lp64);
        assert_eq!(target.char_bits(), 8);
        assert!(!target.plain_char_is_signed());
        assert!(
            !target
                .predefined_macros()
                .iter()
                .any(|(name, _)| *name == "__KERNEL__")
        );
    }
}
