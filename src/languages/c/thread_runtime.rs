//! Explicit C thread-runtime assumptions. The modeled binding is a conditional
//! client-verification profile; no native pthread implementation is certified.

use sha2::{Digest, Sha256};

/// Retained identity of the narrow built-in create/join projection. A verifier
/// attaches this only after checking declaration provenance and call shapes.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ModeledPthreadBinding {
    pub target: super::target::CTarget,
    pub specification_version: u32,
    pub header_digest: [u8; 32],
    pub specification_digest: [u8; 32],
    pub create_name: &'static str,
    pub join_name: &'static str,
    pub requires_null_attributes: bool,
    pub requires_direct_worker: bool,
    pub requires_null_join_result: bool,
}

impl ModeledPthreadBinding {
    pub fn builtin() -> Self {
        Self {
            target: super::target::CTarget::X86_64LinuxUserspace,
            specification_version: 1,
            header_digest: Sha256::digest(include_str!("modeled_pthread.h").as_bytes()).into(),
            specification_digest: Sha256::digest(
                include_str!("modeled_pthread_spec.md").as_bytes(),
            )
            .into(),
            create_name: "pthread_create",
            join_name: "pthread_join",
            requires_null_attributes: true,
            requires_direct_worker: true,
            requires_null_join_result: true,
        }
    }

    pub fn identity(&self) -> String {
        let mut hasher = Sha256::new();
        for part in [
            b"click-modeled-pthread-binding-v1".as_slice(),
            self.target.name().as_bytes(),
            &self.specification_version.to_be_bytes(),
            &self.header_digest,
            &self.specification_digest,
            self.create_name.as_bytes(),
            self.join_name.as_bytes(),
            &[
                self.requires_null_attributes as u8,
                self.requires_direct_worker as u8,
                self.requires_null_join_result as u8,
            ],
        ] {
            hasher.update((part.len() as u64).to_be_bytes());
            hasher.update(part);
        }
        format!("modeled-pthread:{:x}", hasher.finalize())
    }
}

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub enum CThreadRuntime {
    #[default]
    None,
    ModeledPthread,
}

impl CThreadRuntime {
    pub fn from_name(name: &str) -> Option<Self> {
        match name {
            "modeled-pthread" => Some(Self::ModeledPthread),
            _ => None,
        }
    }

    pub const fn name(self) -> Option<&'static str> {
        match self {
            Self::None => None,
            Self::ModeledPthread => Some("modeled-pthread"),
        }
    }

    /// Participates in both proof and incremental-session identities. The
    /// actual built-in declarations and specification bytes invalidate a
    /// cached modeled proof when either changes.
    pub fn identity_suffix(self) -> Option<String> {
        match self {
            Self::None => None,
            Self::ModeledPthread => Some(ModeledPthreadBinding::builtin().identity()),
        }
    }

    pub const fn assumption(self) -> Option<&'static str> {
        match self {
            Self::None => None,
            Self::ModeledPthread => Some(
                "modeled-pthread v1: pthread_create/pthread_join obey the trusted Click create/join specification; native runtime binding unvalidated",
            ),
        }
    }
}
