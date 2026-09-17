//! Registration of the modeled user-space thread primitives.
//!
//! These cover the plumbing only: which declarations become rules carrying
//! `ExternalCallSemantics::ThreadCreate`/`ThreadJoin`, and which declarations
//! and sidecar blocks are refused. The transitions those rules stand for are
//! not implemented yet, so a call to one fails promptly; that diagnostic is
//! checked here and in `mdtests/thread_primitive_not_yet_supported.md`.

use super::super::verification::verify_c0_sources_with_environment;
use crate::kernel::ExternalCallSemantics;

const WORKER_C: &str = r#"#include <pthread.h>

int32 worker_count(void) {
    return 2;
}
"#;

/// The same declarations written out, for the target that has no modeled
/// `<pthread.h>` to include.
const DECLARED_C: &str = r#"typedef unsigned long pthread_t;
typedef struct __click_pthread_attr pthread_attr_t;

int pthread_create(pthread_t *thread, const pthread_attr_t *attr,
                   void *(*start_routine)(void *), void *arg);
int pthread_join(pthread_t thread, void **retval);

int32 worker_count(void) {
    return 2;
}
"#;

fn environment_for(
    click_source: &str,
    c_sources: &[(&str, &str)],
) -> Result<crate::kernel::CExecutionEnvironment, crate::surface::ClickError> {
    verify_c0_sources_with_environment(click_source, c_sources, None, None, None)
        .map(|(_, environment)| environment)
}

#[test]
fn the_user_space_target_registers_both_thread_primitives() {
    let environment = environment_for(
        "target \"x86_64-linux-userspace\";\nverifying \"worker.c\";",
        &[("worker.c", WORKER_C)],
    )
    .expect("a sidecar that only selects the target should verify");
    assert_eq!(
        environment.external_call_semantics("pthread_create"),
        Some(ExternalCallSemantics::ThreadCreate)
    );
    assert_eq!(
        environment.external_call_semantics("pthread_join"),
        Some(ExternalCallSemantics::ThreadJoin)
    );
    // The declarations are also ordinary callees for name resolution, with
    // the signatures the modeled header declared.
    let create = environment
        .get_function("pthread_create")
        .expect("the primitive is a known function");
    assert_eq!(create.parameters().len(), 4);
    assert!(create.contract_claims().is_empty());
    assert!(create.contract_requires().is_empty());
    assert!(create.contract_ensures().is_empty());
    let join = environment
        .get_function("pthread_join")
        .expect("the primitive is a known function");
    assert_eq!(join.parameters().len(), 2);
    assert!(join.contract_claims().is_empty());
}

/// The kernel target models no thread API. The same declarations spelled by
/// hand there stay ordinary undeclared-contract functions, so nothing is
/// registered and no thread diagnostic appears.
#[test]
fn the_kernel_target_registers_no_thread_primitives() {
    let environment = environment_for("verifying \"worker.c\";", &[("worker.c", DECLARED_C)])
        .expect("the default target should verify");
    assert_eq!(environment.external_call_semantics("pthread_create"), None);
    assert_eq!(environment.external_call_semantics("pthread_join"), None);

    let environment = environment_for(
        "target \"x86_64-linux-userspace\";\nverifying \"worker.c\";",
        &[("worker.c", DECLARED_C)],
    )
    .expect("the same declarations under the user-space target should verify");
    assert_eq!(
        environment.external_call_semantics("pthread_create"),
        Some(ExternalCallSemantics::ThreadCreate)
    );
}

/// Recognition is by identity. A same-named declaration of a different shape
/// is a different function than the one the transition is written against,
/// and must say so rather than becoming an ordinary opaque callee.
#[test]
fn a_mismatched_thread_primitive_declaration_names_the_difference() {
    let error = environment_for(
        "target \"x86_64-linux-userspace\";\nverifying \"worker.c\";",
        &[(
            "worker.c",
            "typedef unsigned long pthread_t;\n\
             int pthread_join(pthread_t thread, int *retval);\n\
             int32 worker_count(void) { return 2; }\n",
        )],
    )
    .expect_err("a differently shaped `pthread_join` must not be taken for the primitive");
    assert!(
        error.message().contains("pthread_join")
            && error.message().contains("does not match the modeled")
            && error.message().contains("parameter 2"),
        "{error:?}"
    );

    let error = environment_for(
        "target \"x86_64-linux-userspace\";\nverifying \"worker.c\";",
        &[(
            "worker.c",
            "typedef unsigned long pthread_t;\n\
             int pthread_join(pthread_t thread);\n\
             int32 worker_count(void) { return 2; }\n",
        )],
    )
    .expect_err("a differently shaped `pthread_join` must not be taken for the primitive");
    assert!(
        error.message().contains("takes 1 parameters, not 2"),
        "{error:?}"
    );
}

/// A thread primitive's meaning comes from the kernel, so a user contract for
/// one would be an unchecked concurrency assumption dressed as a declaration.
#[test]
fn a_user_extern_block_for_a_thread_primitive_is_rejected() {
    for name in ["pthread_create", "pthread_join"] {
        let click_source = format!(
            "target \"x86_64-linux-userspace\";\n\
             verifying \"worker.c\";\n\
             extern int32 {name}(int32 handle) {{\n\
                 ensures result == 0;\n\
             }}\n"
        );
        let error = environment_for(&click_source, &[("worker.c", WORKER_C)])
            .expect_err("a thread primitive takes no user contract");
        assert!(
            error.message().contains(name)
                && error.message().contains("checked kernel semantics")
                && error.message().contains("no user contract"),
            "{error:?}"
        );
    }

    // The same block under the kernel target is an ordinary external
    // contract: nothing about that target changes.
    environment_for(
        "verifying \"worker.c\";\n\
         extern int32 pthread_join(int32 handle) {\n\
             ensures result == 0;\n\
         }\n",
        &[("worker.c", "int32 worker_count(void) { return 2; }")],
    )
    .expect("the kernel target has no thread primitives to protect");
}

/// A verified definition of one of these names would be shadowed by the
/// registered rule, leaving the environment claiming a checked transition for
/// a body Click had actually parsed.
#[test]
fn a_verified_definition_of_a_thread_primitive_is_rejected() {
    let error = environment_for(
        "target \"x86_64-linux-userspace\";\nverifying \"worker.c\";",
        &[(
            "worker.c",
            "#include <pthread.h>\n\
             int pthread_join(pthread_t thread, void **retval) { return 0; }\n",
        )],
    )
    .expect_err("a verified source must not define a thread primitive");
    assert!(
        error.message().contains("defines `pthread_join`")
            && error.message().contains("checked kernel semantics"),
        "{error:?}"
    );
}

/// The rules exist before the transitions do. A call must fail promptly and
/// name the primitive, never fall through to the ordinary opaque-contract
/// path, which would report a missing contract instead.
#[test]
fn calling_a_thread_primitive_fails_by_naming_it() {
    let error = environment_for(
        "target \"x86_64-linux-userspace\";\n\
         verifying \"worker.c\";\n\
         int32 join_once() {\n\
             ensures result == 0;\n\
         } by { execute(); simp(); }\n",
        &[(
            "worker.c",
            "#include <pthread.h>\n\
             int32 join_once() {\n\
                 pthread_t handle;\n\
                 return pthread_join(handle, 0);\n\
             }\n",
        )],
    )
    .expect_err("the create/join transitions do not exist yet");
    assert!(
        error.message().contains("pthread_join") && error.message().contains("not yet supported"),
        "{error:?}"
    );
}
