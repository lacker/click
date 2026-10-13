//! Click's system headers as files a compiler import can search.
//!
//! The direct source-bundle preprocessor answers `#include <header>` from
//! Click's own models; it never reads a platform header. A compiler import
//! runs GCC's preprocessor with `-nostdinc`, so this module writes the same
//! models out as header files and the import adds their directory in the
//! slot GCC gives the C library's headers: after the project's `-I` and
//! `-isystem` directories. The headers carry no contracts. A call binds to
//! Click's standard-library contract by the function's name, whichever
//! declaration GCC selects.

use sha2::{Digest, Sha256};

use super::source::{LIMITS_MACROS, char_limits_macros};
use super::target::CTarget;

/// Whether a header file models a Click interface or refuses the include.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum HeaderKind {
    Modeled,
    Refused,
}

impl HeaderKind {
    fn name(self) -> &'static str {
        match self {
            Self::Modeled => "modeled",
            Self::Refused => "refused",
        }
    }
}

#[derive(Clone, Debug)]
pub(crate) struct SystemHeader {
    pub name: &'static str,
    pub kind: HeaderKind,
    pub text: String,
}

/// The system headers the direct preprocessor models for `target`, as
/// `source::expand_source` accepts them. A unit test keeps the two agreeing.
pub(crate) fn modeled_header_names(target: CTarget) -> &'static [&'static str] {
    match target {
        CTarget::X86_64LinuxKernel => &["inttypes.h", "limits.h", "stdbool.h", "stdint.h"],
        CTarget::X86_64LinuxUserspace => &[
            "inttypes.h",
            "limits.h",
            "pthread.h",
            "stdatomic.h",
            "stdbool.h",
            "stddef.h",
            "stdint.h",
            "stdlib.h",
            "string.h",
        ],
    }
}

/// Modeled headers that a compiler import refuses with the reason: they
/// belong to the modeled-pthread runtime, which refuses compiler-imported
/// sources.
const RUNTIME_ONLY: &[&str] = &["pthread.h", "stdatomic.h"];

/// The other headers of C11 and POSIX.1-2017. On a hosted target a C
/// library supplies them, so `__has_include` finds them; Click finds them
/// too and refuses the include by name rather than letting a program take
/// a branch the real build would not take.
const HOSTED_UNMODELED: &[&str] = &[
    "aio.h",
    "arpa/inet.h",
    "assert.h",
    "complex.h",
    "cpio.h",
    "ctype.h",
    "dirent.h",
    "dlfcn.h",
    "errno.h",
    "fcntl.h",
    "fenv.h",
    "float.h",
    "fmtmsg.h",
    "fnmatch.h",
    "ftw.h",
    "glob.h",
    "grp.h",
    "iconv.h",
    "iso646.h",
    "langinfo.h",
    "libgen.h",
    "locale.h",
    "math.h",
    "monetary.h",
    "mqueue.h",
    "ndbm.h",
    "net/if.h",
    "netdb.h",
    "netinet/in.h",
    "netinet/tcp.h",
    "nl_types.h",
    "poll.h",
    "pwd.h",
    "regex.h",
    "sched.h",
    "search.h",
    "semaphore.h",
    "setjmp.h",
    "signal.h",
    "spawn.h",
    "stdalign.h",
    "stdarg.h",
    "stdio.h",
    "stdnoreturn.h",
    "strings.h",
    "stropts.h",
    "sys/ipc.h",
    "sys/mman.h",
    "sys/msg.h",
    "sys/resource.h",
    "sys/select.h",
    "sys/sem.h",
    "sys/shm.h",
    "sys/socket.h",
    "sys/stat.h",
    "sys/statvfs.h",
    "sys/time.h",
    "sys/times.h",
    "sys/types.h",
    "sys/uio.h",
    "sys/un.h",
    "sys/utsname.h",
    "sys/wait.h",
    "syslog.h",
    "tar.h",
    "termios.h",
    "tgmath.h",
    "threads.h",
    "time.h",
    "trace.h",
    "uchar.h",
    "ulimit.h",
    "unistd.h",
    "utime.h",
    "utmpx.h",
    "wchar.h",
    "wctype.h",
    "wordexp.h",
];

/// Where a refusal points the reader.
pub(crate) const COVERAGE_REFERENCE: &str = "docs/reference/language/c.md#system-headers";

/// The header files a compiler import searches for `target`: Click's
/// modeled headers with the text the direct preprocessor uses, and, for the
/// hosted target, refusing stand-ins for the rest of C11 and POSIX.
pub(crate) fn compiler_import_headers(target: CTarget) -> Vec<SystemHeader> {
    let mut headers = Vec::new();
    for &name in modeled_header_names(target) {
        if RUNTIME_ONLY.contains(&name) {
            headers.push(SystemHeader {
                name,
                kind: HeaderKind::Refused,
                text: refusal(
                    name,
                    &format!(
                        "Click's <{name}> belongs to the modeled-pthread runtime, which does not accept compiler-imported sources"
                    ),
                ),
            });
            continue;
        }
        headers.push(SystemHeader {
            name,
            kind: HeaderKind::Modeled,
            text: modeled_text(name, target),
        });
    }
    if target == CTarget::X86_64LinuxUserspace {
        for &name in HOSTED_UNMODELED {
            headers.push(SystemHeader {
                name,
                kind: HeaderKind::Refused,
                text: refusal(
                    name,
                    &format!(
                        "<{name}> is not one of Click's modeled system headers for {}; see {COVERAGE_REFERENCE}",
                        target.name()
                    ),
                ),
            });
        }
    }
    headers.sort_by_key(|header| header.name);
    headers
}

/// The identity of the header set a compiler import searches for `target`:
/// which names exist and whether each is modeled or refused. It decides
/// what an include or `__has_include` finds; the text of each modeled header
/// the compiler actually opens is locked separately.
pub(crate) fn catalog_digest(target: CTarget) -> String {
    let mut data = String::from("click-c-system-header-catalog-v1\0");
    data.push_str(target.name());
    for header in compiler_import_headers(target) {
        data.push('\0');
        data.push_str(header.name);
        data.push('\0');
        data.push_str(header.kind.name());
    }
    hex(&Sha256::digest(data.as_bytes()))
}

/// The SHA-256 of a modeled header's text, as a lock records it.
pub(crate) fn text_digest(text: &str) -> String {
    hex(&Sha256::digest(text.as_bytes()))
}

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

fn refusal(name: &str, reason: &str) -> String {
    format!("/* Click refuses <{name}> in a compiler import. */\n#error \"{reason}\"\n")
}

fn modeled_text(name: &str, target: CTarget) -> String {
    match name {
        "stdint.h" | "inttypes.h" | "stdbool.h" => format!(
            "/* Click's <{name}>: its standard type spellings are built into Click's\n \
             * C types, so this header declares nothing. */\n#pragma once\n"
        ),
        "stddef.h" => "/* Click's <stddef.h>: `NULL`; `size_t` is built into Click's C types. */\n\
             #pragma once\n#undef NULL\n#define NULL ((void*)0)\n"
            .to_string(),
        "limits.h" => {
            let mut text = format!(
                "/* Click's <limits.h> for {}: the LP64 integer limits. */\n#pragma once\n",
                target.name()
            );
            for (macro_name, value) in LIMITS_MACROS
                .iter()
                .chain(char_limits_macros(target).iter())
            {
                text.push_str(&format!("#define {macro_name} {value}\n"));
            }
            text
        }
        "string.h" => include_str!("modeled_string.h").to_string(),
        "stdlib.h" => include_str!("modeled_stdlib.h").to_string(),
        _ => unreachable!("modeled header `{name}` has no compiler-import text"),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::BTreeMap;

    /// Every system header the direct preprocessor accepts for a target is
    /// in that target's modeled list, and every other probed name is refused.
    #[test]
    fn modeled_names_match_the_direct_preprocessor() {
        let probes = modeled_header_names(CTarget::X86_64LinuxUserspace)
            .iter()
            .chain(HOSTED_UNMODELED)
            .copied()
            .collect::<Vec<_>>();
        for target in [CTarget::X86_64LinuxKernel, CTarget::X86_64LinuxUserspace] {
            for name in &probes {
                let source = format!("#include <{name}>\nint x;\n");
                let sources = BTreeMap::from([("main.c", source.as_str())]);
                let accepted =
                    super::super::source::expand_includes_for_target("main.c", &sources, target)
                        .is_ok();
                assert_eq!(
                    accepted,
                    modeled_header_names(target).contains(name),
                    "{} <{name}>",
                    target.name()
                );
            }
        }
    }

    #[test]
    fn import_headers_reuse_the_direct_texts_and_refuse_the_rest() {
        let headers = compiler_import_headers(CTarget::X86_64LinuxUserspace);
        let by_name = headers
            .iter()
            .map(|header| (header.name, header))
            .collect::<BTreeMap<_, _>>();
        assert_eq!(by_name["string.h"].text, include_str!("modeled_string.h"));
        assert_eq!(by_name["string.h"].kind, HeaderKind::Modeled);
        assert!(
            by_name["limits.h"]
                .text
                .contains("#define CHAR_MIN (-128)\n")
        );
        assert!(by_name["stdio.h"].text.contains("#error"));
        assert!(
            by_name["pthread.h"]
                .text
                .contains("modeled-pthread runtime")
        );
        let kernel = compiler_import_headers(CTarget::X86_64LinuxKernel);
        assert!(
            kernel
                .iter()
                .all(|header| header.kind == HeaderKind::Modeled)
        );
        assert!(kernel.iter().any(
            |header| header.name == "limits.h" && header.text.contains("#define CHAR_MIN 0\n")
        ));
        assert_ne!(
            catalog_digest(CTarget::X86_64LinuxKernel),
            catalog_digest(CTarget::X86_64LinuxUserspace)
        );
    }
}
