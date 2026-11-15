# Local array copy after a checked call

This frozen Charon crate reproduces the source pattern encountered in unchanged
`adler2`: a checked helper mutates a local scalar array, then the caller copies
that array by value. Checked calls can discard cached lane values while retaining
initialized storage. Those missing caches must not prevent a copy.

`copy.rs` replaces the first lane with 5, copies the array, and subsequently
changes the original lane to 9. The checked result is 5: the copy captures the
post-call memory state and remains independent of later source writes.
Both Rust function bodies are checked, including the helper's postcondition.
The crate root, source file, edition, extraction artifact, and hashes are locked.

Regressions reject the pre-call value 1, the later source value 9, insufficient
ownership, and read-only authority. Verification, profiling, and expanded
certificates are rechecked; audit runs with the nightly import tests. Kernel
tests cover partial call writes, preservation of known lanes, uninitialized or
incompatible source storage, and compact copies up to a million elements.

This fixes the copy prerequisite of `adler2`'s first nonempty vector path. The
complete four-byte checksum contract remains subsequent work.
