# Original shared byte iteration proof through Charon

`rust-iterators/sum.rs` is a byte-identical copy of the original
`examples/rust-iterators` source, and `frozen.click` archives its original
sidecar, respelled once in today's syntax with its contract and proof
unchanged (`../README.md`, Complete canonical proof-port adoption). The migrated `sum.click` retains
every signature, specification function, precondition, and postcondition.
The native Charon artifact and import lock support offline checks.

The original body sums every byte through implicit shared slice iteration.
The proof relates the iterator's remaining length, `iter.len()`, to the
input prefix, proves a mathematical integer sum, and bounds every checked
signed addition. The original bound and viewed byte range include empty
inputs and arbitrary byte values; no input values or source body are changed.

The proof uses source `byte`/`total` locals, named iteration/read/addition
states, and `loop(0)`, `read(0)`, `assignment(total, 1)`, and `back_edge()`
frontiers. It contains no MIR IDs, generated processed count, or compiler
statement indices. Invariant/ranking closure remains explicit.

Tests compare the source and frozen sidecar byte-for-byte and compare parsed
contracts. They reject missing views, a false sum, and a nondecreasing measure;
verify/profile agree, the complete expansion rechecks, and focused audits
check the read, assignment, and back-edge certificates. The live parity sweep
reextracts the unchanged source and verifies the port separately from the
frozen sidecar's recorded gap.

`rust-iter-references` now also retains the byte-identical original source,
frozen sidecar, and full mathematical sum contract. Its explicit
`for byte in bytes.iter()` stores references; `let { result: loaded_byte } = step();`
names the actual checked byte read without depending on an unnamed MIR local.
The name retains that value as compiler temporaries leave scope. Both ports
share the contract, negative-obligation, verify/profile, expansion, audit, and
live extraction checks.

This checkpoint advances original source-and-contract coverage to 16/16
(100%), including five separate proof ports. Frozen-sidecar compatibility
remains 11/16 (68.75%); default switching and legacy retirement remain open.
