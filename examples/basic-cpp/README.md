# Basic C++ verification

These synthetic, header-free C++20 examples exercise Click's Clang compiler
import. `increment.cpp` is the smallest smoke test: a reference parameter is
mutated and returned. `with_restore.cpp` verifies an RAII guard whose destructor
restores the original value after either return path, while each return value
captures the value before destruction. The `.cpp` files are the same inputs
used by the focused C++ import regressions. `with_restore_caller.cpp` preserves
the original RAII source as an exact prefix, then adds a direct caller whose
precondition starts the referenced cell at 41. Its proof uses the helper's
checked contract to show a result of 7 or 9 and a post-call cell still at 41.

From the repository root, build the pinned Clang exporter and materialize a
compilation database with the absolute path to this checkout:

```sh
scripts/build-cpp-exporter.sh
python3 examples/basic-cpp/prepare.py
```

Then lock and verify each sidecar:

```sh
cargo run --bin click -- import lock examples/basic-cpp/increment.click
cargo run --bin click -- verify examples/basic-cpp/increment.click
cargo run --bin click -- import lock examples/basic-cpp/with_restore.click
cargo run --bin click -- verify examples/basic-cpp/with_restore.click
cargo run --bin click -- import lock examples/basic-cpp/with_restore_caller.click
cargo run --bin click -- verify examples/basic-cpp/with_restore_caller.click
```

The checked-in `compile_commands.json.in` fixes the C++20 target and flags;
`prepare.py` fills only the machine-specific compilation directory. The
generated compilation database, import artifacts, and lockfiles are local
outputs, not checked-in proof inputs. The examples gate performs the same
preparation, import refresh, and verification automatically.
