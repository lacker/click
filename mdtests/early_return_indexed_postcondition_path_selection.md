# Early-return indexed postconditions select a checked lowering path

A consumed model selects the index used by the success outcome. The C body
writes through the ordinary scalar parameter, while the outcome postcondition
and a checked outcome-local memory proposition use a pure helper over the
entry resource. At the return outcome the helper equals that scalar only on
one checked lowering path.

```c filename=early_return_indexed_postcondition_path_selection.c
int32 write_selected(int32 cells[], int32 index, int32 enabled) {
    if (enabled == 0) {
        return 0;
    }
    cells[index] = 1;
    return cells[index];
}
```

```click
verifying "early_return_indexed_postcondition_path_selection.c";

spec enum WriteShape {
    Skip,
    At(int32),
}

spec enum WriteOutcome {
    Skipped,
    Written(int32),
}

function selected_index(shape: WriteShape) -> int32 {
    match shape {
        WriteShape::Skip => 0,
        WriteShape::At(index) => index,
    }
}

resource write_input(cells: int32*, index: int32, enabled: int32) {
    field shape: WriteShape;
    match shape {
        WriteShape::Skip => {
            owns cells[0..2];
            fact index == 0;
            fact enabled == 0;
        },
        WriteShape::At(position) => {
            owns cells[0..2];
            fact index == position;
            fact 0 <= position;
            fact position < 2;
            fact enabled == 1;
        },
    }
}

resource write_result(cells: int32*) {
    field model: WriteOutcome;
    match model {
        WriteOutcome::Skipped => {
            owns cells[0..2];
        },
        WriteOutcome::Written(position) => {
            owns cells[0..2];
            fact 0 <= position;
            fact position < 2;
            fact cells[position] == 1;
        },
    }
}

int32 write_selected(int32 cells[], int32 index, int32 enabled) {
    consumes before: write_input(cells, index, enabled);
    produces after: write_result(cells);
    ensures result == 0 or result == 1;
    ensures enabled == 0 implies after.model == WriteOutcome::Skipped;
    ensures enabled == 1 implies after.model == WriteOutcome::Written(
        selected_index(old(before.shape))
    );
    ensures selected_index(old(before.shape)) == index;
} by {
    match before.shape {
        WriteShape::Skip => {
            unfold(before);
            execute();
            let after = fold(write_result(cells), {
                model: WriteOutcome::Skipped
            });
            have result == 0 by { normalize(); }
            have result == 0 or result == 1 by { left(); }
            have after.model == WriteOutcome::Skipped by { assumption(); }
            have not (enabled == 1) by {
                rewrite(enabled == 0);
                normalize();
            }
            have selected_index(old(before.shape)) == index by {
                rewrite(old(before.shape) == WriteShape::Skip);
                unfold(selected_index(WriteShape::Skip));
                rewrite(index == 0);
                normalize();
            }
            have enabled == 0 implies after.model == WriteOutcome::Skipped by {
                intro();
                assumption();
            }
            have enabled == 1 implies after.model == WriteOutcome::Written(
                selected_index(old(before.shape))
            ) by {
                intro();
                contradiction(enabled == 1);
            }
            have enabled == 1 implies
                result == cells[selected_index(old(before.shape))] by {
                intro();
                contradiction(enabled == 1);
            }
            simp();
        },
        WriteShape::At(position) => {
            unfold(before);
            execute();
            let after = fold(write_result(cells), {
                model: WriteOutcome::Written(index)
            });
            have selected_index(old(before.shape)) == index by {
                rewrite(old(before.shape) == WriteShape::At(position));
                unfold(selected_index(WriteShape::At(position)));
                rewrite(index == position);
                normalize();
            }
            have enabled == 1 implies
                result == cells[selected_index(old(before.shape))] by {
                intro();
                normalize();
            }
            simp();
        },
    }
}
```

```expect
pass
```
