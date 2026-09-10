# Sequence callback refinement: wrong permutation

```click
contract void Source(int32* cells) {
    owns cells[0..2];
    ensures [cells[0], cells[1]] == old([cells[1], cells[0]]);
}

contract void Target(int32* cells) {
    owns cells[0..2];
    ensures [cells[0], cells[1]] == old([cells[0], cells[1]]);
}

theorem transport(callback: void (*)(int32*)) {
    requires Source(callback);
    ensures Target(callback) by {
        unfold(Source);
        unfold(Target);
        simp();
    }
}
```

```expect
fail: contract-refinement proof does not establish `Target(callback)`
```
