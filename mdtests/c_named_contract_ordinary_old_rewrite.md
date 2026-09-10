# Ordinary refinement proofs can rewrite current and old cell values

```click
contract void Source(int32* cells) {
    owns cells[0..2];
    ensures [cells[0], cells[1]] == old([cells[1], cells[0]]);
}

contract void Target(int32* cells) {
    owns cells[0..2];
    ensures cells[0] >= old(cells[1]);
}

theorem lift(callback: void (*)(int32*)) {
    requires Source(callback);
    ensures Target(callback) by {
        unfold(Source);
        unfold(Target);
        have cells[0] == old(cells[1]) implies cells[0] >= old(cells[1]) by {
            intro();
            rewrite(cells[0] == old(cells[1]));
            simp();
        }
        simp();
    }
}
```

```expect
pass
```
