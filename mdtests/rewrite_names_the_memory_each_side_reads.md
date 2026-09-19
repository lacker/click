# a refused rewrite says which memory each side reads

`old(a[m])` and `a[m]` are the same address in two states, so the source
spelling of both is the same read and the two lines that name them say nothing
on their own. The refusal notices that its two sides spell alike, and adds the
rendering that labels the memory each one reads — which is the whole reason the
rewrite found nothing to replace.

```c filename=rewrite_names_the_memory_each_side_reads.c
void mark_one(int32 a[], int32 n, int32 i, int32 m) {
    a[i] = 1;
}
```

```click
verifying "rewrite_names_the_memory_each_side_reads.c";

void mark_one(int32 a[], int32 n, int32 i, int32 m) {
    requires 0 <= i;
    requires i < n;
    requires 0 <= m;
    requires m < n;
    requires n <= 1073741823;
    requires loadable(a[0..n]);
    requires a[m] == 5;
    consumes a[0..n];
    produces a[0..n];
} by {
    step();
    have a[m] == 5 by {
        rewrite(old(a[m]) == 5);
        assumption();
    }
    execute();
    simp();
}
```

```expect
fail: the two spell alike but are different propositions; with each memory labelled they read
```
