# copy3 verifies a small array-copy loop

This is a compact launch-shaped example: two array parameters, a fixed pointer
loop, reads from source memory, writes to destination memory, explicit
source/destination separation, loop invariants, and `old(...)`
postconditions.

```c filename=copy3.c
int32 copy3(int32 dst[3], int32 src[3]) {
    int32 i;
    i = 0;
    while (i < 3) {
        dst[i] = src[i];
        i = i + 1;
    }
    return dst[2];
}
```

```click
verifying "copy3.c";

int32 copy3(int32 dst[3], int32 src[3]) {
    requires loadable(dst[0..3]);
    requires loadable(src[0..3]);
    consumes dst[0..3];
    views src[0..3];
    requires separate(memory(dst[0..3]), memory(src[0..3]));
    ensures copies_first: dst[0] == old(src[0]);
    ensures copies_second: dst[1] == old(src[1]);
    ensures copies_third: dst[2] == old(src[2]);
    ensures returns_third: result == old(src[2]);
} by {
    step();
    step();
    loop {
        invariant i >= 0 and i <= 3;
        invariant forall (k: int32) {
            0 <= k and k < 3 implies src[k] == old(src[k])
        };
        invariant forall (k: int32) {
            0 <= k and k < i implies dst[k] == old(src[k])
        };
        mutable dst[0..3] by frame;

        initialize by simp;
        preserve by {
            step();
            step();
            simp();
        }
    }
    have dst[0] == old(src[0]) by simp;
    have dst[1] == old(src[1]) by simp;
    have dst[2] == old(src[2]) by simp;
    step();
    simp();
}
```

```expect
pass
```
