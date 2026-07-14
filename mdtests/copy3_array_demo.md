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
    requires loadable(dst, 12);
    requires loadable(src, 12);
    requires write(dst[0..3]);
    requires read(src[0..3]);
    requires separate(memory(dst[0..3]), memory(src[0..3]));

    for loop(0) {
        invariant i >= 0;
        invariant i <= 3;
    }

    ensures copies_first: dst[0] == old(src[0]) by auto;
    ensures copies_second: dst[1] == old(src[1]) by auto;
    ensures copies_third: dst[2] == old(src[2]) by auto;
    ensures returns_third: result == old(src[2]) by auto;
}
```

```expect
pass
```
