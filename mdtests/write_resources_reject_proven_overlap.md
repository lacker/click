# write resources reject proven overlap

This checks that Click rejects a resource context with two write resources that
are provably overlapping.

```c filename=duplicate_write.c
int32 duplicate_write(int32* p) {
    return p[0];
}
```

```click
verifying "duplicate_write.c";

int32 duplicate_write(int32* p) {
    consumes p[0..1];
    consumes p[0..1];

    ensures result == old(p[0]) by auto;
}
```

```expect
fail: overlapping write resource facts
```
