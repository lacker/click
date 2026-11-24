# A struct-pointer local spells its pointee's fields

`read_second` takes its record as `void *` and reads it through a
`struct box *` local, as a thread entry point does. A proof failure while
`box` is live names the record's fields through that local: `box->second`,
the way a declared `struct box *` parameter is spelled, not `box[1]`, which
would be the second record.

```c filename=box.c
struct box { int first; int second; };

int read_second(void *argument) {
    struct box *box = argument;
    return box->second;
}
```

```click
target "x86_64-unknown-linux-gnu";
verifying "box.c";

int read_second(void *argument) {
    views (argument as (struct box *))->second;
    requires 0 < (argument as (struct box *))->second;
    ensures 0 < result;
} by {
    step();
    step();
    have 1 < box->second by {
        close();
    }
}
```

```expect
fail: goal: 1 < old(box->second)
```
