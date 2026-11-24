# A call cannot borrow a view from an iterated owner it also transfers

`keep` preserves an independently held view across both calls to `touch`.
Its caller `root` asks to borrow the same cell it transfers inside the
iterated owner, so the call is refused for missing stable view backing.

```c filename=iterated_view_conflict.c
void touch(int32* flags, int32* data, int32 n) {
    data[0] = 1;
}

int32 keep(int32* flags, int32* data, int32 n, int32* b) {
    touch(flags, data, n);
    touch(flags, data, n);
    return *b;
}
int32 root(int32* flags, int32* b) {
    return keep(flags, b, 1, b);
}
```

```click
resource cells(flags: int32*, data: int32*, n: int32) {
    owns flags[0..n];
    forall (k: int32) where 0 <= k and k < n {
        if flags[k] == 0 {
            owns data[k..k + 1];
        }
    }
}

verifying "iterated_view_conflict.c";

void touch(int32* flags, int32* data, int32 n) {
    owns cells(flags, data, n);
    requires n == 1;
    requires flags[0] == 0;
    ensures flags[0] == 0;
} by {
    unfold(cells(flags, data, n));
    unfold(cells(flags, data, n)[0]);
    step();
    have separate(memory(data[0]), memory(flags[0])) by { close(); }
    have separate(statement(0).footprint, memory(flags[0])) by {
        close();
    }
    have flags[0] == old(flags[0]) by {
        preserve(memory(flags[0]), statement(0));
    }
    have flags[0] == 0 by { close(); }
    fold(cells(flags, data, n)[0]);
    fold(cells(flags, data, n));
}

int32 keep(int32* flags, int32* data, int32 n, int32* b) {
    owns cells(flags, data, n);
    views *b;
    requires n == 1;
    requires flags[0] == 0;
    requires separate(memory(flags[0..n]), memory(*b));
    requires separate(memory(data[0..n]), memory(*b));
    ensures result == old(*b);
} by {
    step() {
        requires separate(memory(flags[0..n]), memory(*b)) by close();
        requires separate(memory(data[0..n]), memory(*b)) by close();
    }
    step() {
        requires separate(memory(flags[0..n]), memory(*b)) by close();
        requires separate(memory(data[0..n]), memory(*b)) by close();
    }
    have *b == old(*b) by { close(); }
}
int32 root(int32* flags, int32* b) {
    owns cells(flags, b, 1);
    requires flags[0] == 0;
    ensures result == old(*b);
}
```


```expect
fail: cannot supply `views b[0]` at this call
```
