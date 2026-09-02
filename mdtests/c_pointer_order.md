# relational comparison orders pointers within one array

Pointers into one array, including its one-past endpoint, may be compared by
their element order.

```c filename=c_pointer_order.c
int32 pointer_before(int32 data[], int32 n) {
    int32* end;
    end = data + n;
    return data < end;
}
```

```click
verifying "c_pointer_order.c";

int32 pointer_before(int32 data[], int32 n) {
    requires 1 <= n;
    views data[0..n];
    ensures result == 1 by auto;
}
```

```expect
pass
```
