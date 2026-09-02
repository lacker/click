# subtraction returns an array element distance

Subtracting two pointers into one array returns their signed element
distance.

```c filename=c_pointer_distance.c
int32 pointer_distance(int32 data[], int32 n) {
    int32* end;
    end = data + n;
    return end - data;
}
```

```click
verifying "c_pointer_distance.c";

int32 pointer_distance(int32 data[], int32 n) {
    requires 0 <= n;
    views data[0..n];
    ensures result == n by auto;
}
```

```expect
pass
```
