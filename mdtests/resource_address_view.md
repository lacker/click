# An explicit address views a scalar object's storage

```c filename=address_view.c
int32 value = 7;
int32* current = &value;
int32 read() { return current[0]; }
```

```click
verifying "address_view.c";
int32 read() {
    views &current;
    views current[0..1];
    ensures result == current[0];
} by { execute(); simp(); }
```

```expect
pass
```
