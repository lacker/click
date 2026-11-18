# A borrowed C string decides its signed char terminator comparison

```c filename=terminator.c
int terminator(const char *src, uint64 n) {
    return src[n] == '\0';
}
```

```click
import click::c::string;
target "x86_64-unknown-linux-gnu";
verifying "terminator.c";
int32 terminator(const char* src, uint64 n) {
    views cstr_at(src, n);
    ensures result == 1;
} by {
    open(cstr_at(src, n)) {
    }
}
```

```expect
pass
```
