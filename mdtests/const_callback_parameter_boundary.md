# Click cannot erase a callback parameter's pointee qualification

```c filename=main.c
int ignore(const int *(*f)(const int *)) { return 0; }
```

```click
verifying "main.c";
int ignore(const int *(*f)(int *)) { ensures result == 0; }
```

```expect
fail: signature mismatch
```
