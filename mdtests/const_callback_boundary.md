# A Click callback signature cannot omit the C return qualifier

```c filename=main.c
int ignore(const int *(*f)(int *)) { return 0; }
```

```click
verifying "main.c";
int ignore(int *(*f)(int *)) { ensures result == 0; } by { execute(); simp(); }
```

```expect
fail: signature mismatch
```
