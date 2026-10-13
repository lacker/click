# A block-scope function declaration is not visible after its block

The call after the block names a function no visible declaration or definition provides.

```c filename=c_block_scope_function_declaration_ends_with_its_block.c
int32 run(int32 value) {
    if (value) {
        __attribute__((__noreturn__)) extern void __compiletime_assert_1(void) __attribute__((__error__("Unsupported access size.")));
    }
    __compiletime_assert_1();
    return value;
}
```

```click
verifying "c_block_scope_function_declaration_ends_with_its_block.c";

int32 run(int32 value) {
    ensures result == value by auto;
}
```

```expect
fail: unknown function `__compiletime_assert_1`: no verified source defines it and the sidecar declares no contract for it; describe an implementation outside the verified sources with an `extern` contract
```
