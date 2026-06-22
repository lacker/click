# uint8 character literals

This checks that C0 and Click contracts can use ASCII character literals as
`uint8` values.

```c filename=uint8_literals.c
uint8 uint8_literal() {
    return 'n';
}
```

```click
verifying "uint8_literals.c";

uint8 uint8_literal() {
    ensures returns_literal: result == 'n' by auto;
}
```

```expect
pass
```
