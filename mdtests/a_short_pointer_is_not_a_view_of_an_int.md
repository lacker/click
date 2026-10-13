# A `short *` is not a view of an `int`

The signedness conversion is between integer types of one width. A cast from
`int *` to `short *` retypes the object, which Click does not support.

```c filename=a_short_pointer_is_not_a_view_of_an_int.c
int f(void) {
    int x = 0;
    short *q = (short *)&x;
    return *q;
}
```

```click
verifying "a_short_pointer_is_not_a_view_of_an_int.c";

int32 f() { ensures result == 0 by auto; }
```

```expect
fail: retyping object-pointer casts are unsupported; expected `int16 *`, got `int32 *`
```
