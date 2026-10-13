# a call owes an inline helper's precondition

`add_one`'s body is safe for every argument below the int32 maximum, but its
contract asks for `value < 100`. With a contract, a call applies the contract,
not the body, so `run` owes that precondition at the call, and `run`'s own
`value < 200` does not establish it. Before inline helpers applied their
contracts, the body ran at the call site and this was accepted.

The caller is listed before the helper, so this also pins that the contract
is in force whichever function the sidecar verifies first.

```c filename=include/add.h
#ifndef ADD_H
#define ADD_H
static inline int32 add_one(int32 value) {
    return value + 1;
}
#endif
```

```c filename=inline_helper_contract_precondition_is_owed_at_the_call.c
#include "include/add.h"

int32 run(int32 value) {
    return add_one(value);
}
```

```click
verifying "inline_helper_contract_precondition_is_owed_at_the_call.c";

int32 run(int32 value) {
    requires value < 200;
    ensures result == value + 1;
} by {
    execute();
    simp();
}

int32 add_one(int32 value) {
    requires value < 100;
    ensures result == value + 1;
} by {
    execute();
    simp();
}
```

```expect
fail: precondition clause 1 of `add_one#inline:inline_helper_contract_precondition_is_owed_at_the_call.c`
```
