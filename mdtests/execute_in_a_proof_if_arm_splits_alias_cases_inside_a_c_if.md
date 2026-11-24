# The implicit tail in a proof `if` arm splits alias cases inside a C `if`

The buffer write either overwrites cell zero or preserves it. The proof splits
that alias case explicitly and uses element separation plus a transport
certificate in the preserving arm. Both paths then execute the nested C `if`
and return, without recovering cell zero's value from older stores.

```c filename=execute_in_a_proof_if_arm_splits_alias_cases_inside_a_c_if.c
int32 f(int32 u, int32 w) {
    int32 r;
    int32* buf;
    buf = malloc(16);
    if (buf == 0) {
        return 0;
    }
    buf[0] = 3;
    buf[u] = 7;
    r = 1;
    if (w > 0) {
        r = buf[0];
    }
    free(buf);
    return r;
}
```

```click
import click::separation;
verifying "execute_in_a_proof_if_arm_splits_alias_cases_inside_a_c_if.c";

int32 f(int32 u, int32 w) {
    requires 0 <= u;
    requires u < 4;
    ensures result == 0 or result == 1 or result == 3 or result == 7;
} by {
    step();
    step();
    step();
    if buf == 0 {
    } else {
        step_until(statement(5).entry);
        have buf[0] == 3 by close();
        mark before_store;
        step();
        if u == 0 {
            if w > 0 { step_until(function.exit); } else { step_until(function.exit); }
        } else {
            have 1 <= u by { close() using { u != 0; 0 <= u; }; }
            have separate(memory(buf[1]), memory(buf[0])) by { apply(separation::separate_elements(buf, 1 as uint64, 0 as uint64)); }
            have separate(memory(buf[2]), memory(buf[0])) by { apply(separation::separate_elements(buf, 2 as uint64, 0 as uint64)); }
            have separate(memory(buf[3]), memory(buf[0])) by { apply(separation::separate_elements(buf, 3 as uint64, 0 as uint64)); }
            have separate(memory(buf[u]), memory(buf[0])) by {
                if u == 1 {
                    rewrite(u, 1); close();
                } else {
                    if u == 2 {
                        rewrite(u, 2); close();
                    } else {
                        have u == 3 by { close() using { 1 <= u; u < 4; u != 1; u != 2; }; }
                        rewrite(u, 3); close();
                    }
                }
            }
            have separate(statement(5).footprint, memory(buf[0])) by {
                close() using { separate(memory(buf[u]), memory(buf[0])); };
            }
            have buf[0] == at(before_store, buf[0]) by {
                preserve(memory(buf[0]), statement(5));
            }
            have buf[0] == 3 by {
                rewrite(buf[0], at(before_store, buf[0]));
                close();
            }
            if w > 0 { step_until(function.exit); } else { step_until(function.exit); }
        }
    }
}
```

```expect
pass
```
