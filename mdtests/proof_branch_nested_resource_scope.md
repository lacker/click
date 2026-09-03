# Resource scopes nested inside branch arms

Each proof branch arm may open the resource it needs while proving the
corresponding C arm. The scope closes before the branch joins, preserving the
owned composite resource for the shared continuation.

```c filename=branch_nested_resource_scope.c
int32 branch_nested_resource_scope(int32* p, int32 flag) {
    int32 result;
    if (flag != 0) {
        result = p[0];
    } else {
        result = p[0] + 1;
    }
    return result;
}
```

```click
resource bounded_cell(p: int32*) {
    owns p[0..1];
    fact p[0] >= 0;
    fact p[0] < 2147483647;
}

verifying "branch_nested_resource_scope.c";

int32 branch_nested_resource_scope(int32* p, int32 flag) {
    consumes bounded_cell(p);

    ensures result >= 0 by {
        step();
        branch {
            ensuring {
                fact result >= 0;
                owns bounded_cell(p);
            }
            then {
                open(bounded_cell(p)) {
                    step();
                    have result >= 0 by simp;
                }
            }
            else {
                open(bounded_cell(p)) {
                    step();
                    have result >= 0 by simp;
                }
            }
        }
        step();
        simp();
    }
}
```

```expect
pass
```
