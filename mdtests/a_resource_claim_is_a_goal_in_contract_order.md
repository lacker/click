# A resource claim is a goal in contract order

`owns p[0..1]` claims that the function still holds the cell at exit. Like an
`ensures`, it is a goal, in the order the contract writes it: here it comes
first, so a `normalize()` written for `result == 7` acts on it instead and is
refused. `close()` closes a resource goal whose instance the path holds
(`closers_after_execution_close_a_resource_goal_first.md`).

```c filename=a_resource_claim_is_a_goal_in_contract_order.c
int32 g(int32 p[]) {
    return 7;
}
```

```click
verifying "a_resource_claim_is_a_goal_in_contract_order.c";

int32 g(int32 p[]) {
    owns p[0..1];
    ensures result == 7;
} by {
    step_until(function.exit);
    normalize();
}
```

```expect
fail: `normalize` did not prove the current goal `owns p[0..1]`
```
