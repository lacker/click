# A conjunction guarding domains past the supported length is refused

The right side of `and` is read only where its left side holds, so each
evaluation domain a later conjunct owes is guarded by every conjunct before
it. Those guards grow with the square of the chain's length, so a conjunction
that owes domains under more than 64 earlier conjuncts is refused as
unsupported instead of being lowered slowly. Here each
`defined((x + k) + 1)` owes the domain of its operand `x + k`, so the 66th
conjunct's owes it under 65 earlier conjuncts.

```click
theorem long_chain(x: int32) {
    requires defined((x + 1) + 1) and defined((x + 2) + 1) and defined((x + 3) + 1) and defined((x + 4) + 1) and defined((x + 5) + 1) and defined((x + 6) + 1) and defined((x + 7) + 1) and defined((x + 8) + 1) and defined((x + 9) + 1) and defined((x + 10) + 1) and defined((x + 11) + 1) and defined((x + 12) + 1) and defined((x + 13) + 1) and defined((x + 14) + 1) and defined((x + 15) + 1) and defined((x + 16) + 1) and defined((x + 17) + 1) and defined((x + 18) + 1) and defined((x + 19) + 1) and defined((x + 20) + 1) and defined((x + 21) + 1) and defined((x + 22) + 1) and defined((x + 23) + 1) and defined((x + 24) + 1) and defined((x + 25) + 1) and defined((x + 26) + 1) and defined((x + 27) + 1) and defined((x + 28) + 1) and defined((x + 29) + 1) and defined((x + 30) + 1) and defined((x + 31) + 1) and defined((x + 32) + 1) and defined((x + 33) + 1) and defined((x + 34) + 1) and defined((x + 35) + 1) and defined((x + 36) + 1) and defined((x + 37) + 1) and defined((x + 38) + 1) and defined((x + 39) + 1) and defined((x + 40) + 1) and defined((x + 41) + 1) and defined((x + 42) + 1) and defined((x + 43) + 1) and defined((x + 44) + 1) and defined((x + 45) + 1) and defined((x + 46) + 1) and defined((x + 47) + 1) and defined((x + 48) + 1) and defined((x + 49) + 1) and defined((x + 50) + 1) and defined((x + 51) + 1) and defined((x + 52) + 1) and defined((x + 53) + 1) and defined((x + 54) + 1) and defined((x + 55) + 1) and defined((x + 56) + 1) and defined((x + 57) + 1) and defined((x + 58) + 1) and defined((x + 59) + 1) and defined((x + 60) + 1) and defined((x + 61) + 1) and defined((x + 62) + 1) and defined((x + 63) + 1) and defined((x + 64) + 1) and defined((x + 65) + 1) and defined((x + 66) + 1);
    ensures 1 == 1 by close();
}
```

```expect
fail: unsupported: a conjunction reads a side that owes evaluation domains under more than 64 earlier conjuncts
```
