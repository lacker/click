# pointer parameters may alias without separate

Different pointer parameters are modeled like C pointers: they can refer to
overlapping memory unless the contract says otherwise. This test intentionally
omits `separate(memory(dst[0..1]), memory(src[0..1]))`, so Click must reject the claim that a
write through `dst` preserves `src[0]`.

`src` is read under a bare `viewable(...)` requirement and has no resource
clause of its own, which is what "the contract says otherwise" means here: a
`views src[0..1]` clause beside the transferred `consumes dst[0..1]` *would*
say it, because a contract's transferred and borrowed clauses denote disjoint
memory (`docs/internals/resource-tracker.md`, "The entry partition"). That is
the companion `a_views_clause_is_separate_from_an_owns_clause.md`; a caller
that tries to satisfy both clauses with one range is refused at the call
(`a_caller_cannot_lend_and_transfer_one_range.md`).

```c filename=pointer_params_may_alias_without_separate.c
int32 clobber_dst(int32* dst, int32* src) {
    dst[0] = 1;
    return src[0];
}
```

```click
verifying "pointer_params_may_alias_without_separate.c";

int32 clobber_dst(int32* dst, int32* src) {
    consumes dst[0..1];
    requires viewable(src[0..1]);

    ensures source_unchanged: src[0] == old(src[0]) by auto;
}
```

```expect
fail: clobber_dst.source_unchanged
```
