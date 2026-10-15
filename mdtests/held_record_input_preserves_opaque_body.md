# A held record promise does not reopen unrelated body ranges

The function preserves an opaque resource and reads no descriptor fields. Its
record carrier is the parameter itself. Rechecking that carrier must not demand
permission to evaluate the separate nested backing-pointer expression in the
resource body. A carrier that actually needs a body read must still establish
that read through the checked immediate body.

```c filename=probe.c
struct arena { int32* data; };
struct region { struct arena* arena; int32 start; int32 end; };
int32 idle(struct region* region) { return 0; }
```

```click
resource region_body(region: struct region*) {
    field start: int32;
    field end: int32;
    owns *region;
    owns region->arena->data[start..end];
    fact region->start == start;
    fact region->end == end;
    fact 0 <= start;
    fact start < end;
}
verifying "probe.c";
int32 idle(struct region* region) {
    owns r: region_body(region);
    ensures result == 0;
    ensures r.start == old(r.start);
    ensures r.end == old(r.end);
} by {
    execute();
}
```

```expect
pass
```
