# opaque contracts carry resource propositions

This checks that `separate`, `contains`, and `loadable` are ordinary
state-indexed propositions in an opaque function summary.

```c filename=summarize_resources.c
int32 summarize_resources(int32* p, int32* q) {
    return 0;
}
```

```c filename=use_resource_summary.c
int32 use_resource_summary(int32* p, int32* q) {
    int32 result;
    result = summarize_resources(p, q);
    return result;
}
```

```click
verifying "summarize_resources.c";
verifying "use_resource_summary.c";

int32 summarize_resources(int32* p, int32* q) {
    requires separate(memory(p[0..1]), memory(q[0..1]));
    requires contains(memory(p[0..2]), memory(p[0..1]));
    requires loadable(p[0..1]);

    ensures keeps_separate: separate(memory(p[0..1]), memory(q[0..1])) by auto;
    ensures keeps_containment: contains(memory(p[0..2]), memory(p[0..1])) by auto;
    ensures keeps_loadable: loadable(p[0..1]) by auto;
    ensures returns_zero: result == 0 by auto;
}

int32 use_resource_summary(int32* p, int32* q) {
    requires separate(memory(p[0..1]), memory(q[0..1]));
    requires contains(memory(p[0..2]), memory(p[0..1]));
    requires loadable(p[0..1]);

    ensures keeps_separate: separate(memory(p[0..1]), memory(q[0..1])) by auto;
    ensures keeps_containment: contains(memory(p[0..2]), memory(p[0..1])) by auto;
    ensures keeps_loadable: loadable(p[0..1]) by auto;
    ensures returns_zero: result == 0 by auto;
}
```

```expect
pass
```
