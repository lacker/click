# Refcount Ownership Design Fixture

This directory is a design fixture, not a verified mdtest. It isolates the
ownership question from json-c parsing, strings, allocation, and object variants.

Current Click can prove field reads, field writes, and old-to-new refcount
arithmetic for `examples/jsonc-refcount/`. It cannot yet express the
ghost state needed to prove that a caller owns one reference, that `rc_get`
creates another reference, or that `rc_put` removes one.

## Sample C Shape

The source shape is intentionally tiny:

```c
struct rc_object {
    int32 ref_count;
};

struct rc_object* rc_get(struct rc_object* obj) {
    obj->ref_count = obj->ref_count + 1;
    return obj;
}

int32 rc_put(struct rc_object* obj) {
    obj->ref_count = obj->ref_count - 1;
    if (obj->ref_count == 0) {
        return 1;
    } else {
        return 0;
    }
}
```

The first ownership client we should eventually reject is a double release:

```c
int32 rc_double_put_bad(struct rc_object* obj) {
    int32 first;
    first = rc_put(obj);
    return rc_put(obj);
}
```

## Desired Proof Behavior

A clean ownership model should make these statements expressible:

- `rc_get` preserves object liveness and adds one caller-held reference.
- `rc_put` removes one caller-held reference.
- If `rc_put` removes the final reference, the object stops being live.
- A second `rc_put` without an intervening `rc_get` cannot satisfy the
  precondition.
- Mentioning an ownership fact in a proof does not consume it; only modeled
  state transitions change which ownership facts are true.

## Open Representation Question

The fixture is meant to force one design choice:

- Token model: each owned reference is a ghost token associated with an object.
- Multiplicity model: the proof state stores a ghost count of caller-held
  references per object.

A plain boolean predicate such as `has_ref(obj)` is probably too weak, because
it cannot distinguish one held reference from two held references. The next
language design pass should make one of these representations feel like normal
state-indexed facts rather than special "facts that get consumed."
