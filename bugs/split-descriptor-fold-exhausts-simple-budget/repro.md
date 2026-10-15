# Split descriptor fields retain backing-write frame evidence

The program appends an element, increments its length, and writes the new zero
terminator through the reloaded backing pointer. Its contract owns each
descriptor field separately and keeps descriptor/backing separation explicit.
The proof states the nonnegative append index and the stored-value facts.

```c filename=owned_string_push.c
struct owned_string {
    int32 len;
    int32 cap;
    int32* data;
};

int32 owned_string_push(struct owned_string* owner, int32 value) {
    int32 index;
    index = owner->len;
    owner->data[index] = value;
    owner->len = index + 1;
    owner->data[index + 1] = 0;
    return owner->len;
}
```

```click
verifying "owned_string_push.c";
predicate terminated_at(data: int32[], length: int32) {
    data[length] == 0
}

resource owned_string(owner: struct owned_string*) {
    owns owner->len;
    owns owner->cap;
    owns owner->data;
    owns owner->data[0..owner->cap];
    fact 0 <= owner->len;
    fact owner->len < owner->cap;
    fact terminated_at(owner->data, owner->len);
    fact separate(
        memory(*owner),
        memory(owner->data[0..owner->cap])
    );
}



int32 owned_string_push(struct owned_string* owner, int32 value) {
    requires owner->len + 1 < owner->cap;
    owns owned_string(owner);
    ensures result == old(owner->len) + 1;
    ensures owner->len == old(owner->len) + 1;
    ensures owner->cap == old(owner->cap);
    ensures owner->data == old(owner->data);
    ensures owner->data[old(owner->len)] == value;
    ensures owner->data[owner->len] == 0;
} by {
    unfold(owned_string(owner));
    step();
    step();
    step();
    step();
    step();
    have owner->len == at(statement(4).entry, (index + 1)) by auto;
    step();
    have 0 <= old(owner->len) + 1 by auto;
    have owner->data == old(owner->data) by {
        simp();
    }
    have terminated_at(owner->data, owner->len) by {
        unfold(terminated_at);
        simp();
    }
    have owner->data[old(owner->len)] == value by {
        simp();
    }
    have owner->data[owner->len] == 0 by {
        unfold(terminated_at);
        assumption();
    }
    fold(owned_string(owner));
    have owner->len == (old(owner->len) + 1) by {
        rewrite(owner->len == at(statement(3).entry, (index + 1)));
        assumption();
    }
    assumption();
    assumption();
    assumption();
    assumption();
    assumption();
    assumption();
    assumption();
}

```

```expect
pass
```
