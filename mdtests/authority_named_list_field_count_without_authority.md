# Counting List-valued members still requires exposed authority

```c filename=list_field_helper.c
void bump(int32* pool, int32* p) { p[0] = 7; }
int32 run() {
    int32 pool = 0;
    int32* p = malloc(8);
    if (p == 0) return 0;
    p[0] = 1;
    p[1] = 2;
    bump(&pool, p);
    int32 result = p[0] + p[1];
    free(p);
    return result;
}
```

```click
authorized resource ticket(pool: int32*, p: int32*) {
    field model: List<int32>;
    owns p[0..1];
}
resource control(pool: int32*) { owns authority(ticket(pool, _)); }
verifying "list_field_helper.c";
void bump(int32* pool, int32* p) {
    owns member: ticket(pool, p);
    ensures member.model == old(member.model);
    ensures p[0] == 7;
} by { unfold(member); step(); fold(member); step_until(function.exit); close(); }
int32 run() { ensures result == 0 or result == 9; } by {
    step(); step(); step(); step();
    branch { true => { step_until(function.exit); close(); } false => {} }
    step(); step();
    fold(authority(ticket(&pool, _)));
    let first = fold(ticket(&pool, p), { model: List<int32>::Cons(1, List<int32>::Nil) });
    let second = fold(ticket(&pool, p + 1), { model: List<int32>::Cons(2, List<int32>::Nil) });
    fold(control(&pool));
    step(bump, { member: first });
    have first.model == List<int32>::Cons(1, List<int32>::Nil) by close();
    have second.model == List<int32>::Cons(2, List<int32>::Nil) by close();
    have count(ticket(&pool, _)) == 2 by close();
    unfold(first); unfold(second);
    unfold(authority(ticket(&pool, _)));
    step_until(function.exit); close();
}
```

```expect
fail: count(...) requires owning authority for that population
```
