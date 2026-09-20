# a returned pointer reads across the caller's own locals

The ordinary shape: a function returns a pointer, the caller parks it in a
local, and reads through it. The verifier does not resolve that pointer, so
every store between the call and the read is a store the read has to be told
apart from — including the store of the pointer into `message`, and the store
to `guard`, both of which are the caller's own automatic objects that no
contract can say anything about.

Nothing in the sidecar mentions where `message` points, and no pointer
equality is stated anywhere. What frames the read is that neither `message`
nor `guard` is an object this program can form the address of, so no pointer
value designates either of them.

`string_literals_call.md` is the same shape with no second local;
`a_local_addressed_in_another_function_is_not_framed.md` is this program with
one `&guard` added elsewhere, which is enough to lose it.

```c filename=a_returned_pointer_reads_across_stores_to_caller_locals.c
uint8* literal_source() {
    return "ok";
}

int32 read_literal() {
    uint8* message;
    int32 guard;
    message = literal_source();
    guard = 3;
    return message[1] + guard;
}
```

```click
verifying "a_returned_pointer_reads_across_stores_to_caller_locals.c";

uint8* literal_source() {
    produces result[0..3];
    ensures result[0] == 'o';
    ensures result[1] == 'k';
    ensures result[2] == '\0';
} by {
    execute();
    simp();
}

int32 read_literal() {
    ensures result == 'k' + 3;
} by {
    execute();
    simp();
}
```

```expect
pass
```
