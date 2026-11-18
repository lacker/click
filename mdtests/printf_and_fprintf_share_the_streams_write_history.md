# A literal printf and a modular fprintf through a FILE pointer share one history

```c filename=greeting.c
#include <stdio.h>

int print_percent(FILE *file)
{
    return fprintf(file, "%%");
}

int main(void)
{
    FILE *file = stdout;
    printf("a" "\0ignored");
    print_percent(file);
}
```

```click
verifying "greeting.c";
import click::c::stdio::{stream, write_requests};

theorem prepend_write(bytes: List<uint8>, status: int32, history: List<WriteAttempt>) {
    ensures write_requests(List::Cons(WriteAttempt::Attempt(bytes, status), history))
        == List::Cons(bytes, write_requests(history)) by {
        unfold(write_requests(List::Cons(WriteAttempt::Attempt(bytes, status), history)));
        normalize();
    }
}

int32 print_percent(FILE* file) {
    owns out: stream(file);
    ensures result == 1 or result < 0;
    ensures out.write_history == List::Cons(
        WriteAttempt::Attempt(List::Cons('%', List::Nil), result),
        old(out.write_history));
    ensures write_requests(out.write_history)
        == List::Cons(List::Cons('%', List::Nil), old(write_requests(out.write_history)));
}

int32 main() {
    owns out: stream(stdout);
    ensures result == 0;
    ensures write_requests(out.write_history) == List::Cons(
        List::Cons('%', List::Nil),
        List::Cons(List::Cons('a', List::Nil), List::Nil));
} by {
    unfold(write_requests(List<WriteAttempt>::Nil));
}
```

```expect
pass
```
