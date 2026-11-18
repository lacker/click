verifying "hello.c";
import click::c::stdio::{stream, write_requests};

function greeting() -> List<uint8> {
    List::Cons('h', List::Cons('e', List::Cons('l', List::Cons('l',
    List::Cons('o', List::Cons(',', List::Cons(' ', List::Cons('w',
    List::Cons('o', List::Cons('r', List::Cons('l', List::Cons('d',
    List::Cons('\n', List::Nil)))))))))))))
}

int32 main() {
    owns out: stream(stdout);
    ensures write_requests(out.write_history) == List::Cons(greeting(), List::Nil);
} by {
    unfold(greeting());
    unfold(write_requests(List<WriteAttempt>::Nil));
}
