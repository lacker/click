# represented resource borrow invariant

This checks the intended baseline pattern for learning an invariant from a
represented resource while returning that resource to the caller.

```c filename=inspect_server.c
int32 inspect_server(int32 fd, int32 state[]) {
    return 0;
}
```

```click
affine resource socket_open(fd: int32);

affine resource live_server(fd: int32, state: int32*) {
    contains socket_open(fd);
    contains write(state[0..1]);
    invariant state[0] == 1;
}

verifying "inspect_server.c";

int32 inspect_server(int32 fd, int32 state[]) {
    requires live_server(fd, state);

    ensures live_server(fd, state) by {
        open(live_server(fd, state));
        symbolic_execute();
        close(live_server(fd, state));
    }

    ensures state_is_ready: state[0] == 1 by {
        open(live_server(fd, state));
        symbolic_execute();
        close(live_server(fd, state));
        simp();
    }
}
```

```expect
pass
```
