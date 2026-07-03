# composite resource borrow fact

This checks the intended baseline pattern for learning a fact from a
composite resource while returning that resource to the caller.

```c filename=inspect_server.c
int32 inspect_server(int32 fd, int32 state[]) {
    return 0;
}
```

```click
resource socket_open(fd: int32);

resource live_server(fd: int32, state: int32*) {
    contains socket_open(fd);
    contains write(state[0..1]);
    fact state[0] == 1;
}

verifying "inspect_server.c";

int32 inspect_server(int32 fd, int32 state[]) {
    requires live_server(fd, state);

    ensures live_server(fd, state) by {
        unpack(live_server(fd, state));
        symbolic_execute();
        pack(live_server(fd, state));
    }

    ensures state_is_ready: state[0] == 1 by {
        unpack(live_server(fd, state));
        symbolic_execute();
        pack(live_server(fd, state));
        simp();
    }
}
```

```expect
pass
```
