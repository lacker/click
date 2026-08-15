# composite resource composes abstract resources

This checks that a composite resource can bundle an abstract resource with
memory permission and a fact.

```c filename=init_server.c
int32 init_server(int32 fd, int32 state[]) {
    state[0] = 1;
    return 0;
}
```

```c filename=use_server.c
int32 use_server(int32 fd, int32 state[]) {
    if (state[0] == 1) {
        return fd;
    } else {
        return 0;
    }
}
```

```click
abstract resource socket_open(fd: int32);

resource live_server(fd: int32, state: int32*) {
    contains socket_open(fd);
    owns state[0..1];
    fact state[0] == 1;
}

verifying "init_server.c";
verifying "use_server.c";

int32 init_server(int32 fd, int32 state[]) {
    consumes socket_open(fd);
    consumes state[0..1];

    produces live_server(fd, state) by {
        execute();
        fold(live_server(fd, state));
    }
}

int32 use_server(int32 fd, int32 state[]) {
    consumes live_server(fd, state);

    ensures result == fd by {
        unfold(live_server(fd, state));
        execute();
        fold(live_server(fd, state));
        simp();
    }
}
```

```expect
pass
```
