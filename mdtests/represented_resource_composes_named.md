# represented resource composes named resources

This checks that a represented resource can bundle another named affine
resource with memory permission and an invariant.

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
affine resource socket_open(fd: int32);

affine resource live_server(fd: int32, state: int32*) {
    contains socket_open(fd);
    contains write(state[0..1]);
    invariant state[0] == 1;
}

verifying "init_server.c";
verifying "use_server.c";

int32 init_server(int32 fd, int32 state[]) {
    requires socket_open(fd);
    requires write(state[0..1]);

    ensures live_server(fd, state) by {
        symbolic_execute();
        close(live_server(fd, state));
    }
}

int32 use_server(int32 fd, int32 state[]) {
    requires live_server(fd, state);

    ensures result == fd by {
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
