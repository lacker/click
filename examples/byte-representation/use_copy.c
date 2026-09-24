int f(void);

int use_copy(void) {
    int copied = f();
    if (copied < 0) {
        return 0;
    }
    return copied;
}
