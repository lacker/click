verifying "alias.c";

int alias_write(int *p, const int *q) {
    owns p[0..1];
    views q[0..1];
    requires p == q;
    ensures result == 7;
} by {
    execute();
    simp();
}
