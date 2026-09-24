verifying "rep_copy.c";
verifying "rep_copy_symbolic.c";
verifying "use_copy.c";

int f() {
    ensures result == 18 or result == -1;
} by {
    execute();
    simp();
}

int32 g(uint32 tag, int32 *p, int32 **restored) {
    views p[0..1];
    owns restored[0..1];
    requires tag <= 1000;
    requires 0 <= p[0];
    requires p[0] <= 1000;
    ensures result == -1 or result == tag + p[0];
    ensures result == -1 or restored[0] == p;
} by {
    execute();
    simp();
}

int use_copy() {
    ensures result == 18 or result == 0;
} by {
    step();
    step();
    if copied == 18 {
        execute();
        simp();
    } else {
        have copied == -1 by {
            cases (copied == 18 or copied == -1) {
                contradiction(copied == 18);
            } {
                assumption();
            }
        }
        execute();
        simp();
    }
}
