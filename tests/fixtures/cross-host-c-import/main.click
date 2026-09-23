target "x86_64-linux-userspace";
verifying "main.c";

int answer() {
    ensures result == 42;
} by {
    execute();
    simp();
}
