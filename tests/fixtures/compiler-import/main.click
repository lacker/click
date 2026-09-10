verifying "main.c";

int32 from_header() {
    ensures result == 15;
} by {
    execute();
    simp();
}

int32 answer() {
    ensures result == 15;
} by {
    execute();
    simp();
}
