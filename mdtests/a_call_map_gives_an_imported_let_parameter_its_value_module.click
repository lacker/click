import click::c::string;
extern uint64 measure(const char* s) {
    let n: uint64;
    views cstr_at(s, n);
    ensures result == n;
}
