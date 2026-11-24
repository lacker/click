verifying "span-probe.cpp";

void fill(uint8* p) {
    consumes uninitialized(p[0..4]);
    produces p[0..4];
    ensures p[0] == 120u8;
    ensures p[1] == 86u8;
    ensures p[2] == 52u8;
    ensures p[3] == 18u8;
}

uint32 probe() {
    ensures result == 305419896u32;
} by {
    step_until(call(fill, 0).entry);
    step();
    have ((&obj) as (uint8*))[0] == 120u8 by { close(); }
    have ((&obj) as (uint8*))[1] == 86u8 by { close(); }
    have ((&obj) as (uint8*))[2] == 52u8 by { close(); }
    have ((&obj) as (uint8*))[3] == 18u8 by { close(); }
    step_until(function.exit);
    close();
}
