// A client of the unchanged pcg-c-basic library in ../pcg-basic. It seeds the
// global generator with pcg32_srandom(42, 54), checks the first two outputs
// against the published reference values 0xa15c02b7 and 0x7b47f409, then
// reseeds and checks that the sequence restarts.
verifying "client.c";
verifying "../pcg-basic/pcg_basic.c" as pcg;

import "../pcg-basic/pcg_basic.click";

int32 first_outputs_repeat() {
    owns pcg::pcg32_global.state;
    owns pcg::pcg32_global.inc;
    ensures result == 1;
} by {
    // Seeding leaves a known state. Each draw's output is the XSH-RR
    // formula on the state its call started from, evaluated once that
    // state is known.
    execute_until(statement(2));
    have pcg::pcg32_global.state == 1753877967969059832u64 by { simp(); }
    have pcg::pcg32_global.inc == 109u64 by { simp(); }
    execute_until(statement(8));
    have at(statement(4).entry, pcg::pcg32_global.state) == 3118741472915405573u64 by {
        rewrite(at(statement(4).entry, pcg::pcg32_global.state) == at(statement(2).entry, pcg::pcg32_global.state * 6364136223846793005u64 + pcg::pcg32_global.inc));
        rewrite(at(statement(2).entry, pcg::pcg32_global.state) == 1753877967969059832u64);
        rewrite(at(statement(2).entry, pcg::pcg32_global.inc) == 109u64);
        normalize();
    }
    have at(statement(6).entry, pcg::pcg32_global.state) == 1753877967969059832u64 by { simp(); }
    have first == at(statement(2).entry, ((((uint32)(((pcg::pcg32_global.state >> 18u64) ^ pcg::pcg32_global.state) >> 27u64)) >> ((uint32)(pcg::pcg32_global.state >> 59u64))) | (((uint32)(((pcg::pcg32_global.state >> 18u64) ^ pcg::pcg32_global.state) >> 27u64)) << ((0u32 - (uint32)(pcg::pcg32_global.state >> 59u64)) & 31u32)))) by { simp(); }
    have first == 2707161783u32 by {
        rewrite(first == at(statement(2).entry, ((((uint32)(((pcg::pcg32_global.state >> 18u64) ^ pcg::pcg32_global.state) >> 27u64)) >> ((uint32)(pcg::pcg32_global.state >> 59u64))) | (((uint32)(((pcg::pcg32_global.state >> 18u64) ^ pcg::pcg32_global.state) >> 27u64)) << ((0u32 - (uint32)(pcg::pcg32_global.state >> 59u64)) & 31u32)))));
        rewrite(at(statement(2).entry, pcg::pcg32_global.state) == 1753877967969059832u64);
        normalize();
    }
    have second == at(statement(4).entry, ((((uint32)(((pcg::pcg32_global.state >> 18u64) ^ pcg::pcg32_global.state) >> 27u64)) >> ((uint32)(pcg::pcg32_global.state >> 59u64))) | (((uint32)(((pcg::pcg32_global.state >> 18u64) ^ pcg::pcg32_global.state) >> 27u64)) << ((0u32 - (uint32)(pcg::pcg32_global.state >> 59u64)) & 31u32)))) by { simp(); }
    have second == 2068313097u32 by {
        rewrite(second == at(statement(4).entry, ((((uint32)(((pcg::pcg32_global.state >> 18u64) ^ pcg::pcg32_global.state) >> 27u64)) >> ((uint32)(pcg::pcg32_global.state >> 59u64))) | (((uint32)(((pcg::pcg32_global.state >> 18u64) ^ pcg::pcg32_global.state) >> 27u64)) << ((0u32 - (uint32)(pcg::pcg32_global.state >> 59u64)) & 31u32)))));
        rewrite(at(statement(4).entry, pcg::pcg32_global.state) == 3118741472915405573u64);
        normalize();
    }
    have again == at(statement(6).entry, ((((uint32)(((pcg::pcg32_global.state >> 18u64) ^ pcg::pcg32_global.state) >> 27u64)) >> ((uint32)(pcg::pcg32_global.state >> 59u64))) | (((uint32)(((pcg::pcg32_global.state >> 18u64) ^ pcg::pcg32_global.state) >> 27u64)) << ((0u32 - (uint32)(pcg::pcg32_global.state >> 59u64)) & 31u32)))) by { simp(); }
    have again == 2707161783u32 by {
        rewrite(again == at(statement(6).entry, ((((uint32)(((pcg::pcg32_global.state >> 18u64) ^ pcg::pcg32_global.state) >> 27u64)) >> ((uint32)(pcg::pcg32_global.state >> 59u64))) | (((uint32)(((pcg::pcg32_global.state >> 18u64) ^ pcg::pcg32_global.state) >> 27u64)) << ((0u32 - (uint32)(pcg::pcg32_global.state >> 59u64)) & 31u32)))));
        rewrite(at(statement(6).entry, pcg::pcg32_global.state) == 1753877967969059832u64);
        normalize();
    }
    execute();
    simp();
}
