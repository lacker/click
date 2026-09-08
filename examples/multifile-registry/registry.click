verifying "driver.c";
verifying "beta.c";
verifying "alpha.c";
verifying "data.c";

int32 record_alpha() {
    mutable counters[0].value[0..1], &calls[0..1], batches[0..2] by auto;
    ensures counters[0].value == old(counters[0].value) + 1 by auto;
    ensures calls == old(calls) + 1 by auto;
    ensures batches[0][0] == old(batches[0][0]) + 1 by auto;
    ensures batches[0][1] == old(batches[0][1]) by auto;
    ensures result == old(calls) + old(batches[0][0]) + 2 by auto;
}

int32 record_beta() {
    mutable counters[1].value[0..1], &calls[0..1], batches[0].value[0..1] by auto;
    ensures counters[1].value == old(counters[1].value) + 1 by auto;
    ensures calls == old(calls) + 1 by auto;
    ensures batches[0].value == old(batches[0].value) + 1 by auto;
    ensures result == old(calls) + old(batches[0].value) + 2 by auto;
}

int32 alpha_calls() {
    immutable;
    ensures result == old(calls) by auto;
}

int32 beta_calls() {
    immutable;
    ensures result == old(calls) by auto;
}

int32 registry_run() {
    ensures result == 214 by {
        step();
        step();
        have first == 2 by simp;
        step();
        step();
        have second == 4 by simp;
        step();
        step();
        have third == 102 by simp;
        step();
        step();
        have alpha_total == 2 by simp;
        step();
        step();
        have beta_total == 101 by simp;
        execute();
        simp();
    }
    ensures counters[0].value == 12 by auto;
    ensures counters[1].value == 21 by auto;
    ensures counters[2].value == 99 by auto;
    ensures counters[0].name == 97 by auto;
    ensures counters[1].name == 98 by auto;
    ensures counters[2].name == 122 by auto;
}
