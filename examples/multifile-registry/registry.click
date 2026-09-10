verifying "driver.c";
verifying "beta.c" as beta;
verifying "alpha.c" as alpha;
verifying "data.c";

int32 record_alpha() {
    requires counters[0].value > -1000;
    requires counters[0].value < 1000;
    requires calls > -1000;
    requires calls < 1000;
    requires batches[0][0] > -1000;
    requires batches[0][0] < 1000;
    owns counters[0].value[0..1];
    owns &calls[0..1];
    owns batches[0..2];
    ensures counters[0].value == old(counters[0].value) + 1 by auto;
    ensures calls == old(calls) + 1 by auto;
    ensures batches[0][0] == old(batches[0][0]) + 1 by auto;
    ensures batches[0][1] == old(batches[0][1]) by auto;
    ensures result == old(calls) + old(batches[0][0]) + 2 by auto;
}

int32 record_beta() {
    requires counters[1].value > -1000;
    requires counters[1].value < 1000;
    requires calls > -1000;
    requires calls < 1000;
    requires batches[0].value > -1000;
    requires batches[0].value < 1000;
    owns counters[1].value[0..1];
    owns &calls[0..1];
    owns batches[0].value[0..1];
    ensures counters[1].value == old(counters[1].value) + 1 by auto;
    ensures calls == old(calls) + 1 by auto;
    ensures batches[0].value == old(batches[0].value) + 1 by auto;
    ensures result == old(calls) + old(batches[0].value) + 2 by auto;
}

int32 alpha_calls() {
    ensures result == old(calls) by auto;
}

int32 beta_calls() {
    ensures result == old(calls) by auto;
}

int32 registry_run() {
    requires counters[0].value == 10;
    requires counters[1].value == 20;
    requires counters[2].value == 99;
    requires counters[0].value > -1000;
    requires counters[0].value < 1000;
    requires counters[1].value > -1000;
    requires counters[1].value < 1000;
    requires alpha::calls == 0;
    requires beta::calls == 100;
    requires alpha::calls > -1000;
    requires alpha::calls < 1000;
    requires beta::calls > -1000;
    requires beta::calls < 1000;
    requires alpha::record_alpha::batches[0][0] == 0;
    requires beta::record_beta::batches[0].value == 0;
    requires alpha::record_alpha::batches[0][0] > -1000;
    requires alpha::record_alpha::batches[0][0] < 1000;
    requires beta::record_beta::batches[0].value > -1000;
    requires beta::record_beta::batches[0].value < 1000;
    owns counters[0].value[0..1];
    owns counters[1].value[0..1];
    owns &alpha::calls[0..1];
    owns &beta::calls[0..1];
    owns alpha::record_alpha::batches[0..2];
    owns beta::record_beta::batches[0].value[0..1];
    ensures result == 214 by {
        have counters[0].value > -1000 by simp;
        have counters[0].value < 1000 by simp;
        have alpha::calls > -1000 by simp;
        have alpha::calls < 1000 by simp;
        have alpha::record_alpha::batches[0][0] > -1000 by simp;
        have alpha::record_alpha::batches[0][0] < 1000 by simp;
        step();
        step();
        have first == 2 by simp;
        have counters[0].value > -1000 by simp;
        have counters[0].value < 1000 by simp;
        have alpha::calls > -1000 by simp;
        have alpha::calls < 1000 by simp;
        have alpha::record_alpha::batches[0][0] > -1000 by simp;
        have alpha::record_alpha::batches[0][0] < 1000 by simp;
        step();
        step();
        have second == 4 by simp;
        have counters[1].value > -1000 by simp;
        have counters[1].value < 1000 by simp;
        have beta::calls > -1000 by simp;
        have beta::calls < 1000 by simp;
        have beta::record_beta::batches[0].value > -1000 by simp;
        have beta::record_beta::batches[0].value < 1000 by simp;
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
