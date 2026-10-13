# pcg_basic.c and pcg_basic.h are unchanged from pcg-c-basic at revision
# bc39cd76ac3d541e618606bcc6e1e5ba5e5e6aa3 (see SOURCE.md).
verifying "pcg_basic.c";

uint32 pcg32_random_r(struct pcg_state_setseq_64* rng) {
    owns rng->state;
    owns rng->inc;
    ensures rng->state == old(rng->state * 6364136223846793005u64 + rng->inc) by auto;
    ensures rng->inc == old(rng->inc) by auto;
    ensures result == old((((uint32)(((rng->state >> 18u64) ^ rng->state) >> 27u64)) >> ((uint32)(rng->state >> 59u64)))
        | (((uint32)(((rng->state >> 18u64) ^ rng->state) >> 27u64)) << ((0u32 - (uint32)(rng->state >> 59u64)) & 31u32))) by auto;
}

void pcg32_srandom_r(struct pcg_state_setseq_64* rng, uint64 initstate, uint64 initseq) {
    owns rng->state;
    owns rng->inc;
    ensures rng->inc == ((initseq << 1u64) | 1u64) by auto;
    ensures rng->state == ((0u64 * 6364136223846793005u64 + ((initseq << 1u64) | 1u64)) + initstate) * 6364136223846793005u64 + ((initseq << 1u64) | 1u64) by auto;
}

// The public wrappers pass the file's private `pcg32_global` to the helpers
// above; their contracts own its fields by name.
void pcg32_srandom(uint64 seed, uint64 seq) {
    owns pcg32_global.state;
    owns pcg32_global.inc;
    ensures pcg32_global.inc == ((seq << 1u64) | 1u64) by auto;
    ensures pcg32_global.state == ((0u64 * 6364136223846793005u64 + ((seq << 1u64) | 1u64)) + seed) * 6364136223846793005u64 + ((seq << 1u64) | 1u64) by auto;
}

uint32 pcg32_random() {
    owns pcg32_global.state;
    owns pcg32_global.inc;
    ensures pcg32_global.state == old(pcg32_global.state * 6364136223846793005u64 + pcg32_global.inc) by auto;
    ensures pcg32_global.inc == old(pcg32_global.inc) by auto;
    ensures result == old((((uint32)(((pcg32_global.state >> 18u64) ^ pcg32_global.state) >> 27u64)) >> ((uint32)(pcg32_global.state >> 59u64)))
        | (((uint32)(((pcg32_global.state >> 18u64) ^ pcg32_global.state) >> 27u64)) << ((0u32 - (uint32)(pcg32_global.state >> 59u64)) & 31u32))) by auto;
}
