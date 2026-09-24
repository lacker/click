target "x86_64-linux-userspace";
runtime "modeled-pthread";
verifying "main.c";

predicate range_filled(job: struct range_job*) {
    forall (k: int32) {
        job->begin <= k and k < job->end implies job->output[k] == job->value
    }
}

void *fill_range(void *argument) {
    views &((struct range_job *)argument)->output;
    views ((struct range_job *)argument)->begin;
    views ((struct range_job *)argument)->end;
    views ((struct range_job *)argument)->value;
    owns ((struct range_job *)argument)->output[((struct range_job *)argument)->begin..((struct range_job *)argument)->end];
    requires 0 <= ((struct range_job *)argument)->begin;
    requires ((struct range_job *)argument)->begin <= ((struct range_job *)argument)->end;
    requires 0 <= ((struct range_job *)argument)->end - ((struct range_job *)argument)->begin;
    requires ((struct range_job *)argument)->end - ((struct range_job *)argument)->begin <= 1073741823;
    requires separate(memory(((struct range_job *)argument)[0..6]), memory(((struct range_job *)argument)->output[((struct range_job *)argument)->begin..((struct range_job *)argument)->end]));
    ensures result == 0;
    ensures range_filled((struct range_job *)argument);
} by {
    step();
    step();
    step();
    step();
    loop as fill {
        decreases job->end - index;
        views &job->output;
        views job->begin;
        views job->end;
        views job->value;
        owns job->output[job->begin..job->end];
        invariant job->begin <= index and index <= job->end;
        invariant forall (k: int32) {
            job->begin <= k and k < index implies job->output[k] == job->value
        };

        initialize by {
            have job->begin <= index and index <= job->end by {
                both { normalize(); } and { assumption(); }
            }
            have forall (k: int32) { job->begin <= k and k < index implies job->output[k] == job->value } by {
                intro();
                intro();
                contradiction(job->begin <= k and k < index);
            }
        }
        preserve by {
            mark iteration;
            step();
            have forall (k: int32) {
                job->begin <= k and k <= index implies job->output[k] == job->value
            } by {
                intro();
                intro();
                if k < index {
                    extract(job->begin <= k);
                    instantiate(at(statement(5).entry, forall (k: int32) {
                        job->begin <= k and k < index implies job->output[k] == job->value
                    }), k) using { job->begin <= k; k < index; }
                    simp();
                } else {
                    extract(k <= index);
                    have k == index by {
                        apply(int32_le_and_not_lt_implies_eq(k, index)) using {
                            k <= index;
                            not (k < index);
                        }
                    }
                    rewrite(k == index);
                    simp();
                }
            }
            step();
            have 0 <= at(iteration, index) by {
                simp() using {
                    0 <= job->begin;
                    job->begin <= at(iteration, index);
                }
            }
            have 0 <= job->end by {
                simp() using {
                    0 <= job->begin;
                    job->begin <= job->end;
                }
            }
            have 0 <= 0 - at(iteration, index) + job->end - 1 by {
                arithmetic() using {
                    0 <= at(iteration, index);
                    0 <= job->end;
                    at(iteration, index) < at(iteration, job->end);
                    job->begin <= job->end;
                }
            }
            have 0 - at(iteration, index) + job->end - 1
                < 0 - at(iteration, index) + job->end by {
                arithmetic() using {
                    0 <= at(iteration, index);
                    0 <= job->end;
                    at(iteration, index) < at(iteration, job->end);
                    job->begin <= job->end;
                }
            }
            have forall (k: int32) {
                job->begin <= k and k < index implies job->output[k] == job->value
            } by {
                intro();
                intro();
                extract(job->begin <= k);
                extract(k < index);
                have k <= at(iteration, index) by {
                    apply(int32_lt_successor_implies_le(k, at(iteration, index))) using {
                        k < index;
                    }
                }
                instantiate(at(statement(6).entry, forall (k: int32) {
                    job->begin <= k and k <= index implies job->output[k] == job->value
                }), k) using { job->begin <= k; k <= at(iteration, index); }
                simp();
            }
            simp();
        }
    }
    step();
    simp();
}

int fill_parallel(int output[4]) {
    owns output[0..4];
    ensures result == 0 or result == 1;
    ensures result == 1 implies
        output[0] == 11 and output[1] == 11 and
        output[2] == 22 and output[3] == 22;
    ensures result == 0 implies
        (output[0] == 0 and output[1] == 0 and
         output[2] == 0 and output[3] == 0) or
        (output[0] == 11 and output[1] == 11 and
         output[2] == 0 and output[3] == 0);
} by {
    execute();
    simp();
}
