verifying "fork_join.c";

predicate range_filled(job: struct range_job*) {
    forall (k: int32) {
        job->begin <= k and k < job->end implies job->output[k] == job->value
    }
}

void *fill_range(void *argument) {
    views (argument as (struct range_job *))->output;
    views (argument as (struct range_job *))->begin;
    views (argument as (struct range_job *))->end;
    views (argument as (struct range_job *))->value;
    owns (argument as (struct range_job *))->output[(argument as (struct range_job *))->begin..(argument as (struct range_job *))->end];
    requires 0 <= (argument as (struct range_job *))->begin;
    requires (argument as (struct range_job *))->begin <= (argument as (struct range_job *))->end;
    requires 0 <= (argument as (struct range_job *))->end - (argument as (struct range_job *))->begin;
    requires (argument as (struct range_job *))->end - (argument as (struct range_job *))->begin <= 1073741823;
    requires separate(memory(*(argument as (struct range_job *))), memory((argument as (struct range_job *))->output[(argument as (struct range_job *))->begin..(argument as (struct range_job *))->end]));
    ensures result == 0;
    ensures range_filled(argument as (struct range_job *));
} by {
    step();
    step();
    step();
    step();
    loop as fill {
        decreases job->end - index;
        views job->output;
        views job->begin;
        views job->end;
        views job->value;
        owns job->output[job->begin..job->end];
        invariant job->begin <= index and index <= job->end;
        invariant forall (k: int32) {
            job->begin <= k and k < index implies job->output[k] == job->value
        };

        initialize by {
            have job->begin <= index and index <= job->end;
            have forall (k: int32) { job->begin <= k and k < index implies job->output[k] == job->value } by {
                intro();
                intro();
                contradiction(job->begin <= k and k < index);
            }
        }
        preserve by {
            have separate(memory(*job), memory(job->output[job->begin..job->end]));
            mark iteration;
            have job->begin <= index;
            step();
            have job->output == at(iteration, job->output) and
                 job->begin == at(iteration, job->begin) and
                 job->end == at(iteration, job->end) and
                 job->value == at(iteration, job->value) by {
                transport(at(iteration, job->output) == at(iteration, job->output) and
                          at(iteration, job->begin) == at(iteration, job->begin) and
                          at(iteration, job->end) == at(iteration, job->end) and
                          at(iteration, job->value) == at(iteration, job->value),
                          job->output == at(iteration, job->output) and
                          job->begin == at(iteration, job->begin) and
                          job->end == at(iteration, job->end) and
                          job->value == at(iteration, job->value)) using {
                    at(iteration, separate(memory(*job), memory(job->output[job->begin..job->end])));
                    at(iteration, job->begin) <= index;
                    index < at(iteration, job->end);
                };
            }
            have forall (k: int32) {
                job->begin <= k and k <= index implies job->output[k] == job->value
            } by {
                intro();
                intro();
                if k < index {
                    extract(job->begin <= k);
                    instantiate(at(region(5).entry, forall (k: int32) {
                        job->begin <= k and k < index implies job->output[k] == job->value
                    }), k) using { job->begin <= k; k < index; job->begin == at(iteration, job->begin); };
                    solve();
                } else {
                    extract(k <= index);
                    have k == index;
                    rewrite(k == index);
                    solve();
                }
            }
            step();
            have 0 <= at(iteration, index);
            have 0 <= job->end;
            have 0 - at(iteration, index) + job->end - 1
                < 0 - at(iteration, index) + job->end by {
                solve() using {
                    0 <= at(iteration, index);
                    0 <= job->end;
                    at(iteration, index) < at(iteration, job->end);
                    job->begin <= job->end;
                };
            }
            have forall (k: int32) {
                job->begin <= k and k < index implies job->output[k] == job->value
            } by {
                intro();
                intro();
                extract(job->begin <= k);
                extract(k < index);
                have k <= at(iteration, index);
                instantiate(at(region(6).entry, forall (k: int32) {
                    job->begin <= k and k <= index implies job->output[k] == job->value
                }), k) using { job->begin <= k; k <= at(iteration, index); job->begin == at(iteration, job->begin); };
                solve();
            }
            solve();
        }
    }
    step();
    solve();
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
    step_until(statement(5));
    have first_job.output == output;
    have second_job.output == output;
    step();
    branch {
        step_until(function.exit);
        solve();
    } else {}
    step();
    branch {
        step();
        have range_filled(&first_job);
        have forall (k: int32) {
            first_job.begin <= k and k < first_job.end implies first_job.output[k] == first_job.value
        } by { unfold(range_filled); assumption(); }
        have first_job.output[0] == first_job.value;
        have first_job.output[1] == first_job.value;
        have output[0] == 11;
        have output[1] == 11;
        step_until(function.exit);
        solve();
    } else {}
    step();
    have range_filled(&first_job);
    have forall (k: int32) {
        first_job.begin <= k and k < first_job.end implies first_job.output[k] == first_job.value
    } by { unfold(range_filled); assumption(); }
    have first_job.output[0] == first_job.value;
    have first_job.output[1] == first_job.value;
    have output[0] == 11;
    have output[1] == 11;
    step();
    have range_filled(&second_job);
    have forall (k: int32) {
        second_job.begin <= k and k < second_job.end implies second_job.output[k] == second_job.value
    } by { unfold(range_filled); assumption(); }
    have second_job.output[2] == second_job.value;
    have second_job.output[3] == second_job.value;
    have output[2] == 22;
    have output[3] == 22;
    step_until(function.exit);
    solve();
}
