# The frozen worker verifies with direct borrowed and owned clauses

The C worker is unchanged from `examples/concurrency-fork-join/fork_join.c`.
Direct `views` clauses allow a future caller to lend its job record while
transferring the output slice. Certificate synthesis must spell the output
pointer through the cast `void *` parameter or the struct-pointer local,
including when checking an expanded quantified readability proof.

```c filename=fill_range.c
#include <stddef.h>

struct range_job {
    int *output;
    int begin;
    int end;
    int value;
};

void *fill_range(void *argument) {
    struct range_job *job = argument;
    for (int index = job->begin; index < job->end; ++index) {
        job->output[index] = job->value;
    }
    return NULL;
}
```

```click
target "x86_64-unknown-linux-gnu";
verifying "fill_range.c";
import click::separation;
import click::integer;

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
    requires 0 <= to_integer((argument as (struct range_job *))->end - (argument as (struct range_job *))->begin);
    requires to_integer((argument as (struct range_job *))->end - (argument as (struct range_job *))->begin) <= 1073741823;
    requires separate(memory(*(argument as (struct range_job *))), memory((argument as (struct range_job *))->output[(argument as (struct range_job *))->begin..(argument as (struct range_job *))->end]));
    ensures result == 0;
    ensures range_filled(argument as (struct range_job *));
} by {
    step();
    step();
    step();
    step();
    loop fill {
        decreases to_integer(job->end) - to_integer(index);
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
            have job->begin <= index and index <= job->end by {
                all { job->begin <= index => { normalize(); } index <= job->end => { close(); } }
            }
            have forall (k: int32) { job->begin <= k and k < index implies job->output[k] == job->value } by {
                intro();
                intro();
                contradiction(job->begin <= k and k < index);
            }
        }
        maintain by {
            // The output store leaves the range descriptor and earlier cells intact.
            mark before_write;
            have separate(memory(*job), memory(job->output[job->begin..job->end])) by { close(); }
            have contains(memory(job->output[job->begin..job->end]), memory(job->output[index])) by {
                apply(separation::contains_element(job->output, job->begin, job->end, index));
            }
            apply(separation::contains_refl(memory(*job)));
            apply(separation::separate_restrict(memory(*job), memory(job->output[job->begin..job->end]),
                memory(*job), memory(job->output[index])));
            step() by { close(); }

            have separate(loop(0).statement(0).footprint, at(before_write, memory(*job))) by {
                normalize() using {
                    separate(at(before_write, memory(job->output[index])), at(before_write, memory(*job)));
                };
            }
            apply(separation::contains_refl(loop(0).statement(0).footprint));
            have contains(at(before_write, memory(*job)), at(before_write, memory(job->begin))) by { normalize(); }
            apply(separation::separate_restrict(loop(0).statement(0).footprint, at(before_write, memory(*job)),
                loop(0).statement(0).footprint, at(before_write, memory(job->begin))));
            have job->begin == at(before_write, job->begin) by {
                preserve(at(before_write, memory(job->begin)), loop(0).statement(0));
            }
            have contains(at(before_write, memory(*job)), at(before_write, memory(job->output))) by { normalize(); }
            apply(separation::separate_restrict(loop(0).statement(0).footprint, at(before_write, memory(*job)),
                loop(0).statement(0).footprint, at(before_write, memory(job->output))));
            have job->output == at(before_write, job->output) by {
                preserve(at(before_write, memory(job->output)), loop(0).statement(0));
            }
            have contains(at(before_write, memory(*job)), at(before_write, memory(job->end))) by { normalize(); }
            apply(separation::separate_restrict(loop(0).statement(0).footprint, at(before_write, memory(*job)),
                loop(0).statement(0).footprint, at(before_write, memory(job->end))));
            have job->end == at(before_write, job->end) by {
                preserve(at(before_write, memory(job->end)), loop(0).statement(0));
            }
            have contains(at(before_write, memory(*job)), memory(at(before_write, &job->value)[0])) by { normalize(); }
            apply(separation::separate_restrict(loop(0).statement(0).footprint, at(before_write, memory(*job)),
                loop(0).statement(0).footprint, memory(at(before_write, &job->value)[0])));
            have load<int32>(at(before_write, &job->value)) == at(before_write, load<int32>(&job->value)) by {
                preserve(memory(at(before_write, &job->value)[0]), loop(0).statement(0));
            }
            have job->value == at(before_write, job->value) by { close(); }

            have forall (k: int32) { job->begin <= k and k <= index implies job->output[k] == job->value } by {
                intro();
                intro();
                if k < index {
                    instantiate(at(before_write, forall (k: int32) {
                        job->begin <= k and k < index implies job->output[k] == job->value
                    }), k);
                    have at(before_write, job->begin) <= k and k < at(before_write, index) by {
                        rewrite(at(before_write, job->begin), job->begin);
                        close();
                    }
                    apply(at(before_write, job->begin) <= k and k < at(before_write, index) implies
                        at(before_write, job->output[k]) == at(before_write, job->value));
                    have k != at(before_write, index) by { close() using { k < index; }; }
                    have separate(at(before_write, memory(job->output[k])), at(before_write, memory(job->output[index]))) by {
                        apply(separation::separate_elements(at(before_write, job->output), k, at(before_write, index)));
                    }
                    have separate(loop(0).statement(0).footprint, at(before_write, memory(job->output[k]))) by {
                        normalize() using {
                            separate(at(before_write, memory(job->output[k])), at(before_write, memory(job->output[index])));
                        };
                    }
                    have load<int32>(at(before_write, &job->output[k])) == at(before_write, job->output[k]) by {
                        preserve(at(before_write, memory(job->output[k])), loop(0).statement(0));
                    }
                    rewrite(job->output, at(before_write, job->output));
                    rewrite(job->value, at(before_write, job->value));
                    close();
                } else {
                    have k == index;
                    rewrite(k, index);
                    close();
                }
            }

            // The increment moves the inclusive prefix back to the loop invariant.
            mark after_write;
            step();
            have at(before_write, index) < job->end by {
                rewrite(job->end, at(before_write, job->end));
                close();
            }
            have at(after_write, index) < 2147483647 by {
                apply(integer::int32_less_than_less_equal_transitive(at(after_write, index), job->end, 2147483647));
            }
            apply(integer::int32_increment_below_max_is_defined(at(after_write, index)));
            have to_integer(index) == to_integer(at(before_write, index)) + 1 by {
                have to_integer(index) == to_integer(at(after_write, index) + 1) by { close(); }
                apply(integer::int32_add_to_integer(at(after_write, index), 1));
                close();
            }
            have forall (k: int32) { job->begin <= k and k < index implies job->output[k] == job->value } by {
                intro();
                intro();
                have k <= at(after_write, index) by {
                    have to_integer(k) < to_integer(index) by { close(); }
                    apply(integer::lt_le_predecessor(to_integer(k), to_integer(index)));
                    have to_integer(at(after_write, index)) == to_integer(index) - 1 by {
                        rewrite(to_integer(index), to_integer(at(before_write, index)) + 1);
                        close();
                    }
                    have to_integer(k) <= to_integer(at(after_write, index)) by {
                        rewrite(to_integer(at(after_write, index)), to_integer(index) - 1);
                        close();
                    }
                    apply(integer::int32_to_integer_less_equal_implies_less_equal(k, at(after_write, index)));
                }
                instantiate(at(after_write, forall (k: int32) {
                    job->begin <= k and k <= index implies job->output[k] == job->value
                }), k);
                have at(after_write, job->begin) <= k and k <= at(after_write, index) by { close(); }
                apply(at(after_write, job->begin) <= k and k <= at(after_write, index) implies
                    at(after_write, job->output[k]) == at(after_write, job->value));
                close();
            }
            have job->begin <= index by {
                have at(after_write, job->begin) <= at(after_write, index) by { close(); }
                apply(integer::int32_increment_lower_bound(at(after_write, index), at(after_write, job->begin), job->end));
                have to_integer(job->begin) <= to_integer(index) by { close(); }
                apply(integer::int32_to_integer_less_equal_implies_less_equal(job->begin, index));
            }
            have index <= job->end by {
                apply(integer::int32_increment_upper_bound(at(after_write, index), job->end));
                have to_integer(index) <= to_integer(job->end) by { close(); }
                apply(integer::int32_to_integer_less_equal_implies_less_equal(index, job->end));
            }
            have 0 <= to_integer(job->end) - to_integer(index) by {
                close() using { index <= job->end; };
            }
            have to_integer(job->end) - to_integer(index) < at(before_write, to_integer(job->end) - to_integer(index)) by {
                rewrite(to_integer(index), to_integer(at(before_write, index)) + 1);
                rewrite(at(before_write, job->end), job->end);
                close();
            }
            close();
        }
    }
    step();
    close();
}
```

```expect
pass
```
