# A `maintain` cases rejoin keeps only the facts every arm proved

In a loop's `maintain` proof, a `cases` rejoins its arms. Each arm closes its
own back edge, and then the rejoined path's back edge is closed again with
only the facts every arm proved. Here each arm proves a different bound on `b
/ 1000`, so the rejoined path has none, and its closure fails. The error
names the `cases` and says how to keep such a fact.

```c filename=a_preserve_cases_rejoin_keeps_only_the_facts_every_arm_proved.c
unsigned long f(unsigned long b)
{
	int i = 0;

	while (b >> 32) {
		b = b / 1000;
		i++;
	}
	return b;
}
```

```click
verifying "a_preserve_cases_rejoin_keeps_only_the_facts_every_arm_proved.c";
uint64 f(uint64 b) {
    requires 1u64 <= b;
    requires b <= 18446744073709u64;
    ensures true;
} by {
    step_until(loop(0).entry);
    loop {
        decreases b;
        invariant 1u64 <= b;
        invariant (i == 0 and b <= 18446744073709u64) or (i == 1 and b <= 18446744073u64) or (i == 2 and b <= 18446744u64);
        initialize by close();
        maintain by {
            have (b >> 32) != 0u64;
            have 4294967296u64 <= b;
            have (i == 0 and b <= 18446744073709u64) or (i == 1 and b <= 18446744073u64) by {
                cases {
                    i == 0 and b <= 18446744073709u64 => { close(); }
                    i == 1 and b <= 18446744073u64 => { close(); }
                    i == 2 and b <= 18446744u64 => {
                        have b < 4294967296u64;
                        contradiction(4294967296u64 <= b);
                    }
                }
            }
            cases {
                i == 0 and b <= 18446744073709u64 => {
                    mark head;
                    step_until(loop.back_edge);
                    have 4294967296u64 <= at(head, b);
                    have at(head, b) <= 18446744073709u64 by { close(); }
                    have 1u64 <= at(head, b) / 1000u64;
                    have at(head, b) / 1000u64 < at(head, b);
                    have at(head, b) / 1000u64 <= 18446744073u64;
                    have at(head, i) + 1 == 1 and at(head, b) / 1000u64 <= 18446744073u64 by { close(); }
                }
                i == 1 and b <= 18446744073u64 => {
                    mark head;
                    step_until(loop.back_edge);
                    have 4294967296u64 <= at(head, b);
                    have at(head, b) <= 18446744073u64 by { close(); }
                    have 1u64 <= at(head, b) / 1000u64;
                    have at(head, b) / 1000u64 < at(head, b);
                    have at(head, b) / 1000u64 <= 18446744u64;
                    have at(head, i) + 1 == 2 and at(head, b) / 1000u64 <= 18446744u64 by { close(); }
                }
            }
        }
    }
}
```

```expect
fail: This path left the `cases` at tactic 3, whose arms rejoined at the back edge
```
