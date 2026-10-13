# A loop clause grows with the loops before it

A `loop { decreases ...; invariant ...; }` clause over one small loop costs
work that grows roughly quadratically with the number of earlier loops in the
function, so a function of N sequential loops is roughly cubic: 64
four-iteration loops take 47 seconds.

Reproduced on master `e28770b20` with `scripts/step-scaling-hunt.py`:

```c
int32 caller(int32* p) {        /* owns p[0..4] */
    int32 i;
    i = 0;
    while (i < 4) { p[i] = 0; i = i + 1; }
    i = 0;
    while (i < 4) { p[i] = 1; i = i + 1; }
    ...                          /* N loops */
    return 0;
}
```

each proved by `step(); loop { decreases 4 - i; invariant i >= 0;
invariant i <= 4; }`.

```sh
python3 scripts/step-scaling-hunt.py loops --sizes 4,8,16,24
```

The last loop clause charges 4,460, 15,054, 58,704 and 132,304 units at
N = 4, 8, 16 and 24 (2.6 s for that one clause at N = 24). At N = 64 the 52nd
clause alone took 51 s and the run hit the ten-minute bound.

Diagnosis (master `b769df57d`): each loop leaves facts about its own copy
of the loop variable on the path (`0 <= i_j`, `i_j <= 4`, `!(i_j < 4)`), and
nothing drops them when `i = 0` makes that copy dead. All of them meet at
the constant bound `4`. Deciding a later loop's `i < 4`,
`has_lower_bound_above` takes every `i_j` filed under `4` as a candidate
lower bound and decides `i_j > i` for each, so a decision makes one
candidate decision per earlier loop, and each of those runs the decision
procedure's rules over the whole path.

Partly fixed: the order walk those decisions run (`has_order_path`) read
every order fact at every node it reached, and walks from the same source
repeated the same exploration. It now reads the edges filed under the
node's equality-graph class (`TransportEdgeIndex`) and shares a source's
reachable states (`TransportReach`). Charged work is unchanged (the scan
charged nothing for the facts it read), but N = 32 verifies in 6.6 s
instead of 70 s, and N = 64 verifies in 47 s where it hit the ten-minute
bound.

What remains: the clause still makes one candidate decision per earlier
loop, and each still runs other per-decision rules that read the whole
path (`has_condition_fact`'s scanned fallback, the 64-bit order-fact
scan, `bitvector_constant_from_direct_equalities`), so a clause's work and
time are still about quadratic in the earlier loops. Indexing those rules
would leave the candidate count linear; a constant clause needs the dead
copies' facts not to be candidates at all, for example by retiring facts
whose terms nothing live mentions.

Acceptance: a multi-size regression over `loops` shows each loop clause's
work and time constant in the number of earlier loops, up to logarithmic
factors; each loop's invariants and termination are still checked; no budget
or threshold is raised.
