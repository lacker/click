#!/usr/bin/env python3
"""Hunt for C shapes whose simple `step` work grows with unrelated state.

A simple tactic must cost work proportional to its own input and the C
operation it executes (docs/internals/verification-efficiency.md). Each shape
below generates one natural C function and an explicit one-`step()`-per-
statement proof at several sizes N, verifies it with `CLICK_TIMINGS`, and
prints every step's deterministic work. A shape whose per-step work stays flat
as N grows is fine; one whose largest step grows is a perverse function: a
program `step` cannot check at a cost proportional to the line being checked.

    python3 scripts/step-scaling-hunt.py [SHAPE ...] [--sizes 1,4,16,64,128]

Uses the optimized verifier at `$CARGO_TARGET_DIR/profiling/click` (build it
with `cargo build --profile profiling --bin click`). Generated mdtests are
kept under a temporary directory, printed at the end, for reproduction.
"""
import argparse
import os
import re
import subprocess
import sys
import tempfile

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
CLICK = os.path.join(os.environ.get("CARGO_TARGET_DIR", os.path.join(ROOT, "target")), "profiling", "click")


def mdtest(title, c, click):
    return f"# {title}\n\n```c filename=hunt.c\n{c}\n```\n\n```click\n{click}\n```\n\n```expect\npass\n```\n"

def many_calls(n):
    calls = "\n".join("    touch(flags, data, k);" for _ in range(n))
    c = f"""struct box {{
    int32 v;
}};

void touch(int32* flags, int32* data, int32 k) {{
    return;
}}

int32 caller(int32* flags, int32* data, int32 k, struct box* b) {{
    b->v = 5;
{calls}
    return b->v;
}}"""
    steps = "\n".join("    step();" for _ in range(n + 2))
    click = f"""verifying "hunt.c";

void touch(int32* flags, int32* data, int32 k) {{
    owns flags[0..k];
    owns data[0..k];
}} by {{
    execute();
    simp();
}}

int32 caller(int32* flags, int32* data, int32 k, struct box* b) {{
    owns flags[0..k];
    owns data[0..k];
    owns *b;
    ensures result == 5;
}} by {{
{steps}
    simp();
}}"""
    return mdtest(f"many calls {n}", c, click)


def many_objects(n, calls=1):
    params = ", ".join(f"struct box* b{i}" for i in range(n))
    sets = "\n".join(f"    b{i}->v = {i};" for i in range(n))
    body_calls = "\n".join("    touch(flags, data, k);" for _ in range(calls))
    reads = " + ".join(f"b{i}->v" for i in range(n))
    c = f"""struct box {{
    int32 v;
}};

void touch(int32* flags, int32* data, int32 k) {{
    return;
}}

int32 caller(int32* flags, int32* data, int32 k, {params}) {{
    int32 total;
{sets}
{body_calls}
    total = {reads};
    return total;
}}"""
    owns = "\n".join(f"    owns *b{i};" for i in range(n))
    expected = sum(range(n))
    steps = "\n".join("    step();" for _ in range(1 + n + calls + 2))
    click = f"""verifying "hunt.c";

void touch(int32* flags, int32* data, int32 k) {{
    owns flags[0..k];
    owns data[0..k];
}} by {{
    execute();
    simp();
}}

int32 caller(int32* flags, int32* data, int32 k, {params}) {{
    owns flags[0..k];
    owns data[0..k];
{owns}
    ensures result == {expected};
}} by {{
{steps}
    simp();
}}"""
    return mdtest(f"many objects {n}", c, click)

def objects_and_calls(n):
    return many_objects(n, calls=n)

SHAPES = {'many_calls': many_calls, 'many_objects': many_objects, 'objects_and_calls': objects_and_calls}

TOUCH_C = """void touch(int32* flags, int32* data, int32 k) {
    return;
}"""
TOUCH_CLICK = """void touch(int32* flags, int32* data, int32 k) {
    owns flags[0..k];
    owns data[0..k];
} by {
    execute();
    simp();
}"""

def aliases(n):
    params = ", ".join(f"struct box* q{i}" for i in range(n))
    reads = " + ".join(f"q{i}->v" for i in range(n))
    c = f"""struct box {{
    int32 v;
}};

{TOUCH_C}

int32 caller(int32* flags, int32* data, int32 k, struct box* b, {params}) {{
    int32 total;
    b->v = 1;
    touch(flags, data, k);
    total = {reads};
    return total;
}}"""
    requires = "\n".join(f"    requires q{i} == b;" for i in range(n))
    steps = "\n".join("    step();" for _ in range(5))
    click = f"""verifying "hunt.c";

{TOUCH_CLICK}

int32 caller(int32* flags, int32* data, int32 k, struct box* b, {params}) {{
    owns flags[0..k];
    owns data[0..k];
    owns *b;
{requires}
    ensures result == {n};
}} by {{
{steps}
    simp();
}}"""
    return mdtest(f"aliases {n}", c, click)

def order_chain(n):
    params = ", ".join(f"int32 x{i}" for i in range(n + 1))
    stores = "\n".join(f"    data[x{i}] = {i};" for i in range(1, n + 1))
    c = f"""int32 caller(int32* data, int32 len, {params}) {{
    int32 first;
    data[x0] = 100;
{stores}
    first = data[x0];
    return first;
}}"""
    requires = "\n".join(f"    requires x{i} < x{i+1};" for i in range(n))
    steps = "\n".join("    step();" for _ in range(1 + 1 + n + 2))
    click = f"""verifying "hunt.c";

int32 caller(int32* data, int32 len, {params}) {{
    owns data[0..len];
    requires 0 <= x0;
{requires}
    requires x{n} < len;
    ensures result == 100;
}} by {{
{steps}
    simp();
}}"""
    return mdtest(f"order chain {n}", c, click)

def deep_chain(n):
    params = ", ".join(f"struct node* n{i}" for i in range(n + 1))
    links = "\n".join(f"    n{i}->next = n{i+1};" for i in range(n))
    path = "n0" + "->next" * n
    c = f"""struct node {{
    struct node* next;
    int32 v;
}};

{TOUCH_C}

int32 caller(int32* flags, int32* data, int32 k, {params}) {{
    int32 out;
{links}
    n{n}->v = 9;
    touch(flags, data, k);
    out = {path}->v;
    return out;
}}"""
    owns = "\n".join(f"    owns *n{i};" for i in range(n + 1))
    steps = "\n".join("    step();" for _ in range(1 + n + 1 + 1 + 2))
    click = f"""verifying "hunt.c";

{TOUCH_CLICK}

int32 caller(int32* flags, int32* data, int32 k, {params}) {{
    owns flags[0..k];
    owns data[0..k];
{owns}
    ensures result == 9;
}} by {{
{steps}
    simp();
}}"""
    return mdtest(f"deep chain {n}", c, click)

SHAPES.update({'aliases': aliases, 'order_chain': order_chain, 'deep_chain': deep_chain})


def branches(n):
    ifs = "\n".join(f"""    if (a{i} > 0) {{
        s = s + 1;
    }}""" for i in range(n))
    params = ", ".join(f"int32 a{i}" for i in range(n))
    c = f"""int32 caller({params}) {{
    int32 s;
    s = 0;
{ifs}
    return s;
}}"""
    arms = "\n".join(
        f"""        branch ensuring {{
            fact 0 <= s;
            fact s <= {i + 1};
        }} then {{
            step();
            have 0 <= s by {{ simp(); }}
            have s <= {i + 1} by {{ simp(); }}
        }} else {{
            have s <= {i + 1} by {{ simp(); }}
        }}"""
        for i in range(n)
    )
    click = f"""verifying "hunt.c";

int32 caller({params}) {{
    ensures result >= 0 by {{
        step();
        step();
{arms}
        step();
        simp();
    }}
}}"""
    return mdtest(f"branches {n}", c, click)


def straight_line(n):
    decls = "\n".join(f"    int32 x{i};" for i in range(1, n + 1))
    assigns = "\n".join(f"    x{i} = x{i - 1} + 1;" for i in range(1, n + 1))
    c = f"""int32 caller(int32 x0) {{
{decls}
{assigns}
    return x{n};
}}"""
    steps = "\n".join("    step();" for _ in range(2 * n + 1))
    click = f"""verifying "hunt.c";

int32 caller(int32 x0) {{
    requires 0 <= x0;
    requires x0 <= 1000000;
    ensures result == x0 + {n};
}} by {{
{steps}
    simp();
}}"""
    return mdtest(f"straight line {n}", c, click)


def loops(n):
    body = "\n".join(f"""    i = 0;
    while (i < 4) {{
        p[i] = {k};
        i = i + 1;
    }}""" for k in range(n))
    c = f"""int32 caller(int32* p) {{
    int32 i;
{body}
    return 0;
}}"""
    proof = "\n".join(
        """    step();
    loop { decreases 4 - i; invariant i >= 0; invariant i <= 4; }"""
        for _ in range(n)
    )
    click = f"""verifying "hunt.c";

int32 caller(int32* p) {{
    owns p[0..4];
    ensures result == 0;
}} by {{
    step();
{proof}
    step();
    simp();
}}"""
    return mdtest(f"loops {n}", c, click)


def const_array(n):
    stores = "\n".join(f"    data[{i}] = {i};" for i in range(n))
    c = f"""int32 caller(int32* data) {{
    int32 first;
{stores}
    first = data[0];
    return first;
}}"""
    steps = "\n".join("    step();" for _ in range(n + 3))
    click = f"""verifying "hunt.c";

int32 caller(int32* data) {{
    owns data[0..{n}];
    ensures result == 0;
}} by {{
{steps}
    simp();
}}"""
    return mdtest(f"constant-index array {n}", c, click)


def many_callees(n):
    callees_c = "\n\n".join(f"""void touch{i}(int32* data) {{
    return;
}}""" for i in range(n))
    calls = "\n".join(f"    touch{i}(data);" for i in range(n))
    c = f"""{callees_c}

int32 caller(int32* data, struct box* b) {{
    b->v = 5;
{calls}
    return b->v;
}}"""
    c = "struct box {\n    int32 v;\n};\n\n" + c
    callees_click = "\n\n".join(f"""void touch{i}(int32* data) {{
    owns data[0..4];
}} by {{
    execute();
    simp();
}}""" for i in range(n))
    steps = "\n".join("    step();" for _ in range(n + 2))
    click = f"""verifying "hunt.c";

{callees_click}

int32 caller(int32* data, struct box* b) {{
    owns data[0..4];
    owns *b;
    ensures result == 5;
}} by {{
{steps}
    simp();
}}"""
    return mdtest(f"many callees {n}", c, click)


def unrelated_facts(n):
    params = ", ".join(f"int32 a{i}" for i in range(n))
    requires = "\n".join(f"    requires a{i} < {i + 1000};" for i in range(n))
    c = f"""struct box {{
    int32 v;
}};

{TOUCH_C}

int32 caller(int32* flags, int32* data, int32 k, struct box* b, {params}) {{
    b->v = 5;
    touch(flags, data, k);
    return b->v;
}}"""
    click = f"""verifying "hunt.c";

{TOUCH_CLICK}

int32 caller(int32* flags, int32* data, int32 k, struct box* b, {params}) {{
    owns flags[0..k];
    owns data[0..k];
    owns *b;
{requires}
    ensures result == 5;
}} by {{
    step();
    step();
    step();
    simp();
}}"""
    return mdtest(f"unrelated facts {n}", c, click)


SHAPES.update(
    {
        "branches": branches,
        "straight_line": straight_line,
        "loops": loops,
        "const_array": const_array,
        "many_callees": many_callees,
        "unrelated_facts": unrelated_facts,
    }
)



def heap_objects(n):
    decls = "\n".join(f"    struct box* p{i};" for i in range(n))
    makes = "\n".join(f"    p{i} = make_box();\n    p{i}->v = {i};" for i in range(n))
    drops = "\n".join(f"    drop_box(p{i});" for i in range(n))
    c = f"""struct box {{
    int32 v;
}};

int32 caller() {{
{decls}
{makes}
{drops}
    return 0;
}}"""
    make_proof = "\n".join(
        f"""    step();
    unfold(boxed(p{i}));
    step();
    fold(boxed(p{i}));"""
        for i in range(n)
    )
    steps = "\n".join("    step();" for _ in range(n))
    click = f"""verifying "hunt.c";

resource boxed(p: struct box*) {{
    owns *p;
}}

extern struct box* make_box() {{
    produces boxed(result);
}}

extern void drop_box(struct box* p) {{
    consumes boxed(p);
}}

int32 caller() {{
    ensures result == 0;
}} by {{
{steps}
{make_proof}
{steps}
    step();
    simp();
}}"""
    return mdtest(f"heap objects {n}", c, click)


SHAPES["heap_objects"] = heap_objects


STEP = re.compile(r"click timing: tactic caller\S* \d+ step class simple .* ([0-9.]+)s work (\d+)")
# Proof-structure tactics: `loop` clauses (classified smart) and `branch`
# and other containers (control). A `loop` clause over one small loop should
# not grow with the loops before it either.
CONTROL = re.compile(
    r"click timing: tactic caller\S* \d+ (loop|branch|\w+) class (?:control|smart) .* ([0-9.]+)s work (\d+)"
)


def verify(path):
    out = subprocess.run(
        [CLICK, "verify", path],
        env=dict(os.environ, CLICK_TIMINGS="1", RUST_MIN_STACK="8388608"),
        capture_output=True,
        text=True,
    )
    lines = (out.stdout + out.stderr).splitlines()
    steps = [(int(m.group(2)), float(m.group(1))) for m in map(STEP.match, lines) if m]
    controls = [int(m.group(3)) for m in map(CONTROL.match, lines) if m and m.group(1) in ("loop", "branch")]
    return out.returncode == 0, steps, controls, out.stdout + out.stderr


def main():
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("shapes", nargs="*", default=list(SHAPES))
    parser.add_argument("--sizes", default="1,4,16,64,128")
    args = parser.parse_args()
    sizes = [int(size) for size in args.sizes.split(",")]
    if not os.access(CLICK, os.X_OK):
        sys.exit(f"error: no optimized verifier at {CLICK}; run `cargo build --profile profiling --bin click`")
    directory = tempfile.mkdtemp(prefix="click-step-hunt.")
    for shape in args.shapes:
        largest = []
        largest_control = []
        mean_ms = []
        for n in sizes:
            path = os.path.join(directory, f"{shape}_{n}.md")
            with open(path, "w") as handle:
                handle.write(SHAPES[shape](n))
            ok, steps, controls, output = verify(path)
            if not ok or not steps:
                print(f"{shape:18} N={n:<4} did not verify: {path}")
                print(output[-1500:])
                break
            work = [units for units, _ in steps]
            largest.append(max(work))
            largest_control.append(max(controls, default=0))
            mean_ms.append(1000 * sum(seconds for _, seconds in steps) / len(steps))
            print(
                f"{shape:18} N={n:<4} steps={len(steps):<4} total={sum(work):<9} "
                f"largest step={max(work):<7} mean step={mean_ms[-1]:.2f} ms"
                + (f" largest control={max(controls)}" if controls else "")
            )
        if len(largest) >= 2:
            # Work is deterministic. Time also catches costs no work budget
            # charges, such as hashing; it is compared from the second size,
            # past the first sizes' fixed overhead, and is noisier.
            # Compare from the second size: the smallest pays fixed costs
            # (the first call, the first store into a block) that later
            # sizes share, which reads as growth.
            first = min(1, len(largest) - 2)
            growth = largest[-1] / largest[first]
            timing = mean_ms[-1] / mean_ms[first]
            control = largest_control[-1] / largest_control[first] if largest_control[first] else 1
            verdict = "GROWS" if max(growth, timing, control) > 2 else "flat"
            print(
                f"{shape:18} largest step x{growth:.1f}, mean step time x{timing:.1f}, "
                f"largest loop/branch x{control:.1f} from N={sizes[first]} to "
                f"N={sizes[len(largest) - 1]}: {verdict}"
            )
    print(f"generated mdtests: {directory}")


if __name__ == "__main__":
    main()
