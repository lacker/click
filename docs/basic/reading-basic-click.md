# Reading A Basic Click File

When you open a `.click` file, read it in this order.

## 1. Source Files

Start at the top:

```click
verifying "file.c";
```

This tells you which C source the sidecar is proving.

## 2. Function Signature

Find the function block:

```click
int32 max(int32 a, int32 b) {
    ...
}
```

The signature should match the C function. At this point, ignore the contract
body and read the C code if you do not know what the implementation does.

## 3. Requirements

Read every `requires` clause:

```click
requires n >= 0;
requires valid_range(p[0..n]);
```

These are the assumptions for the proof. If the contract seems too strong, the
requirements are the first place to look.

## 4. Guarantees

Read each `ensures` clause as a separate promised fact:

```click
ensures result >= a by auto;
ensures result >= b by auto;
```

The guarantee says what Click is proving. The `by` clause says how.

## 5. Effects

For pointer code, check frame clauses:

```click
immutable src[0..n] by frame;
mutable dst[0..n] by frame;
```

These describe which memory is preserved and which memory may change.

## 6. Proof Details

Only after you understand the claim should you read the proof script:

```click
by {
    symbolic_execute();
    unfold(sorted);
    simp();
    close();
}
```

Most simple proofs use `auto`. A script usually means the proof needs a named
predicate unfolded, an existential witness, a loop VC, or explicit frame
reasoning.

## A Basic Reading Checklist

Ask:

1. Which C file is being verified?
2. Which C function does this block describe?
3. What assumptions does the proof make?
4. What facts does the function promise?
5. Is the proof about return values, memory, or both?
6. Is the proof automated, simplified, framed, or scripted?

That is enough to understand simple Click code. Intermediate Click adds memory
validity, aliasing, loops, predicates, pure functions, and eventually ghost
state.
