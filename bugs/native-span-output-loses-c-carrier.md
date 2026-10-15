# Native span output admission loses an ordinary C pointer carrier

Soundness: incomplete. The archived object-model implementation rejects a
verified ordinary C helper when its output resource owns a pointer field and
that field's backing buffer. This is a branch compatibility regression; no
false acceptance is demonstrated by this witness.

Priority: P2. Blocks activation of the affected object-model machinery.

## Reproduction

The following unchanged C and claims pass fresh checking, smart expansion,
checking the expanded source, and retained-session rechecking on the
`7920aaf0e`-based entry-fold extraction delivered in PR #937. The frozen archive
`e3d84a785` rejects the caller at `init` with
`native input span requires an exact unresolved or loaded identity`.
The conditional-record repair checkpoint `132cb424b` still rejects it.

# A C buffer resource survives a modular output call
```c filename=probe.c
struct buffer { int32* data; };
void init(struct buffer* owner, int32* data) { owner->data = data; }
void probe(struct buffer* owner, int32* data) { init(owner, data); }
```
```click
verifying "probe.c";
resource buffer(owner: struct buffer*) {
    owns owner->data;
    owns owner->data[0..1];
}
void init(struct buffer* owner, int32* data) {
    consumes *owner;
    consumes data[0..1];
    produces buffer(owner);
    ensures owner->data == data;
} by { execute(); fold(buffer(owner)); simp(); }
void probe(struct buffer* owner, int32* data) {
    consumes *owner;
    consumes data[0..1];
    produces buffer(owner);
    ensures owner->data == data;
} by { execute(); simp(); }
```
```expect
pass
```

## Evidence and invariant

The original detachable-buffer project fails at its first `detachable_buffer_init`
call with the same error. The fixed-baseline audit also records archive failures
in owned-split-buffer and owned-segmented-buffer with this message; those rows
need individual rechecking before crediting a common repair.

A bounded local probe shows source entry admitting the backing pointer with an
unresolved designation. During the modular output transfer, admission instead
receives a fresh symbolic pointer with no designation. The output's stored-pointer
value equation does not itself authenticate an object domain. Disabling inherited
address-only observation in the span reader preserves actual stored carriers, but
does not by itself repair the original project: the summary has already lost that
carrier before this read.

Keep automatic ordinary C resource annotations separate from explicit typed
validity. A legacy C resource must not activate the strict native profile merely
because its source pointer has a scalar type. Conversely, byte authority and
address equalities must never establish `valid_place`, replace an existing
complete domain, or authorize a native typed access. Repair output transport or
the compatibility annotation boundary without weakening these invariants.

## Recovery experiment

On the archive-based recovery branch, the resource-spec wrappers now preserve
legacy C span geometry without installing a typed input witness. Explicit
validity and direct native span requirements continue using the strict check;
known domains remain authoritative. Actual stored-carrier reads also disable
inherited address-only observation while retaining pointer-cell read authority.

This restores the unchanged detachable-buffer project and the reduced witness
in all four proof modes. Split-buffer and segmented-buffer advance past the
identity error but still fail at later folds (`owner->data[0..owner->split]`
and `owner->second_data[0..owner->second_len]`, respectively). They are not
restored projects. This is a preserved candidate on unmerged native-entry
machinery, not an upstream activation verdict.

## Acceptance

- Preserve the original C, contracts and resource bodies.
- Restore the reduced caller and original affected projects; check fresh,
  expanded-source and retained-session behavior for the reduced witness.
- Retain explicit `valid_place` rejection for a carrier lacking typed evidence,
  strict-native rejection, and bounds/type rejection for known complete domains.
- Check pointer-cell readability and initialization before reading its complete
  carrier, including when the surrounding context uses address-only observation.
- Attribute the introducing change; do not submit the accumulated archive as an
  independently validated activation or claim baseline acceptance closes P1
  pointer-domain soundness defects.


## Cursor input model follow-up

The original cursor shared pipeline passes all four proof modes after early
restoration of certified C input-field copies and preservation. This is not
a general closure of returned-view carrier matching. A narrower caller still
fails with the original `input_cursor_take.c`, its resource definitions and
its `input_cursor_take` contract from `examples/input-cursor/input_cursor.click`.
Append this C wrapper to the unchanged take source:

```c
int32 caller(struct input_cursor* owner) { return input_cursor_take(owner); }
```

Use the same resources and callee proof, and this caller:

```click
int32 caller(struct input_cursor* owner) {
    requires owner->pos < owner->len;
    owns input_cursor(owner);
    ensures result == old(owner->data[owner->pos]);
    ensures owner->pos == old(owner->pos) + 1;
    ensures owner->len == old(owner->len);
    ensures owner->data == old(owner->data);
} by { execute(); simp(); }
```

The caller receives an unresolved model identity for `owner`. Its returned
`readable_input` view uses a pointer with an exact loaded-read identity, but
matching reports that no viewed input backs it. This differs from the original
shared pipeline's legacy cursor arguments, which now work. Diagnose the input
and output complete read identities and their numeric spellings before changing
any equality rule. An address equation alone must not establish full identity.
The local reduction is preserved in
`target/cursor-take-output-preservation-reduction/`; the source above and the
tracked original example reconstruct it after build artifacts are removed.
