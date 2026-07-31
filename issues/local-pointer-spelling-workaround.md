# proof_advance_pointer_local carries a hand-written have

mdtest `proof_advance_pointer_local` (passing, not quarantined) works
around a certificate-generation gap: generation cannot synthesize a
point-qualified spelling (`at(statement(1).exit, selected)`) for a
local pointer that an `advance` abstracts into a fresh symbolic block —
no recorded program-point state binds the local to the abstracted
value. The mdtest's proof writes that `have` explicitly.

Measured dead end: teaching `synthesize_surface_pointer` to look up
pointer-valued locals does not help.

Done when: the explicit `have` deletes cleanly and generation finds the
spelling itself.
