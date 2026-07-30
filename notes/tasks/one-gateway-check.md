# One-gateway check: no bypass around TacticCertificate replay

Status: open
Claimed:

Scope: one bounded code audit (reading task, not a refactor) verifying
that every smart-tactic success commits through TacticCertificate
replay with no bypass path. Follows from the settled invariant that
TacticCertificate is the smart/simple boundary.

Where to look: src/lang/click/proof.rs — replay_smart_plan,
lower_internal_plan_to_surface_certificate, replay_internal_plan, and
every call site of the internal-plan executor; confirm each smart
acceptance path routes through certificate replay and that no
error-recovery or legacy arm accepts an internal plan directly.

Done when: a short written finding (extend this file) either confirming
the single gateway or listing concrete bypass sites as new tasks.
