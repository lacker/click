# proof.rs panic sites reachable from user input

Status: open
Claimed:

Scope (design-review honorable mention): 35 panic!/unreachable! sites
in src/lang/click/proof.rs are reachable from user-dependent data
(e.g. the old proof.rs:20043) and turn diagnosable proof bugs into
crashes. Convert the reachable ones to ClickError diagnostics.

Method: enumerate with `grep -n 'panic!\|unreachable!' src/lang/click/proof.rs`,
classify each as invariant-true (fine) vs user-reachable (fix), and
convert the latter with a targeted mdtest per conversion where
practical.

Done when: no user-reachable panic remains, each conversion has a
diagnostic message naming the failing construct, gates green.
