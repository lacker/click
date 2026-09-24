# Soundness bugs found by the bug hunt

One `.md` file per confirmed or strongly evidenced soundness bug, parallel to
`issues/`: these are defects found by hunting, filed for the fixer rather than
for the roadmap. Each file states the violated invariant, a small intended
regression, and acceptance criteria. An accepted bug is deleted here when its
fix, regression coverage, and documentation land.

- [The annotation quantifier counter is raised into other producers' bands](quantifier-counter-rises-into-other-producers.md) — statically confirmed
- [The interface join erases a deallocation one arm performed](interface-join-erases-one-arm-deallocation.md) — machine-confirmed
