# json-c numeric-field example

This directory is a synthetic, frozen json-c-shaped fixture. Its C is written
for Click and is not copied from the json-c repository. It exercises a numeric
`double` field through the same pointer, contract, and memory-resource shape as
the reference-count example. It is a regression fixture, not a launch target;
current priorities follow [the rbtree launch roadmap](../../docs/internals/roadmap.md).

The fixture covers a read-only numeric accessor and a mutating scale operation.
The latter intentionally mixes an `int32` argument with a `double` field so the
C usual arithmetic conversion boundary is exercised at the source level.
