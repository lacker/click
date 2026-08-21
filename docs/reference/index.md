# Technical reference

The technical reference defines Click's public surface. It is lookup material:
each page describes what exists, where it is valid, and exactly what it means.
For explanations that connect several features, use the
[concepts](../concepts/index.md).

## Language

The [language reference](language/index.md) covers every user-visible Surface
Click construct and the supported C0 subset. It distinguishes Surface Click,
Kernel Click, and C fragments, and records unsupported neighboring forms.

## Tactics

The [tactic reference](tactics/index.md) covers simple certificate steps, smart
search operations, and structured control flow. It documents the proof state
each tactic accepts and produces.

## Command-line interface

The [command-line reference](cli/index.md) covers `click verify`,
`click profile`, `click expand`, and `click audit`, including their targets,
options, defaults, output, and exit behavior.

## Standard library

The [standard-library reference](library/index.md) covers every public theorem,
function, predicate, and abstract resource loaded from `stdlib/prelude.click`.

## Glossary

The [glossary](glossary.md) defines terms for readers who know programming but
are new to theorem provers.

## Examples and limitations

The [examples catalog](examples.md) maps features to their executable mdtests
and example projects. The [limitations](language/limitations.md) state current
language and verification boundaries.
