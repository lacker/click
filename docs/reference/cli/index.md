# Command-line interface

The `click` executable provides four subcommands:

```text
click verify   Verify a sidecar, proof unit, project, or examples directory.
click profile  Measure verification and identify slow tactics.
click expand   Replace smart proof source with its checked simple certificate.
click audit    Check expansion across a project or repository.
```

Use `click --help` for the command list and `click COMMAND --help` for exact
command syntax. A successful command, including a help request, exits with
status 0. Invalid arguments, failed verification, exhausted hard limits, and
I/O or audit failures print a diagnostic to standard error and exit with
status 1.

## Commands

- [`click verify`](verify.md) is the ordinary correctness command.
- [`click profile`](profile.md) attributes verification work after correctness
  is established.
- [`click expand`](expand.md) rewrites selected smart proof source into an
  independently replayed certificate.
- [`click audit`](audit.md) checks the expansion boundary across many sites.

## Common target forms

Commands accept one or more of these target forms, as documented on each
command page:

- a `.click` sidecar;
- a one-based `PATH:LINE:COLUMN` source location;
- a project directory containing sidecars;
- a directory whose immediate subdirectories are projects;
- an mdtest file or mdtest directory;
- the repository root for a combined audit.

Use `--` before a positional path that begins with a hyphen. Duration values
accept plain seconds or a number followed by `ms`, `s`, `m`, or `h`.

## Environment variables

[Environment variables](environment.md) documents user-facing diagnostics,
fixture selection, and contributor-only A/B controls. Most users do not need
environment variables for ordinary verification.
