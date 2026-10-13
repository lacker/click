# Clamp

The repository README's quick start. `clamp.c` is ordinary C using `int`, and
`clamp.click` proves that the result lies in `[lo, hi]` and that a value
already in range is returned unchanged. The requirement `lo <= hi` is needed:
without it, `x < lo` returns `lo`, which can exceed `hi`.

`by auto` proves both postconditions. Run `click verify clamp.click` in this
directory; `tests/examples.rs` checks that the README shows these files and
that command's output.
