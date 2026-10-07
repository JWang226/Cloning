# Lean proof maintenance

Keep public declaration statements, assumptions, and the result-index `#check`
commands intact during performance cleanup. Treat an uncalled public declaration
as part of the proof API; textual searches alone do not establish that it is dead.

Profile a suspected hotspot before changing imports, splitting a module, adding
an instance cache, or rewriting a proof for speed. Compare one intervention at a
time with matched imports and flags, at least three pairs for elapsed claims,
and plain compiler CPU controls when profiler formatting is material. Retain the
evidence and revert changes without a demonstrated benefit. Do not raise
heartbeat limits to conceal a regression.

The measured Weyl integral proof rewrites `vectorProjector` to `rankOneOperator`
before its `change`. Preserve this local equality bridge unless a new controlled
measurement supports replacing it: conversion under `tracePairing` can unfold
chosen basis and CFC data. Use existing named trace equalities to bridge bundled
trace representations where a profile demonstrates that conversion is expensive;
do not roll out similar edits to unmeasured files.

The measured `wernerOutput_trace_one` proof uses `traceCLM_apply` and the channel's
`trace_preserving` equality explicitly. Preserve that bridge under the same
measurement rule; restoring the old `change ... at htp` reintroduces a measured
conversion hotspot.

For project-only elaboration benchmarks, preserve package artifacts and invalidate
only the owned targets recorded by `scripts/benchmark_elaboration.py`. Keep the
pinned Lean/Lake configuration fixed. Current legacy module headers are an
explicit compatibility choice; a global modern-header migration needs its own
API, proof-body audit/export coverage, and performance evidence.

The [elaboration report](../ELABORATION_REPORT_2026-10-06.md) and archived evidence
document the measurements.
After proof changes, refresh the selected shared audit and both checker records
before presenting them as verification of the current sources. Keep historical
records immutable and the semantic review's recorded scope unchanged.
