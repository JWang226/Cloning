# Compiler helper compatibility repair

The first complete Nanoda attempt failed during export validation, before the
Nanoda parser or kernel ran. Its historical input was the passed
[completion audit](completion-pass/run.json), covering 982 implementation
modules and 14,375 project constants. The [failed run](nanoda/records/20261004T040757.497668Z/run.json)
and [failure diagnostic](nanoda/records/20261004T040757.497668Z/failure-diagnostic.json)
retain that scope; this attempt provides no independent-kernel certificate.

The export contained every requested root: 14,403 roots, including the project
inventory and builtin prerequisites, and 83,463 declarations after dependency
traversal. Its [declaration diagnostic](nanoda/records/20261004T040757.497668Z/export-diagnostic.json)
identified exactly 30 definitions with `safety = partial`. All were generated
`_unsafe_rec` helpers. The pinned [Lean elaborator](https://github.com/leanprover/lean4/blob/00659f8e6071d7e46131ed643bf8003b99b044e9/src/Lean/Elab/PreDefinition/Basic.lean#L282-L298)
creates these helpers for recursive executable code; their names do not mean
that the corresponding mathematical definitions were declared `partial`.
The pinned, unmodified [Nanoda parser](https://github.com/ammkrn/nanoda_lib/blob/418320295890faed83a96fd97907b12a3b6728c2/src/parser.rs#L759-L760)
rejects both unsafe and partial definitions. The runner's strict export guard
therefore rejected a stream that the actual parser also cannot accept.

The archived [dependency scan](nanoda/records/20261004T040757.497668Z/CheckPartialDependencies.lean)
inspected the types and available values of 492,016 safe constants in the full
imported environment. It found zero references to any of the 30 helpers, as
recorded in the [scan log](nanoda/records/20261004T040757.497668Z/partial-dependencies.log).
This establishes the recorded reference property; it is not a type-checking
verdict or an identity comparison between the old and rebuilt environments.

The source repair adds exactly 30 `noncomputable` prefixes across 15 files:
29 definitions and one instance. The [annotation patch](kernel-compatibility/annotations.patch)
changes only those prefixes. Declaration signatures, recursive equations,
mathematical proof bodies, and the reference manuscript are unchanged as source
text. The [line-by-line validation](kernel-compatibility/annotation-validation.json)
confirms exactly 30 prefix insertions and no other source-text changes in those
15 files; the archived repair evidence has a [checksum manifest](kernel-compatibility/SHA256SUMS.json).
Representative affected files are [PBWNormalOrdering.lean](../Cloning/PBWNormalOrdering.lean)
and [YoungTwoRowMoment.lean](../Cloning/YoungTwoRowMoment.lean); the complete
[source-location inventory](nanoda/records/20261004T040757.497668Z/partial-source-locations.json)
identifies every originating declaration. These annotations request that Lean
omit executable code generation for those declarations.

The [compiled definition comparison](kernel-compatibility/comparison.json)
passed after the integrated build. All 30 originating declarations have exactly
identical metadata-stripped types and values, universe parameters, and safety
flags before and after the repair. The archived before/after SHA-256 records
agree; the full representation files remain in local scratch storage.

The [rebuilt project inventory](kernel-compatibility/project-safety-inventory.json)
contains 14,345 unique declarations across 982 implementation modules, with
zero unsafe and zero partial declarations. The [name-set comparison](kernel-compatibility/project-safety-comparison.json)
shows that exactly the 30 generated runtime helpers disappeared, with no new
declarations and no removal of any old safe project declaration.

The verification policy still selects every project constant from the bound
audit, including private and generated declarations, and recursively exports
all dependencies. No root is filtered from an existing inventory, and neither
the exporter nor Nanoda is patched. The strict safety checks and the allowlist
`propext`, `Quot.sound`, `Classical.choice` remain unchanged; see the
[Nanoda runner](nanoda/reproduce.py) and its [scope instructions](nanoda/README.md).

An [unbound preliminary diagnostic](nanoda/diagnostics/20261004T051640.548545Z/diagnostic.json)
exported every one of the 14,345 rebuilt project roots and the fixed builtin
prerequisites. Strict export validation passed for 83,433 declarations. Nanoda
reported no type-checking errors, but its [actual output](nanoda/diagnostics/20261004T051640.548545Z/nanoda.stdout)
also reported a pretty-printer error because the axiom report had no output
destination. The strict success gate rejected that qualified result. The
configuration now routes the axiom report to stdout, and a preflight guard
rejects a missing report destination; no kernel or axiom policy changed.
This diagnostic is separate from the required audit-bound full runner.

The fresh full build passed all 4,563 jobs. The all-declaration audit in
[kernel-compatible-pass](kernel-compatible-pass/run.json) passed for all 14,345
current project constants and 6,350 source theorems/lemmas, with only the three
permitted axioms. All source and artifact integrity gates passed. The
[saved-evidence check](kernel-compatible-checkpoint.json) verified 995 evidence
files against the current source/configuration inventory. The tool lock now
binds this new audit. The [final Comparator run](comparator/records/20261004T055545.209379Z/run.json)
passed all 27 explicit statement comparisons, dependency and axiom checks, and
Lean kernel replay in trusted local mode without a sandbox. The
[final Nanoda run](nanoda/records/20261004T055629.624926Z/run.json) passed all
83,433 exported declarations, including every current project root and all its
dependencies, with the exact unqualified success message and all post-checks.
The historical count of 14,375 remains attached to the historical completion
audit. Cached compiled-input provenance remains trusted; the two checker
verdicts do not replace the manuscript-to-statement semantic review.
