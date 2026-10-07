# Lean formalization of mixed-state cloning

The remaining proof obligations are closed. The current library contains 982 implementation modules; `lake build All` passes with 4,563 jobs. The complete current-tree shared axiom audit passed for 14,344 unique compiled project constants, with aggregate axioms `propext`, `Classical.choice`, and `Quot.sound`. Source/artifact stability and [saved-evidence validation](verification/cleanup-checkpoint.json) passed.

The [manuscript-to-Lean map](PROOF_MAP.md) reconciles all 27 named manuscript results. See the [proof wiki](../docs/index.html), [result index](../docs/results/index.html), [completion scope](PROGRESS.md), [original completion semantic review](verification/completion-semantic-review.md), [current statement review](https://jwang226.github.io/Cloning/statement-review.html), and [fresh verification record](verification/cleanup-pass/run.json). The current statement review preserves the original AI-assisted review scope and records fresh revalidation of three unchanged typed Lean probes.

Run all three checks from the repository root:

```sh
bash scripts/verify.sh all
```

For the Lean build and complete axiom audit alone, use `bash scripts/verify.sh lean`. From `formalization/`, build an individual entry point with e.g. `lake build ProjectorBounds`. The [verification instructions](scripts/README.md) distinguish saved-evidence validation from a new Lean run.

The [root README](../README.md#check-it-yourself) gives the Lean, [Comparator](verification/comparator/README.md), and [Nanoda](verification/nanoda/README.md) reproducer commands. Comparator passed all 27 statement comparisons and Lean kernel replay in trusted local mode without a sandbox. The unmodified Nanoda kernel passed all 83,432 exported declarations, covering every current project root and its dependencies.

The [compiler compatibility report](verification/kernel-compatibility.md) records the 30 `noncomputable` prefixes that suppress unused generated partial runtime helpers while preserving the mathematical definitions. The original 14,375-constant audit and subsequent 14,345-constant compatibility audit remain historical evidence. The [dead-code sweep](../DEAD_CODE_REPORT_2026-10-06.md) then removed one unused private theorem; the current audit covers 14,344 constants. The [elaboration report](../ELABORATION_REPORT_2026-10-06.md) records the measured proof cleanup.

Conjectures remain explicitly marked as conjectures. The exact all-density optimum remains open; its bounds are proved. The older conditional assembly is separate from the final physical constructions.
