# Lean formalization of mixed-state cloning

The remaining proof obligations are closed. The current library contains 982 implementation modules; `lake build All` passes with 4,563 jobs. The complete current-tree axiom audit passed for 14,345 unique compiled project constants, using only the three standard Lean axioms. Source/artifact stability and saved-evidence validation passed.

The [manuscript-to-Lean map](PROOF_MAP.md) reconciles all 27 named manuscript results. See the [proof wiki](../docs/index.html), [result index](../docs/results/index.html), [completion scope](PROGRESS.md), [semantic review](verification/completion-semantic-review.md), and [fresh verification record](verification/kernel-compatible-pass/run.json).

Run all three checks from the repository root:

```sh
bash scripts/verify.sh all
```

For the Lean build and complete axiom audit alone, use `bash scripts/verify.sh lean`. From `formalization/`, build an individual entry point with e.g. `lake build ProjectorBounds`. The [verification instructions](scripts/README.md) distinguish saved-evidence validation from a new Lean run.

The [root README](../README.md#check-it-yourself) gives the Lean, [Comparator](verification/comparator/README.md), and [Nanoda](verification/nanoda/README.md) reproducer commands. Comparator passed all 27 statement comparisons and Lean kernel replay in trusted local mode without a sandbox. The unmodified Nanoda kernel passed all 83,433 exported declarations, covering every current project root and its dependencies.

The [compiler compatibility report](verification/kernel-compatibility.md) records the 30 `noncomputable` prefixes that suppress unused generated partial runtime helpers while preserving the mathematical definitions. The original 14,375-constant audit remains historical evidence.

Conjectures remain explicitly marked as conjectures. The exact all-density optimum remains open; its bounds are proved. The older conditional assembly is separate from the final physical constructions.
