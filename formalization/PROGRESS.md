# Mixed-state cloning formalization: completion record

The remaining proof obligations are closed. The current library contains **982 implementation modules**; the complete `lake build All` passed (**4,563 jobs**) and the all-declaration axiom audit passed for **14,345 unique compiled project constants**. Source/artifact stability passed. Comparator and the unmodified independent Nanoda kernel passed against this same audited source.

The [manuscript-to-Lean map](PROOF_MAP.md) reconciles **all 27 named theorem, proposition, lemma and corollary statements** of the frozen working manuscript snapshot. It records concrete declarations, dimension offsets, root-versus-squared fidelity, uniformity and order of limits. The [completion semantic review](verification/completion-semantic-review.md) records the statement differences found and resolved. Read the [paper](https://arxiv.org/abs/2609.35986); the audited snapshot remains the one identified in [SOURCE.json](SOURCE.json).

## Completed scope

- Actual all-CPTP known-spectrum and regular compact-set unknown-spectrum minimax limits, prescribed-channel compact-uniform attainment, and exact covariance.
- Literal Grassmann projector minimax, uniform attainment, finite converse, and general-rank dimension-moment bounds with explicit upper rates.
- Physical full-environment PCT fidelity and strict comparison; fixed rank-bound PCT support factorization, projector bounds and strict comparison.
- The same prescribed rank-bound PCT channel has finite guarantees for every state of rank at most r, with exact exponent rD−1 and uniform adversarial-state-sequence bounds.
- Physical Schur decomposition, multiplicities, characters, dimensions, Cartan maps and two-way compact-window LAN.
- Literal symmetric inverse-Gram PBW bases of complete weight spaces, uniform fixed-height O(N^(-1/2)) estimates, and Cartan splitting with exact product-binomial coefficients.
- General rank compression for arbitrary supported positive spectra, the channel identity for every complex input operator, and the physical Gibbs fidelity factorization.
- Arbitrary shrinking-window sector mixtures and character normalization; arbitrary-kernel lifted-fidelity factorization with the exact uniform bad-mass hypothesis.
- The exact uniform exponential Young-tail bound and compact-uniform raw randomized-dilation L1 convergence with moving covariance.
- Genuine Weyl/idler reconstruction and squeezing dilation, arbitrary covariant CP/TNI least-noise bounds, finite-inverse-limit weighted fidelity, and arbitrary positive hybrid targets.
- Gaussian optimum and converse for every real radius on the actual score polytope, with intrinsic measure normalization proved by Haar uniqueness.
- All-density minimax bounds, exact scalar infimum, ratio monotonicity and majorization counterexample, large-gain comparisons, physical small-error target brackets, boundary divergence, and actual qubit noncommuting limits.

## Verification

- Pinned Lean: `leanprover/lean4:v4.29.0-rc6`.
- Pinned Mathlib: `f156f7abd91ac67adb22bf999e5a71ba22e22e41`.
- Fresh integrated build: passed, 4,563 jobs.
- Complete compiled-declaration axiom audit: passed in [kernel-compatible-pass](verification/kernel-compatible-pass/run.json), covering 14,345 unique constants and 6,350 source theorems/lemmas.
- Allowed axioms: only `propext`, `Classical.choice`, `Quot.sound`; no placeholders or added project axioms.
- Source and compiled-artifact stability checks: passed.
- [Saved-evidence validation](verification/kernel-compatible-checkpoint.json): passed against the current source/configuration inventory.
- Audit completed (UTC): `2026-10-04T05:54:37.522297+00:00`.
- [Comparator run](verification/comparator/records/20261004T055545.209379Z/run.json): passed for 27 named-result statements and proof dependencies; trusted local execution, no sandbox.
- [Nanoda run](verification/nanoda/records/20261004T055629.624926Z/run.json): passed for every audited project root and its dependencies; 83,433 declarations checked.

Reproduce the audit using [scripts/README.md](scripts/README.md) and the [concise reproducer commands](../README.md#check-it-yourself). Comparator's [statement comparison and Lean replay](verification/comparator/README.md) and Nanoda's [independent Rust kernel check](verification/nanoda/README.md) remain distinct from the Lean build, axiom audit, and saved-evidence validation. Cached compiled-input provenance remains trusted.

The [compiler compatibility repair](verification/kernel-compatibility.md) adds 30 `noncomputable` prefixes across 15 files, retaining every old safe project declaration. The historical [completion audit](verification/completion-pass/run.json) covered 14,375 constants; the current full inventory has 14,345 after the 30 generated partial runtime helpers ceased to be generated. No root filtering or checker patch is used.

The initial [Comparator failure](verification/comparator/records/20261004T035736.789819Z/run.json) and [Nanoda export-safety failure](verification/nanoda/records/20261004T040757.497668Z/run.json) remain preserved as historical attempts.

The [offline proof wiki](../docs/index.html) provides twelve informal guides with verified Lean pointers, named-result statements, searchable source, and explicit scope notes.

## Scope boundary

The manuscript's degenerate-spectrum and fixed-rank formulas remain explicitly marked as conjectures. The exact all-density asymptotic optimum is not claimed: the proved lower and upper bounds remain distinct. External literature attributions and speculative discussion are not additional proved theorems.

The older conditional assembly in `Cloning/Main.lean` remains unchanged under its original hypotheses. The final physical main theorems are separate unconditional constructions. “Unconditional” here means no unproved mathematical input beyond the stated model assumptions and the three standard Lean axioms.

The source is the frozen working manuscript identified in [SOURCE.json](SOURCE.json); its hash is unchanged. Equality to other manuscript versions is not asserted. The [previous progress document](verification/pre-completion-progress.md), [twelfth-pass audit](verification/twelfth-pass/run.json), and earlier records remain preserved as historical evidence.
