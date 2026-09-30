# Quantum mixed-state cloning

This repository contains the mixed-state cloning manuscripts and their Lean 4 formalization. The formalization is organized by mathematical result, following the presentation of [openai/ten-proofs](https://github.com/openai/ten-proofs).

**Status: substantial partial formalization. The full cloning theorems are not yet proved end to end in Lean.** The checked component results and the conditional main-theorem assembly are distinguished below. The remaining mathematical inputs are explicit hypotheses, not project axioms.

- [Manuscript](Cloning/cloning.pdf) · [LaTeX source](Cloning/cloning.tex)
- [Version 2 manuscript](Cloning/paper_v2/cloningv2.pdf) · [LaTeX source](Cloning/paper_v2/cloningv2.tex)
- [Formalization status](formalization.yaml) · [Detailed proof report](formalization/verification/seventh-pass/README.md) · [Semantic audit](formalization/verification/seventh-pass/PROOF_AUDIT.md)

## The results

Each entry point imports the relevant proofs and checks the names of its principal declarations. All proof implementations live in [`formalization/Cloning/`](formalization/Cloning/).

| Result | Lean entry point | Proved scope |
| --- | --- | --- |
| Lifted sector fidelity | [LiftedSectorFidelity.lean](formalization/LiftedSectorFidelity.lean) | Exact finite-matrix sector factorization, trimming estimates, and convergence from explicit classical/sector approximation hypotheses |
| Projector bounds and channel converse | [ProjectorBounds.lean](formalization/ProjectorBounds.lean) | Concrete matrix bounds and Kraus-channel converse; physical representation identification remains separate |
| Classical rounding and Young moments | [ClassicalRounding.lean](formalization/ClassicalRounding.lean) | Coordinate-lattice rounding and density bridge; both dimension-product moments for the concrete rank-two law |
| Occupation and coherent limits | [OccupationLimits.lean](formalization/OccupationLimits.lean) | Actual occupation CPTP channel and fixed-complex-amplitude trace-norm limit in the explicit two-level tensor model |
| Gaussian coherent-state mixtures | [CoherentGaussianMixtures.lean](formalization/CoherentGaussianMixtures.lean) | One- and finite-multimode trace-class Bochner integrals equal the corresponding thermal operators |
| Bosonic channels and seeded optimum | [BosonicSeededOptimum.lean](formalization/BosonicSeededOptimum.lean) | Actual channels, least-noise bounds, and exact fidelity optimum over arbitrary joint idler density states |
| Quantum fidelity inequalities | [QuantumFidelity.lean](formalization/QuantumFidelity.lean) | Finite- and infinite-dimensional fidelity, continuity, data processing, and weighted bounds |
| Compactness of CP maps | [CompactCPLimits.lean](formalization/CompactCPLimits.lean) | Common subsequence and completely positive trace-class limit, with sharp trace bound and covariance |
| LAN transfer estimates | [LANTransfer.lean](formalization/LANTransfer.lean) | Channel-composition and statistical comparison estimates assuming approximation bounds; no physical LAN construction |
| Cloning theorem assembly | [ConditionalCloningTheorems.lean](formalization/ConditionalCloningTheorems.lean) | **Conditional:** known/unknown-spectrum conclusions from explicitly stated remaining inputs |

The audited library contains **136 modules and 1,348 source theorem/lemma declarations**. Its axiom audit covers **2,753 unique compiled project constants**, including definitions, instances, private declarations, and generated helpers. The navigation entry points add no new theorems.

## Building the formalization

The project pins **Lean 4.29.0-rc6** and Mathlib commit [`f156f7a`](https://github.com/leanprover-community/mathlib4/tree/f156f7abd91ac67adb22bf999e5a71ba22e22e41). With [elan](https://github.com/leanprover/elan) installed, run from the repository root:

```sh
cd formalization
lake exe cache get
lake build All
```

Build an individual result by its entry-point name:

```sh
lake build BosonicSeededOptimum
```

[`All.lean`](formalization/All.lean) imports the complete library and all ten result entry points. Keep the committed toolchain and dependency manifest when reproducing the checked results.

## Proof checking

The saved seventh-pass checkpoint records a clean compilation and a full Lean axiom-dependency audit. The reorganized project also passes a fresh `lake build All`; see the [build record](formalization/verification/organized-build/result.json). It contains no `sorry`, admitted proofs, or custom axioms; the only permitted axioms are `propext`, `Classical.choice`, and `Quot.sound`.

From `formalization/`, verify the source and evidence hashes, or rerun the axiom audit after building:

```sh
python3 scripts/check_checkpoint.py
python3 scripts/audit.py --jobs 3
```

See [verification instructions](formalization/scripts/README.md) for the distinction between checking the saved evidence and running a fresh audit. The historical evidence is preserved in [`verification/seventh-pass/`](formalization/verification/seventh-pass/); it is not overwritten by the fresh-audit command. This project has a Lean kernel dependency audit, not a Comparator certificate.

## Remaining mathematical inputs

The end-to-end formalization still requires:

- The universal Weyl-covariant channel representation needed to extend the proved seeded optimum to all relevant channels.
- Physical Schur/Cartan identifications and uniform PBW/Fock estimates.
- General-rank Young laws and uniform local limits, including the root-hyperplane measure and compatibility fallback.
- Physical LAN channels and their uniform approximation estimates, and the continuous classical–quantum averaging constructions.
- The remaining physical embedding and channel identifications for the purification-and-cloning comparison.

The detailed [obligation table](formalization/verification/seventh-pass/README.md#remaining-end-to-end-obligations) records the boundary between each proved component and its remaining application.

## Source provenance

The formalization was developed against the frozen [`reference/cloning.tex`](formalization/reference/cloning.tex), whose SHA-256 and provenance are recorded in [`SOURCE.json`](formalization/SOURCE.json). That snapshot is not byte-identical to the manuscript drafts currently in this repository. The status above does not assert a complete formalization of the newer version 2 manuscript.

External sources, pinned revisions, and the adapted Physlib modules are documented in [`EXTERNAL_RESOURCES.json`](formalization/EXTERNAL_RESOURCES.json). The applicable [Physlib Apache-2.0 license](formalization/PHYSLIB-LICENSE.txt) and source headers are preserved. The layout reference supplies organizational conventions; its proofs, license, and independent-checking claims are not copied into this project.
