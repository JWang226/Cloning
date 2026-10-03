# Quantum mixed-state cloning

This repository contains the mixed-state cloning manuscripts and their Lean 4 formalization. The formalization is organized by mathematical result, following the presentation of [openai/ten-proofs](https://github.com/openai/ten-proofs).

**Status: substantial partial formalization. The full cloning theorems are not yet proved end to end in Lean.** The checked component results and the conditional main-theorem assembly are distinguished below. The remaining mathematical inputs are explicit hypotheses, not project axioms.

- [Manuscript](Cloning/cloning.pdf) · [LaTeX source](Cloning/cloning.tex)
- [Version 2 manuscript](Cloning/paper_v2/cloningv2.pdf) · [LaTeX source](Cloning/paper_v2/cloningv2.tex)
- [Formalization status](formalization.yaml) · [Current progress](formalization/PROGRESS.md) · [Latest verification](formalization/verification/latest.json) · [Historical semantic audit](formalization/verification/seventh-pass/PROOF_AUDIT.md)

## The results

Each entry point imports the relevant proofs and checks the names of its principal declarations. All proof implementations live in [`formalization/Cloning/`](formalization/Cloning/).

| Result | Lean entry point | Proved scope |
| --- | --- | --- |
| Lifted sector fidelity | [LiftedSectorFidelity.lean](formalization/LiftedSectorFidelity.lean) | Exact finite-matrix sector factorization, trimming estimates, and convergence from explicit classical/sector approximation hypotheses |
| Projector bounds and channel converse | [ProjectorBounds.lean](formalization/ProjectorBounds.lean) | Concrete matrix bounds and Kraus-channel converse; physical representation identification remains separate |
| Classical rounding and Young moments | [ClassicalRounding.lean](formalization/ClassicalRounding.lean) | Actual Young fallback and error bounds; Euclidean root-hyperplane volume/covariance; rank-two law moments; general-rank local limit remains open |
| Occupation and coherent limits | [OccupationLimits.lean](formalization/OccupationLimits.lean) | Full Werner CPTP map and physical sandwich; thermal output limit; two-way compact-uniform coherent comparison in arbitrary finite dimension |
| Gaussian coherent-state mixtures | [CoherentGaussianMixtures.lean](formalization/CoherentGaussianMixtures.lean) | One- and finite-multimode trace-class Bochner integrals equal the corresponding thermal operators |
| Bosonic channels and seeded optimum | [BosonicSeededOptimum.lean](formalization/BosonicSeededOptimum.lean) | Seeded optimum; actual strongly continuous irreducible Weyl representation and algebraic covariant multiplier classification |
| Quantum fidelity inequalities | [QuantumFidelity.lean](formalization/QuantumFidelity.lean) | Actual quantum and continuous classical–quantum fidelity, weighted bounds, and sigma-finite Bochner Jensen |
| Compactness of CP maps | [CompactCPLimits.lean](formalization/CompactCPLimits.lean) | Explicit Gaussian CPTP averages and one common subsequence with an exactly covariant CP limit; trace loss is explicit |
| LAN transfer estimates | [LANTransfer.lean](formalization/LANTransfer.lean) | Transfer estimates and constructed pure-product two-way channels; mixed-state physical LAN remains open |
| Cloning theorem assembly | [ConditionalCloningTheorems.lean](formalization/ConditionalCloningTheorems.lean) | **Conditional:** known/unknown-spectrum conclusions from explicitly stated remaining inputs |

The audited library contains **195 modules and 1,832 source theorem/lemma declarations**. Its axiom audit covers **3,776 unique compiled project constants**, including definitions, instances, private declarations, and generated helpers. The navigation entry points add no new theorems.

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

The latest full checkpoint records a successful `lake build All` and a Lean
axiom-dependency audit of every compiled project constant. See the
[completion record](formalization/verification/eighth-pass/run.json) and
[current proof report](formalization/PROGRESS.md). The source has no `sorry`,
admitted proofs, or custom axioms; permitted axioms are `propext`,
`Classical.choice`, and `Quot.sound`.

From `formalization/`, verify the source and evidence hashes, or rerun the axiom audit after building:

```sh
python3 scripts/check_checkpoint.py
python3 scripts/audit.py --jobs 3
```

See [verification instructions](formalization/scripts/README.md) for the distinction between checking the saved evidence and running a fresh audit. The latest evidence includes the exact source snapshot, raw axiom reports, and source/configuration hashes. The historical [`seventh-pass`](formalization/verification/seventh-pass/) evidence is preserved separately; fresh audits do not overwrite it. This project has a Lean kernel dependency audit, not a Comparator certificate.

## Remaining mathematical inputs

The end-to-end formalization still requires:

- Universal arbitrary-idler reconstruction from CP/normality, amplifier Weyl intertwining, and the composite-gain reduction.
- Physical Schur/Cartan identifications for general Young sectors and uniform PBW/Fock estimates.
- General-rank Young-law concentration and compact-spectrum uniform local limits. Root-hyperplane geometry and compatibility fallback are now proved.
- Physical mixed-state LAN channels and their uniform errors. Pure-product comparison channels are now constructed in every finite dimension.
- The manuscript-specific flat-prior payoff and weighted trace estimates. Explicit Gaussian averaging and the continuous classical–quantum fidelity foundations are proved.
- The remaining PCT partial-trace, rotation, and Gaussian-mixture identifications.

The [current obligation table](formalization/PROGRESS.md) gives the exact proved
endpoints and remaining application steps. The full cloning assembly remains
conditional; the additional constructions do not remove those remaining premises.

## Source provenance

The formalization was developed against the frozen [`reference/cloning.tex`](formalization/reference/cloning.tex), whose SHA-256 and provenance are recorded in [`SOURCE.json`](formalization/SOURCE.json). That snapshot is not byte-identical to the manuscript drafts currently in this repository. The status above does not assert a complete formalization of the newer version 2 manuscript.

External sources, pinned revisions, and the adapted Physlib modules are documented in [`EXTERNAL_RESOURCES.json`](formalization/EXTERNAL_RESOURCES.json). The applicable [Physlib Apache-2.0 license](formalization/PHYSLIB-LICENSE.txt) and source headers are preserved. The layout reference supplies organizational conventions; its proofs, license, and independent-checking claims are not copied into this project.
