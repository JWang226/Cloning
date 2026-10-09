# Follow-up to the statement audit · 8 October 2026

The comments identify one substantive mismatch: Lean proves projector optimality and a uniformly attaining cloner, but does not identify that cloner with the paper’s finite transportation-LP construction. The PCT identification is already proved, and the physical Schur decomposition, multiplicities and character have explicit supporting theorems. The frozen manuscript also matches official arXiv v1 byte-for-byte.

This is an AI-assisted source trace against implementation revision `ae86c08f2861d30ac1ec681b52ecd7c2675e9457`, responding to the supplied comments. It is not a fresh statement review of all 27 results, external peer review, or a new Lean, Comparator or Nanoda run. It supplements the earlier review of Theorems 1.1–1.3 without changing that review’s scope or saved evidence.

Paper: [Asymptotically Optimal Mixed-State Cloning, arXiv v1](https://arxiv.org/abs/2609.35986v1).

## Theorem 1.3: a real construction mismatch

The paper’s Theorem 1.3 names the cloner from §4.2, which selects a minimizer of a finite transportation problem. The Lean target instead names `Cloning.TensorCloning.prescribedRankFlatChannel`, using `Cloning.YoungFlatCoupling.positiveFlatCoupling` from [YoungFlatCouplingPhysical.lean](../Cloning/YoungFlatCouplingPhysical.lean). This density-overlap coupling has proved exact marginals and supports the proved asymptotic attainment.

The relevant endpoints are [PhysicalFlatGrassmannTheorem.lean](../Cloning/PhysicalFlatGrassmannTheorem.lean) and [TensorCloningPrescribedLimits.lean](../Cloning/TensorCloningPrescribedLimits.lean). They certify the same optimal value and a uniformly attaining channel. They do not certify the particular finite LP-selected channel in the paper’s attainment sentence. This qualification was already recorded in the [proof map](../PROOF_MAP.md) and the earlier projector statement review.

The appropriate next proof task is to formalize the paper’s finite LP selection and prove its channel attains the limit. Equality with the overlap coupling is not necessary and should not be assumed. The current coupling could serve as a feasible witness for the LP’s good-event estimate if its bound matches the paper’s cost and tolerance sequence. Alternatively, a manuscript revision could explicitly allow this different attaining construction. Neither proof nor manuscript has been changed in this follow-up.

## PCT: the physical identification already exists

The comment’s second “untraced identification” is resolved by existing Lean declarations:

- [WernerPhysicalChannel.lean](../Cloning/WernerPhysicalChannel.lean), `Cloning.GeneralSymmetricOccupation.wernerChannel_physical_sandwich`, identifies the occupation channel with the binomial-scaled physical symmetric-projector sandwich. Its extra identity is on the whole added tensor register.
- [PCTGlobalWerner.lean](../Cloning/PCTGlobalWerner.lean), `Cloning.PCTGlobal.sectorChannel_physical_sandwich`, transports that equality into the physical register for every complex occupation input matrix.
- [PCTGlobalPhysical.lean](../Cloning/PCTGlobalPhysical.lean), `channel_matrix_apply` and `channel_apply`, identify the full fixed CPTP channel with the constructed Haar-moment purifier, literal Werner cloning, regrouping and partial trace on arbitrary inputs. On density tensor powers the purifier equals the literal Haar mixture; `channel_tensorPower` gives the resulting physical PCT action.
- [PCTRankPurificationGeneralHaar.lean](../Cloning/PCTRankPurificationGeneralHaar.lean), `Cloning.PCTRankPurification.channel_of_purification`, proves the rank-bound version for any unit purification with the required reduced density. It does not require full rank or simple spectrum.

The transport has explicit support: [GeneralSymmetricOccupation.lean](../Cloning/GeneralSymmetricOccupation.lean) identifies the occupation isometry’s range with the permutation-invariant symmetric subspace; [GeneralSymmetricDimension.lean](../Cloning/GeneralSymmetricDimension.lean) proves the binomial dimension. The purifier’s Haar action is established in [PCTPurificationChannelAction.lean](../Cloning/PCTPurificationChannelAction.lean). The headline full-rank channel in [PCTPrescribedFull.lean](../Cloning/PCTPrescribedFull.lean) is defined using this physical PCT channel.

Thus the proposed weakening to “PCT in occupation form” is unnecessary. The audit did not trace these bridges; that does not mean the bridges are absent.

## Schur sectors: proved physical content and narrower remaining bridges

The library constructs the actual tensor representation and proves its decomposition, rather than assuming a Schur–Weyl decomposition premise:

| Physical assertion | Existing declaration |
|---|---|
| Orthogonal, exhaustive tensor-register splitting | `Cloning.TensorLie.recursivePhysicalDecomposition_is_decomposition` in [TensorSchurMultiplicityDecomposition.lean](../Cloning/TensorSchurMultiplicityDecomposition.lean) |
| Every physical copy is isometric to the canonical partition sector, intertwining all matrix tensor powers | `PhysicalHighestTensor.canonicalIsometry` and `canonicalIsometry_tensorOperator` in [TensorSchurDecompositionData.lean](../Cloning/TensorSchurDecompositionData.lean) |
| Exact standard-tableau multiplicity, with no count or decomposition premise | `recursivePhysicalDecomposition_copyCount` in [TensorSchurDecompositionMultiplicity.lean](../Cloning/TensorSchurDecompositionMultiplicity.lean) |
| Physical character’s Weyl alternant identity | `partitionCharacterPolynomial_weyl` in [TensorSchurDecompositionWeylCharacter.lean](../Cloning/TensorSchurDecompositionWeylCharacter.lean) |
| Character evaluation agrees with the physical partition function for nonnegative spectra | `eval_physicalCharacterPolynomial_nonneg` in [TensorSchurDecompositionCharacter.lean](../Cloning/TensorSchurDecompositionCharacter.lean) |

The canonical sector is generated by actual lowering words from a constructed highest tensor; its irreducibility is proved in [TensorCyclicSectorIrreducible.lean](../Cloning/TensorCyclicSectorIrreducible.lean). [TensorSchurDecompositionIsometry.lean](../Cloning/TensorSchurDecompositionIsometry.lean) assembles the physical copies into an isometric block decomposition and proves tensor-power intertwining. The paper defines its sector character by the trace of the highest-weight representation, so these results supply substantial correspondence evidence.

Two more specific identifications remain untraced in the library:

1. A separately constructed Specht module, its dimension, and a simultaneous `U(d) × S_n` equivariant decomposition. The existing physical `U(d)` decomposition and exact tableau multiplicities do not themselves formalize the symmetric-group action on multiplicity spaces.
2. A direct equality between the physical character and the separate semistandard `Cloning.YoungGeneral.schurPolynomial` definition. The physical Weyl identity is proved, but this cross-definition equality is not. Since `physicalSectorCharacter` uses a trace norm, any such evaluation statement must state the needed nonnegative-spectrum hypothesis.

These boundaries should be distinguished from a missing physical decomposition or an assumed multiplicity formula.

## Provenance and checker scope

The [new provenance record](arxiv-v1-provenance-2026-10-08.json) records a verified HTTPS retrieval of the official arXiv v1 source archive and direct byte comparison of its manuscript member with the frozen reference. Both are 197,184 bytes with SHA-256 `6f2453656031201968aef5cc9c043f7116bb7a1ed1cd2cebb2b905e3df94038d`. This resolves the arXiv v1 version question. [SOURCE.json](../SOURCE.json) retains the historically accurate uncertainty about the original uploaded attachment; no later-version identity is asserted.

Comparator checks a project-relative specification. Its 27 target types are written explicitly, but share this project’s mathematical definitions and were not independently authored or reviewed merely because Comparator passes. The pinned checker compares target types and their defining constants; it separately audits solution-proof axioms and replays proofs in Lean’s kernel. It does not require the proofs to match the challenge’s deliberate `sorry` placeholders, and does not establish correspondence with the English paper. Nanoda provides the separate independent Rust kernel check, not independent manuscript interpretation.

Lightweight consistency checks confirmed that the selected October 7 Comparator record matches its saved status hash, the 27 claims, current pinned wrappers/configuration/toolchain, and the frozen manuscript hash. Current README and wiki wording now distinguishes these checks and links the physical bridges. Historical run records, challenge files, proof sources and the earlier semantic review remain unchanged.
