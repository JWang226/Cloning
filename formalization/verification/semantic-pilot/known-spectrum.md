# Known-spectrum statement audit pilot

**No excess premise or mathematical mismatch found in the reviewed endpoints.** This covers the all-channel value limit and compact-uniform fidelity of the Lean prescribed known-spectrum channel. Correspondence of that copy-based channel to the manuscript construction was inspected through its operational components and existing character/block identities; this review does not add a single all-input operator-equality theorem to the manuscript's abstract Schur lifting.

This is a fresh agent review, not external peer review or a certificate that natural-language mathematics has been translated correctly. It selectively applies the [lean-statement-audit checklist](https://github.com/scottnarmstrong/LeanAutoformalizationSkills/blob/main/skills/lean-statement-audit/SKILL.md); no skill was installed, no draft-proof workflow adopted, and no theorem source changed. Raw source reconstruction preceded implementation inspection and consultation of the earlier completion review.

## Pinned scope and paper reconstruction

Paper reader reference: [Asymptotically Optimal Mixed-State Cloning, Theorem 1.1 and §§1.1, 2.1, 2.3, 3.3](https://arxiv.org/abs/2609.35986). The audited mathematical text is the repository's frozen reference snapshot, not an assertion that any later arXiv revision has identical bytes. Its SHA-256 is `6f2453656031201968aef5cc9c043f7116bb7a1ed1cd2cebb2b905e3df94038d`.

Source locations below are plain provenance locators, not download links: `formalization/reference/cloning.tex:163–205` gives the standing regime and formulas; `300–313` states Theorem 1.1; `864–990` defines the finite channel; `1258–1275` proves uniform achievability; `1737–1763` completes the converse.

Independently reconstructed statement: fix finite dimension D≥2; mₙ/n→γ>1; fix a real spectrum p₁>…>p_D>0 with sum 1. With ρₚ,U=U diag(p) U*, compare the **entire** output against ρₚ,U tensor mₙ using **unsquared** root fidelity ‖√A√B‖₁. The limit of sup over every n→mₙ CPTP channel, followed by inf over every U∈U(D), is the product over i<j of

`(√γ + √((pⱼ/pᵢ)(γ−1+pⱼ/pᵢ))) / (γ+pⱼ/pᵢ)`.

The prescribed channel may depend on p, but not U. For every compact K inside the simple full-rank chamber, one sample threshold works for **all p∈K and all U** at each tolerance ε>0. The spectral set may be empty or a singleton; no interior/regular-closure premise belongs to this known-spectrum statement. The finite convention is partial trace when mₙ≤n, including identity at equality.

Targets:

- [knownSpectrumValue_tendsto](https://github.com/JWang226/Cloning/blob/d2ccb294f6a69d2cd65aa807cb9bfd1d9f829999/formalization/Cloning/PhysicalCloningKnownTheorem.lean#L45), namespace `Cloning.TensorCloning`, lines 45–61.
- [eventually_uniform_prescribedKnownSpectrumChannel_payoff](https://github.com/JWang226/Cloning/blob/d2ccb294f6a69d2cd65aa807cb9bfd1d9f829999/formalization/Cloning/TensorCloningPrescribedLimits.lean#L29), same namespace, lines 29–38.

## Complete exported binder ledger

There are no exported universe or instance binders in either target. Standard finite-index, Hilbert-space, topology, matrix and order instances are synthesized for the concrete carriers, not supplied by the caller. Each table counts its own rows; expanded fields are listed separately rather than silently treating a spectrum bundle as one premise.

Value-limit target: **6 binders: SOURCE 1, STANDING 4, TYPING 1, EXCESS 0**.

| Binder | Information/type | Class | Source correspondence |
|---|---|---|---|
| k | Implicit `ℕ`; physical dimension k+1 | TYPING | Finite dimension, source 163 |
| p | Explicit `SimpleSpectrum (k+1)` | SOURCE | Every p in the simple chamber, 174–175 and 301 |
| m | Explicit `ℕ → ℕ` | STANDING | Output-size sequence, 163–171 |
| g | Explicit `ℝ` | STANDING | Fixed limiting gain γ, 164–165 |
| hg | Explicit `1 < g` | STANDING | Gain greater than one, 165 |
| hratio | Explicit convergence of `(m n : ℝ)/(n : ℝ)` to g | STANDING | Exact gain convergence, 164–165 |

Uniform target: **9 input binders: SOURCE 2, STANDING 4, TYPING 3, EXCESS 0**.

| Binder | Information/type | Class | Source correspondence |
|---|---|---|---|
| d | Implicit `ℕ`; physical dimension d+1 | TYPING | Finite dimension, 163 |
| K | Explicit `Set (SimpleSpectrum (d+1))` | SOURCE | Every compact spectral set, 311–312 |
| hK | Explicit `IsCompact K` | SOURCE | Compactness, 311–312 and 1260 |
| m | Explicit `ℕ → ℕ` | STANDING | Output sizes, 163–171 |
| γ | Explicit `ℝ` | STANDING | Fixed limiting gain, 164–165 |
| hγ | Explicit `1 < γ` | STANDING | Gain condition, 165 |
| hgain | Explicit convergence of `(m n : ℝ)/n` to γ | STANDING | Gain regime, 164–165 |
| ε | Explicit `ℝ` | TYPING | Epsilon form of uniform convergence, 311–312 and 1270–1274 |
| hε | Explicit `0 < ε` | TYPING | Positive convergence tolerance, same locations |

The conclusion also binds n inside `Eventually` (TYPING), then p (SOURCE), its membership proof p∈K (SOURCE), and U (SOURCE). Their order is `∀ ε>0, eventually n, ∀ p∈K, ∀ U`; the threshold cannot depend on the current p or U. There is no selected eigenbasis, maximizer, or bounded subset of competitors.

Common expansion of every `SimpleSpectrum D` occurrence: **4 fields: SOURCE 1, STANDING 3, EXCESS 0** ([Main.lean](https://github.com/JWang226/Cloning/blob/d2ccb294f6a69d2cd65aa807cb9bfd1d9f829999/formalization/Cloning/Main.lean#L24), 24–28).

| Field | Type | Class | Source correspondence |
|---|---|---|---|
| eigenvalue | `Fin D → ℝ` | SOURCE | Real spectral vector p, 172–180 |
| positive | `∀ i, 0 < eigenvalue i` | STANDING | Full rank, 175 |
| strictAnti | `StrictAnti eigenvalue` | STANDING | Strictly decreasing eigenvalues, 175 |
| normalized | `∑ i, eigenvalue i = 1` | STANDING | Trace-one affine hyperplane, 172–175 |

`StrictAnti` expands to the pairwise implication i<j→pⱼ<pᵢ. It is not a spectral-gap estimate supplied to the theorem. The compact topology is induced by the eigenvalue map, with an embedding theorem ([PhysicalCloningConverseSpectrum.lean](https://github.com/JWang226/Cloning/blob/d2ccb294f6a69d2cd65aa807cb9bfd1d9f829999/formalization/Cloning/PhysicalCloningConverseSpectrum.lean#L12), 12–32); compactness therefore refers to the ordinary spectral topology, not an unrelated chosen topology.

Two harmless extensions are explicit: Lean includes D=1, which covers every D≥2 requested in the paper; m maps to naturals and may be zero at finitely many indices, and n starts at zero with Lean's total real division convention. The proved `eventually_output_gt_input` shows the gain regime eventually gives mₙ>n>0. No finite exceptional value affects either limit. These are domain extensions, not hidden extra premises.

## Definition and carrier audit

| Object/expanded fields | Inspection and verdict |
|---|---|
| `PairIndex`, `SimpleSpectrum.ratio`, `orbitalValue`, `Thermal.modeFactor` | Exact literal product over each i<j once, with pⱼ/pᵢ and the displayed rationalized factor. BODY_MATCH/PUBLIC_CARRIER: OK on the source domain. No optimizer or asserted limit is used. Main 30–43; Thermal 220–221. |
| `Register`, `TensorRegister` | Finite complex Hilbert registers `lp (A→ℂ) 2`, with tensor basis indexed by `Fin n → Fin D`. These are the complete n-copy registers, not symmetric sectors or marginal-state carriers. PCTPartialTrace 14; TensorLieGenerators 21. |
| `MatrixFidelity.State` | Fields: matrix (TYPING), positive semidefinite (STANDING), trace=1 (STANDING). The actual orbit matrix is U diag(p) U*. The target and input tensor states are the literal matrix tensor powers; their norm/trace normalization is proved. MatrixFidelity 102–105; PCTPhysicalState 19–23, 41–50; PCTUnitaryTransportChannels 15–21. |
| `unitary (Matrix … ℂ)` | Fields: underlying square matrix (TYPING), U*U=1 and UU*=1 (both STANDING). These enumerate the entire U(D); they impose no covariance or chosen-frame condition on the competitor. Mathlib Algebra/Star/Unitary 35–36. |
| `QuantumChannel` | Complex-linear trace-class map (TYPING); positivity, trace preservation, complete positivity (each STANDING, exactly the source meaning of channel). `IsCompletelyPositive` quantifies every finite ancilla and every positive operator block; `BlockPositive` tests all vectors, including entangled vectors. No channel covariance, Gaussian form, sector action, LAN property, contraction bound or asymptotic estimate is a field. InfiniteTraceClassChannels 126–132; InfiniteCompletelyPositive 25–31, 167–171. |
| `PositiveTraceClass`, `TraceClass` | Actual bounded operators with the analytic trace-class property, and positivity. These are source carrier restrictions (STANDING) plus packaging (TYPING), not a substituted abstract payoff. The trace-class property is summability of the absolute operator in a Hilbert basis, with basis independence proved. InfiniteTraceClass 73–77, 246–248; InfiniteTraceClassSpace 196; HybridStates 29–30. |
| `rootFidelity`, `statePayoff`, `spectrumPayoff` | Root fidelity is exactly trace norm of √A√B. The input full tensor state is acted on by the actual channel; the target is the full m-copy tensor state. There is no square, purification surrogate, average over sites, or built-in limiting answer. InfiniteFidelity 23–25; HybridStates 40–41; TensorCloningPayoff 14–17, 33–39. |
| `knownSpectrumValue`, `LAN.minimaxValue` | Literal channel supremum outside unitary infimum. The theorem proves payoff is in [0,1] and supplies an actual admissible channel, avoiding empty/unbounded conditional-complete-order fallback behavior. TensorCloningPayoff 43–44; LAN 52–53; PhysicalCloningKnownTheorem 17–29. |

All fields above fall into STANDING or TYPING; **no EXCESS structure field was found**. Literal definitions have WELL_DEFINEDNESS/CHARACTERIZATION: N/A_LITERAL. The analytic trace norm selects a witness basis, but `traceNorm_eq_of_hilbertBasis` proves independence of that selection; BODY_MATCH and CHOICE_INDEPENDENCE: OK. No choice selects an optimal physical payoff.

### Prescribed finite channel

[TensorCloningChannel.lean](https://github.com/JWang226/Cloning/blob/d2ccb294f6a69d2cd65aa807cb9bfd1d9f829999/formalization/Cloning/TensorCloningChannel.lean#L97) constructs the channel from a complete physical Schur-copy decomposition. The output-copy weights are actual sector characters and are independent of the input copy; grouping them by shape is **proved** to give the exact target Young-label law (`tensorYoungPMF_eq_map_copies`, TensorLANEmbeddingSchurWeights 32–36). Equal characters within a shape give uniform multiplicity-copy sampling (TensorSchurDecompositionPMF 29–61). This is the copy-coordinate implementation of target-label sampling followed by a maximally mixed multiplicity register.

Compatible sectors apply the actual Cartan channel with coefficient dim(input)/dim(output); its all-complex-input matrix action is proved (`physicalCartanChannel_partitionMatrixOperator`, TensorCartanChannel 124–140; Compression 82–84). Incompatible sectors use trace replacement by I/dim (`partitionInvariantState_op`, TensorCloningGlobalCovarianceState 21–23; TensorCloningChannel 30–45). Those branches are expressly prescribed by the paper at 904–911, so they are not invented fallback values. `prescribedChannel` then selects exact partial trace at m≤n and the constructed cloner at m>n (TensorCloningPrescribed 13–36, 52–54), matching source 167–171.

BODY_MATCH: OK for the reviewed operational components and stated branch conventions. PUBLIC_CARRIER: OK on the theorem's spectra/gain domain. This is a noncomputable mathematical construction, not an executable quantum circuit. Highest tensors and Schur decompositions are selected from proved existence results; no final optimum or fidelity estimate is assumed as part of that selection.

**Boundary:** the code packages irreducible copies rather than an explicit Specht factor, and this pilot did not locate or produce a single theorem equating its full channel on every input to a separately encoded manuscript `𝒬[K]`. The component identities support the operational correspondence; exact all-input representation equivalence is not an additional certified result of this review. No altered finite sampling rule analogous to an alternative transport coupling was found.

## Actual dependency consumption

The proof of the value endpoint consumes `limsup_knownSpectrumValue_le` and `eventually_knownSpectrumValue_lower`; neither is assumed by the caller. The upper bound constructs a whitening basis from `exists_whitening_frame`, enumerates every root pair, constructs `physicalCompactWindowLAN`, and passes that full bundle to `limsup_knownSpectrumValue_le_of_compactWindowLAN` (PhysicalCloningKnownTheorem 33–41). The bundle's forward/reverse CPTP sequences and every-compact-window approximation field are produced by `nonempty_physicalCompactWindowLAN` (TensorLANEmbeddingCompactLAN 19–50). The choice of LAN maps is an internal existence witness, not the definition of the source's prescribed cloner; uniqueness is neither claimed nor needed.

The lower bound applies the actual `knownSpectrumChannel`; its typical-sector and concentration estimates are proved upstream and consumed through `eventually_knownSpectrumChannel_payoff_lower` and `LAN.candidate_le_minimaxValue` (TensorCloningAchievability 49–90). Bounds needed for the real sup/inf are supplied by actual payoff nonnegativity/≤1, not theorem assumptions.

Uniform achievability consumes the compact-uniform retained-mixture theorem, the vanishing bad-label tail, the exact label affinity 1, and unitary covariance (TensorCloningUniformKnown 26–107). The retained-mixture theorem quantifies every normalized mixture over typical input copies and proves uniformity via compact subsequences (TensorCloningRetainedTypical 85–126). Finally `eventually_output_gt_input` removes the finite partial-trace branch. The saved probe reconstructs these upper/lower/prescribed compositions as Lean terms with only the source inputs.

Stale comments in legacy `Main` and `CompactWindowLAN` modules describe their earlier conditional stage; they do not change the final exports or supply hypotheses to these targets. The earlier completion review was consulted only after source, binder and definition reconstruction. Its general statement is consistent with these fresh checks; the finite copy/Specht representation qualification above is made explicit here.

## Reproduction and observed result

The [saved probe](known-spectrum.lean.txt) is plain text outside the proof inventory. Copying it to a temporary `.lean` file avoids adding any audited source module. From the repository root, with the pinned Elan toolchain installed:

```bash
set -e
probe_dir="$(mktemp -d)"
cp formalization/verification/semantic-pilot/known-spectrum.lean.txt "$probe_dir/known-spectrum.lean"
cd formalization
PATH="$HOME/.elan/bin:$PATH" lake env lean "$probe_dir/known-spectrum.lean"
rm -rf "$probe_dir"
```

Observed final execution: **exit code 0**, 2026-10-06 07:20:02–07:20:27 UTC, **25.185234 seconds**, pinned `leanprover/lean4:v4.29.0-rc6`. All twelve named exact-type/definition/composition witnesses compiled without errors. The native shared collector checked the two actual targets, four audited definitions, and all twelve probe proofs (**18 roots**, **69,784 visited constants**); its aggregate axioms were exactly `propext`, `Quot.sound`, and `Classical.choice`. The log ends with `KNOWN_SPECTRUM_SEMANTIC_PROBES_PASSED` and the run record also requires the successful process exit. All 31 reviewed input hashes were rechecked unchanged after execution.

Retained evidence: [final output](known-spectrum.log), [final run record](known-spectrum-run.json), and the [exact saved probe](known-spectrum.lean.txt), SHA-256 `416877625fe1c1b19676b3fc6220b346d6780d8c5b029393aa63905485a98c27`. The log SHA-256 is `8db8458f98277005d75cda041724463dac03d498dcb278f6c01e3a8d8b9065bf`. The command used `/Users/jw/.elan/bin/lake env lean <temporary known-spectrum.lean>`, with `/Users/jw/.elan/bin` prepended to PATH; its exact temporary path, timestamps and environment are in the run record. The temporary directory was removed.

An initial probe had two newline/dot-notation parsing errors in the expanded fidelity types. The [failed output](known-spectrum-attempt-1.log), [failed record](known-spectrum-attempt-1-run.json), and [exact first probe](known-spectrum-attempt-1.lean.txt) are retained. Only the diagnostic text was corrected; theorem files were untouched. A prior-error guard in the final probe also prevents its local marker after earlier errors. The initial source-only axiom marker was never accepted as proof of a successful process.

This did not rerun the full build, full axiom inventory, Comparator or Nanoda. Full-source binding remains the existing audit run `6b2c09f61388362d9ff3ae3f63285b9dd09e0cd95254150273bacba6cd9c799a`. These native applications certify the specified Lean types, equations and compositions; they do not mechanically certify the English interpretation or every upstream representation lemma.

## Identity appendix

Review base HEAD: `d2ccb294f6a69d2cd65aa807cb9bfd1d9f829999`. Source hashes are SHA-256 of the actual bytes read; paths below are relative to `formalization/`.

```text
6f2453656031201968aef5cc9c043f7116bb7a1ed1cd2cebb2b905e3df94038d  reference/cloning.tex
dc6d65016fad3123d44bf17b5bf0598286284ab16ba75d5c17eb22ed11f47361  lean-toolchain
ddeb0d2c8217676fc393afd24c13629993c580f35f9d8ad15240c6a167b020c1  lakefile.toml
e4630915680b82b58c6a005e1ba1e515e865e5541c7e665d4a2d57f783eeadb4  lake-manifest.json
68e463f5ce045ca91c84d47f8ee855e9a60204243e230c39b089db991f3a96a2  Cloning/Main.lean
3712d3a57ddd4981a655fda069347d882491b9bc21c81db2f84bc80acd51bd4a  Cloning/PhysicalCloningKnownTheorem.lean
bb8c6b6f780df2c1bf5162b85a319f59df7024788a104de274c8eb98e9b5d6bf  Cloning/TensorCloningPrescribedLimits.lean
af755f3e81246eeed1ffbb52b298bf6cb3c78e7f57a7d28763abda3365e4cb24  Cloning/TensorCloningPayoff.lean
0b6e4b00d37aa17dd5580c09d63c62d1eb63c4c461c4d2e5c797c1b9967e3787  Cloning/TensorCloningPrescribed.lean
d3dc50c83b60b9e7a734b11aed79064d33bbdf3b44b9b210f093f1c94e0b9a91  Cloning/Thermal.lean
32245e1d9a8ba1f5956156790869ec778b8f5998ca2ed9fa1d4cac131cf84346  Cloning/InfiniteCompletelyPositive.lean
3b6d9de42b5722026719eeb442a58f06fd9a392cc779ab7c74a38794569c6eb7  Cloning/InfiniteTraceClassChannels.lean
28a756850d972dd2ef713f00f74f7e8de29f1c24f5a9a35cadab96750f39569c  Cloning/InfiniteFidelity.lean
7044f14288df0b6682f367969b6ad58837b2c7ccf7cb136b93790ab1ec1726b9  Cloning/HybridStates.lean
44ee813d8916b24ac7153e40e8492059706d61c51772d6aa332ff29bca58984d  Cloning/PCTPhysicalState.lean
9eff2831f65aaf27d9d81958f1a14501a9126e4a389de0db9e76bf6a0990e57a  Cloning/PCTUnitaryTransportChannels.lean
503c5ef4f74c5c4c6000229764cb0869b769efba78d441b2936ce52a391dccd2  Cloning/LAN.lean
0a0e998effe332789c55ebc24b0e7127cd6b860f96439f7662ad907fb88573fe  Cloning/PhysicalCloningConverseSpectrum.lean
b38c910d8582455309ac795ba18c8d73380f5445d726a0c163cf09b6b493ec2d  Cloning/TensorCloningChannel.lean
bf74846b8decf409d047cc770ab77870c7f93ec0a0c94caadbdf23073079a033  Cloning/TensorCartanChannel.lean
dd5db1cddf9a343bbfc84b80132518238eaa3f2cf45b07769622c65d289b842c  Cloning/TensorCloningGlobalCovarianceState.lean
968d7cf59879fe40f29bbb5d8c90de0c9b0e59aa50011a085a15576a9cdecdc5  Cloning/TensorLANEmbeddingSchurWeights.lean
bdcc17da380ea14fb861401979fdc722ec9c91e4514c88547844d864ac296a78  Cloning/TensorSchurDecompositionPMF.lean
b4cd88018fd30e32b890acd1d117c7396591251608beb387d1483b88d722e947  Cloning/TensorCloningUniformKnown.lean
20a79ee0c59ac586c8b650ba17d3c7e612284c08894963eabcdc5ea649516d3f  Cloning/TensorCloningRetainedTypical.lean
381bd8fe6623931d23af23419d51c0e74a34876c5b5b86b69959b4e294951df5  Cloning/TensorCloningAchievability.lean
5393e1e4b1b90f39917c1130d2e5992404c21462630d6ea82aa610c948bfa426  Cloning/PhysicalCloningConverseKnown.lean
bc240c6df778ac8db5539b1c94304558727ee7bed7a6cc8db0af0e1956808f09  Cloning/TensorLANEmbeddingCompactLAN.lean
a846101b521644c414f143c6a0596365b91bf4cca7449654c7c70adceb112ff4  Cloning/PCTPhysicalFidelityLAN.lean
af7c34c1c0b75186cbf5697492f2d4dba85c47f8fdb8d78f38cf4571e424e7b6  Cloning/PCTJointGaussianWhitening.lean
8989a10ec2f035d84eeadeb1ab47af9dbbbb80ccbfcdf85f31577d3c5e55f3c9  Cloning/InfiniteTraceClass.lean
```
