# Independent reviews of the ninth-pass constructions

These read-only semantic reviews were performed by agents other than the authors of the reviewed branches. They supplement the Lean build and all-compiled-constant axiom audit; they are not an independent proof-assistant certificate. The main mixed-state cloning theorem remains conditional.

## Normal duals and quantum-positive multipliers

The reviewer checked the actual trace-class/Heisenberg pairing, CP amplification, finite entangled block test, multiplier normalization, continuity, and cocycle orientation. The block indices `B[j,i] A[i,j]` and the Weyl phases agree. Positivity and the multiplier bound are derived from the genuine channel; no operator-norm contraction or quantum-positive multiplier premise is imposed on the physical endpoint. Characteristic injectivity and the transformed idler kernel do not assert idler-density existence.

Result: no semantic defect found.

## Direct sharp Gaussian bound

The flat-prior/convolution author independently reviewed the positive-kernel Hilbert completion, finite-index to finite-subset positivity, Bochner integral Cauchy–Schwarz, scalar recurrence, and actual-channel wrapper. The feature inner product and conjugation orientations agree with the kernel. For `h=(r²−1)/2`, the normalization satisfies `A(t)² B(t)=A(T(t))`. The invariant domain `t_i≥h>0` supplies the uniform bound `2^d`, and bounded repeated squaring forces the normalized quantity to be at most one. The vacuum multiplier `exp(-h sum |a_i|²)` independently saturates the resulting constant `prod π/(t_i+h)`.

There is no hidden moment, idler, or representation-theorem assumption. The theorem is a sharp Gaussian test; it does not assert full number-distribution stochastic domination.

Result: no semantic defect found. A further independent helper review checked kernel orientation, gain, hypotheses, and the empty mode case.

## Thermal Fourier bridge and universal orbital assembly

Both the quantum-positive/Fourier author and the flat-prior author reviewed the final assembly. The input is the literal normalized product-geometric trace-class operator. Its trace-one property follows from `traceCLM_vectorMixture` and `productGeometric_hasSum`. The channel may have arbitrary correlated, non-Gaussian noise; no diagonal-noise or factorization hypothesis occurs.

The Fourier normalization is `π^(-d)`. The amplified width is

`α(amplified(r²,q)) = r² α(q) + (r²−1)/2`,

with the plus sign. The norm-to-real-part bound has a nonnegative prefactor. The actual fidelity witness is exactly a positive scalar multiple of the geometric thermal operator with parameter `sqrt(q/x)`. Multiplying the two thermal-test moments by that scalar yields `prod F(q_i,x_i)`, in the root-fidelity convention.

Input and target have the same thermal parameter `q`, while the target displacement has amplitude gain `r=sqrt γ`. The square from Jensen/weighted fidelity is removed correctly. The eventual radius is chosen before the arbitrary competitor, so the supremum over channels precedes the limit. Trace loss is handled by the proved scalar normalization of a covariant CP trace-nonincreasing map; no weak-operator continuity of fidelity is used.

Result: no semantic defect found. The review identified that `UniversalGaussianConverse` itself uses integer radii `n+1`. The separately compiled and reviewed `UniversalGaussianRealBox` closes that gap.

## Arbitrary real box radii

The Fourier author independently reviewed `UniversalGaussianRealBox`. For positive real radii the payoff is exactly the literal normalized Lebesgue box integral. Box inclusion is coordinatewise, the root-fidelity integrand is nonnegative, and continuity on compact boxes gives integrability. The exact volume ratio is `((n+1)/L)^D`, where `D` is the real phase-space dimension. With `n=floor L`, the ratio is bounded by `(1+1/L)^D`, tending to one. The threshold remains outside the arbitrary-channel quantifier. The channel range is nonempty and bounded above, and its optimal payoff is nonnegative, preventing any empty-supremum or unbounded-limsup artifact. Zero modes are included.

Result: no semantic defect found. The final endpoint now has the literal all-real-radius `limsup sup_channel` scope.

## Physical PCT construction

The general-Young author reviewed the physical projector and PCT chain independently. The canonical `physicalProjector` is defined from permutation invariance before a frame is chosen. Full-basis surjectivity identifies its entire range, and the full frame resolution supplies literal identity operators on spectator slots. The normalization is the required binomial dimension ratio. Slot cardinalities and the requirement `m_n≥n` agree.

Tensor regrouping, partial-trace coefficients, conjugations, and literal reduced-density matrix tensor powers are correct. The frame-independent output follows from the physical Werner sandwich. The existence endpoint constructs a full orthonormal frame through every normalized purification in the stated dimension. The Gaussian integral is genuinely Bochner-integrable. Environment randomization cancels pointwise, so measurability of a separately supplied environment-isometry family is unnecessary in the constant integral.

Result: no semantic defect or vacuity found. The branch proves the randomized-purification output formula and its product-mixture limit. It does not construct the universal CPTP random-purification map from unknown mixed inputs, prove equivalence of all equal-reduced-state purifications, or supply mixed-state LAN/final PCT fidelity.

## Young concentration and dimension moments

The PBW author reviewed the standard-word/tableau definitions, row-content encoding, highest-weight bound, and PMF interface. The ballot-word and semistandard conditions match the claimed combinatorics. The exponential tail is derived for the literal `f^μ s_μ(p)` weights, uniformly on the ordered closed simplex. PMF applications retain their exact mass-formula hypothesis; neither normalization nor physical Schur-law identification is claimed.

Fallback error decay uses the proved concentration estimate. The general-rank forward and inverse moment limits concern explicit crossing-root products at the flat spectrum, under a genuine PMF with the exact formula. They do not establish a local central limit theorem, representation-space dimension identity, or sharp general-rank rate.

Result: no semantic defect found.

## PBW/root cutoff estimates

The normal-dual author reviewed the PBW Gram route. An initial fine-root-height versus grouped-cutoff issue was identified and corrected before freezing the branch. The final transfer uses `PBWRootGram` to align the local root-filtration bounds with the cutoff required by normal ordering. Wick factorial/delta evaluation is derived; Gram convergence is a conclusion, not an assumption. Actual highest-weight spaces and their local root/CCR defect estimates remain physical inputs.

Result after correction: no remaining semantic defect found.

## Hybrid Gaussian witnesses and weighted maps

The normal-dual reviewer checked the exact Gaussian parameterization, bounded square-root density-ratio witness, inverse affinity moment, translated Gaussian integral, and the concrete thermal instantiation. Integrability is proved for actual positive trace-class-valued L1 fields. The weighted quantum map preserves complete positivity at every finite ancilla size. Its coarse trace/norm estimate follows from L1 trace preservation; the sharp Gaussian shift-mass estimate is a separate proved lemma.

Result: no defect or vacuity found. These statements do not yet assemble the full hybrid Gaussian minimax converse or establish its sharp weighted residual trace bound after all covariance/compactness limits.

## Verification discipline

The historical all-constant auditor and evidence checker are unchanged from the previously verified checkpoint. The new audit snapshots every Lean source and dependency pin, builds `All`, hashes the compiled artifacts, and verifies all exported project constants using the same allowed axiom set. Earlier seventh/eighth-pass evidence is preserved. No source mutation is permitted during the full audit. Final counts and source hashes come from the new completion record, not from branch-local reports.

## Final documentation review

The general-Young author independently compared the progress report and all ten public navigation files with the new theorem signatures. Young normalization/physical-law premises, PBW local hypotheses, hybrid assembly limits, PCT protocol/fidelity limits, and root-fidelity/gain conventions were represented accurately. Exact audit counts and metadata were left for finalization from the completed audit.

## Completed full audit

The final full `lake build All` and three-worker compiled-declaration audit passed: 251 implementation modules, 2,269 source lemmas/theorems, and 4,817 unique compiled project constants. Every worker exited zero; placeholder and unexpected-axiom scans passed. Source/dependency inputs and compiled-artifact hashes stayed unchanged during the run. The saved-evidence checker then passed against the exact current source. The completion record is `ninth-pass/run.json`, selected by `latest.json`.
