# Independent reviews of the eighth-pass constructions

These are read-only semantic reviews by separate agents. They supplement the Lean build and all-constant axiom audit; they are not an independent proof-assistant certificate.

## Recovery, fidelity, Werner output, and checker review

Eighth-pass independent semantic review
Reviewer: young_compatibility subagent (not author of the reviewed modules).
Scope: read-only review of the eight named Lean modules, key imported definitions,
and scripts/check_checkpoint.py plus scripts/audit.py and the pinned archived audit engine.

RESULT: No mathematical correctness blocker or disguised conclusion-as-premise found
in the reviewed statements. One checker reproducibility defect was found and fixed.

LEAN STATEMENTS
- IsometricRecovery.lean: actual CPTP adjoint compression plus trace replacement;
  contraction trace bound and left-inverse identity are proved, including arbitrary
  nonpositive trace-class inputs. A replacement density state is an explicit,
  appropriate input; no recovery identity is assumed.
- OccupationRecovery.lean: genuine channel on the whole tensor space, exact padded
  product-projector output, and trace-norm coherent limit for each fixed complex z.
  It does not assert uniformity in z.
- ChannelAveraging.lean: Bochner probability average is genuinely CPTP. The explicit
  regularity hypothesis is AEStronglyMeasurable evaluation at every trace-class
  input. Integrability is derived from the channel norm bound.
- InfiniteFidelityConcavity.lean: binary nonnegative-weight joint superadditivity
  for actual root fidelity, hence normalized-weight concavity. No commutativity,
  finite-dimensionality, or faithful-state assumption is hidden.
- WernerPhysicalPullback.lean: the physical symmetric sandwich is exactly identified
  with the occupation mixture before taking the thermal trace-norm limit. The
  final theorem uses a chosen reference basis pure product, s >= 1, m(n) >= n,
  and m(n)/n -> gamma > 1. Arbitrary rotated/local inputs are not asserted here.
- HybridJensen.lean: concavity and continuity apply to the closed positive cone
  in the real trace-class product Banach space. The finite-measure argument treats
  zero measure separately and cancels the positive total-mass normalization using
  proved homogeneity. Fields need integrable positive trace-class densities; unit
  mass is not required. No measurable choice of fidelity optimizers is assumed.
- HybridJensenSigmaFinite.lean: the exhaustion consists of increasing measurable
  finite-mass sets with union the whole space. Restrictions are kept unnormalized.
  Integrability gives norm convergence of both Bochner marginals and convergence
  of the integrated fidelity; actual trace-norm fidelity continuity passes the
  finite-measure inequality to the limit. Sigma-finiteness is explicit.
- HybridWeightedFidelity.lean: target is the actual density g(x) T. The substantive
  witness premise is a single finite M bounding tr[T (W + epsilon I)^(-1)] for
  EVERY epsilon > 0, with bounded W >= 0; W itself need not have a bounded inverse.
  This premise is not proved for any particular proposed thermal witness here.
  Also explicit: T a density state; integrable g >= 0; chi > 0; integrability of
  chi*tr(R(x)W) and g/chi. No normalization of g or R is needed for the inequality.

VERIFICATION
A focused Lean import/axiom check of nine principal endpoints completed with exit 0:
recovery left inverse; coherent recovery limit; averaged channel; binary fidelity
concavity; physical Werner trace-norm limit; finite and sigma-finite Jensen;
operator-valued Jensen; weighted hybrid fidelity. Every report used only propext,
Classical.choice, and Quot.sound. Driver: /tmp/eighth-pass-review-axioms.lean.
This is a focused independent check, not the pending full-project audit.

CHECKER DEFECT AND FIX
Original latest validator unconditionally copied audit-shards although the default
serial audit (--jobs 1) never creates that directory. Reproduced with the exact
pinned engine and current sources in a temporary directory: generation exit 0,
audit-shards absent. Root changed the latest validator to copy only when the
source directory exists. Independently tested the actual changed AST branch:
(1) absent serial directory succeeds; (2) present sharded evidence copies exactly.
The existing auditor replay still validates required sharded files for jobs > 1.
No full fresh latest-certificate replay was performed in this review; root is
preparing that audit. The checker accurately calls itself saved-evidence integrity
and exact current-source/config matching, not a fresh kernel check or signature.


## Hybrid, Young geometry, and Gaussian averaging review

Independent semantic review by hybrid_model

Young modules reviewed:
- YoungCompatibility.lean
- YoungCompatibilityPMF.lean
- YoungCompatibilityFallback.lean
- YoungHyperplane.lean
- YoungHyperplaneVolume.lean
- YoungHyperplaneSampling.lean
- YoungHyperplaneCovariance.lean

No correctness issue found in the reviewed definitions and theorem statements.
The root hyperplane is the actual sum-zero subtype of EuclideanSpace, and the affine lattice retains the dependent final coordinate. The module parameter d counts head coordinates; therefore the physical number of rows is d+1 throughout. The proved Gram determinant d+1, Euclidean cell volume sqrt(d+1), density prefactor sqrt(N)^d/sqrt(d+1), covariance determinant (d+1)*product(p), and inverse quadratic form sum(x_i^2/p_i) have the correct normalization. rootCovariance_apply identifies the constructed CG matrix endomorphism with the actual ambient diag(p)-p*p^T restriction, avoiding a coordinate-only interpretation.

The fallback PMF is a genuine pushforward of the actual normalized uniform-dither PMF. On incompatible raw labels it uses exactly the manuscript's one-row partition (m,0,...,0). This fallback produces a valid Young output but need not be Cartan compatible on bad inputs; no theorem claims otherwise. Compatibility on typical inputs is proved from a common positive spectral gap and the finite coordinate-error bound. The eventual sample threshold is outside all spectrum/law quantifiers, so the claimed uniformity is genuine. An arbitrary epsilon_n -> 0 is sufficient for the deterministic compatibility assertion, but is not asserted to yield Young concentration. The separate hbad premise remains necessary; in particular the code does not infer concentration for windows shrinking too rapidly. No general Young local limit, normalized character asymptotic, or Frobenius/Stirling estimate is supplied by these geometry modules.

Weyl/Gaussian modules reviewed:
- WeylGaussianPrior.lean
- WeylFoelner.lean
- WeylCovariantization.lean (supporting definitions and shift identity)

No correctness issue found in the reviewed definitions and theorem statements.
priorDensity is the literal product of exp(-|z|^2)/pi complex Gaussian densities. Its integral is proved to be one, and gaussianPrior is volume.withDensity of that function. expandingGaussianPrior is its pushforward under z -> (n+1) z, hence each complex-coordinate second moment scales by (n+1)^2. The exact shifted-density formula uses p(z-b/(n+1)), with the correct sign and scale.

translatedChannel(gain,Phi,a) conjugates input by D(a) and output by D(-gain*a); gain is explicitly amplitude gain, equal to sqrt(gamma) in the manuscript. Its shift formula Gamma_a(D(b) A D(b)^*) = D(gain*b) Gamma_(a+b)(A) D(gain*b)^* is consistent, including cancellation of Weyl phases. The finite covariance-defect estimate follows from the L1 distance of the two actual prior densities times the norm of a positive input. Positive TP channels preserve that input norm exactly. Translation continuity is obtained in the actual L1 Haar norm and is composed with b/(n+1) -> 0.

The all-trace-class extension correctly uses the positive/negative Jordan decomposition of the self-adjoint real and imaginary components. It asserts convergence for each fixed input, not operator-norm convergence or uniformity over all inputs. That is the right hypothesis for the common compact-observable CP-limit theorem. The Gaussian averaging arguments alone do not prove preservation of flat-prior minimax/Bayes fidelity payoffs, the amplified-channel classification, or trace preservation of a compact limit; those remain separate obligations.

Own hybrid proof verification:
Eight Hybrid*.lean modules built successfully, with 63 named lemmas/theorems and 17 definitions. The ten main declarations were individually audited with #print axioms; all depend only on propext, Classical.choice, Quot.sound. No sorry, admit or custom axiom appears in the source scan. The sigma-finite Jensen theorem applies to actual positive trace-class-valued Lebesgue densities and does not assume measurable Uhlmann optimizers. The weighted hybrid theorem uses actual g(y)T fields and bounded regularized inverse moments; RHS integrability is an ordinary finiteness premise. Fibrewise data processing is proved, but no arbitrary continuous classical-quantum-channel classification or general hybrid LAN existence is asserted.

Additional WeylFoelnerLimit review:
The limit statement returns one actual complex-linear CP map and one strictly increasing subsequence, with convergence for every trace-class input and every compact output observable, plus all-displacement covariance. The fixed positive-input trace bound is inherited exactly from CPTP averaging and supplied with constant c=1 to the existing common CP compactness theorem. Covariance uses the already proved defect convergence for every trace-class input. The conclusion is explicitly trace-nonincreasing, so possible escape of trace is retained. No claim of trace-norm convergence, uniform channel convergence, or flat-prior payoff preservation is present. No semantic defect found.


## Additional cross-reviews

The general coherent-product author reviewed the actual Weyl Gaussian integral,
scalar commutant, character classification, and covariant multiplier calculation.
The phase and gain conventions agree throughout. The final abstract helper is
instantiated by proved concrete displacement laws; it adds no hypothesis to the
public multiplier theorem. Unitality and contraction remain explicit assumptions
of the separate multiplier normalization and norm-bound lemmas.

The Weyl/Følner author reviewed the symmetric splitting, combinatorial balance,
and full Werner CPTP construction. The physical sandwich theorem handles every
complex symmetric-input matrix and the full computational environment identity.
It does not assume irreducibility, trace preservation, or balance. General Young
sectors remain outside this one-row construction.

## Final integration review

A separate read-only reviewer checked repository status documents and navigation
entry points against the new theorem signatures. Module coverage is exact; source
links resolve. The descriptions preserve the boundaries between pure-product
comparison and mixed-state LAN, algebraic Weyl multipliers and idler reconstruction,
and Gaussian covariant limits and performance-preserving flat-prior reduction.
The source/evidence replay checker has no remaining blocking integrity finding.
The full Werner channel-to-thermal-limit connection compiled after the initial
scope review and is included in the final documentation.
