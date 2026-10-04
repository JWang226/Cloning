# Completion statement review

This review concerns the unchanged working manuscript `reference/cloning.tex`,
SHA-256 `6f2453656031201968aef5cc9c043f7116bb7a1ed1cd2cebb2b905e3df94038d`.
It supplements the Lean build and compiled-constant axiom audit. It is a
statement-correspondence review, not an independent compiler certificate or
external peer review. The exact declarations and their hypotheses are indexed
in [PROOF_MAP.md](../PROOF_MAP.md).

## Physical main results

The final known-spectrum and regular compact-set unknown-spectrum minimax
theorems optimize over actual completely positive, trace-preserving maps.
Their endpoints do not assume a LAN witness, a sector-fidelity estimate, or a
channel-action identity. The physical Schur decomposition, sector maps,
classical label laws, two-way LAN maps, and Gaussian optimization are constructed
upstream. The regular-closure condition is stated in the full trace-one affine
hyperplane. It is not silently applied to a singleton spectral set.

The projector result ranges over literal Hermitian rank-r projections and all
physical competitors. Its cloner attains the limit uniformly on that family.
The full-environment PCT limit and the rank-bound PCT projector comparison use
fixed, input-independent channels. The latter is an upper bound and strict
comparison; it does not assert an unproved fixed-gain fidelity limit.

## Corrections made during literal statement reconciliation

| Issue found | Completed proof scope |
|---|---|
| Protocol-specific typical windows were narrower than the sector proposition. | Arbitrary shrinking windows, one compact-uniform threshold, every finite common-target mixture, and eventual admissibility of initially signed target labels. |
| Sequential character convergence was not the displayed compact-uniform formula. | Arbitrary shrinking windows, the exact ratio `p^mu / s_mu(p)`, and uniformity over all spectra and partitions. |
| The physical Young-tail estimate retained a polynomial prefactor. | A sharper elementary moment-generating-function estimate gives the literal `exp(-N^(1/3)/4)` bound after a dimension-only threshold, uniformly including singular and repeated spectra. |
| Convergence of an orthonormal frame did not establish the claimed rate or identify the chosen frame. | Literal inverse-square-root Gram frames, bases of complete exact-weight spaces, invertible Gram matrices, and uniform fixed-height `C/sqrt(N)` bounds. The Cartan estimate has the actual finite product-binomial coefficients. |
| Flat support compression did not prove the arbitrary-spectrum compression lemma. | Actual rank-embedding/Cartan restriction square, the all-complex-input channel identity, arbitrary supported Gibbs states, and the exact square-root dimension-ratio fidelity factor. |
| Uniform affinity did not itself imply the uniform rounded-density assertion. | Compact-uniform raw rounded-density L1 convergence with the current spectrum's dilated Gaussian covariance. |
| A finite conditional trimming estimate was not yet the arbitrary-kernel asymptotic factorization. | The uniform shrinking-window estimates are assembled with vanishing discarded joint-label mass for arbitrary spectrum-dependent stochastic transitions and the actual lifted channels. |
| The weighted lemma exposed a bound on every regularization instead of a finite inverse-moment limit. | Direct passage of the regularized inequality to that finite right limit; the hybrid version allows arbitrary positive trace-class targets, including zero, and nonnormalized nonnegative integrable scalar fields. |

## Supplementary claims

- The prescribed rank-bound PCT guarantee covers every literal matrix rank at
  most r, with exponent rD−1 and no supplied purification or support witness.
  Its lower bound is uniform even for sample-dependent adversarial states.
- All-density minimax lower/upper bounds, the exact spectral infimum, ratio-wise
  monotonicity, the majorization counterexample, and large-gain exponents are
  separate proved statements. They do not determine the all-density optimum.
- Small-error claims concern squared fidelity. For each sufficiently small error, the physical target
  brackets hold for sufficiently large samples, with the cutoff allowed to
  depend on the error. The iterated asymptotics take sample size to infinity
  before taking error to zero. The universal cloner's brackets are uniform over all
  eigenbases. No joint finite-sample/small-error rate is inferred.
- Projector PCT has actual liminf/limsup purity envelopes and target brackets.
  These do not assume existence of an additional fixed-gain fidelity limit.
- The compact positive-gap spectral example has an explicit interior point,
  compactness, affine regular closure, the exact feasibility threshold, and
  failure of regular closure at the endpoint singleton in dimension at least two.
- Qubit noncommuting limits concern the actual all-channel minimax and an
  explicit spectrum sequence. The constant preparation channel is CPTP, is
  uniform over the orbit, and clones the maximally mixed state exactly.

The manuscript's degenerate-spectrum and fixed-rank conjectures remain
conjectures. The legacy conditional assembly remains available under its
original hypotheses and is not used as a substitute for the final physical
theorems. Source provenance and the limits of attachment identification remain
as recorded in `SOURCE.json`.
