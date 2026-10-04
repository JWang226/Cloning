# Independent reviews of the tenth-pass constructions

These semantic reviews supplement Lean compilation and the full compiled-constant audit. They do not assert that the complete mixed-state cloning theorem has been proved. All work in this pass is local.

## Physical orbital amplifier and optimality

The hybrid-converse author reviewed the six physical amplifier/attainment modules and their Kraus/isometry dependencies. The output retains the amplified signal coordinate, and the exact coherent kernel retains the required phases. The noise parameter `1-1/γ` gives displacement gain `sqrt γ`. The vacuum output width and scaled input-vacuum width differ by `(γ-1)/2`, with the correct positive sign. Characteristic injectivity gives the actual thermal output, rather than an equality of formal Gaussian labels.

The constructed channel attains the root-fidelity mode-factor product at every displacement and under every probability prior. The real-radius optimum has the channel supremum before the limit; no equality of finite-radius optimal payoffs is claimed. Empty mode products are valid. No semantic defect was found.

## Vacuum boundary and trace-class continuity

The quantum-positive and attainment reviewers independently checked `ThermalParameterContinuity`. The positive approximation remains strictly below one and converges to every physical parameter in `[0,1)`, including zero. The occupation weights are genuine normalized nonnegative laws. The existing countable Scheffe theorem yields convergence in the actual trace norm. Continuity of the fixed physical amplifier then transports its thermal-output identity to vacuum modes. The scalar mode-factor convergence uses the same approximation. There is no circular appeal to the desired limiting channel output. The nonnormalizable boundary `q=1` is excluded.

## Actual hybrid channels and averaging

The Young/RSK author reviewed `HybridChannel` and `HybridChannelAveraging`. Complete positivity and integrated trace preservation give a uniform norm bound of two on every complex L1 input. The simple-function density argument does not require a measurable pointwise Jordan decomposition. The closed convex cone of almost-everywhere positive finite operator matrices gives genuine finite-ancilla CP for Bochner averages. The integrated trace is a bounded functional and commutes with the average.

The actual translation action is an isometry with proved group law, strong continuity, complete positivity and trace preservation. Expanding density averages have a covariance coefficient independent of the original competitor, bounded by four and tending to zero for every displacement. The order of quantifiers allows a different competitor at every scale.

## Sharp hybrid residual and converse

The Young/RSK author and physical-amplifier author reviewed the sharp trace, residual, and payoff assembly. The normalized compact bumps form a proved approximate identity in operator-valued L1. Fubini and the exact translated Gaussian integral give the classical factor; no approximate-identity or sharp trace-bound premise remains.

One subsequence preserves every compact quantum pairing. The residual may lose trace or be zero; the proof correctly retains this loss. In the nonzero case, covariance and irreducibility give scalar normalization, and testing its vacuum output shows that the scalar is at most the classical factor. The thermal witness moment therefore retains that factor. Weighted fidelity produces the square of the desired root-fidelity bound, and nonnegativity justifies taking the positive root. No weak-operator continuity of fidelity is assumed.

The final expanding-prior theorem is uniform over arbitrary hybrid channels, including channels with classical-quantum correlations. The real-radius reduction uses exact box inclusion and the volume ratio tending to one, with the threshold outside the channel quantifier.

## Physical hybrid attainment

The quantum-positive author independently reviewed the dilation, fibre channel, output identification, fidelity factorization and optimum-limit endpoints. Classical dilation is literally `r^(-k) A(y/r)`; its Jacobian, L1 isometry, integrated trace and finite-block complete positivity are proved. Composition with the physical amplifier acts on all correlated L1 inputs, not just product states. Exact covariance follows from the actual classical and quantum actions.

On the reference Gaussian-thermal state the output precision is `a/γ` and its thermal parameter is `1-(1-q)/γ`. The integrated root fidelity is `classicalBase(γ)^(k/2) * prod modeFactor(γ,q_i)`. One fixed physical channel supplies the lower bound at every prior/radius. The real-radius optimal limit follows by matching this lower bound with the uniform converse. Zero classical or quantum dimensions are allowed.

## Actual Young normalization

The root review checked that the new normalization theorem uses the actual reversible finite-array insertion equivalence, standard-word branching and the previously defined tableau weights. It proves total mass `(sum p_i)^N` for arbitrary real alphabet weights, then constructs `tableauPMF` for nonnegative unit-sum spectra. Neither normalization nor existence of a distribution with the desired mass formula is assumed.

The constructed PMF now supplies concentration, fallback convergence, and flat-spectrum forward/inverse crossing-root dimension moments directly. Physical Schur measurement and representation-dimension identification remain separate. The general local central limit theorem is not claimed.

## Universal full-environment random purification

The Young/RSK author reviewed the finite matrix channel, Haar construction and tensor-product action. The channel is independent of the unknown input state. Positivity of its Haar moment and identity partial trace give an actual CPTP square-root sandwich. The entangled vector is intentionally unnormalized; adding a factor `1/d` would break trace preservation.

Left Haar invariance gives commutation with tensor unitaries. Polynomial uniqueness on a product of unit circles extends diagonal-unitary commutation to arbitrary diagonal entries; the Hermitian spectral theorem then gives the required commutation with the positive square root of the input. The resulting Haar mixture consists of actual purifications, each with the claimed reduced tensor-power density.

The construction uses an environment with the full system dimension. It does not yet give the rank-adapted smaller-environment protocol. The convention `vec(sqrt(ρ) U)` acts on the environment by `U` transposed; the physical adapter must and does track that transpose, rather than silently treating it as `U`. The physical output link passed independent review and compilation. The matrix/register lift has literal computational coefficients, and the slot insertion uses the full unnormalized identity with the correct symmetric-dimension ratio. The final endpoint is trace-norm convergence to the reduced Gaussian product mixture. The downstream `physicalCloneTraceCLM` is explicitly only a continuous linear map: global CPTP extension, rank adaptation and final fidelity remain unproved.

## Concrete tensor Lie operators

The quantum-positive author reviewed the four `TensorLie*` modules. Their one-slot operators implement input letter `b` to output letter `a`. Adjoints, same-slot products, disjoint-slot commutation and the collective `gl_d` commutator have the correct indices and signs. The collective Cartan operator counts occupancy, and its norm bound is derived from the actual operator construction.

The normalized highest tensor has one-row weight `(n,0,...,0)` and is annihilated by raising generators `a<b`. Its actual word-height cutoff has the proved lowering and raising shifts. This does not construct arbitrary Young sectors. A shifted ambient word-height cutoff would not be a valid general-partition vacuum filtration; the next general construction must use the cyclic span generated by lowering words.

## Remaining LAN interface review

A separate read-only review confirmed that the existing infinite-dimensional LAN transfer acts between Hilbert-space trace-class models. General quantum-to-hybrid instruments and hybrid-to-quantum recovery maps need explicit mixed CP/TP interfaces and composition. The existing hybrid fidelity data-processing theorem is fibrewise; it does not establish monotonicity for every mixed instrument. These obligations are now explicit in the progress report. A two-by-two fidelity-block witness gives a concrete route for quantum-to-hybrid monotonicity without measurable optimizer selection.

The converse uses fixed-spectrum, fixed-window LAN followed by the sample-size limit and then the expanding-prior limit. The classical covariance must also be connected to the product-Gaussian interface through an actual coordinate/channel transformation or a whitened local chart. None of these remaining interfaces is claimed to follow from the already proved scalar Gaussian affinity formulas alone.

## Verification status

The historical auditor, allowed axiom policy and earlier checkpoint archives are unchanged. The complete build and all three audit workers passed on `2026-10-03T10:02:14.187452+00:00`. The [completion record](tenth-pass/run.json) covers 310 implementation modules, 2,809 source theorem/lemma declarations and 6,122 unique compiled project constants. It records no unexpected axioms, missing modules, missing reports or conflicting reports. All source/dependency and compiled-artifact hashes remained unchanged. The only allowed axioms are `propext`, `Classical.choice` and `Quot.sound`.
