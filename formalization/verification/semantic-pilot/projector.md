# Projector-state statement review

Reviewed 2026-10-06 against revision `d2ccb294f6a69d2cd65aa807cb9bfd1d9f829999`.
This is an AI-assisted source correspondence review, with targeted Lean probes.
It is not external peer review or a replacement for the recorded kernel checks.

**Finding:** the all-channel optimum, literal projector family, root fidelity,
and uniform attaining-channel limit agree with Theorem 1.3. The finite attaining
channel uses a different coupling construction from the paper: Lean's density
overlap coupling is not identified with the paper's selected transportation-LP
minimizer. Equality of those finite constructions is outside this result.

## Source reconstruction

Read [Theorem 1.3](https://arxiv.org/html/2609.35986v1#S1.Thmtheorem3),
the standing conventions in [§1.1](https://arxiv.org/html/2609.35986v1#S1.SS1),
and the argument in [§4.2](https://arxiv.org/html/2609.35986v1#S4.SS2) and
[§4.3](https://arxiv.org/html/2609.35986v1#S4.SS3).
The frozen manuscript has SHA-256
`6f2453656031201968aef5cc9c043f7116bb7a1ed1cd2cebb2b905e3df94038d`;
relevant line ranges are 166–210, 406–430, 1933–2081, and 2083–2233.
These source passages were reconstructed before consulting earlier review prose.

For fixed physical dimension D≥2 and 1≤r<D, every input is the full product
state (P/r)⊗n, for a Hermitian idempotent P of rank r. One channel is selected
before the adversary chooses P. The paper optimizes over all CPTP maps and
uses unsquared fidelity against the entire output product state. With mₙ/n→γ>1,
the value converges to γ^(−r(D−r)/2). Its constructed channel attains that value.

## Exported binders

The probe prints complete exported types using `#check @...`, so section
parameters are included. Locations below are relative to `formalization/Cloning/`.
SOURCE means an explicit paper input, STANDING a convention in §1.1, and TYPING
an encoding requirement or a bound variable of the conclusion. No EXCESS
mathematical premise was found in these three exported declarations.

| Export / location | Every binder, in order | Classification and interpretation |
| --- | --- | --- |
| `PhysicalFlatGrassmann.minimaxValue_tendsto`, `PhysicalFlatGrassmannTheorem.lean:54` (section parameters at :14) | `(r k : ℕ) (hr : 0<r) (m : ℕ→ℕ) (γ : ℝ) (hγ : 1<γ) (hratio : Tendsto (m n/n) atTop (𝓝 γ))` | r, hr: SOURCE. k: TYPING, D=r+k. m, γ, hγ, hratio: STANDING. All are explicit; no instance arguments. |
| `TensorCloning.prescribedRankFlatChannel_uniform`, `TensorCloningPrescribedLimits.lean:57` | `(r k : ℕ) (hr : 0<r) (m : ℕ→ℕ) (γ : ℝ) (hγ : 1<γ) (hgain : Tendsto (m n/n) atTop (𝓝 γ)) (ε : ℝ) (hε : 0<ε)`; conclusion `∀ᶠ n, ∀ P : Projector r k, ...` | Same inputs, with ε, hε, n, P encoding uniform convergence. All declaration parameters explicit; no instance arguments. |
| `TensorCloning.prescribedRankFlatChannel_covariant`, `TensorCloningPrescribedLimits.lean:50` | `(r k : ℕ) (hr : 0<r) (n m : ℕ) (U : Matrix (Fin (r+k)) (Fin (r+k)) ℂ) (hU : Uᴴ*U=1) (X : TraceClass (TensorRegister n (Fin (r+k))))` | r, hr and unitary U: SOURCE; k, n, m, X: TYPING for the finite covariance identity. hU is unitarity in finite dimension. No assumption about the channel's action is supplied by the caller. |

The formal theorem also includes k=0 (D=r, the singleton boundary noted after
Theorem 1.3) and allows zero output sizes at exceptional finite indices. These
are extensions of the paper's domain, not added hypotheses. The gain assumption
proves eventually n<mₙ, hence eventual positive output sizes. The prescribed
channel selects exact restriction for m≤n (`TensorCloningPrescribed.lean:13`).
The probe checks k=0 gives limit 1 and D−r=k gives the same exponent.

## Carriers and definitions

| Object / location | Expanded content and assessment |
| --- | --- |
| `Projector`, `PhysicalFlatGrassmannOrbit.lean:17` | Subtype of actual complex D×D matrices with precisely `IsHermitian ∧ P*P=P ∧ rank=r`. No orbit witness or achievability premise hidden in the carrier. |
| `state`, same file :80; `MatrixFidelity.State`, `MatrixFidelity.lean:102` | Matrix is literally `(1/r) • P`. The state fields are a matrix, positivity, and trace one. Positivity/normalization are proved from the projector conditions; callers do not supply them separately. |
| `tensorPower`, `PCTPurificationChannel.lean:66`; `tensorState`, `PCTPhysicalState.lean:41` | Word-basis entries are `∏ i, ρ (a i) (b i)`, lifted to the register operator. This is the full tensor product. |
| `QuantumChannel`, `InfiniteCompletelyPositive.lean:167` | Extends `PositiveTracePreservingMap`: complex-linear trace-class map, preservation of positivity, preservation of trace (`InfiniteTraceClassChannels.lean:126`), plus complete positivity. The latter tests positive operator blocks at every finite ancilla dimension (:29). There is no covariance, Schur-block, or special-channel restriction on competitors. |
| Channel/register instances | General channel types require normed additive groups, complex inner-product spaces and completeness on input/output. The endpoints fix them to concrete finite tensor registers; they are synthesized structures, not free mathematical hypotheses. `Fin` supplies finite indexing/decidable equality. The local `Nonempty (Fin (r+k))` is constructed from hr. |
| `payoff` / `minimaxValue`, `PhysicalFlatGrassmannTheorem.lean:18,25` | `statePayoff` applies the competing channel to the input tensor state and compares with the output tensor state. `LAN.minimaxValue` is literally `⨆ Φ, ⨅ P, payoff Φ P` (`LAN.lean:52`). Bounds and nonempty witnesses are proved upstream, so this is not an empty or unbounded-real optimization convention. |
| `rootFidelity`, `HybridStates.lean:40`; `InfiniteFidelity.lean:23` | Definition unfolds to the trace norm of `sqrt A * sqrt B`. No square, division by rank, or limiting formula is inserted into the payoff. |
| `prescribedRankFlatChannel`, `TensorCloningPrescribed.lean:59` | Depends on r,k,hr,n,m only; neither P nor an adversarial unitary is an argument. Its restriction branch handles m≤n. |

## Producer–consumer checks and construction qualification

`PhysicalFlatGrassmannTheorem.lean:27–62` proves equality of the literal
projector and orbit payoff ranges, using `orbitProjector_surjective`
(`PhysicalFlatGrassmannOrbit.lean:61`) and the state equality at :95. It then
applies the actual orbit minimax theorem, rather than accepting a supplied
orbit representation as a premise.

`PhysicalFlatCloningTheorem.lean:14–36` derives mₙ→∞ from the gain and combines
the constructed lower bound with the all-channel upper bound.
`TensorFlatProjectorAchievability.lean:14–18` constructs `rankFlatChannel` by
applying `flatCoupledChannel` to `rankFlatCoupling` and its two proved exact
marginal identities. Its lower-bound proof (:21–34) consumes that same coupling's
fidelity limit. `YoungFlatCouplingRank.lean:40–49` discharges the coupling and
compatibility conditions using the constructed object and prior theorems.
No coupling, compatibility probability, or limiting-fidelity witness remains
as an endpoint assumption.

The upper bound consumes the finite physical channel bound in
`PhysicalFlatConverseFinite.lean:117`, whose proof quantifies over arbitrary
`QuantumChannel` values and derives the required orbit integral estimate.
`PhysicalFlatGrassmannUniform.lean:84–105` obtains one eventual event for the
lower and upper bounds, then quantifies over all P. Its upper estimate uses the
constructed channel's proved exact covariance. Finally,
`TensorCloningPrescribedLimits.lean:57–65` substitutes the prescribed channel
on the eventual mₙ>n event. Thus its threshold is independent of P.

**Construction qualification:** the paper's §4.2 fixes a slowly vanishing
εₙ and chooses a finite transportation-LP minimizer of the bad shape-distance
probability (frozen lines 1977–1983). Lean instead defines `positiveFlatCoupling`
by `densityCoupling` (`YoungFlatCouplingPhysical.lean:35–42`): integrate the
overlap `min(f,g)` over label bins and complete the residual marginals
(`YoungFlatCouplingEvents.lean:15–27`, `YoungFlatCouplingDensity.lean:15–19`).
At zero sample sizes it uses an independent completion, outside the asymptotic
tail. This supplies an alternative channel with exact marginals and the proved
optimal limit. The inspected declarations do not prove LP minimality or equality
with the paper's chosen finite channel. The numerical optimum and existence of
an attaining channel are supported; identification of that specific witness
must remain qualified.

## Native checks and limits of evidence

`projector.lean.txt` contains complete-type displays and ten small applications
or definitional equalities: literal projector and P/r, expanded physical minimax,
both endpoints, orbit transfer, coupling composition, dimension exponent,
k=0 boundary, and the eventual finite-size convention. Reproduce after preparing
the project with `bash scripts/verify.sh lean`, from the repository root:

```sh
cp formalization/verification/semantic-pilot/projector.lean.txt /tmp/cloning-semantic-projector.lean
(cd formalization && lake env lean -DautoImplicit=false /tmp/cloning-semantic-projector.lean)
```

The retained final log and run record report the actual successful execution.
An initial probe used an unnecessary `dsimp only` before a definitional equality;
Lean rejected that no-progress tactic. Removing it left the direct `rfl` check.
No implementation proof was changed.

The existing complete per-declaration inventory reports only `propext`,
`Classical.choice`, and `Quot.sound` for the three reviewed endpoints. Its bound
run SHA-256 is `6b2c09f61388362d9ff3ae3f63285b9dd09e0cd95254150273bacba6cd9c799a`.
This pilot reused that axiom evidence; it did not rerun Comparator or Nanoda.
The probes certify the displayed types, definitions and applications, not the
English interpretation. This is a scoped endpoint review, not a new line-by-line
semantic review of every upstream representation or asymptotic lemma.
