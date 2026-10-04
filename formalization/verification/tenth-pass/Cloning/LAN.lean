import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Order.LiminfLimsup
import Mathlib.Tactic.Linarith

open Filter MeasureTheory
open scoped Topology

namespace Cloning.LAN

/-! # LAN fidelity transfer and minimax completion

The finite-dimensional and Gaussian state spaces remain abstract. The
contractivity, data-processing, fidelity-continuity and LAN estimates below
are explicit inputs; no assertion here constructs the quantum LAN channels.
The conclusions, including the genuine supremum/infimum minimax reduction,
are proved from those inputs.
-/

/-- The channel-composition estimate in Lemma `LAN-fidelity-transfer`.
`dist` represents trace distance with the normalization used in the paper;
`FB` and `FG` represent its root fidelities. -/
theorem fidelity_transfer
    {A B G H : Type*} [PseudoMetricSpace A] [PseudoMetricSpace B]
    [PseudoMetricSpace H]
    (FB : B → B → ℝ) (FG : H → H → ℝ)
    (S : G → A) (M : A → B) (T : B → H)
    (hM : ∀ x y, dist (M x) (M y) ≤ dist x y)
    (hT : ∀ x y, dist (T x) (T y) ≤ dist x y)
    (hdata : ∀ x y, FB x y ≤ FG (T x) (T y))
    (hcontinuity : ∀ x x' y y', FG x y ≤ FG x' y' +
      Real.sqrt (dist x x') + Real.sqrt (dist y y'))
    (ρ : A) (σ : B) (Φ : G) (Ψ : H) (δ η : ℝ)
    (hδ : dist (S Φ) ρ ≤ δ) (hη : dist (T σ) Ψ ≤ η) :
    FB (M ρ) σ ≤ FG (T (M (S Φ))) Ψ + Real.sqrt δ + Real.sqrt η := by
  have hd : dist (T (M ρ)) (T (M (S Φ))) ≤ δ :=
    (hT _ _).trans ((hM _ _).trans (by simpa only [dist_comm] using hδ))
  have hc := hcontinuity (T (M ρ)) (T (M (S Φ))) (T σ) Ψ
  have hd' := Real.sqrt_le_sqrt hd
  have hη' := Real.sqrt_le_sqrt hη
  have hm := hdata (M ρ) σ
  linarith

/-- Vanishing trace-distance errors give a vanishing uniform transfer error. -/
theorem transfer_error_tendsto {δ η : ℕ → ℝ}
    (hδ : Tendsto δ atTop (𝓝 0)) (hη : Tendsto η atTop (𝓝 0)) :
    Tendsto (fun n => Real.sqrt (δ n) + Real.sqrt (η n)) atTop (𝓝 0) := by
  simpa using (Real.continuous_sqrt.continuousAt.tendsto.comp hδ).add
    (Real.continuous_sqrt.continuousAt.tendsto.comp hη)

/-- A genuine worst-case minimax value; channel choices are indexed by `I`. -/
noncomputable def minimaxValue {I P : Type*} (payoff : I → P → ℝ) : ℝ :=
  ⨆ i, ⨅ p, payoff i p

/-- The optimized limiting-model average against a normalized prior. -/
noncomputable def bayesValue {J Θ : Type*} [MeasurableSpace Θ]
    (ν : Measure Θ) (payoff : J → Θ → ℝ) : ℝ :=
  ⨆ j, ∫ θ, payoff j θ ∂ν

/-- A single admissible channel with a uniform fidelity lower bound gives
the same lower bound on the minimax value. The upper fidelity bound ensures
that the real supremum is taken over a bounded family. -/
theorem candidate_le_minimaxValue
    {I P : Type*} [Nonempty P] (payoff : I → P → ℝ)
    (candidate : I) (a : ℝ)
    (hupper : ∀ i p, payoff i p ≤ 1)
    (hlower : ∀ p, a ≤ payoff candidate p)
    (hnonneg : ∀ i p, 0 ≤ payoff i p) :
    a ≤ minimaxValue payoff := by
  classical
  have hbelow (i : I) : BddBelow (Set.range (payoff i)) := by
    refine ⟨0, ?_⟩
    rintro x ⟨p, rfl⟩
    exact hnonneg i p
  have hbdd : BddAbove (Set.range (fun i => ⨅ p, payoff i p)) := by
    refine ⟨1, ?_⟩
    rintro x ⟨i, rfl⟩
    exact (ciInf_le (hbelow i) (Classical.arbitrary P)).trans (hupper i _)
  exact (le_ciInf hlower).trans (le_ciSup hbdd candidate)

/-- Restricting a global worst case to a local chart, transferring channels,
and integrating against a probability prior transfers an upper bound on the
Gaussian Bayes payoff to the finite-sample minimax value.

Neither a maximizing channel nor an attained worst-case parameter is needed.
The local chart need not be injective. -/
theorem minimax_le_average_bound
    {I J P Θ : Type*} [Nonempty I] [MeasurableSpace Θ]
    (ν : Measure Θ) [IsProbabilityMeasure ν]
    (payoff : I → P → ℝ) (gaussian : J → Θ → ℝ)
    (localChart : Θ → P) (transfer : I → J) (ε B : ℝ)
    (hnonneg : ∀ i p, 0 ≤ payoff i p)
    (htransfer : ∀ i θ,
      payoff i (localChart θ) ≤ gaussian (transfer i) θ + ε)
    (hintegrable : ∀ j, Integrable (gaussian j) ν)
    (hbound : ∀ j, (∫ θ, gaussian j θ ∂ν) ≤ B) :
    minimaxValue payoff ≤ B + ε := by
  unfold minimaxValue
  apply ciSup_le
  intro i
  have hbelow : BddBelow (Set.range (payoff i)) := by
    refine ⟨0, ?_⟩
    rintro x ⟨p, rfl⟩
    exact hnonneg i p
  have hpoint : ∀ θ, (⨅ p, payoff i p) ≤ gaussian (transfer i) θ + ε :=
    fun θ => (ciInf_le hbelow (localChart θ)).trans (htransfer i θ)
  have havg := integral_mono (integrable_const (⨅ p, payoff i p))
    ((hintegrable (transfer i)).add (integrable_const ε)) hpoint
  simp only [Pi.add_apply] at havg
  rw [integral_add (hintegrable (transfer i)) (integrable_const ε)] at havg
  simp only [integral_const, probReal_univ, one_smul] at havg
  have hb := hbound (transfer i)
  linarith

/-- In particular, LAN transfer bounds the global minimax value by the
supremum over all limiting-model channels, including those not obtained by
transferring a finite-sample channel. -/
theorem minimax_le_bayesValue
    {I J P Θ : Type*} [Nonempty I] [MeasurableSpace Θ]
    (ν : Measure Θ) [IsProbabilityMeasure ν]
    (payoff : I → P → ℝ) (gaussian : J → Θ → ℝ)
    (localChart : Θ → P) (transfer : I → J) (ε : ℝ)
    (hnonneg : ∀ i p, 0 ≤ payoff i p)
    (htransfer : ∀ i θ,
      payoff i (localChart θ) ≤ gaussian (transfer i) θ + ε)
    (hintegrable : ∀ j, Integrable (gaussian j) ν)
    (hleone : ∀ j θ, gaussian j θ ≤ 1) :
    minimaxValue payoff ≤ bayesValue ν gaussian + ε := by
  have hbdd : BddAbove (Set.range (fun j => ∫ θ, gaussian j θ ∂ν)) := by
    refine ⟨1, ?_⟩
    rintro x ⟨j, rfl⟩
    have h := integral_mono (hintegrable j) (integrable_const (1 : ℝ)) (hleone j)
    simpa only [integral_const, probReal_univ, one_smul] using h
  exact minimax_le_average_bound ν payoff gaussian localChart transfer ε _
    hnonneg htransfer hintegrable (fun j => le_ciSup hbdd j)

/-- The integrated finite-sample LAN converse. The only link required
between finite and Gaussian channel classes is closure under composition
with the two LAN maps (`hcompose`). The Gaussian supremum may include
additional channels. -/
theorem lan_minimax_le_bayesValue
    {A B G H I J P Θ : Type*}
    [PseudoMetricSpace A] [PseudoMetricSpace B] [PseudoMetricSpace H]
    [Nonempty I] [MeasurableSpace Θ]
    (ν : Measure Θ) [IsProbabilityMeasure ν]
    (FB : B → B → ℝ) (FG : H → H → ℝ)
    (S : G → A) (M : I → A → B) (T : B → H)
    (C : J → G → H) (transferred : I → J)
    (hcompose : ∀ i x, C (transferred i) x = T (M i (S x)))
    (hM : ∀ i x y, dist (M i x) (M i y) ≤ dist x y)
    (hT : ∀ x y, dist (T x) (T y) ≤ dist x y)
    (hdata : ∀ x y, FB x y ≤ FG (T x) (T y))
    (hcontinuity : ∀ x x' y y', FG x y ≤ FG x' y' +
      Real.sqrt (dist x x') + Real.sqrt (dist y y'))
    (hFBnonneg : ∀ x y, 0 ≤ FB x y) (hFGleone : ∀ x y, FG x y ≤ 1)
    (ρ : P → A) (σ : P → B) (Φ : Θ → G) (Ψ : Θ → H)
    (localChart : Θ → P) (δ η : ℝ)
    (hδ : ∀ θ, dist (S (Φ θ)) (ρ (localChart θ)) ≤ δ)
    (hη : ∀ θ, dist (T (σ (localChart θ))) (Ψ θ) ≤ η)
    (hintegrable : ∀ j, Integrable (fun θ => FG (C j (Φ θ)) (Ψ θ)) ν) :
    minimaxValue (fun i p => FB (M i (ρ p)) (σ p)) ≤
      bayesValue ν (fun j θ => FG (C j (Φ θ)) (Ψ θ)) +
        (Real.sqrt δ + Real.sqrt η) := by
  apply minimax_le_bayesValue ν _ _ localChart transferred _
    (fun i p => hFBnonneg _ _)
  · intro i θ
    rw [hcompose]
    have h := fidelity_transfer FB FG S (M i) T (hM i) hT hdata hcontinuity
      (ρ (localChart θ)) (σ (localChart θ)) (Φ θ) (Ψ θ) δ η (hδ θ) (hη θ)
    simpa only [add_assoc] using h
  · exact hintegrable
  · exact fun j θ => hFGleone _ _

/-- The order of limits in the converse: first let sample size tend to
infinity for a fixed local window, then let that window grow. No diagonal
uniformity in the window is assumed. -/
theorem two_scale_eventually_upper
    (u b : ℕ → ℝ) (error : ℕ → ℕ → ℝ) (V : ℝ)
    (hbound : ∀ L, ∀ᶠ n in atTop, u n ≤ b L + error L n)
    (herror : ∀ L, Tendsto (error L) atTop (𝓝 0))
    (hb : Tendsto b atTop (𝓝 V)) :
    ∀ ε > 0, ∀ᶠ n in atTop, u n < V + ε := by
  intro ε hε
  obtain ⟨L, hL⟩ := (hb.eventually_lt_const (show V < V + ε / 2 by linarith)).exists
  have he := (herror L).eventually_lt_const (show (0 : ℝ) < ε / 2 by linarith)
  filter_upwards [hbound L, he] with n hn hen
  linarith

/-- The paper's `limsup` converse, with the lower boundedness of fidelity
made explicit so that the real-valued `limsup` is well behaved. -/
theorem two_scale_limsup_le
    (u b : ℕ → ℝ) (error : ℕ → ℕ → ℝ) (V : ℝ)
    (hnonneg : ∀ n, 0 ≤ u n)
    (hbound : ∀ L, ∀ᶠ n in atTop, u n ≤ b L + error L n)
    (herror : ∀ L, Tendsto (error L) atTop (𝓝 0))
    (hb : Tendsto b atTop (𝓝 V)) : limsup u atTop ≤ V := by
  apply le_of_forall_pos_le_add
  intro ε hε
  exact limsup_le_of_le (isCoboundedUnder_le_of_le atTop hnonneg)
    ((two_scale_eventually_upper u b error V hbound herror hb ε hε).mono
      fun _ h => le_of_lt h)

/-- Combining the two-scale converse with an achievability lower bound
proves ordinary convergence of the optimal finite-sample fidelities. -/
theorem minimax_converges
    (u b : ℕ → ℝ) (error : ℕ → ℕ → ℝ) (V : ℝ)
    (hbound : ∀ L, ∀ᶠ n in atTop, u n ≤ b L + error L n)
    (herror : ∀ L, Tendsto (error L) atTop (𝓝 0))
    (hb : Tendsto b atTop (𝓝 V))
    (hachieve : ∀ ε > 0, ∀ᶠ n in atTop, V - ε < u n) :
    Tendsto u atTop (𝓝 V) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hu := two_scale_eventually_upper u b error V hbound herror hb ε hε
  filter_upwards [hu, hachieve ε hε] with n hn hn'
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

/-- A channel-level achievability bound and the two-scale minimax converse
combine to give convergence of the genuine optimized worst-case payoff.
The finite-sample admissible-channel type may depend on sample size. -/
theorem minimax_converges_of_candidates
    {I : ℕ → Type*} {P : Type*} [Nonempty P]
    (payoff : (n : ℕ) → I n → P → ℝ)
    (candidate : (n : ℕ) → I n) (a b : ℕ → ℝ)
    (error : ℕ → ℕ → ℝ) (V : ℝ)
    (hnonneg : ∀ n i p, 0 ≤ payoff n i p)
    (hupper : ∀ n i p, payoff n i p ≤ 1)
    (hcandidate : ∀ n p, a n ≤ payoff n (candidate n) p)
    (ha : Tendsto a atTop (𝓝 V))
    (hbound : ∀ L, ∀ᶠ n in atTop,
      minimaxValue (payoff n) ≤ b L + error L n)
    (herror : ∀ L, Tendsto (error L) atTop (𝓝 0))
    (hb : Tendsto b atTop (𝓝 V)) :
    Tendsto (fun n => minimaxValue (payoff n)) atTop (𝓝 V) := by
  apply minimax_converges _ b error V hbound herror hb
  intro ε hε
  have ha' := ha.eventually_const_lt (show V - ε < V by linarith)
  filter_upwards [ha'] with n hn
  exact hn.trans_le (candidate_le_minimaxValue (payoff n) (candidate n)
    (a n) (hupper n) (hcandidate n) (hnonneg n))

/-- Extension from the dense interior of a compact spectral set to its
boundary, applied to a continuous Gaussian optimum. Use the subtype of the
compact set as `P` and its relative interior as `D`. -/
theorem upper_bound_on_dense_set
    {P : Type*} [TopologicalSpace P] (D : Set P) (hD : Dense D)
    (F : P → ℝ) (hF : Continuous F) (a : ℝ)
    (hbound : ∀ p ∈ D, a ≤ F p) : ∀ p, a ≤ F p := by
  exact hD.induction hbound (isClosed_le continuous_const hF)

/-- Taking the infimum over all spectra after extending the converse from
the dense interior. -/
theorem upper_bound_infimum_of_dense
    {P : Type*} [Nonempty P] [TopologicalSpace P]
    (D : Set P) (hD : Dense D) (F : P → ℝ) (hF : Continuous F)
    (a : ℝ) (hbound : ∀ p ∈ D, a ≤ F p) : a ≤ ⨅ p, F p := by
  exact le_ciInf (upper_bound_on_dense_set D hD F hF a hbound)

end Cloning.LAN
