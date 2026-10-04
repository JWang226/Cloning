import Cloning.HybridFoelnerPayoff
import Cloning.HybridFoelner
import Cloning.HybridL1Fidelity
import Cloning.HybridOrbitPayoff

/-! The universal hybrid Gaussian converse for actual expanding-prior channel
averages. Both the original competitor and the averaging scale may vary. -/
noncomputable section
open scoped ComplexOrder InnerProductSpace Topology BigOperators
open Filter MeasureTheory Cloning.InfiniteTraceClass
open Cloning.MultimodeCoherent
namespace Cloning.Hybrid
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
variable {k s : ℕ}

/-- The canonical Gaussian--thermal reference in the actual positive L¹ cone. -/
def gaussianThermalPositive (a : Fin k → ℝ) (ha : ∀ i, 0 < a i)
    (q : Fin s → ℝ) (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i < 1) :
    PositiveL1 (Fock s) (volume : Measure (Fin k → ℝ)) :=
  (gaussianThermalField a ha q hq0 hq1).toPositiveL1

lemma PositiveL1.rootFidelity_toPositiveL1 (A : PositiveL1 (Fock s)
    (volume : Measure (Fin k → ℝ)))
    (R : PositiveField (H := Fock s) (volume : Measure (Fin k → ℝ))) :
    A.rootFidelity R.toPositiveL1 = A.field.rootFidelity R :=
  PositiveField.rootFidelity_eq_of_toL1_eq rfl (PositiveL1.field_toL1 R.toPositiveL1)

namespace PhaseDensity
variable (p : PhaseDensity k s)

/-- The actual averaged output is bounded for arbitrary changing competitors
and every sequence of scales tending to infinity. -/
theorem foelner_output_eventually_le
    (Λ : ℕ → HybridChannel k s) (scale : ℕ → ℕ) (hscale : Tendsto scale atTop atTop)
    (a : Fin k → ℝ) (ha : ∀ i, 0 < a i) (g : ℝ) (hg : 1 < g)
    (q : Fin s → ℝ) (hq0 : ∀ i, 0 < q i) (hq1 : ∀ i, q i < 1) :
    ∀ ε > 0, ∀ᶠ n in atTop,
      ((gaussianThermalPositive a ha q (fun i => (hq0 i).le) hq1).map
        (p.foelnerChannel (Real.sqrt g) (Λ n) (scale n))).rootFidelity
        (gaussianThermalPositive a ha q (fun i => (hq0 i).le) hq1) ≤
      Thermal.classicalBase g ^ ((k : ℝ) / 2) *
        (∏ i, Thermal.fidelity (q i) (Thermal.amplified g (q i))) + ε := by
  let A := gaussianThermalPositive a ha q (fun i => (hq0 i).le) hq1
  let L := fun n => p.foelnerMap (Real.sqrt g) (Λ n) (scale n)
  let R := fun n => (A.map (p.foelnerChannel (Real.sqrt g) (Λ n) (scale n))).field
  have hR (n : ℕ) : (R n).toL1 = L n
      (gaussianThermalField a ha q (fun i => (hq0 i).le) hq1).toL1 :=
    PositiveL1.field_toL1 _
  have hc : ∀ n h X, ‖L n (classicalTranslation h X) -
      classicalTranslation (Real.sqrt g • h) (L n X)‖ ≤
        p.covarianceError (scale n) (h, 0) * ‖X‖ :=
    fun n h X => p.foelnerMap_classical_covariance_bound (Real.sqrt g) (Λ n) h X (scale n)
  have hq (z : Fin s → ℂ) (X : HybridSpace k s) :
      Tendsto (fun n => ‖L n (quantumL1Action z X) -
        quantumL1Action (Real.sqrt g • z) (L n X)‖) atTop (𝓝 0) := by
    have hb (n : ℕ) : ‖L n (quantumL1Action z X) -
        quantumL1Action (Real.sqrt g • z) (L n X)‖ ≤
        p.covarianceError (scale n) (0, z) * ‖X‖ := by
      simpa only [Prod.smul_mk, smul_zero, hybridTranslation_quantum] using
        p.foelnerMap_covariance_bound (Real.sqrt g) (Λ n) (0, z) X (scale n)
    exact squeeze_zero (fun _ => norm_nonneg _) hb
      (by simpa using ((p.covarianceError_tendsto (0, z)).comp hscale).mul_const ‖X‖)
  have h := eventually_gaussianThermal_output_rootFidelity_le L
    (fun n => (p.foelnerChannel (Real.sqrt g) (Λ n) (scale n)).completelyPositive)
    (fun n => (p.foelnerChannel (Real.sqrt g) (Λ n) (scale n)).tracePreserving)
    a ha g hg q hq0 hq1 (fun n h => p.covarianceError (scale n) (h, 0))
    (fun n => ((p.continuous_covarianceError (scale n)).comp
      (continuous_id.prodMk continuous_const)).aestronglyMeasurable)
    (B := 4) (fun n h => by
      rw [Real.norm_of_nonneg (p.covarianceError_nonneg _ _)]
      exact p.covarianceError_le_four _ _)
    (fun h => (p.covarianceError_tendsto (h, 0)).comp hscale) hc hq R hR
  intro ε hε
  filter_upwards [h ε hε] with n hn
  exact (PositiveL1.rootFidelity_toPositiveL1 _ _).trans_le hn

/-- The eventual scale is chosen before the arbitrary original hybrid
channel. This is the quantifier order needed for `limsup sup_channel`. -/
theorem eventually_forall_foelner_output_le
    (a : Fin k → ℝ) (ha : ∀ i, 0 < a i) (g : ℝ) (hg : 1 < g)
    (q : Fin s → ℝ) (hq0 : ∀ i, 0 < q i) (hq1 : ∀ i, q i < 1) :
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ Λ : HybridChannel k s,
      ((gaussianThermalPositive a ha q (fun i => (hq0 i).le) hq1).map
        (p.foelnerChannel (Real.sqrt g) Λ n)).rootFidelity
        (gaussianThermalPositive a ha q (fun i => (hq0 i).le) hq1) ≤
      Thermal.classicalBase g ^ ((k : ℝ) / 2) *
        (∏ i, Thermal.fidelity (q i) (Thermal.amplified g (q i))) + ε := by
  classical
  intro ε hε
  by_contra h
  have hf : ∃ᶠ n in atTop, ∃ Λ : HybridChannel k s,
      Thermal.classicalBase g ^ ((k : ℝ) / 2) *
          (∏ i, Thermal.fidelity (q i) (Thermal.amplified g (q i))) + ε <
        ((gaussianThermalPositive a ha q (fun i => (hq0 i).le) hq1).map
          (p.foelnerChannel (Real.sqrt g) Λ n)).rootFidelity
          (gaussianThermalPositive a ha q (fun i => (hq0 i).le) hq1) := by
    simpa only [Filter.Frequently, not_exists, not_lt, not_forall] using h
  obtain ⟨scale, hscale, hbad⟩ := exists_seq_forall_of_frequently hf
  choose Λ hΛ using hbad
  have he := p.foelner_output_eventually_le Λ scale hscale a ha g hg q hq0 hq1
    (ε / 2) (by linarith)
  obtain ⟨n, hn⟩ := he.exists
  have hb := hΛ n
  linarith

/-- The full universal expanding-prior converse for physical hybrid orbit
fidelity. The input and target have the same Gaussian and thermal covariance;
the target displacement has physical amplitude gain `sqrt g`. -/
theorem eventually_forall_gaussian_orbitPayoff_le
    (a : Fin k → ℝ) (ha : ∀ i, 0 < a i) (g : ℝ) (hg : 1 < g)
    (q : Fin s → ℝ) (hq0 : ∀ i, 0 < q i) (hq1 : ∀ i, q i < 1) :
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ Λ : HybridChannel k s,
      (∫ ξ, orbitPayoff (Real.sqrt g) Λ
        (gaussianThermalPositive a ha q (fun i => (hq0 i).le) hq1)
        (gaussianThermalPositive a ha q (fun i => (hq0 i).le) hq1) ξ ∂p.expandingPrior n) ≤
      Thermal.classicalBase g ^ ((k : ℝ) / 2) *
        (∏ i, Thermal.fidelity (q i) (Thermal.amplified g (q i))) + ε := by
  intro ε hε
  filter_upwards [p.eventually_forall_foelner_output_le a ha g hg q hq0 hq1 ε hε]
    with n hn
  intro Λ
  exact (integral_orbitPayoff_le_average (p.expandingPrior n) (Real.sqrt g) Λ _ _).trans (hn Λ)

/-- The manuscript's explicit classical--orbital product factor, with the
channel supremum allowed independently at every expanding-prior radius. -/
theorem eventually_forall_gaussian_orbitPayoff_le_modeFactor
    (a : Fin k → ℝ) (ha : ∀ i, 0 < a i) (g : ℝ) (hg : 1 < g)
    (q : Fin s → ℝ) (hq0 : ∀ i, 0 < q i) (hq1 : ∀ i, q i < 1) :
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ Λ : HybridChannel k s,
      (∫ ξ, orbitPayoff (Real.sqrt g) Λ
        (gaussianThermalPositive a ha q (fun i => (hq0 i).le) hq1)
        (gaussianThermalPositive a ha q (fun i => (hq0 i).le) hq1) ξ ∂p.expandingPrior n) ≤
      Thermal.classicalBase g ^ ((k : ℝ) / 2) *
        (∏ i, Thermal.modeFactor g (q i)) + ε := by
  have h := p.eventually_forall_gaussian_orbitPayoff_le a ha g hg q hq0 hq1
  simp_rw [Thermal.fidelity_amplified_eq_modeFactor hg (hq0 _).le (hq1 _)] at h
  exact h

end PhaseDensity
end Cloning.Hybrid
