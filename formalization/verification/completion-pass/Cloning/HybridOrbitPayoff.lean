import Cloning.HybridFoelner
import Cloning.HybridL1Jensen
import Cloning.WeylFoelnerPayoff

/-! The physical hybrid orbit payoff on actual positive L¹ states and exact
invariance under the joint classical/quantum translation action. -/
noncomputable section
open scoped ComplexOrder InnerProductSpace Topology
open MeasureTheory Filter Cloning.InfiniteTraceClass Cloning.InfiniteFidelity
open Cloning.MultimodeCoherent
namespace Cloning.Hybrid
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {k s : ℕ}

abbrev HybridPositive (k s : ℕ) := PositiveL1 (Fock s) (volume : Measure (Fin k → ℝ))

def translatedPositive (ξ : PhaseSpace k s) (A : HybridPositive k s) : HybridPositive k s :=
  A.map (translationChannel ξ)

@[simp] lemma translatedPositive_val (ξ : PhaseSpace k s) (A : HybridPositive k s) :
    (translatedPositive ξ A).1 = hybridTranslation ξ A.1 := rfl

@[simp] lemma translatedPositive_neg_cancel (ξ : PhaseSpace k s) (A : HybridPositive k s) :
    translatedPositive (-ξ) (translatedPositive ξ A) = A := by
  apply Subtype.ext
  simp only [translatedPositive_val, ← hybridTranslation_add, neg_add_cancel, hybridTranslation_zero]

lemma hybridTranslation_ae (ξ : PhaseSpace k s) (A : HybridSpace k s) :
    hybridTranslation ξ A =ᵐ[volume]
      fun y => displacementTraceMap ξ.2 (A (y - ξ.1)) := by
  filter_upwards [quantumL1Action_ae ξ.2 (classicalTranslation ξ.1 A), classicalTranslation_ae ξ.1 A]
    with y hy hz
  change quantumL1Action ξ.2 (classicalTranslation ξ.1 A) y = _
  rw [hy, hz]

/-- The actual integrated fidelity is invariant under both simultaneous
classical translation and Weyl conjugation. -/
theorem translatedPositive_rootFidelity (ξ : PhaseSpace k s) (A B : HybridPositive k s) :
    (translatedPositive ξ A).rootFidelity (translatedPositive ξ B) = A.rootFidelity B := by
  rw [PositiveL1.rootFidelity_eq_integral, PositiveL1.rootFidelity_eq_integral]
  calc
    _ = ∫ y, extendedRootFidelity (A.1 (y - ξ.1), B.1 (y - ξ.1)) := by
      apply integral_congr_ae
      have hpA := (measurePreserving_sub_right volume ξ.1).quasiMeasurePreserving.ae A.2
      have hpB := (measurePreserving_sub_right volume ξ.1).quasiMeasurePreserving.ae B.2
      filter_upwards [hybridTranslation_ae ξ A.1, hybridTranslation_ae ξ B.1, hpA, hpB]
        with y hAy hBy hA hB
      change extendedRootFidelity (hybridTranslation ξ A.1 y, hybridTranslation ξ B.1 y) = _
      rw [hAy, hBy]
      have hp := displacedPositive_rootFidelity ξ.2
        (⟨A.1 (y - ξ.1), hA⟩ : PositiveTraceClass (Fock s))
        (⟨B.1 (y - ξ.1), hB⟩ : PositiveTraceClass (Fock s))
      simp only [displacementTraceMap_eq_channel]
      rw [extendedRootFidelity_eq _ _
        ((displacementChannel ξ.2).map_nonneg _ hA)
        ((displacementChannel ξ.2).map_nonneg _ hB), extendedRootFidelity_eq _ _ hA hB]
      exact hp
    _ = _ := integral_sub_right_eq_self (μ := volume)
      (fun y : Fin k → ℝ => extendedRootFidelity (A.1 y, B.1 y)) ξ.1

/-- Fidelity at the physical displaced input and its gain-scaled target. -/
def orbitPayoff (r : ℝ) (Λ : HybridChannel k s) (A B : HybridPositive k s)
    (ξ : PhaseSpace k s) : ℝ :=
  ((translatedPositive ξ A).map Λ).rootFidelity (translatedPositive (r • ξ) B)

lemma orbitPayoff_eq_translated (r : ℝ) (Λ : HybridChannel k s)
    (A B : HybridPositive k s) (ξ : PhaseSpace k s) :
    orbitPayoff r Λ A B ξ = (A.map (translatedChannel r Λ ξ)).rootFidelity B := by
  have h := translatedPositive_rootFidelity (-(r • ξ))
    ((translatedPositive ξ A).map Λ) (translatedPositive (r • ξ) B)
  rw [translatedPositive_neg_cancel] at h
  have he : translatedPositive (-(r • ξ)) ((translatedPositive ξ A).map Λ) =
      A.map (translatedChannel r Λ ξ) := by
    apply Subtype.ext
    rfl
  rw [he] at h
  exact h.symm

lemma continuous_orbitPayoff (r : ℝ) (Λ : HybridChannel k s) (A B : HybridPositive k s) :
    Continuous (orbitPayoff r Λ A B) := by
  have hc : Continuous (fun ξ => A.map (translatedChannel r Λ ξ)) :=
    (continuous_translatedChannel r Λ A.1).subtype_mk _
  have h := PositiveL1.continuous_rootFidelity.comp (hc.prodMk (continuous_const (y := B)))
  exact h.congr (fun ξ => (orbitPayoff_eq_translated r Λ A B ξ).symm)

lemma integrable_orbitPayoff (ν : Measure (PhaseSpace k s)) [IsProbabilityMeasure ν]
    (r : ℝ) (Λ : HybridChannel k s) (A B : HybridPositive k s) :
    Integrable (orbitPayoff r Λ A B) ν := by
  apply (integrable_const (Real.sqrt ‖A.1‖ * Real.sqrt ‖B.1‖)).mono'
    (continuous_orbitPayoff r Λ A B).aestronglyMeasurable
  exact Eventually.of_forall fun ξ => by
    rw [orbitPayoff_eq_translated, Real.norm_of_nonneg (PositiveL1.rootFidelity_nonneg _ _)]
    simpa only [PositiveL1.norm_map] using
      PositiveL1.rootFidelity_le_sqrt (A.map (translatedChannel r Λ ξ)) B

/-- Concavity retains the original prior payoff in the actual averaged output. -/
theorem integral_orbitPayoff_le_average (ν : Measure (PhaseSpace k s)) [IsProbabilityMeasure ν]
    (r : ℝ) (Λ : HybridChannel k s) (A B : HybridPositive k s) :
    (∫ ξ, orbitPayoff r Λ A B ξ ∂ν) ≤ (A.map (covariantAverage ν r Λ)).rootFidelity B := by
  have h := PositiveL1.integral_rootFidelity_const_le
    (fun ξ => A.map (translatedChannel r Λ ξ))
    (channel_family_integrable ν (translatedChannel r Λ)
      (fun C => (continuous_translatedChannel r Λ C).aestronglyMeasurable) A.1)
    (A.map (covariantAverage ν r Λ)) B (by rfl)
  simpa only [orbitPayoff_eq_translated] using h

end Cloning.Hybrid
