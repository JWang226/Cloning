import Cloning.HybridChannelAveraging
import Cloning.HybridCovariantQuantum

/-! Actual hybrid translated competitors and their probability averages. -/
noncomputable section
open scoped ComplexOrder Topology
open MeasureTheory Filter Cloning.InfiniteTraceClass Cloning.MultimodeCoherent
namespace Cloning.Hybrid
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {k s : ℕ}

abbrev PhaseSpace (k s : ℕ) := (Fin k → ℝ) × (Fin s → ℂ)
abbrev HybridSpace (k s : ℕ) := Lp (TraceClass (Fock s)) 1 (volume : Measure (Fin k → ℝ))
abbrev HybridChannel (k s : ℕ) := Channel (Fock s) (Fock s) (volume : Measure (Fin k → ℝ))

def translationChannel (ξ : PhaseSpace k s) : HybridChannel k s where
  map := hybridTranslation ξ
  completelyPositive := hybridTranslation_completelyPositive ξ
  tracePreserving := hybridTranslation_tracePreserving ξ

/-- Translate input and undo the output shift at amplitude gain `r`. -/
def translatedChannel (r : ℝ) (Λ : HybridChannel k s) (ξ : PhaseSpace k s) :
    HybridChannel k s :=
  (translationChannel (-(r • ξ))).comp (Λ.comp (translationChannel ξ))

@[simp] lemma translatedChannel_apply (r : ℝ) (Λ : HybridChannel k s)
    (ξ : PhaseSpace k s) (A : HybridSpace k s) :
    (translatedChannel r Λ ξ).map A = hybridTranslation (-(r • ξ)) (Λ.map (hybridTranslation ξ A)) := rfl

set_option backward.isDefEq.respectTransparency true in
lemma continuous_translatedChannel (r : ℝ) (Λ : HybridChannel k s) (A : HybridSpace k s) :
    Continuous (fun ξ => (translatedChannel r Λ ξ).map A) := by
  have h₁ : Continuous (fun ξ : PhaseSpace k s => -(r • ξ)) :=
    (continuous_id.const_smul r).neg
  have h₂ : Continuous (fun ξ : PhaseSpace k s => Λ.map (hybridTranslation ξ A)) :=
    Λ.map.continuous.comp (continuous_hybridTranslation A)
  have h := (continuous_hybridTranslation_joint (k := k) (s := s)).comp (h₁.prodMk h₂)
  exact h

def covariantAverageMap (ν : Measure (PhaseSpace k s)) [IsProbabilityMeasure ν]
    (r : ℝ) (Λ : HybridChannel k s) : HybridSpace k s →L[ℂ] HybridSpace k s :=
  averageCLM ν (translatedChannel r Λ)
    (fun A => (continuous_translatedChannel r Λ A).aestronglyMeasurable)

@[simp] lemma covariantAverageMap_apply (ν : Measure (PhaseSpace k s)) [IsProbabilityMeasure ν]
    (r : ℝ) (Λ : HybridChannel k s) (A : HybridSpace k s) :
    covariantAverageMap ν r Λ A = ∫ ξ, (translatedChannel r Λ ξ).map A ∂ν := rfl

/-- Averaging over a probability prior gives an actual hybrid CPTP channel. -/
def covariantAverage (ν : Measure (PhaseSpace k s)) [IsProbabilityMeasure ν]
    (r : ℝ) (Λ : HybridChannel k s) : HybridChannel k s :=
  Channel.average ν (translatedChannel r Λ)
    (fun A => (continuous_translatedChannel r Λ A).aestronglyMeasurable)

@[simp] lemma covariantAverage_map (ν : Measure (PhaseSpace k s)) [IsProbabilityMeasure ν]
    (r : ℝ) (Λ : HybridChannel k s) : (covariantAverage ν r Λ).map = covariantAverageMap ν r Λ := rfl

lemma translatedChannel_shift (r : ℝ) (Λ : HybridChannel k s)
    (ξ η : PhaseSpace k s) (A : HybridSpace k s) :
    (translatedChannel r Λ ξ).map (hybridTranslation η A) =
      hybridTranslation (r • η) ((translatedChannel r Λ (ξ + η)).map A) := by
  simp only [translatedChannel_apply, ← hybridTranslation_add]
  rw [show r • η + -(r • (ξ + η)) = -(r • ξ) by rw [smul_add]; abel]

lemma covariantAverageMap_shift (ν : Measure (PhaseSpace k s)) [IsProbabilityMeasure ν]
    (r : ℝ) (Λ : HybridChannel k s) (η : PhaseSpace k s) (A : HybridSpace k s) :
    covariantAverageMap ν r Λ (hybridTranslation η A) =
      hybridTranslation (r • η) (∫ ξ, (translatedChannel r Λ (ξ + η)).map A ∂ν) := by
  have hi : Integrable (fun ξ => (translatedChannel r Λ (ξ + η)).map A) ν :=
    channel_family_integrable ν (fun ξ => translatedChannel r Λ (ξ + η))
      (fun B => ((continuous_translatedChannel r Λ B).comp
        (continuous_id.add continuous_const)).aestronglyMeasurable) A
  rw [covariantAverageMap_apply]
  simp_rw [translatedChannel_shift]
  exact (hybridTranslation (r • η)).integral_comp_comm hi

end Cloning.Hybrid
