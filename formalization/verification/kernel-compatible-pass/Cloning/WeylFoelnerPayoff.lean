import Cloning.WeylFoelnerLimit
import Cloning.HybridJensenSigmaFinite
import Cloning.ThermalWitness

/-! Root-fidelity performance of actual Weyl-averaged competitors.
The average payoff is controlled by an actual averaged output and hence by a
compact thermal witness. These estimates do not restore escaping trace. -/

noncomputable section
open scoped ComplexOrder InnerProductSpace Topology BigOperators
open Filter MeasureTheory Cloning.InfiniteTraceClass Cloning.InfiniteFidelity
open Cloning.Hybrid
namespace Cloning.MultimodeCoherent
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {d : ℕ}

/-- Displacement of an arbitrary positive trace-class operator. -/
def displacedPositive (a : Fin d → ℂ) (A : PositiveTraceClass (Fock d)) :
    PositiveTraceClass (Fock d) :=
  PositiveTraceClass.map (displacementChannel a).toPositiveTracePreservingMap A

@[simp] theorem displacedPositive_val (a : Fin d → ℂ)
    (A : PositiveTraceClass (Fock d)) : (displacedPositive a A).1 =
      displacementTraceMap a A.1 := (displacementTraceMap_eq_channel a A.1).symm

@[simp] theorem displacedPositive_neg_cancel (a : Fin d → ℂ)
    (A : PositiveTraceClass (Fock d)) : displacedPositive (-a) (displacedPositive a A) = A := by
  apply Subtype.ext
  simp only [displacedPositive_val, displacementTraceMap_neg_cancel]

/-- Exact fidelity invariance under the actual infinite-dimensional Weyl unitaries. -/
theorem displacedPositive_rootFidelity (a : Fin d → ℂ)
    (A B : PositiveTraceClass (Fock d)) :
    (displacedPositive a A).rootFidelity (displacedPositive a B) = A.rootFidelity B := by
  apply le_antisymm
  · have h := fidelity_data_processing (displacementChannel (-a))
      (displacedPositive a A).1 (displacedPositive a B).1
      (displacedPositive a A).2 (displacedPositive a B).2
    change (displacedPositive a A).rootFidelity (displacedPositive a B) ≤
      (displacedPositive (-a) (displacedPositive a A)).rootFidelity
        (displacedPositive (-a) (displacedPositive a B)) at h
    simpa only [displacedPositive_neg_cancel] using h
  · exact fidelity_data_processing (displacementChannel a) A.1 B.1 A.2 B.2

/-- The physical orbit payoff at phase-space amplitude `a`. Inputs and targets
may be arbitrary positive trace-class states, including mixed thermal states. -/
def orbitPayoff (gain : ℝ) (Φ : QuantumChannel (Fock d) (Fock d))
    (A B : PositiveTraceClass (Fock d)) (a : Fin d → ℂ) : ℝ :=
  (PositiveTraceClass.map Φ.toPositiveTracePreservingMap (displacedPositive a A)).rootFidelity
    (displacedPositive (gain • a) B)

/-- Undoing the target displacement identifies the orbit fidelity with the
fidelity of the translated channel at the fixed reference input. -/
theorem orbitPayoff_eq_translated (gain : ℝ) (Φ : QuantumChannel (Fock d) (Fock d))
    (A B : PositiveTraceClass (Fock d)) (a : Fin d → ℂ) :
    orbitPayoff gain Φ A B a =
      (PositiveTraceClass.map (translatedChannel gain Φ a).toPositiveTracePreservingMap A).rootFidelity B := by
  have h := displacedPositive_rootFidelity (-(gain • a))
    (PositiveTraceClass.map Φ.toPositiveTracePreservingMap (displacedPositive a A))
    (displacedPositive (gain • a) B)
  rw [displacedPositive_neg_cancel] at h
  have he : displacedPositive (-(gain • a))
      (PositiveTraceClass.map Φ.toPositiveTracePreservingMap (displacedPositive a A)) =
      PositiveTraceClass.map (translatedChannel gain Φ a).toPositiveTracePreservingMap A := by
    apply Subtype.ext
    simp only [displacedPositive_val, PositiveTraceClass.map, translatedChannel_apply]
  rw [he] at h
  exact h.symm

/-- The physical fidelity payoff is continuous in the displacement parameter. -/
lemma continuous_orbitPayoff (gain : ℝ) (Φ : QuantumChannel (Fock d) (Fock d))
    (A B : PositiveTraceClass (Fock d)) : Continuous (orbitPayoff gain Φ A B) := by
  have he : orbitPayoff gain Φ A B = fun a =>
      (PositiveTraceClass.map (translatedChannel gain Φ a).toPositiveTracePreservingMap A).rootFidelity B :=
    funext (orbitPayoff_eq_translated gain Φ A B)
  rw [he]
  have hc : Continuous (fun a =>
      PositiveTraceClass.map (translatedChannel gain Φ a).toPositiveTracePreservingMap A) :=
    (continuous_translatedChannel gain Φ A.1).subtype_mk _
  exact Continuous.comp
    (f := fun a => (PositiveTraceClass.map
      (translatedChannel gain Φ a).toPositiveTracePreservingMap A, B))
    PositiveTraceClass.continuous_rootFidelity (hc.prodMk continuous_const)

lemma integrable_orbitPayoff (μ : Measure (Fin d → ℂ)) [IsProbabilityMeasure μ]
    (gain : ℝ) (Φ : QuantumChannel (Fock d) (Fock d))
    (A B : PositiveTraceClass (Fock d)) : Integrable (orbitPayoff gain Φ A B) μ := by
  let R : (Fin d → ℂ) → PositiveTraceClass (Fock d) := fun a =>
    ⟨(translatedChannel gain Φ a).toLinearMap A.1,
      (translatedChannel gain Φ a).map_nonneg A.1 A.2⟩
  have hc : Continuous R := (continuous_translatedChannel gain Φ A.1).subtype_mk _
  have hf : Integrable (fun a => (R a).rootFidelity B) μ := by
    apply (integrable_const (Real.sqrt ‖A.1‖ * Real.sqrt ‖B.1‖)).mono'
      ((PositiveTraceClass.continuous_rootFidelity.comp
        (hc.prodMk continuous_const)).aestronglyMeasurable)
    exact Eventually.of_forall fun a => by
      change ‖(R a).rootFidelity B‖ ≤ Real.sqrt ‖A.1‖ * Real.sqrt ‖B.1‖
      rw [Real.norm_of_nonneg (PositiveTraceClass.rootFidelity_nonneg _ _)]
      have h := PositiveTraceClass.rootFidelity_le_sqrt (R a) B
      have he : ‖(R a).1‖ = ‖A.1‖ :=
        (translatedChannel gain Φ a).toPositiveTracePreservingMap.norm_map_of_nonneg A.1 A.2
      rwa [he] at h
  have he : orbitPayoff gain Φ A B = fun a => (R a).rootFidelity B := by
    funext a
    exact orbitPayoff_eq_translated gain Φ A B a
  rwa [he]

/-- Any probability average retains the averaged root-fidelity payoff of the
original competitor. The output is the actual CPTP Bochner average. -/
theorem integral_orbitPayoff_le_average (μ : Measure (Fin d → ℂ)) [IsProbabilityMeasure μ]
    (gain : ℝ) (Φ : QuantumChannel (Fock d) (Fock d))
    (A B : PositiveTraceClass (Fock d)) :
    (∫ a, orbitPayoff gain Φ A B a ∂μ) ≤
      (PositiveTraceClass.map (covariantAverage μ gain Φ).toPositiveTracePreservingMap A).rootFidelity B := by
  have h := PositiveField.integral_fidelity_le_fidelity_integral
    (fun a => (translatedChannel gain Φ a).toLinearMap A.1)
    (fun _ : Fin d → ℂ => B.1)
    (quantumChannel_family_integrable μ (translatedChannel gain Φ)
      (fun C => (continuous_translatedChannel gain Φ C).aestronglyMeasurable) A.1)
    (integrable_const B.1)
    (fun a => (translatedChannel gain Φ a).map_nonneg A.1 A.2) (fun _ => B.2)
  simp only [integral_const, probReal_univ, one_smul] at h
  simpa only [orbitPayoff_eq_translated] using h

/-- A pointwise orbit lower bound is retained at the reference state by every
probability average; there is no bounded-support or finite-energy premise. -/
theorem lower_bound_le_average (μ : Measure (Fin d → ℂ)) [IsProbabilityMeasure μ]
    (gain : ℝ) (Φ : QuantumChannel (Fock d) (Fock d))
    (A B : PositiveTraceClass (Fock d)) {c : ℝ}
    (hc : ∀ a, c ≤ orbitPayoff gain Φ A B a) :
    c ≤ (PositiveTraceClass.map (covariantAverage μ gain Φ).toPositiveTracePreservingMap A).rootFidelity B := by
  apply le_trans _ (integral_orbitPayoff_le_average μ gain Φ A B)
  simpa only [integral_const, probReal_univ, smul_eq_mul, one_mul] using
    integral_mono (integrable_const c) (integrable_orbitPayoff μ gain Φ A B) hc

/-- A compact-witness bound on the actual averaged output bounds the original
prior-averaged fidelity. The inverse moment is explicitly regularized. -/
theorem integral_orbitPayoff_sq_le_weight (μ : Measure (Fin d → ℂ)) [IsProbabilityMeasure μ]
    (gain : ℝ) (Φ : QuantumChannel (Fock d) (Fock d))
    (A B : PositiveTraceClass (Fock d)) (W : (Fock d) →L[ℂ] (Fock d))
    (hW : 0 ≤ W) {M : ℝ} (hM : 0 ≤ M)
    (hInv : ∀ ε : ℝ, 0 < ε →
      (tracePairing B.1 (CFC.rpow (regularizedWeight W ε) (-1))).re ≤ M) :
    (∫ a, orbitPayoff gain Φ A B a ∂μ) ^ 2 ≤
      (tracePairing ((covariantAverage μ gain Φ).toLinearMap A.1) W).re * M := by
  have h := integral_orbitPayoff_le_average μ gain Φ A B
  have hn : 0 ≤ ∫ a, orbitPayoff gain Φ A B a ∂μ :=
    integral_nonneg (fun _ => PositiveTraceClass.rootFidelity_nonneg _ _)
  have hf := fidelity_sq_le_of_regularized_inverse_moment
    ((covariantAverage μ gain Φ).map_nonneg A.1 A.2) B.2 hW
    ((covariantAverage μ gain Φ).toLinearMap A.1).2 B.1.2 hM hInv
  exact (sq_le_sq₀ hn (PositiveTraceClass.rootFidelity_nonneg _ _)).mpr h |>.trans hf

end Cloning.MultimodeCoherent
