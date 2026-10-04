import Cloning.PhysicalCloningConversePreparation
import Cloning.PCTUnitaryTransportChannels

/-! Exact removal of the fixed classical Gaussian register for the known-
spectrum experiment, using genuine preparation and integration channels. -/
noncomputable section
open scoped Topology BigOperators
open MeasureTheory
namespace Cloning.PhysicalCloningConverse
open Cloning.InfiniteTraceClass Cloning.Hybrid Cloning.MultimodeCoherent
open Cloning.MultimodeCoherentGaussianMixture Cloning.PCTPhysicalFidelity
open Cloning.ThermalWitness Cloning.PCTUnitaryTransport
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
variable {k s : ℕ}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def prepareStandard (k s : ℕ) : QuantumToHybrid (Fock s) (Fock s) (volume : Measure (Fin k → ℝ)) :=
  QuantumToHybrid.prepare (standardDensity k) (integrable_standardDensity k)
    (standardDensity_nonneg k) (integral_standardDensity k)

def removeClassicalReverse
    (S : HybridToQuantum (Fock s) H (volume : Measure (Fin k → ℝ))) :
    HybridToQuantum (Fock s) H (volume : Measure (Fin 0 → ℝ)) :=
  postQuantum (S.compQuantumToHybrid (prepareStandard k s)) HybridToQuantum.integrate

def removeClassicalForward
    (T : QuantumToHybrid H (Fock s) (volume : Measure (Fin k → ℝ))) :
    QuantumToHybrid H (Fock s) (volume : Measure (Fin 0 → ℝ)) :=
  (prepareStandard 0 s).compQuantum (HybridToQuantum.integrate.compQuantumToHybrid T)

@[simp] theorem removeClassicalReverse_prepare
    (S : HybridToQuantum (Fock s) H (volume : Measure (Fin k → ℝ)))
    (D : TraceClass (Fock s)) :
    (removeClassicalReverse S).map ((prepareStandard 0 s).map D) =
      S.map ((prepareStandard k s).map D) := by
  change S.map ((prepareStandard k s).map (HybridToQuantum.integrate.map ((prepareStandard 0 s).map D))) = _
  simp only [prepareStandard, HybridToQuantum.integrate_prepare]

theorem removeClassicalForward_error
    (T : QuantumToHybrid H (Fock s) (volume : Measure (Fin k → ℝ)))
    (A : TraceClass H) (D : TraceClass (Fock s)) :
    ‖(removeClassicalForward T).map A - (prepareStandard 0 s).map D‖ ≤
      ‖T.map A - (prepareStandard k s).map D‖ := by
  change ‖(prepareStandard 0 s).map (HybridToQuantum.integrate.map (T.map A)) -
    (prepareStandard 0 s).map D‖ ≤ _
  rw [← map_sub]
  change ‖prepareL1 (standardDensity 0) (integrable_standardDensity 0)
    (HybridToQuantum.integrate.map (T.map A)-D)‖ ≤ _
  rw [norm_prepareL1 _ _ (standardDensity_nonneg 0) (integral_standardDensity 0)]
  have he : HybridToQuantum.integrate.map ((prepareStandard k s).map D) = D :=
    HybridToQuantum.integrate_prepare (standardDensity k) (integrable_standardDensity k)
      (standardDensity_nonneg k) (integral_standardDensity k) D
  have hle := HybridToQuantum.integrate_norm_le (T.map A - (prepareStandard k s).map D)
  simpa only [map_sub, he] using hle

/-- The zero-dimensional classical model, still in the genuine hybrid
channel category, has the same literal thermal quantum state. -/
def orbitalReference (p : SimpleSpectrum (k+1)) (e : Fin s ≃ PairIndex (k+1)) : HybridPositive 0 s :=
  gaussianThermalPositive (fun _ : Fin 0 => 1/2) (fun _ => by norm_num)
    (fun i => p.ratio (e i)) (fun i => (p.ratio_pos (e i)).le) (fun i => p.ratio_lt_one (e i))

theorem translated_orbitalReference_eq_prepare (p : SimpleSpectrum (k+1))
    (e : Fin s ≃ PairIndex (k+1)) (ξ : PhaseSpace 0 s) :
    (translatedPositive ξ (orbitalReference p e)).1 =
      (prepareStandard 0 s).map (displacedProductThermal p e ξ.2) := by
  have hξ : ξ.1 = 0 := Subsingleton.elim _ _
  rw [translatedPositive_val]
  change hybridTranslation ξ (gaussianThermalField _ _ _ _ _).toL1 = _
  rw [gaussianThermalField_toL1]
  have hpair : ξ = (0,ξ.2) := by ext <;> simp [hξ]
  rw [hpair, Cloning.PCTHybridMixture.hybridTranslation_prepare, classicalTranslation_zero]
  rfl

def orbitalParameters (e : Fin s ≃ PairIndex (k+1)) (ξ : PhaseSpace 0 s) : Parameters k :=
  (0,fun a => ξ.2 (e.symm a))

theorem continuous_orbitalParameters (e : Fin s ≃ PairIndex (k+1)) :
    Continuous (orbitalParameters e) := by unfold orbitalParameters; fun_prop

theorem orbitalParameters_sum_zero (e : Fin s ≃ PairIndex (k+1)) (ξ : PhaseSpace 0 s) :
    ∑ i, (orbitalParameters e ξ).1 i = 0 := by simp [orbitalParameters]

theorem model_orbitalParameters_eq_prepare (p : SimpleSpectrum (k+1))
    (b : Fin (k+1) → EuclideanSpace ℝ (Fin (k+1))) (e : Fin s ≃ PairIndex (k+1))
    (ξ : PhaseSpace 0 s) :
    (model p b e (orbitalParameters e ξ)).1 =
      (prepareStandard k s).map (displacedProductThermal p e ξ.2) := by
  rw [model_eq_prepare_translated]
  have hw : PCTJointGaussianWhitening.whiten p.eigenvalue b (0 : Fin (k+1) → ℝ) = 0 := by
    funext i
    simp [PCTJointGaussianWhitening.whiten]
  simp only [orbitalParameters, Equiv.symm_apply_apply, hw]
  change prepareL1 (fun x => standardDensity k (x-0)) _ _ = _
  simp only [sub_zero]
  rfl

theorem orbitalParameters_smul (e : Fin s ≃ PairIndex (k+1)) (c : ℝ) (ξ : PhaseSpace 0 s) :
    orbitalParameters e (c • ξ) = c • orbitalParameters e ξ := by ext <;> simp [orbitalParameters]

end Cloning.PhysicalCloningConverse
