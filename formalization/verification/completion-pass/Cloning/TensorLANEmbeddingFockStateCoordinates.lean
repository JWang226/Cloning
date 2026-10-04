import Cloning.TensorLANEmbeddingFockCoordinates
import Cloning.TensorGibbsThermalIdentification
import Cloning.TensorGibbsPhysicalDisplacement
import Cloning.PhysicalCloningConversePreparation

/-! The actual root-indexed thermal/Weyl target in every allowed finite mode
coordinate system of the physical LAN model. -/
noncomputable section
open scoped BigOperators Topology Classical InnerProductSpace
namespace Cloning.TensorLAN
open Cloning.MultimodeCoherent Cloning.MultimodeCoherentGaussianMixture
open Cloning.InfiniteTraceClass Cloning.TensorLie Cloning.TensorLocalUnitary
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

private theorem conjugation_comp' {H K L : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L]
    (V : K →L[ℂ] L) (W : H →L[ℂ] K) (A : TraceClass H) :
    conjugationLinearMap V (conjugationLinearMap W A) = conjugationLinearMap (V.comp W) A := by
  apply Subtype.ext
  ext x
  simp only [conjugationLinearMap_coe, operatorConjugation_apply,
    ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.comp_apply]

theorem fockReindex_displacementTraceMap {a b : ℕ} (e : Fin a ≃ Fin b)
    (z : Fin a → ℂ) (A : TraceClass (Fock a)) :
    conjugationLinearMap (fockReindex e).toLinearIsometry.toContinuousLinearMap
      (displacementTraceMap z A) =
    displacementTraceMap (fun j => z (e.symm j))
      (conjugationLinearMap (fockReindex e).toLinearIsometry.toContinuousLinearMap A) := by
  rw [displacementTraceMap_eq_channel, displacementTraceMap_eq_channel]
  change conjugationLinearMap (fockReindex e).toLinearIsometry.toContinuousLinearMap
      (conjugationLinearMap (displacement z) A) =
    conjugationLinearMap (displacement (fun j => z (e.symm j)))
      (conjugationLinearMap (fockReindex e).toLinearIsometry.toContinuousLinearMap A)
  rw [conjugation_comp', conjugation_comp']
  congr 2
  apply ContinuousLinearMap.ext
  intro x
  exact fockReindex_displacement e z x

theorem rootFockReindex_thermal {d s : ℕ} (e : Fin s ≃ PositiveRoot d)
    (p : Fin d → ℝ) (hp : ∀ a, 0 < p a) (hord : StrictAnti p) :
    conjugationLinearMap (rootFockReindex e).toLinearIsometry.toContinuousLinearMap (rootThermalState p) =
      vectorMixture (numberBasis s) (ThermalWitness.productGeometric (fun i =>
        p (e i).1.2 / p (e i).1.1)) := by
  rw [rootThermalState_eq_productGeometric]
  have h := fockReindex_productGeometric
    ((Fintype.equivFin (PositiveRoot d)).symm.trans e.symm) (rootThermalParameter p)
    (fun i => (div_pos (hp _) (hp _)).le)
    (fun i => rootBoltzmann_lt_one p hp hord _)
  simpa only [rootFockReindex, rootThermalParameter, rootBoltzmann, Equiv.symm_trans_apply,
    Equiv.symm_symm, Equiv.symm_apply_apply] using h

theorem rootFockReindex_displacedThermal {d s : ℕ} (e : Fin s ≃ PositiveRoot d)
    (p : Fin d → ℝ) (hp : ∀ a, 0 < p a) (hord : StrictAnti p)
    (z : PositiveRoot d → ℂ) :
    conjugationLinearMap (rootFockReindex e).toLinearIsometry.toContinuousLinearMap (rootDisplacedThermal p z) =
      displacementTraceMap (fun i => z (e i))
        (vectorMixture (numberBasis s) (ThermalWitness.productGeometric (fun i =>
          p (e i).1.2 / p (e i).1.1))) := by
  rw [rootDisplacedThermal, ← displacementTraceMap_eq_channel]
  have he := fockReindex_displacementTraceMap
    ((Fintype.equivFin (PositiveRoot d)).symm.trans e.symm) (rootFockAmplitude z) (rootThermalState p)
  change conjugationLinearMap (rootFockReindex e).toLinearIsometry.toContinuousLinearMap
    (displacementTraceMap (rootFockAmplitude z) (rootThermalState p)) = _
  unfold rootFockReindex
  rw [he]
  have hz : (fun j => rootFockAmplitude z
      (((Fintype.equivFin (PositiveRoot d)).symm.trans e.symm).symm j)) = fun i => z (e i) := by
    funext i
    simp only [rootFockAmplitude, Equiv.symm_trans_apply, Equiv.symm_symm, Equiv.symm_apply_apply]
  rw [hz]
  exact congrArg (displacementTraceMap (fun i => z (e i)))
    (rootFockReindex_thermal e p hp hord)

theorem rootFockReindex_displacedProductThermal {k s : ℕ}
    (p : SimpleSpectrum (k+1)) (e : Fin s ≃ PairIndex (k+1))
    (z : PositiveRoot (k+1) → ℂ) :
    conjugationLinearMap (rootFockReindex e).toLinearIsometry.toContinuousLinearMap
      (rootDisplacedThermal p.eigenvalue z) =
      PhysicalCloningConverse.displacedProductThermal p e (fun i => z (e i)) := by
  exact rootFockReindex_displacedThermal e p.eigenvalue p.positive p.strictAnti z

end Cloning.TensorLAN
