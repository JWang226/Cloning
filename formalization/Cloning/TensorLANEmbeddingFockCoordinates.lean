import Cloning.TensorLANEmbeddingFockReindex

/-! Exact thermal and Weyl covariance of arbitrary mode relabeling. -/
noncomputable section
open scoped BigOperators Topology Classical InnerProductSpace
namespace Cloning.TensorLAN
open Cloning.MultimodeCoherent Cloning.MultimodeCoherentGaussianMixture
open Cloning.InfiniteTraceClass
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
variable {a b : ℕ}

@[simp] theorem fockReindex_symm (e : Fin a ≃ Fin b) :
    (fockReindex e).symm = fockReindex e.symm := by
  apply LinearIsometryEquiv.ext
  intro x
  apply (fockReindex e).injective
  rw [LinearIsometryEquiv.apply_symm_apply]
  apply lp.ext
  funext k
  simp only [fockReindex_apply, Equiv.symm_symm, Equiv.symm_apply_apply, Equiv.apply_symm_apply]

theorem displacementPhase_reindex (e : Fin a ≃ Fin b) (z w : Fin a → ℂ) :
    displacementPhase (fun j => z (e.symm j)) (fun j => w (e.symm j)) =
      displacementPhase z w :=
  e.symm.prod_comp (fun i => ComplexCoherent.displacementPhase (z i) (w i))

/-- Relabeling intertwines the actual Weyl operators on the entire Fock space. -/
theorem fockReindex_displacement (e : Fin a ≃ Fin b) (z : Fin a → ℂ) (x : Fock a) :
    fockReindex e (displacement z x) =
      displacement (fun j => z (e.symm j)) (fockReindex e x) := by
  have he : (fockReindex e).toLinearIsometry.toContinuousLinearMap.comp
      ((displacement z).comp (fockReindex e).symm.toLinearIsometry.toContinuousLinearMap) =
        displacement (fun j => z (e.symm j)) := by
    apply continuousLinearMap_ext_coherent
    intro w
    simp only [ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap, LinearIsometryEquiv.coe_toLinearIsometry,
      fockReindex_symm, fockReindex_coherentVector, Equiv.symm_symm,
      displacement_coherentVector, map_smul]
    congr 1
    · have h := displacementPhase_reindex e z (fun i => w (e i))
      simpa only [Equiv.apply_symm_apply] using h.symm
    · congr 1
      funext j
      simp
  have h := congrArg (fun T : Fock b →L[ℂ] Fock b => T (fockReindex e x)) he
  simpa only [ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap, LinearIsometryEquiv.coe_toLinearIsometry,
    LinearIsometryEquiv.symm_apply_apply] using h

/-- The positive geometric weights and every occupation vector are transported
by the same exact unitary, hence so is their trace-class density. -/
theorem fockReindex_productGeometric (e : Fin a ≃ Fin b) (q : Fin a → ℝ)
    (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i < 1) :
    conjugationLinearMap (fockReindex e).toLinearIsometry.toContinuousLinearMap
      (vectorMixture (numberBasis a) (ThermalWitness.productGeometric q)) =
    vectorMixture (numberBasis b) (ThermalWitness.productGeometric (fun j => q (e.symm j))) := by
  let Φ := QuantumChannel.ofIsometry (fockReindex e).toLinearIsometry
  have hs := summable_weighted_projectors (numberBasis a) (numberBasis a).orthonormal.norm_eq_one
    (ThermalWitness.productGeometric q) (Thermal.multimode_geometric_hasSum hq0 hq1).summable
  change Φ.toPositiveTracePreservingMap.toContinuousLinearMap
    (∑' k, (ThermalWitness.productGeometric q k : ℂ) • vectorProjector (numberBasis a k)) = _
  rw [ContinuousLinearMap.map_tsum _ hs]
  simp only [map_smul]
  change (∑' k, (ThermalWitness.productGeometric q k : ℂ) •
    conjugationLinearMap (fockReindex e).toLinearIsometry.toContinuousLinearMap (vectorProjector (numberBasis a k))) = _
  simp only [conjugationLinearMap_vectorProjector, LinearIsometry.coe_toContinuousLinearMap,
    LinearIsometryEquiv.coe_toLinearIsometry, fockReindex_numberBasis]
  rw [← (modeOccupationEquiv e).tsum_eq]
  unfold vectorMixture
  apply tsum_congr
  intro k
  simp only [modeOccupationEquiv, Equiv.coe_fn_mk, Equiv.apply_symm_apply]
  congr 2
  unfold ThermalWitness.productGeometric
  have he := e.prod_comp (fun j => Thermal.geometric (q (e.symm j)) (k j))
  simpa only [Equiv.symm_apply_apply] using he

end Cloning.TensorLAN
