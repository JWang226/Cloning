import Cloning.PhysicalFlatPinchingInflation

/-! The actual inflated input commutes with the entire polynomial tensor
representation, hence is invariant under every physical unitary orbit. -/
noncomputable section
open scoped BigOperators InnerProductSpace Classical ComplexOrder Matrix
namespace Cloning.PhysicalFlatConverse
open Cloning.PCT Cloning.TensorLie Cloning.TensorLAN Cloning.InfiniteTraceClass
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
set_option synthInstance.maxHeartbeats 200000
local instance (n d : ℕ) : FiniteDimensional ℂ (TensorRegister n (Fin d)) :=
  (registerBasis (Fin n → Fin d)).toOrthonormalBasis.toBasis.finiteDimensional_of_finite

theorem canonicalEmbedding_adjoint_tensorOperator {n d : ℕ} (H : PhysicalHighestTensor n d)
    (X : Matrix (Fin d) (Fin d) ℂ) :
    H.canonicalEmbedding.toContinuousLinearMap.adjoint.comp (tensorOperator n X) =
      (H.canonicalTensorOperator X).comp H.canonicalEmbedding.toContinuousLinearMap.adjoint := by
  have he : (tensorOperator n Xᴴ).comp H.canonicalEmbedding.toContinuousLinearMap =
      H.canonicalEmbedding.toContinuousLinearMap.comp (H.canonicalTensorOperator Xᴴ) := by
    apply ContinuousLinearMap.ext
    intro x
    exact (H.canonicalEmbedding_tensorOperator Xᴴ x).symm
  have ha := congrArg ContinuousLinearMap.adjoint he
  simpa only [ContinuousLinearMap.adjoint_comp, tensorOperator_star,
    PhysicalHighestTensor.canonicalTensorOperator, cyclicTensorOperator_star,
    ContinuousLinearMap.adjoint_adjoint] using ha

theorem embedded_copyIdentity_commutes {n d : ℕ} (H : PhysicalHighestTensor n d)
    (X : Matrix (Fin d) (Fin d) ℂ) :
    tensorOperator n X *
        (conjugationLinearMap H.canonicalEmbedding.toContinuousLinearMap (copyIdentity H)).1 =
      (conjugationLinearMap H.canonicalEmbedding.toContinuousLinearMap (copyIdentity H)).1 *
        tensorOperator n X := by
  have he : (tensorOperator n X).comp H.canonicalEmbedding.toContinuousLinearMap =
      H.canonicalEmbedding.toContinuousLinearMap.comp (H.canonicalTensorOperator X) := by
    apply ContinuousLinearMap.ext
    intro x
    exact (H.canonicalEmbedding_tensorOperator X x).symm
  change (tensorOperator n X).comp
      (H.canonicalEmbedding.toContinuousLinearMap.comp H.canonicalEmbedding.toContinuousLinearMap.adjoint) =
    (H.canonicalEmbedding.toContinuousLinearMap.comp H.canonicalEmbedding.toContinuousLinearMap.adjoint).comp
      (tensorOperator n X)
  rw [← ContinuousLinearMap.comp_assoc, he, ContinuousLinearMap.comp_assoc,
    ← canonicalEmbedding_adjoint_tensorOperator, ← ContinuousLinearMap.comp_assoc]

theorem inflatedTensor_commutes (n d : ℕ) (p : Fin d → ℝ) (X : Matrix (Fin d) (Fin d) ℂ) :
    tensorOperator n X * (inflatedTensor n d p).1 = (inflatedTensor n d p).1 * tensorOperator n X := by
  change tensorOperator n X * inclusionCLM (∑ i : SchurCopy n d, _) =
    inclusionCLM (∑ i : SchurCopy n d, _) * tensorOperator n X
  rw [map_sum, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul, mul_smul_comm, smul_mul_assoc, inclusionCLM_apply, embedded_copyIdentity_commutes]

theorem inflatedTensor_unitary (n d : ℕ) (p : Fin d → ℝ)
    (U : Matrix (Fin d) (Fin d) ℂ) (hU : Uᴴ * U = 1) :
    conjugationLinearMap (tensorOperator n U) (inflatedTensor n d p) = inflatedTensor n d p := by
  apply Subtype.ext
  change tensorOperator n U * (inflatedTensor n d p).1 * (tensorOperator n U).adjoint = _
  rw [inflatedTensor_commutes, mul_assoc, ← tensorOperator_star, ← tensorOperator_mul,
    mul_eq_one_comm.mp hU, tensorOperator_one, mul_one]

theorem flatInflatedInput_unitary (n r k : ℕ)
    (U : Matrix (Fin (r+k)) (Fin (r+k)) ℂ) (hU : Uᴴ * U = 1) :
    conjugationLinearMap (tensorOperator n U) (flatInflatedInput n r k) = flatInflatedInput n r k :=
  inflatedTensor_unitary n (r+k) _ U hU

end Cloning.PhysicalFlatConverse
