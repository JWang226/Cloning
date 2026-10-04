import Cloning.PhysicalFlatPinchingCovariance
import Cloning.PhysicalFlatConverseOrbit

/-! The same actual inflated input dominates the entire rank-flat physical
unitary orbit. -/
noncomputable section
open scoped BigOperators InnerProductSpace Classical ComplexOrder Matrix
namespace Cloning.PhysicalFlatConverse
open Cloning.PCT Cloning.TensorLie Cloning.TensorLAN Cloning.InfiniteTraceClass
open Cloning.PCTUnitaryTransport Cloning.PCTPhysicalState
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
local instance (n d : ℕ) : FiniteDimensional ℂ (TensorRegister n (Fin d)) :=
  (registerBasis (Fin n → Fin d)).toOrthonormalBasis.toBasis.finiteDimensional_of_finite

theorem matrixTensorPower_conjugate (n d : ℕ) (U X : Matrix (Fin d) (Fin d) ℂ) :
    matrixTensorPower (U * X * Uᴴ) n =
      conjugationLinearMap (tensorOperator n U) (matrixTensorPower X n) := by
  apply Subtype.ext
  change tensorOperator n (U*X*Uᴴ) = tensorOperator n U * tensorOperator n X * (tensorOperator n U).adjoint
  rw [tensorOperator_mul, tensorOperator_mul, tensorOperator_star]

theorem rotatedTensor_le_inflatedTensor (n d : ℕ) (p : Fin d → ℝ)
    (hp : ∀ a, 0 ≤ p a) (hord : Antitone p)
    (U : Matrix (Fin d) (Fin d) ℂ) (hU : Uᴴ*U=1) :
    (matrixTensorPower (U * Matrix.diagonal (fun a => (p a : ℂ)) * Uᴴ) n).1 ≤
      (inflatedTensor n d p).1 := by
  have h := conjugationLinearMap_nonneg (tensorOperator n U)
    (inflatedTensor n d p - matrixTensorPower (Matrix.diagonal (fun a => (p a : ℂ))) n)
    (by exact sub_nonneg.mpr (matrixTensorPower_le_inflatedTensor n d p hp hord))
  rw [map_sub, inflatedTensor_unitary n d p U hU, ← matrixTensorPower_conjugate] at h
  exact sub_nonneg.mp h

theorem orbit_tensorState_le_flatInflatedInput (n r k : ℕ) (hr : 0 < r)
    (U : unitary (Matrix (Fin (r+k)) (Fin (r+k)) ℂ)) :
    letI : Nonempty (Fin (r+k)) := ⟨⟨0,Nat.lt_of_lt_of_le hr (Nat.le_add_right r k)⟩⟩
    ((tensorState (orbitState r k hr U) n).1).1 ≤ (flatInflatedInput n r k).1 := by
  letI : Nonempty (Fin (r+k)) := ⟨⟨0,Nat.lt_of_lt_of_le hr (Nat.le_add_right r k)⟩⟩
  exact rotatedTensor_le_inflatedTensor n (r+k) _ (rankFlatSpectrum_nonneg r k)
    (rankFlatSpectrum_antitone r k) U (Unitary.star_mul_self_of_mem U.property)

theorem schurPinching_tensorState (n d : ℕ) [Nonempty (Fin d)] (ρ : Cloning.MatrixFidelity.State (Fin d)) :
    (schurPinching n d).toLinearMap (tensorState ρ n).1 = (tensorState ρ n).1 :=
  schurPinching_matrixTensorPower n d ρ.matrix

end Cloning.PhysicalFlatConverse
