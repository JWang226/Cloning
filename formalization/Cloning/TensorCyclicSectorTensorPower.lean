import Cloning.TensorCyclicSectorOperators
import Cloning.PCTPurificationChannel
import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Analysis.Calculus.Deriv.Mul

/-! Literal tensor-power operators for physical cyclic-sector covariance. -/
noncomputable section
open scoped BigOperators InnerProductSpace Matrix
namespace Cloning.TensorLie
open Cloning.PCT Cloning.InfiniteFiniteCorner Cloning.PCTPurificationChannel
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {n d : ℕ}

/-- Computational coefficient action of the actual register matrix lift. -/
theorem register_ofMatrix_apply {I : Type*} [Fintype I] [DecidableEq I]
    (M : Matrix I I ℂ) (x : Register I) (w : I) :
    ofMatrix (registerBasis I) M x w = ∑ v, M w v * x v := by
  rw [← register_inner_single, ← registerBasis_apply, inner_ofMatrix_apply (registerBasis I).orthonormal]
  simp only [registerBasis_apply, register_inner_single]

/-- Matrix lifting is continuous and linear, on the whole finite matrix space. -/
def registerMatrixCLM {I : Type*} [Fintype I] [DecidableEq I] :
    Matrix I I ℂ →L[ℂ] (Register I →L[ℂ] Register I) :=
  LinearMap.toContinuousLinearMap {
    toFun := ofMatrix (registerBasis I)
    map_add' := by
      intro M N
      ext x w
      simp only [register_ofMatrix_apply, Matrix.add_apply, add_mul, Finset.sum_add_distrib,
        ContinuousLinearMap.add_apply, lp.coeFn_add, Pi.add_apply]
    map_smul' := by
      intro c M
      ext x w
      simp only [register_ofMatrix_apply, Matrix.smul_apply, smul_eq_mul, mul_assoc,
        ← Finset.mul_sum, RingHom.id_apply, ContinuousLinearMap.smul_apply, lp.coeFn_smul, Pi.smul_apply] }

@[simp] theorem registerMatrixCLM_apply {I : Type*} [Fintype I] [DecidableEq I]
    (M : Matrix I I ℂ) : registerMatrixCLM M = ofMatrix (registerBasis I) M := rfl

/-- Literal `X` on every tensor factor, on the complete physical register. -/
def tensorOperator (n : ℕ) (X : Matrix (Fin d) (Fin d) ℂ) :
    TensorRegister n (Fin d) →L[ℂ] TensorRegister n (Fin d) :=
  registerMatrixCLM (tensorPower n X)

@[simp] theorem tensorOperator_apply (X : Matrix (Fin d) (Fin d) ℂ)
    (x : TensorRegister n (Fin d)) (w : Fin n → Fin d) :
    tensorOperator n X x w = ∑ v, (∏ t, X (w t) (v t)) * x v :=
  register_ofMatrix_apply _ x w

theorem tensorOperator_mul (X Y : Matrix (Fin d) (Fin d) ℂ) :
    tensorOperator n (X * Y) = tensorOperator n X * tensorOperator n Y := by
  simp only [tensorOperator, tensorPower_mul, registerMatrixCLM_apply,
    ofMatrix_mul (registerBasis _).orthonormal]

@[simp] theorem tensorOperator_one : tensorOperator n (1 : Matrix (Fin d) (Fin d) ℂ) = 1 := by
  ext x w
  simp only [tensorOperator, tensorPower_one, registerMatrixCLM_apply, register_ofMatrix_apply,
    Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
    if_true, ContinuousLinearMap.one_apply]

theorem tensorOperator_star (X : Matrix (Fin d) (Fin d) ℂ) :
    tensorOperator n Xᴴ = (tensorOperator n X).adjoint := by
  simp only [tensorOperator, tensorPower_star, registerMatrixCLM_apply, ofMatrix_conjTranspose,
    ContinuousLinearMap.star_eq_adjoint]

/-- Unitary matrices induce genuine isometries on the full tensor register. -/
theorem tensorOperator_norm (U : Matrix (Fin d) (Fin d) ℂ) (hU : Uᴴ * U = 1)
    (x : TensorRegister n (Fin d)) : ‖tensorOperator n U x‖ = ‖x‖ := by
  have he : (tensorOperator n U).adjoint * tensorOperator n U = 1 := by
    rw [← tensorOperator_star, ← tensorOperator_mul, hU, tensorOperator_one]
  have hinner : ⟪tensorOperator n U x, tensorOperator n U x⟫_ℂ = ⟪x, x⟫_ℂ := by
    rw [← ContinuousLinearMap.adjoint_inner_right]
    change ⟪x, ((tensorOperator n U).adjoint * tensorOperator n U) x⟫_ℂ = _
    rw [he, ContinuousLinearMap.one_apply]
  have hs : ‖tensorOperator n U x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ), hinner, ← norm_sq_eq_re_inner (𝕜 := ℂ)]
  nlinarith [norm_nonneg (tensorOperator n U x), norm_nonneg x]

end Cloning.TensorLie
