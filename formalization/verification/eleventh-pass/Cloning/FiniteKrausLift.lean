import Cloning.PCTPurificationChannelPhysical
import Cloning.InfiniteRectangularKraus

/-! Lifting normalized finite rectangular matrix Kraus families to genuine channels of physical trace-class registers. -/
noncomputable section
open scoped BigOperators Matrix InnerProductSpace ComplexOrder
open Cloning.InfiniteTraceClass Cloning.PCT Cloning.PCTPurificationChannel

namespace Cloning.FiniteKrausLift

set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

variable {I J K : Type*} [Fintype I] [Fintype J] [Fintype K]
  [DecidableEq I] [DecidableEq J] [DecidableEq K]

local instance registerFiniteDimensional (L : Type*) [Fintype L] [DecidableEq L] :
    FiniteDimensional ℂ (Register L) :=
  (registerBasis L).toOrthonormalBasis.toBasis.finiteDimensional_of_finite

/-- Actual rectangular matrix action on the finite Hilbert register. -/
def matrixRegister (M : Matrix J I ℂ) : Register I →L[ℂ] Register J :=
  LinearMap.toContinuousLinearMap
    { toFun x := ⟨fun a => ∑ b, M a b * x b, memℓp_gen (by
        simp only [ENNReal.toReal_ofNat]; exact (hasSum_fintype _).summable)⟩
      map_add' x y := by
        ext a
        change (∑ b, M a b * (x b + y b)) = (∑ b, M a b * x b) + ∑ b, M a b * y b
        simp only [mul_add, Finset.sum_add_distrib]
      map_smul' c x := by ext a; simp [Finset.mul_sum, mul_left_comm] }

@[simp] theorem matrixRegister_apply (M : Matrix J I ℂ) (x : Register I) (a : J) :
    matrixRegister M x a = ∑ b, M a b * x b := rfl

@[simp] theorem matrixRegister_single (M : Matrix J I ℂ) (b : I) (a : J) :
    matrixRegister M (lp.single 2 b 1) a = M a b := by
  simp [matrixRegister_apply, lp.single_apply, Pi.single_apply]

@[simp] theorem matrixRegister_one :
    matrixRegister (1 : Matrix I I ℂ) = ContinuousLinearMap.id ℂ (Register I) := by
  ext x a
  simp [Matrix.one_apply]

theorem matrixRegister_mul (M : Matrix K J ℂ) (N : Matrix J I ℂ) :
    matrixRegister (M * N) = (matrixRegister M).comp (matrixRegister N) := by
  ext x a
  simp only [matrixRegister_apply, Matrix.mul_apply, Finset.sum_mul,
    ContinuousLinearMap.comp_apply, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

theorem matrixRegister_sum {ι : Type*} [Fintype ι] (M : ι → Matrix J I ℂ) :
    matrixRegister (∑ k, M k) = ∑ k, matrixRegister (M k) := by
  ext x a
  simp only [matrixRegister_apply, Matrix.sum_apply, Finset.sum_mul,
    ContinuousLinearMap.sum_apply, lp.coeFn_sum, Finset.sum_apply]
  exact Finset.sum_comm

theorem matrixRegister_adjoint_single (M : Matrix J I ℂ) (a : J) (b : I) :
    (matrixRegister M).adjoint (lp.single 2 a 1) b = star (M a b) := by
  rw [← register_inner_single, ContinuousLinearMap.adjoint_inner_right]
  simp only [lp.inner_single_right, RCLike.inner_apply, matrixRegister_single,
    one_mul, starRingEnd_apply]

theorem matrixRegister_conjTranspose (M : Matrix J I ℂ) :
    matrixRegister M.conjTranspose = (matrixRegister M).adjoint := by
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro x y
  simp only [lp.inner_eq_tsum, tsum_fintype, RCLike.inner_apply, matrixRegister_apply,
    Matrix.conjTranspose_apply, starRingEnd_apply, star_sum, StarMul.star_mul,
    star_star, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem registerLiftCLM_operator (M : Matrix I I ℂ) :
    (registerLiftCLM M).1 = matrixRegister M := by
  apply register_operator_ext
  intro a b
  rw [registerLiftCLM_coefficient, matrixRegister_single]

theorem conjugation_matrixRegister (M : Matrix J I ℂ) (X : Matrix I I ℂ) :
    conjugationLinearMap (matrixRegister M) (registerLiftCLM X) =
      registerLiftCLM (M * X * M.conjTranspose) := by
  apply Subtype.ext
  rw [conjugationLinearMap_coe, registerLiftCLM_operator, registerLiftCLM_operator,
    matrixRegister_mul, matrixRegister_mul, matrixRegister_conjTranspose]
  rfl

/-- Matrix Kraus normalization implies the actual Hilbert-space normalization. -/
theorem matrixRegister_kraus_complete {ι : Type*} [Fintype ι]
    (M : ι → Matrix J I ℂ) (hM : ∑ k, (M k).conjTranspose * M k = 1) :
    RectangularKrausComplete (fun k => matrixRegister (M k)) := by
  have hop : (∑ k, (matrixRegister (M k)).adjoint.comp (matrixRegister (M k))) =
      ContinuousLinearMap.id ℂ (Register I) := by
    simp_rw [← matrixRegister_conjTranspose, ← matrixRegister_mul]
    rw [← matrixRegister_sum, hM, matrixRegister_one]
  intro x
  have hi : ∑ k, ⟪matrixRegister (M k) x, matrixRegister (M k) x⟫_ℂ = ⟪x, x⟫_ℂ := by
    simp_rw [← ContinuousLinearMap.adjoint_inner_right]
    rw [← inner_sum]
    change ⟪x, ∑ k, ((matrixRegister (M k)).adjoint.comp (matrixRegister (M k))) x⟫_ℂ = _
    rw [← ContinuousLinearMap.sum_apply, hop]
    rfl
  have hnJ (y : Register J) : (⟪y, y⟫_ℂ).re = ‖y‖ ^ 2 :=
    (norm_sq_eq_re_inner (𝕜 := ℂ) y).symm
  have hnI : (⟪x, x⟫_ℂ).re = ‖x‖ ^ 2 :=
    (norm_sq_eq_re_inner (𝕜 := ℂ) x).symm
  have hn : ∑ k, ‖matrixRegister (M k) x‖ ^ 2 = ‖x‖ ^ 2 := by
    simpa only [Complex.re_sum, hnJ, hnI] using congrArg Complex.re hi
  exact hn ▸ hasSum_fintype (fun k => ‖matrixRegister (M k) x‖ ^ 2)

/-- A genuine CPTP channel, constructed from finite matrix Kraus normalization. -/
def channel {ι : Type*} [Fintype ι] (M : ι → Matrix J I ℂ)
    (hM : ∑ k, (M k).conjTranspose * M k = 1) : QuantumChannel (Register I) (Register J) :=
  QuantumChannel.ofRectangularKraus (fun k => matrixRegister (M k))
    (matrixRegister_kraus_complete M hM)

/-- Exact agreement on every complex input matrix, including nonpositive inputs. -/
theorem channel_registerLiftCLM {ι : Type*} [Fintype ι]
    (M : ι → Matrix J I ℂ) (hM : ∑ k, (M k).conjTranspose * M k = 1)
    (X : Matrix I I ℂ) :
    (channel M hM).toLinearMap (registerLiftCLM X) =
      registerLiftCLM (Channels.krausMap M X) := by
  change (∑' k, conjugationLinearMap (matrixRegister (M k)) (registerLiftCLM X)) = _
  rw [tsum_fintype]
  simp_rw [conjugation_matrixRegister]
  rw [← map_sum]
  rfl


end Cloning.FiniteKrausLift
