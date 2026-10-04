import Cloning.TensorLocalUnitaryCoordinates
import Cloning.TensorCyclicSectorOperators
import Cloning.TensorCyclicSectorCovariance
import Mathlib.Analysis.Complex.RealDeriv

/-! The scalar unitary commutant of each actual physical cyclic sector.
Unitary invariance is differentiated through the literal tensor exponential;
no abstract representation identification or irreducibility premise is used. -/
noncomputable section
open scoped BigOperators InnerProductSpace Matrix Topology Matrix.Norms.L2Operator
open NormedSpace
namespace Cloning.PhysicalFlatConverse
open Cloning.TensorLie Cloning.TensorLocalUnitary
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
set_option synthInstance.maxHeartbeats 100000
variable {n d : ℕ}
local instance : NormedAlgebra ℚ (Matrix (Fin d) (Fin d) ℂ) := NormedAlgebra.restrictScalars ℚ ℂ _

local instance : FiniteDimensional ℂ (TensorRegister n (Fin d)) :=
  (Cloning.PCT.registerBasis (Fin n → Fin d)).toOrthonormalBasis.toBasis.finiteDimensional_of_finite

/-- Orthogonal compression, as a continuous linear map on actual operators. -/
def sectorCompression (S : Submodule ℂ (TensorRegister n (Fin d))) :
    (TensorRegister n (Fin d) →L[ℂ] TensorRegister n (Fin d)) →L[ℂ] (S →L[ℂ] S) :=
  LinearMap.toContinuousLinearMap {
    toFun F := S.orthogonalProjection.comp (F.comp S.subtypeL)
    map_add' F G := by apply ContinuousLinearMap.ext; intro x; simp
    map_smul' c F := by apply ContinuousLinearMap.ext; intro x; simp }

variable (Ω : TensorRegister n (Fin d)) (mu : Fin d → ℂ)
    (hweight : ∀ a, collectiveGenerator n a a Ω = mu a • Ω)
    (hraise : ∀ a b, a < b → collectiveGenerator n a b Ω = 0)

local instance : NormedSpace ℂ (cyclicSector Ω) := Submodule.normedSpace (cyclicSector Ω)
local instance : NormedSpace ℝ (cyclicSector Ω) := Submodule.normedSpace (cyclicSector Ω)

theorem sectorCompression_tensorOperator (X : Matrix (Fin d) (Fin d) ℂ) :
    sectorCompression (cyclicSector Ω) (tensorOperator n X) =
      cyclicTensorOperator Ω mu hweight hraise X := by
  apply ContinuousLinearMap.ext
  intro x
  apply Subtype.ext
  exact Submodule.starProjection_eq_self_iff.mpr
    (cyclicSector_tensorOperator_invariant Ω mu hweight hraise X x.property)

theorem sectorCompression_collectiveGenerator (a b : Fin d) :
    sectorCompression (cyclicSector Ω) (collectiveGenerator n a b) =
      cyclicGenerator Ω mu hweight hraise a b := by
  apply ContinuousLinearMap.ext
  intro x
  apply Subtype.ext
  exact Submodule.starProjection_eq_self_iff.mpr
    (cyclicSector_generator_invariant Ω mu hweight hraise a b x.property)

/-- The genuine derivative of the restricted tensor exponential. -/
theorem cyclicTensorOperator_exp_hasDerivAt_zero (Y : Matrix (Fin d) (Fin d) ℂ) :
    HasDerivAt (fun t : ℝ => cyclicTensorOperator Ω mu hweight hraise (matrixExpPath Y (t : ℂ)))
      (sectorCompression (cyclicSector Ω) (collectiveMatrix (n := n) Y)) 0 := by
  have hh := (sectorCompression (cyclicSector Ω)).hasFDerivAt.comp_hasDerivAt (0 : ℂ)
    (tensorOperator_matrixExpPath_hasDerivAt_zero (n := n) Y)
  rw [← Complex.ofReal_zero] at hh
  have hh' := hh.scomp (0 : ℝ) Complex.ofRealCLM.hasDerivAt
  simpa only [Function.comp_def, Complex.ofRealCLM_apply, Complex.ofReal_one, one_smul,
    sectorCompression_tensorOperator Ω mu hweight hraise] using hh'

/-- Commutation with every physical unitary already forces commutation with
all actual complex collective matrix units. -/
theorem cyclicTensorOperator_unitary_commutes_generators
    (T : cyclicSector Ω →L[ℂ] cyclicSector Ω)
    (hT : ∀ U : unitary (Matrix (Fin d) (Fin d) ℂ),
      T * cyclicTensorOperator Ω mu hweight hraise U =
        cyclicTensorOperator Ω mu hweight hraise U * T) :
    ∀ a b, T * cyclicGenerator Ω mu hweight hraise a b =
      cyclicGenerator Ω mu hweight hraise a b * T := by
  let C : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] (cyclicSector Ω →L[ℂ] cyclicSector Ω) :=
    (sectorCompression (cyclicSector Ω)).toLinearMap.comp collectiveMatrixLM
  have hskew (Y : Matrix (Fin d) (Fin d) ℂ) (hY : star Y = -Y) : T * C Y = C Y * T := by
    have he (t : ℝ) : matrixExpPath Y (t : ℂ) ∈ unitary (Matrix (Fin d) (Fin d) ℂ) := by
      apply exp_mem_unitary_of_mem_skewAdjoint
      change star ((t : ℂ) • Y) = -((t : ℂ) • Y)
      simp only [star_smul, Complex.star_def, Complex.conj_ofReal, hY, smul_neg]
    have hfun : (fun t : ℝ => T * cyclicTensorOperator Ω mu hweight hraise (matrixExpPath Y (t : ℂ))) =
        (fun t : ℝ => cyclicTensorOperator Ω mu hweight hraise (matrixExpPath Y (t : ℂ)) * T) :=
      funext (fun t => hT ⟨_, he t⟩)
    have hd := cyclicTensorOperator_exp_hasDerivAt_zero Ω mu hweight hraise Y
    have hleft := hd.const_mul T
    have hright := hd.mul_const T
    rw [hfun] at hleft
    exact hleft.unique hright
  have hall (X : Matrix (Fin d) (Fin d) ℂ) : T * C X = C X * T := by
    let Y := X - star X
    let Z := Complex.I • (X + star X)
    have hY : star Y = -Y := by simp [Y]
    have hZ : star Z = -Z := by
      simp only [Z, star_smul, star_add, star_star, Complex.star_def, Complex.conj_I,
        neg_smul, smul_add]
      abel
    have h1 := hskew Y hY
    have h2 := hskew Z hZ
    have he : (2 : ℂ) • C X = C Y - Complex.I • C Z := by
      rw [← map_smul, ← map_smul, ← map_sub]
      congr 1
      simp only [Y, Z, smul_smul, Complex.I_mul_I, neg_one_smul]
      module
    have hc : T * ((2 : ℂ) • C X) = ((2 : ℂ) • C X) * T := by
      rw [he]
      apply ContinuousLinearMap.ext
      intro x
      simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.sub_apply,
        ContinuousLinearMap.smul_apply, map_sub, map_smul]
      have h1x := DFunLike.congr_fun h1 x
      have h2x := DFunLike.congr_fun h2 x
      simp only [ContinuousLinearMap.mul_apply] at h1x h2x
      rw [h1x,h2x]
    apply ContinuousLinearMap.ext
    intro x
    have hx := DFunLike.congr_fun hc x
    simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.smul_apply, map_smul] at hx
    exact (smul_right_injective _ (by norm_num : (2 : ℂ) ≠ 0)) hx
  intro a b
  have hh := hall (Matrix.single a b (1 : ℂ))
  simpa only [C, LinearMap.comp_apply, ContinuousLinearMap.coe_coe, collectiveMatrixLM_apply,
    collectiveMatrix_single, one_smul, sectorCompression_collectiveGenerator Ω mu hweight hraise] using hh

/-- Actual tensor-unitary commutants on a normalized physical highest-weight
sector are scalar. -/
theorem cyclicTensorOperator_unitary_commutant_scalar (hΩ : ‖Ω‖ = 1)
    (T : cyclicSector Ω →L[ℂ] cyclicSector Ω)
    (hT : ∀ U : unitary (Matrix (Fin d) (Fin d) ℂ),
      T * cyclicTensorOperator Ω mu hweight hraise U =
        cyclicTensorOperator Ω mu hweight hraise U * T) :
    ∃ c : ℂ, T = c • ContinuousLinearMap.id ℂ (cyclicSector Ω) := by
  obtain ⟨c,hc⟩ := cyclicGenerator_commutant_scalar Ω mu hweight hraise hΩ T.toLinearMap
    (fun a b x => DFunLike.congr_fun
      (cyclicTensorOperator_unitary_commutes_generators Ω mu hweight hraise T hT a b) x)
  refine ⟨c, ?_⟩
  apply ContinuousLinearMap.ext
  intro x
  exact DFunLike.congr_fun hc x

end Cloning.PhysicalFlatConverse
