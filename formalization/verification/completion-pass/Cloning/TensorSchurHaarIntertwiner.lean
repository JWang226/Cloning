import Cloning.PhysicalFlatConverseHaar

/-! Distinct physical highest weights have no nonzero unitary intertwiner.
The statement is proved for the actual cyclic tensor sectors, including
sectors in different tensor powers. -/
noncomputable section
open scoped BigOperators InnerProductSpace Matrix Topology Matrix.Norms.L2Operator
namespace Cloning.TensorLie
open Cloning.PCT Cloning.PhysicalFlatConverse Cloning.TensorLocalUnitary
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
variable {n m d : ℕ}
local instance haarIntertwinerRatMatrixNormedAlgebra : NormedAlgebra ℚ (Matrix (Fin d) (Fin d) ℂ) := NormedAlgebra.restrictScalars ℚ ℂ _
local instance haarIntertwinerRegisterFiniteDimensional (n d : ℕ) : FiniteDimensional ℂ (TensorRegister n (Fin d)) :=
  (registerBasis (Fin n → Fin d)).toOrthonormalBasis.toBasis.finiteDimensional_of_finite

theorem cyclicSector_intertwiner_eq_zero
    (Ω : TensorRegister n (Fin d)) (Ψ : TensorRegister m (Fin d))
    (mu nu : Fin d → ℂ) (hne : mu ≠ nu)
    (hΩ : ‖Ω‖=1) (hΨ : ‖Ψ‖=1)
    (hΩweight : ∀ a, collectiveGenerator n a a Ω = mu a • Ω)
    (hΨweight : ∀ a, collectiveGenerator m a a Ψ = nu a • Ψ)
    (hΩraise : ∀ a b, a<b → collectiveGenerator n a b Ω=0)
    (hΨraise : ∀ a b, a<b → collectiveGenerator m a b Ψ=0)
    (T : TensorRegister m (Fin d) →ₗ[ℂ] TensorRegister n (Fin d))
    (hT : ∀ x ∈ cyclicSector Ψ, T x ∈ cyclicSector Ω)
    (hcomm : ∀ a b x, x ∈ cyclicSector Ψ →
      T (collectiveGenerator m a b x) = collectiveGenerator n a b (T x)) :
    ∀ x ∈ cyclicSector Ψ, T x = 0 := by
  let c := ⟪Ω,T Ψ⟫_ℂ
  have htop : T Ψ = c • Ω := by
    apply cyclicSector_raising_kernel Ω hΩ hΩraise (hT Ψ (highest_mem_cyclicSector Ψ))
    intro a b hab
    rw [← hcomm a b Ψ (highest_mem_cyclicSector Ψ),hΨraise a b hab,map_zero]
  have hΩne : Ω ≠ 0 := by intro h; simpa [h] using hΩ
  have hc : c=0 := by
    by_contra hc
    apply hne
    funext a
    have hh := hcomm a a Ψ (highest_mem_cyclicSector Ψ)
    rw [hΨweight,map_smul,htop,map_smul,hΩweight,smul_smul,smul_smul] at hh
    have hs : nu a*c = c*mu a := (smul_left_injective ℂ hΩne) hh
    exact (mul_right_cancel₀ hc (by simpa only [mul_comm c] using hs)).symm
  have hz : T Ψ=0 := by rw [htop,hc,zero_smul]
  have hw : ∀ w, T (loweringWord Ψ w)=0 := by
    intro w
    induction w with
    | nil => exact hz
    | cons a w ih =>
      rw [loweringWord,hcomm a.val.2 a.val.1 _ (loweringWord_mem_cyclicSector Ψ w),ih,map_zero]
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx => obtain ⟨w,rfl⟩ := hx; exact hw w
  | zero => exact map_zero T
  | add x y hx hy ihx ihy => rw [map_add,ihx,ihy,add_zero]
  | smul a x hx ih => rw [map_smul,ih,smul_zero]

section Rectangular
variable (Ω : TensorRegister n (Fin d)) (Ψ : TensorRegister m (Fin d))
    (mu nu : Fin d → ℂ)
    (hΩweight : ∀ a, collectiveGenerator n a a Ω = mu a • Ω)
    (hΨweight : ∀ a, collectiveGenerator m a a Ψ = nu a • Ψ)
    (hΩraise : ∀ a b, a<b → collectiveGenerator n a b Ω=0)
    (hΨraise : ∀ a b, a<b → collectiveGenerator m a b Ψ=0)
local instance haarIntertwinerSourceComplexNormedSpace : NormedSpace ℂ (cyclicSector Ω) := Submodule.normedSpace (cyclicSector Ω)
local instance haarIntertwinerSourceRealNormedSpace : NormedSpace ℝ (cyclicSector Ω) := Submodule.normedSpace (cyclicSector Ω)
local instance haarIntertwinerTargetComplexNormedSpace : NormedSpace ℂ (cyclicSector Ψ) := Submodule.normedSpace (cyclicSector Ψ)
local instance haarIntertwinerTargetRealNormedSpace : NormedSpace ℝ (cyclicSector Ψ) := Submodule.normedSpace (cyclicSector Ψ)

theorem cyclicTensorOperator_unitary_intertwines_generators
    (T : cyclicSector Ψ →L[ℂ] cyclicSector Ω)
    (hT : ∀ U : unitary (Matrix (Fin d) (Fin d) ℂ),
      T.comp (cyclicTensorOperator Ψ nu hΨweight hΨraise U) =
        (cyclicTensorOperator Ω mu hΩweight hΩraise U).comp T) :
    ∀ a b, T.comp (cyclicGenerator Ψ nu hΨweight hΨraise a b) =
      (cyclicGenerator Ω mu hΩweight hΩraise a b).comp T := by
  let C : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] (cyclicSector Ω →L[ℂ] cyclicSector Ω) :=
    (sectorCompression (cyclicSector Ω)).toLinearMap.comp collectiveMatrixLM
  let D : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] (cyclicSector Ψ →L[ℂ] cyclicSector Ψ) :=
    (sectorCompression (cyclicSector Ψ)).toLinearMap.comp collectiveMatrixLM
  let L : (cyclicSector Ψ →L[ℂ] cyclicSector Ψ) →L[ℂ] (cyclicSector Ψ →L[ℂ] cyclicSector Ω) :=
    LinearMap.toContinuousLinearMap {
      toFun F := T.comp F
      map_add' F G := by ext x; simp
      map_smul' c F := by ext x; simp }
  let R : (cyclicSector Ω →L[ℂ] cyclicSector Ω) →L[ℂ] (cyclicSector Ψ →L[ℂ] cyclicSector Ω) :=
    LinearMap.toContinuousLinearMap {
      toFun F := F.comp T
      map_add' F G := by ext x; simp
      map_smul' c F := by ext x; simp }
  have hskew (Y : Matrix (Fin d) (Fin d) ℂ) (hY : star Y = -Y) : T.comp (D Y) = (C Y).comp T := by
    have he (t : ℝ) : matrixExpPath Y (t : ℂ) ∈ unitary (Matrix (Fin d) (Fin d) ℂ) := by
      apply NormedSpace.exp_mem_unitary_of_mem_skewAdjoint
      change star ((t:ℂ) • Y) = -((t:ℂ) • Y)
      simp only [star_smul,Complex.star_def,Complex.conj_ofReal,hY,smul_neg]
    have hfun : (fun t : ℝ => T.comp (cyclicTensorOperator Ψ nu hΨweight hΨraise (matrixExpPath Y (t:ℂ)))) =
        (fun t : ℝ => (cyclicTensorOperator Ω mu hΩweight hΩraise (matrixExpPath Y (t:ℂ))).comp T) :=
      funext (fun t => hT ⟨_,he t⟩)
    have hl := (L.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0:ℝ)
      (cyclicTensorOperator_exp_hasDerivAt_zero Ψ nu hΨweight hΨraise Y)
    have hr := (R.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0:ℝ)
      (cyclicTensorOperator_exp_hasDerivAt_zero Ω mu hΩweight hΩraise Y)
    change HasDerivAt (fun t : ℝ => T.comp (cyclicTensorOperator Ψ nu hΨweight hΨraise (matrixExpPath Y (t:ℂ))))
      (T.comp (D Y)) 0 at hl
    change HasDerivAt (fun t : ℝ => (cyclicTensorOperator Ω mu hΩweight hΩraise (matrixExpPath Y (t:ℂ))).comp T)
      ((C Y).comp T) 0 at hr
    rw [hfun] at hl
    exact hl.unique hr
  have hall (X : Matrix (Fin d) (Fin d) ℂ) : T.comp (D X) = (C X).comp T := by
    let Y := X-star X
    let Z := Complex.I • (X+star X)
    have hY : star Y = -Y := by simp [Y]
    have hZ : star Z = -Z := by
      simp only [Z,star_smul,star_add,star_star,Complex.star_def,Complex.conj_I,
        neg_smul,smul_add]
      abel
    have h1 := hskew Y hY
    have h2 := hskew Z hZ
    have he : (2:ℂ) • X = Y-Complex.I • Z := by
      simp only [Y,Z,smul_smul,Complex.I_mul_I,neg_one_smul]
      module
    have heC : (2:ℂ) • C X = C Y-Complex.I • C Z := by
      rw [← map_smul,← map_smul,← map_sub]
      exact congrArg C he
    have heD : (2:ℂ) • D X = D Y-Complex.I • D Z := by
      rw [← map_smul,← map_smul,← map_sub]
      exact congrArg D he
    have hc : T.comp ((2:ℂ) • D X) = ((2:ℂ) • C X).comp T := by
      rw [heD,heC]
      apply ContinuousLinearMap.ext
      intro x
      simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.sub_apply,
        ContinuousLinearMap.smul_apply,map_sub,map_smul]
      have h1x := DFunLike.congr_fun h1 x
      have h2x := DFunLike.congr_fun h2 x
      simp only [ContinuousLinearMap.comp_apply] at h1x h2x
      rw [h1x,h2x]
    apply ContinuousLinearMap.ext
    intro x
    have hx := DFunLike.congr_fun hc x
    simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.smul_apply,map_smul] at hx
    exact (smul_right_injective _ (by norm_num : (2:ℂ) ≠ 0)) hx
  intro a b
  have hh := hall (Matrix.single a b (1:ℂ))
  simpa only [C,D,LinearMap.comp_apply,ContinuousLinearMap.coe_coe,collectiveMatrixLM_apply,
    collectiveMatrix_single,one_smul,
    sectorCompression_collectiveGenerator Ω mu hΩweight hΩraise,
    sectorCompression_collectiveGenerator Ψ nu hΨweight hΨraise] using hh

theorem cyclicTensorOperator_unitary_intertwiner_eq_zero
    (hne : mu ≠ nu) (hΩ : ‖Ω‖=1) (hΨ : ‖Ψ‖=1)
    (T : cyclicSector Ψ →L[ℂ] cyclicSector Ω)
    (hT : ∀ U : unitary (Matrix (Fin d) (Fin d) ℂ),
      T.comp (cyclicTensorOperator Ψ nu hΨweight hΨraise U) =
        (cyclicTensorOperator Ω mu hΩweight hΩraise U).comp T) : T=0 := by
  let S := cyclicSector Ψ
  let F := (cyclicSector Ω).subtype.comp (T.toLinearMap.comp S.orthogonalProjection.toLinearMap)
  have hproj (x : S) : S.orthogonalProjection x=x := by
    apply Subtype.ext
    exact Submodule.starProjection_eq_self_iff.mpr x.property
  have hF (x : S) : F x = (T x : TensorRegister n (Fin d)) := by
    change (T (S.orthogonalProjection x) : TensorRegister n (Fin d)) = _
    rw [hproj]
  have hh := cyclicSector_intertwiner_eq_zero Ω Ψ mu nu hne hΩ hΨ hΩweight hΨweight hΩraise hΨraise F
    (fun x _ => (T (S.orthogonalProjection x)).property) (by
      intro a b x hx
      let xx : S := ⟨x,hx⟩
      have he : F (collectiveGenerator m a b x) =
          (T (cyclicGenerator Ψ nu hΨweight hΨraise a b xx) : TensorRegister n (Fin d)) :=
        hF (cyclicGenerator Ψ nu hΨweight hΨraise a b xx)
      rw [he]
      have ht := DFunLike.congr_fun
        (cyclicTensorOperator_unitary_intertwines_generators Ω Ψ mu nu hΩweight hΨweight hΩraise hΨraise T hT a b) xx
      change T (cyclicGenerator Ψ nu hΨweight hΨraise a b xx) =
        cyclicGenerator Ω mu hΩweight hΩraise a b (T xx) at ht
      rw [ht,cyclicGenerator_coe_apply,hF xx])
  apply ContinuousLinearMap.ext
  intro x
  apply Subtype.ext
  exact (hF x).symm.trans (hh x x.property)

end Rectangular
end Cloning.TensorLie
