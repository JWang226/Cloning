import Cloning.InfiniteFiniteCorner
import Mathlib.Analysis.SpecificLimits.Normed

/-! Quantitative polar normalization at the identity. The square-root estimate
is Lipschitz at the identity, rather than the general Hölder estimate. -/
noncomputable section
open scoped ComplexOrder InnerProductSpace Topology
namespace Cloning.PBWSymmetricFrame
open ContinuousLinearMap
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000

lemma abs_sqrt_sub_one_le (x : ℝ) : |Real.sqrt x-1|≤|x-1| := by
  by_cases hx : 0≤x
  · have hs := Real.sq_sqrt hx
    have hp := Real.sqrt_nonneg x
    by_cases h : 1≤x
    · have hroot : 1≤Real.sqrt x := by nlinarith
      rw [abs_of_nonneg (by linarith : 0≤Real.sqrt x-1),
        abs_of_nonneg (by linarith : 0≤x-1)]
      nlinarith
    · have hroot : Real.sqrt x≤1 := by nlinarith
      rw [abs_of_nonpos (by linarith : Real.sqrt x-1≤0),
        abs_of_nonpos (by linarith : x-1≤0)]
      nlinarith
  · rw [Real.sqrt_eq_zero_of_nonpos (le_of_not_ge hx)]
    rw [abs_of_nonpos (by linarith : x-1≤0)]
    norm_num
    linarith

variable {E H : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem norm_sqrt_sub_one_le (G : E →L[ℂ] E) (hG : 0≤G) :
    ‖CFC.sqrt G-1‖≤‖G-1‖ := by
  have hs : CFC.sqrt G=cfc Real.sqrt G := by
    rw [CFC.sqrt_eq_real_sqrt G hG, cfcₙ_eq_cfc]
  have hself : IsSelfAdjoint G := IsSelfAdjoint.of_nonneg hG
  have hsub : cfc (fun x : ℝ=>Real.sqrt x-1) G=CFC.sqrt G-1 := by
    rw [cfc_sub Real.sqrt (fun _ : ℝ=>1) G, ←hs, cfc_const_one ℝ G]
  have hid : cfc (fun x : ℝ=>x-1) G=G-1 := by
    rw [cfc_sub (fun x : ℝ=>x) (fun _ : ℝ=>1) G, cfc_id' ℝ G, cfc_const_one ℝ G]
  rw [←hsub]
  apply norm_cfc_le (norm_nonneg _)
  intro x hx
  have h := norm_apply_le_norm_cfc (fun x : ℝ=>x-1) G hx
  rw [hid] at h
  exact (abs_sqrt_sub_one_le x).trans h

def gram (V : E →L[ℂ] H) : E →L[ℂ] E := V.adjoint.comp V

theorem gram_nonneg (V : E →L[ℂ] H) : 0≤gram V := by
  exact (gram V).nonneg_iff_isPositive.mpr (ContinuousLinearMap.isPositive_adjoint_comp_self V)

def polar (V : E →L[ℂ] H) : E →L[ℂ] H :=
  V.comp (Ring.inverse (CFC.sqrt (gram V)))

theorem sqrt_isUnit (V : E →L[ℂ] H) (hV : IsUnit (gram V)) :
    IsUnit (CFC.sqrt (gram V)) := (CFC.isUnit_sqrt_iff _ (gram_nonneg V)).mpr hV

theorem polar_mul_sqrt (V : E →L[ℂ] H) (hV : IsUnit (gram V)) :
    (polar V).comp (CFC.sqrt (gram V))=V := by
  rw [polar, ContinuousLinearMap.comp_assoc]
  change V.comp (Ring.inverse (CFC.sqrt (gram V))*CFC.sqrt (gram V))=V
  rw [Ring.inverse_mul_cancel _ (sqrt_isUnit V hV)]
  exact V.comp_id

theorem polar_adjoint_comp_self (V : E →L[ℂ] H) (hV : IsUnit (gram V)) :
    (polar V).adjoint.comp (polar V)=1 := by
  let S := CFC.sqrt (gram V)
  have hS : star S=S := (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg (gram V))).star_eq
  have hI : star (Ring.inverse S)=Ring.inverse S := by rw [←Ring.inverse_star,hS]
  have hSS : S*S=gram V := CFC.sqrt_mul_sqrt_self _ (gram_nonneg V)
  have hunit : IsUnit S := sqrt_isUnit V hV
  change ((V.comp (Ring.inverse S)).adjoint).comp (V.comp (Ring.inverse S))=1
  rw [ContinuousLinearMap.adjoint_comp]
  change (star (Ring.inverse S)).comp (V.adjoint.comp (V.comp (Ring.inverse S)))=1
  rw [hI, ←ContinuousLinearMap.comp_assoc V.adjoint V]
  change Ring.inverse S*(gram V*Ring.inverse S)=1
  rw [←hSS]
  calc
    Ring.inverse S*(S*S*Ring.inverse S)=(Ring.inverse S*S)*(S*Ring.inverse S) := by simp only [mul_assoc]
    _ = 1 := by rw [Ring.inverse_mul_cancel _ hunit, Ring.mul_inverse_cancel _ hunit, one_mul]

theorem polar_norm (V : E →L[ℂ] H) (hV : IsUnit (gram V)) (x : E) :
    ‖polar V x‖=‖x‖ := by
  rw [ContinuousLinearMap.apply_norm_eq_sqrt_inner_adjoint_left,
    polar_adjoint_comp_self V hV]
  exact (norm_eq_sqrt_re_inner (𝕜 := ℂ) x).symm

/-- Symmetric normalization changes each vector by at most the Gram operator
error times the norm of its coefficient vector. -/
theorem polar_sub_apply_le (V : E →L[ℂ] H) (hV : IsUnit (gram V)) (x : E) :
    ‖polar V x-V x‖≤‖gram V-1‖*‖x‖ := by
  have he : polar V x-V x=polar V ((1-CFC.sqrt (gram V)) x) := by
    rw [ContinuousLinearMap.sub_apply, one_apply, map_sub]
    congr 1
    exact (congrArg (fun T : E →L[ℂ] H=>T x) (polar_mul_sqrt V hV)).symm
  rw [he,polar_norm V hV]
  apply ((1-CFC.sqrt (gram V)).le_opNorm x).trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg x)
  rw [norm_sub_rev]
  exact norm_sqrt_sub_one_le _ (gram_nonneg V)

end Cloning.PBWSymmetricFrame
