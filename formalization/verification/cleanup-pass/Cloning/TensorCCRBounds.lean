import Cloning.TensorCCR
import Cloning.TensorCCRScalar
import Cloning.TensorCyclicError

/-! Uniform cross-root CCR bounds on literal cyclic tensor cutoffs. -/
noncomputable section
open scoped BigOperators InnerProductSpace
namespace Cloning.TensorLie
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {n d : ℕ}

private theorem scaled_root_norm_le
    (Ω : TensorRegister n (Fin d)) (mu : Fin d → ℕ)
    (hweight : ∀ a, collectiveGenerator n a a Ω = (mu a : ℂ) • Ω)
    (hraise : ∀ a b, a < b → collectiveGenerator n a b Ω = 0)
    (r : ℕ) {x : TensorRegister n (Fin d)} (hx : x ∈ cyclicCutoff Ω r)
    (u v : Fin d) (huv : u ≠ v) {g h δ : ℝ} (hδ : 0 < δ)
    (hg : δ ≤ g) (hh : δ ≤ h)
    (hres : |(mu u : ℝ) - mu v| = |g - h|) :
    ‖((Real.sqrt g)⁻¹ * (Real.sqrt h)⁻¹) • collectiveGenerator n u v x‖ ≤
      Real.sqrt (((r : ℝ) + 1) / δ + 2 * r * ((r : ℝ) + 1) / δ ^ 2) * ‖x‖ := by
  have hs : 0 ≤ (Real.sqrt g)⁻¹ * (Real.sqrt h)⁻¹ := by positivity
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs]
  calc
    _ ≤ ((Real.sqrt g)⁻¹ * (Real.sqrt h)⁻¹) *
        (Real.sqrt (((r : ℝ) + 1) * (|g - h| + 2 * r)) * ‖x‖) := by
      apply mul_le_mul_of_nonneg_left _ hs
      simpa only [hres] using root_norm_le_cyclicCutoff Ω mu hweight hraise u v huv r hx
    _ ≤ _ := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right (normalized_root_scalar_bound hδ hg hh r) (norm_nonneg x)

/-- Distinct normalized roots have a uniform vanishing off-diagonal CCR error
when all retained highest-weight gaps exceed `δ`. -/
theorem normalized_offdiagonal_commutator_norm_le
    (Ω : TensorRegister n (Fin d)) (mu : Fin d → ℕ)
    (hweight : ∀ a, collectiveGenerator n a a Ω = (mu a : ℂ) • Ω)
    (hraise : ∀ a b, a < b → collectiveGenerator n a b Ω = 0)
    (r : ℕ) {x : TensorRegister n (Fin d)} (hx : x ∈ cyclicCutoff Ω r)
    (a b c e : Fin d) (hne : (a, b) ≠ (c, e)) {δ : ℝ} (hδ : 0 < δ)
    (hab : δ ≤ (mu a : ℝ) - mu b) (hce : δ ≤ (mu c : ℝ) - mu e) :
    ‖normalizedAnnihilator n mu a b (normalizedCreator n mu c e x) -
      normalizedCreator n mu c e (normalizedAnnihilator n mu a b x)‖ ≤
      Real.sqrt (((r : ℝ) + 1) / δ + 2 * r * ((r : ℝ) + 1) / δ ^ 2) * ‖x‖ := by
  have he := congrArg (fun T : TensorRegister n (Fin d) →L[ℂ] TensorRegister n (Fin d) => T x)
    (normalized_root_commutator (n := n) mu a b c e)
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.mul_apply,
    ContinuousLinearMap.smul_apply] at he
  rw [he]
  by_cases hbe : b = e
  · have hca : c ≠ a := by
      intro hca
      exact hne (Prod.ext hca.symm hbe)
    simp only [hbe, if_true, hca, if_false, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.zero_apply, sub_zero]
    apply scaled_root_norm_le Ω mu hweight hraise r hx a c hca.symm hδ
      (by simpa only [hbe] using hab) hce
    congr 1
    ring
  · by_cases hca : c = a
    · simp only [hbe, if_false, hca, if_true, ContinuousLinearMap.sub_apply,
        ContinuousLinearMap.zero_apply, zero_sub, smul_neg, norm_neg]
      apply scaled_root_norm_le Ω mu hweight hraise r hx e b (Ne.symm hbe) hδ hab
        (by simpa only [hca] using hce)
      congr 1
      ring
    · simp only [hbe, hca, if_false, sub_self, ContinuousLinearMap.zero_apply,
        smul_zero, norm_zero]
      positivity

theorem normalized_CCR_norm_le
    (Ω : TensorRegister n (Fin d)) (mu : Fin d → ℕ)
    (hweight : ∀ a, collectiveGenerator n a a Ω = (mu a : ℂ) • Ω)
    (hraise : ∀ a b, a < b → collectiveGenerator n a b Ω = 0)
    (r : ℕ) {x : TensorRegister n (Fin d)} (hx : x ∈ cyclicCutoff Ω r)
    (a b c e : Fin d) {δ : ℝ} (hδ : 0 < δ)
    (hab : δ ≤ (mu a : ℝ) - mu b) (hce : δ ≤ (mu c : ℝ) - mu e) :
    ‖normalizedAnnihilator n mu a b (normalizedCreator n mu c e x) -
      normalizedCreator n mu c e (normalizedAnnihilator n mu a b x) -
      (if (a, b) = (c, e) then (1 : ℂ) else 0) • x‖ ≤ rootError r δ * ‖x‖ := by
  by_cases he : (a, b) = (c, e)
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
    simp only [if_true, one_smul]
    apply (normalized_diagonal_defect_norm_le Ω mu hweight r hx a b (hδ.trans_le hab)).trans
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg x)
    exact (div_le_div_of_nonneg_left (by positivity) hδ hab).trans (le_max_left _ _)
  · simp only [he, if_false, zero_smul, sub_zero]
    exact (normalized_offdiagonal_commutator_norm_le Ω mu hweight hraise r hx a b c e he hδ hab hce).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg x))

end Cloning.TensorLie
