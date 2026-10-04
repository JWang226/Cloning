import Cloning.TensorRootBounds

/-! Normalized physical root operators and their actual local CCR defects. -/
noncomputable section
open scoped BigOperators InnerProductSpace
namespace Cloning.TensorLie
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {n d : ℕ}

def normalizedAnnihilator (n : ℕ) (mu : Fin d → ℕ) (a b : Fin d) :
    TensorRegister n (Fin d) →L[ℂ] TensorRegister n (Fin d) :=
  (Real.sqrt ((mu a : ℝ) - mu b))⁻¹ • collectiveGenerator n a b

def normalizedCreator (n : ℕ) (mu : Fin d → ℕ) (a b : Fin d) :
    TensorRegister n (Fin d) →L[ℂ] TensorRegister n (Fin d) :=
  (Real.sqrt ((mu a : ℝ) - mu b))⁻¹ • collectiveGenerator n b a

theorem normalized_root_commutator (mu : Fin d → ℕ) (a b c e : Fin d) :
    normalizedAnnihilator n mu a b * normalizedCreator n mu c e -
      normalizedCreator n mu c e * normalizedAnnihilator n mu a b =
    ((Real.sqrt ((mu a : ℝ) - mu b))⁻¹ *
      (Real.sqrt ((mu c : ℝ) - mu e))⁻¹) •
      ((if b = e then collectiveGenerator n a c else 0) -
        (if c = a then collectiveGenerator n e b else 0)) := by
  simp only [normalizedAnnihilator, normalizedCreator, smul_mul_smul_comm,
    mul_comm (Real.sqrt ((mu c : ℝ) - mu e))⁻¹, ← smul_sub]
  rw [collectiveGenerator_commutator]

theorem inv_sqrt_mul_inv_sqrt {g : ℝ} (hg : 0 < g) :
    (Real.sqrt g)⁻¹ * (Real.sqrt g)⁻¹ = g⁻¹ := by
  rw [← mul_inv, Real.mul_self_sqrt hg.le]

theorem normalized_diagonal_commutator (mu : Fin d → ℕ) (a b : Fin d)
    (hgap : 0 < (mu a : ℝ) - mu b) :
    normalizedAnnihilator n mu a b * normalizedCreator n mu a b -
      normalizedCreator n mu a b * normalizedAnnihilator n mu a b =
    ((mu a : ℝ) - mu b)⁻¹ •
      (collectiveGenerator n a a - collectiveGenerator n b b) := by
  rw [normalized_root_commutator, inv_sqrt_mul_inv_sqrt hgap]
  simp

theorem normalizedCreator_adjoint (mu : Fin d → ℕ) (a b : Fin d) :
    (normalizedCreator n mu a b).adjoint = normalizedAnnihilator n mu a b := by
  rw [normalizedCreator, ← ContinuousLinearMap.star_eq_adjoint, star_smul, star_trivial,
    ContinuousLinearMap.star_eq_adjoint, collectiveGenerator_adjoint]
  rfl

theorem normalized_inner_adjoint (mu : Fin d → ℕ) (a b : Fin d)
    (x y : TensorRegister n (Fin d)) :
    ⟪normalizedCreator n mu a b x, y⟫_ℂ =
      ⟪x, normalizedAnnihilator n mu a b y⟫_ℂ := by
  rw [← normalizedCreator_adjoint mu a b, ContinuousLinearMap.adjoint_inner_right]

/-- The normalized same-root CCR defect is at most `2R/gap` on the actual
cyclic cutoff; no CCR property is an input assumption. -/
theorem normalized_diagonal_defect_norm_le
    (Ω : TensorRegister n (Fin d)) (mu : Fin d → ℕ)
    (hweight : ∀ a, collectiveGenerator n a a Ω = (mu a : ℂ) • Ω)
    (r : ℕ) {x : TensorRegister n (Fin d)} (hx : x ∈ cyclicCutoff Ω r)
    (a b : Fin d) (hgap : 0 < (mu a : ℝ) - mu b) :
    ‖normalizedAnnihilator n mu a b (normalizedCreator n mu a b x) -
      normalizedCreator n mu a b (normalizedAnnihilator n mu a b x) - x‖ ≤
    (2 * r / ((mu a : ℝ) - mu b)) * ‖x‖ := by
  have he := congrArg (fun T : TensorRegister n (Fin d) →L[ℂ] TensorRegister n (Fin d) => T x)
    (normalized_diagonal_commutator (n := n) mu a b hgap)
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.mul_apply,
    ContinuousLinearMap.smul_apply] at he
  rw [he]
  have hscalar : (((mu a : ℂ) - mu b) • x) = ((mu a : ℝ) - mu b) • x := by
    simp only [← Complex.ofReal_natCast, ← Complex.ofReal_sub, RCLike.real_smul_eq_coe_smul (K := ℂ)]
    rfl
  have hid : ((mu a : ℝ) - mu b)⁻¹ •
      (((mu a : ℂ) - mu b) • x) = x := by
    rw [hscalar, smul_smul, inv_mul_cancel₀ (ne_of_gt hgap), one_smul]
  have hdef : ((mu a : ℝ) - mu b)⁻¹ •
      (collectiveGenerator n a a x - collectiveGenerator n b b x) - x =
      ((mu a : ℝ) - mu b)⁻¹ •
      (collectiveGenerator n a a x - collectiveGenerator n b b x -
        ((mu a : ℂ) - mu b) • x) := by
    symm
    rw [smul_sub, hid]
  rw [hdef, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hgap)]
  calc
    _ ≤ ((mu a : ℝ) - mu b)⁻¹ * ((2 * r : ℝ) * ‖x‖) :=
      mul_le_mul_of_nonneg_left (cartan_difference_defect_norm_le Ω mu hweight r hx a b)
        (inv_nonneg.mpr hgap.le)
    _ = _ := by ring

end Cloning.TensorLie
