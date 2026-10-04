import Cloning.TensorCyclicIndependence
import Cloning.TensorPBWWeight

/-! Exact scalar relation between raw physical lowering words and the oscillator
normalization used in the proved Gram limit. -/
noncomputable section
open scoped BigOperators InnerProductSpace
namespace Cloning.TensorLie
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {n d : ℕ}

noncomputable def loweringScale (mu : Fin d → ℕ) : List (PositiveRoot d) → ℂ
  | [] => 1
  | a :: w => (((Real.sqrt ((mu a.val.1 : ℝ) - mu a.val.2))⁻¹ : ℝ) : ℂ) * loweringScale mu w

def normalizedLoweringScale (mu : Fin d → ℕ) (w : List (PositiveRoot d)) : ℂ :=
  ((Real.sqrt (PBW.occupationFactorial w : ℝ))⁻¹ : ℂ) * loweringScale mu w

def normalizedLoweringWord (Ω : TensorRegister n (Fin d)) (mu : Fin d → ℕ)
    (w : List (PositiveRoot d)) : TensorRegister n (Fin d) :=
  PBW.normalizedWord (fun a : PositiveRoot d => normalizedCreator n mu a.val.1 a.val.2) w Ω

theorem creator_word_eq_loweringScale (Ω : TensorRegister n (Fin d)) (mu : Fin d → ℕ)
    (w : List (PositiveRoot d)) :
    PBW.word (fun a : PositiveRoot d => normalizedCreator n mu a.val.1 a.val.2) w Ω =
      loweringScale mu w • loweringWord Ω w := by
  induction w with
  | nil => simp [PBW.word, loweringScale, loweringWord]
  | cons a w ih =>
    rw [PBW.word_cons, ih]
    simp only [normalizedCreator, ContinuousLinearMap.smul_apply, map_smul,
      loweringScale, loweringWord, RCLike.real_smul_eq_coe_smul (K := ℂ),
      smul_smul]
    congr 1
    exact mul_comm _ _

theorem normalizedLoweringWord_eq_scale (Ω : TensorRegister n (Fin d)) (mu : Fin d → ℕ)
    (w : List (PositiveRoot d)) :
    normalizedLoweringWord Ω mu w = normalizedLoweringScale mu w • loweringWord Ω w := by
  simp only [normalizedLoweringWord, PBW.normalizedWord, creator_word_eq_loweringScale,
    normalizedLoweringScale, smul_smul]

theorem loweringScale_ne_zero (mu : Fin d → ℕ)
    (hgap : ∀ a : PositiveRoot d, 0 < (mu a.val.1 : ℝ) - mu a.val.2)
    (w : List (PositiveRoot d)) : loweringScale mu w ≠ 0 := by
  induction w with
  | nil => simp [loweringScale]
  | cons a w ih =>
    exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (inv_ne_zero
      (ne_of_gt (Real.sqrt_pos.mpr (hgap a))))) ih

theorem normalizedLoweringScale_ne_zero (mu : Fin d → ℕ)
    (hgap : ∀ a : PositiveRoot d, 0 < (mu a.val.1 : ℝ) - mu a.val.2)
    (w : List (PositiveRoot d)) : normalizedLoweringScale mu w ≠ 0 := by
  apply mul_ne_zero _ (loweringScale_ne_zero mu hgap w)
  apply inv_ne_zero
  apply Complex.ofReal_ne_zero.mpr
  apply ne_of_gt
  apply Real.sqrt_pos.mpr
  exact_mod_cast PBW.occupationFactorial_pos w

theorem normalizedLoweringWord_mem_cyclicCutoff
    (Ω : TensorRegister n (Fin d)) (mu : Fin d → ℕ)
    (w : List (PositiveRoot d)) {R : ℤ} (hR : (loweringHeight w : ℤ) ≤ R) :
    normalizedLoweringWord Ω mu w ∈ cyclicCutoff Ω R := by
  rw [normalizedLoweringWord_eq_scale]
  exact (cyclicCutoff Ω R).smul_mem _ (loweringWord_mem_cyclicCutoff Ω w hR)

theorem cartan_normalizedLoweringWord
    (Ω : TensorRegister n (Fin d)) (mu : Fin d → ℕ)
    (hweight : ∀ a, collectiveGenerator n a a Ω = (mu a : ℂ) • Ω)
    (w : List (PositiveRoot d)) (a : Fin d) :
    collectiveGenerator n a a (normalizedLoweringWord Ω mu w) =
      ((mu a : ℂ) + (loweringWeight w a : ℂ)) • normalizedLoweringWord Ω mu w := by
  rw [normalizedLoweringWord_eq_scale, map_smul,
    cartan_loweringWord Ω (fun a => (mu a : ℂ)) hweight]
  exact smul_comm _ _ _

/-- Root normalization changes no finite span when its root gaps are positive. -/
theorem span_normalizedLoweringWord_eq {ι : Type*}
    (Ω : TensorRegister n (Fin d)) (mu : Fin d → ℕ)
    (hgap : ∀ a : PositiveRoot d, 0 < (mu a.val.1 : ℝ) - mu a.val.2)
    (words : ι → List (PositiveRoot d)) :
    Submodule.span ℂ (Set.range (fun i => normalizedLoweringWord Ω mu (words i))) =
      Submodule.span ℂ (Set.range (fun i => loweringWord Ω (words i))) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro x ⟨i, rfl⟩
    dsimp only
    rw [normalizedLoweringWord_eq_scale]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · apply Submodule.span_le.mpr
    rintro x ⟨i, rfl⟩
    have h := Submodule.smul_mem
      (Submodule.span ℂ (Set.range (fun i => normalizedLoweringWord Ω mu (words i))))
      (normalizedLoweringScale mu (words i))⁻¹ (Submodule.subset_span ⟨i, rfl⟩)
    simpa only [normalizedLoweringWord_eq_scale, smul_smul,
      inv_mul_cancel₀ (normalizedLoweringScale_ne_zero mu hgap _), one_smul] using h

end Cloning.TensorLie
