import Cloning.TensorPBWDominance

/-! Actual finite tensor occupation bounds exhaust the cyclic sector at a
finite root-height cutoff, yielding an unconditional polynomial dimension bound. -/
noncomputable section
open scoped BigOperators
namespace Cloning.TensorLie
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {n d : ℕ}

/-- A nonzero physical lowering word cannot have root height above `n*d`.
The bound follows from its literal nonnegative tensor occupations. -/
theorem loweringWord_height_le_tensorSize
    (Ω : TensorRegister n (Fin d)) (mu : Fin d → ℕ)
    (hweight : ∀ a, collectiveGenerator n a a Ω = (mu a : ℂ) • Ω)
    (w : List (PositiveRoot d)) (hw : loweringWord Ω w ≠ 0) :
    loweringHeight w ≤ n * d := by
  obtain ⟨v, hv⟩ : ∃ v : Fin n → Fin d, loweringWord Ω w v ≠ 0 := by
    by_contra! h
    apply hw
    ext v
    exact h v
  have he : (loweringHeight w : ℤ) + ∑ a : Fin d, (a.val : ℤ) * mu a =
      ∑ a : Fin d, (a.val : ℤ) * occupancy v a := by
    rw [← loweringWeight_index_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a _
    have ha := loweringWord_occupancy_eq_weight Ω mu hweight w v hv a
    rw [ha]
    ring
  have hbound : (∑ a : Fin d, (a.val : ℤ) * occupancy v a) ≤
      (d : ℤ) * ∑ a : Fin d, (occupancy v a : ℤ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro a _
    apply mul_le_mul_of_nonneg_right
    · exact_mod_cast a.isLt.le
    · exact Int.natCast_nonneg _
  have hsum : (∑ a : Fin d, (occupancy v a : ℤ)) = n := by
    exact_mod_cast sum_occupancy v
  have hn : 0 ≤ ∑ a : Fin d, (a.val : ℤ) * mu a :=
    Finset.sum_nonneg (fun a _ => mul_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _))
  rw [hsum] at hbound
  have : (loweringHeight w : ℤ) ≤ (n : ℤ) * d := by nlinarith
  exact_mod_cast this

theorem loweringWord_eq_zero_of_tensorSize_lt
    (Ω : TensorRegister n (Fin d)) (mu : Fin d → ℕ)
    (hweight : ∀ a, collectiveGenerator n a a Ω = (mu a : ℂ) • Ω)
    (w : List (PositiveRoot d)) (hw : n * d < loweringHeight w) :
    loweringWord Ω w = 0 := by
  by_contra h
  exact (not_lt_of_ge (loweringWord_height_le_tensorSize Ω mu hweight w h)) hw

/-- The full physical cyclic sector is exactly the finite tensor-height
cutoff. This is derived from occupations, not from a PBW basis assumption. -/
theorem cyclicSector_eq_tensorSize_cutoff
    (Ω : TensorRegister n (Fin d)) (mu : Fin d → ℕ)
    (hweight : ∀ a, collectiveGenerator n a a Ω = (mu a : ℂ) • Ω) :
    cyclicSector Ω = cyclicCutoff Ω ((n * d : ℕ) : ℤ) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro x ⟨w, rfl⟩
    by_cases hw : loweringWord Ω w = 0
    · rw [hw]
      exact Submodule.zero_mem _
    · exact loweringWord_mem_cyclicCutoff Ω w (by
        exact_mod_cast loweringWord_height_le_tensorSize Ω mu hweight w hw)
  · exact cyclicCutoff_le_cyclicSector Ω _

/-- A polynomial upper bound in the literal tensor length for every physical
cyclic highest sector, including weights with zero root gaps. -/
theorem finrank_cyclicSector_le_polynomial
    (Ω : TensorRegister n (Fin d)) (mu : Fin d → ℕ)
    (hweight : ∀ a, collectiveGenerator n a a Ω = (mu a : ℂ) • Ω) :
    Module.finrank ℂ (cyclicSector Ω) ≤
      (n * d + 1) ^ Fintype.card (PositiveRoot d) := by
  rw [cyclicSector_eq_tensorSize_cutoff Ω mu hweight]
  exact finrank_cyclicCutoff_le_polynomial Ω (n * d)

end Cloning.TensorLie
