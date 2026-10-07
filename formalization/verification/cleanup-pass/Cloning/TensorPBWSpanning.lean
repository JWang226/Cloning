import Cloning.TensorPBWStraightening
import Cloning.TensorPBWOccupations
import Cloning.TensorCyclicSector
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! Canonical occupation spanning of actual tensor cutoffs, and uniform
polynomial bounds on their dimensions. -/
noncomputable section
open scoped BigOperators
namespace Cloning.TensorLie
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {n d : ℕ}

local instance : FiniteDimensional ℂ (TensorRegister n (Fin d)) :=
  (Cloning.PCT.registerBasis (Fin n → Fin d)).toOrthonormalBasis.toBasis.finiteDimensional_of_finite

/-- Every bounded physical cyclic cutoff is spanned by the finite canonical
occupation list. This is an exact equality, valid even when some vectors vanish
or are linearly dependent. -/
theorem cyclicCutoff_eq_span_canonical (Ω : TensorRegister n (Fin d)) (R : ℕ) :
    cyclicCutoff Ω (R : ℤ) = Submodule.span ℂ
      (Set.range (fun k : HeightOccupation d R => loweringWord Ω (canonicalWord k.val))) := by
  rw [cyclicCutoff_eq_ordered_span]
  apply congrArg (Submodule.span ℂ)
  ext x
  constructor
  · rintro ⟨w, hw, hheight, rfl⟩
    have hk : occupationHeight (fun a => w.count a) ≤ R := by
      simpa only [occupationHeight, ← loweringHeight_eq_sum_count] using hheight
    refine ⟨⟨fun a => w.count a, hk⟩, ?_⟩
    simp only [canonicalWord_counts_of_ordered w hw]
  · rintro ⟨k, rfl⟩
    exact ⟨canonicalWord k.val, canonicalWord_ordered _,
      (canonicalWord_height _).trans_le k.property, rfl⟩

/-- Exact total-height component of the physical lowering-word span. -/
def cyclicHeightSpace (Ω : TensorRegister n (Fin d)) (H : ℕ) :
    Submodule ℂ (TensorRegister n (Fin d)) :=
  Submodule.span ℂ {x | ∃ w : List (PositiveRoot d), loweringHeight w = H ∧
    x = loweringWord Ω w}

theorem cyclicHeightSpace_le_cutoff (Ω : TensorRegister n (Fin d)) (H : ℕ) :
    cyclicHeightSpace Ω H ≤ cyclicCutoff Ω (H : ℤ) := by
  apply Submodule.span_le.mpr
  rintro x ⟨w, hw, rfl⟩
  exact loweringWord_mem_cyclicCutoff Ω w (by omega)

theorem cyclicHeightSpace_eq_span_canonical (Ω : TensorRegister n (Fin d)) (H : ℕ) :
    cyclicHeightSpace Ω H = Submodule.span ℂ
      {x | ∃ k : HeightOccupation d H, occupationHeight k.val = H ∧
        x = loweringWord Ω (canonicalWord k.val)} := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro x ⟨w, hw, rfl⟩
    apply loweringWord_mem_of_ordered Ω _ w.length H (loweringWeight w)
      _ w le_rfl hw rfl
    intro v hv _ hvH _
    have hk : occupationHeight (fun a => v.count a) = H := by
      simpa only [occupationHeight, ← loweringHeight_eq_sum_count] using hvH
    apply Submodule.subset_span
    exact ⟨⟨fun a => v.count a, hk.le⟩, hk,
      by rw [canonicalWord_counts_of_ordered v hv]⟩
  · apply Submodule.span_le.mpr
    rintro x ⟨k, hk, rfl⟩
    exact Submodule.subset_span ⟨canonicalWord k.val, (canonicalWord_height _).trans hk, rfl⟩

/-- The finite canonical occupation spanning family gives an unconditional
cutoff dimension bound; no asymptotic or positive root-gap premise is needed. -/
theorem finrank_cyclicCutoff_le_card (Ω : TensorRegister n (Fin d)) (R : ℕ) :
    Module.finrank ℂ (cyclicCutoff Ω (R : ℤ)) ≤ Fintype.card (HeightOccupation d R) := by
  rw [cyclicCutoff_eq_span_canonical]
  exact finrank_range_le_card _

theorem finrank_cyclicCutoff_le_polynomial (Ω : TensorRegister n (Fin d)) (R : ℕ) :
    Module.finrank ℂ (cyclicCutoff Ω (R : ℤ)) ≤
      (R + 1) ^ Fintype.card (PositiveRoot d) :=
  (finrank_cyclicCutoff_le_card Ω R).trans (HeightOccupation.card_le R)

theorem finrank_cyclicHeightSpace_le_polynomial (Ω : TensorRegister n (Fin d)) (H : ℕ) :
    Module.finrank ℂ (cyclicHeightSpace Ω H) ≤
      (H + 1) ^ Fintype.card (PositiveRoot d) :=
  (Submodule.finrank_mono (cyclicHeightSpace_le_cutoff Ω H)).trans
    (finrank_cyclicCutoff_le_polynomial Ω H)

/-- The full cyclic sector is the sum of its exact total-height pieces. -/
theorem cyclicSector_eq_iSup_cyclicHeightSpace (Ω : TensorRegister n (Fin d)) :
    cyclicSector Ω = ⨆ H : ℕ, cyclicHeightSpace Ω H := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro x ⟨w, rfl⟩
    apply (le_iSup (fun H => cyclicHeightSpace Ω H) (loweringHeight w))
    exact Submodule.subset_span ⟨w, rfl, rfl⟩
  · apply iSup_le
    intro H
    exact (cyclicHeightSpace_le_cutoff Ω H).trans (cyclicCutoff_le_cyclicSector Ω _)

end Cloning.TensorLie
