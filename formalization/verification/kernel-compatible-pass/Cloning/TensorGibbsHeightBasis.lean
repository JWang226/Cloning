import Cloning.TensorGibbsTrace
import Cloning.TensorPBWCutoffBasis

/-! Exact occupation bases of each physical height space, obtained from the
proved cutoff basis. -/
noncomputable section
open scoped BigOperators InnerProductSpace
namespace Cloning.TensorLie
open Cloning.PCT
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
variable {n d : ℕ}
local instance : FiniteDimensional ℂ (TensorRegister n (Fin d)) :=
  (registerBasis (Fin n → Fin d)).toOrthonormalBasis.toBasis.finiteDimensional_of_finite

abbrev ExactHeightOccupation (d H : ℕ) :=
  {k : HeightOccupation d H // occupationHeight k.val = H}

def canonicalHeightVector (Ω : TensorRegister n (Fin d)) (mu : Fin d → ℕ) (H : ℕ)
    (k : ExactHeightOccupation d H) : sectorHeightSpace Ω H :=
  ⟨⟨normalizedLoweringWord Ω mu (canonicalWord k.val.val),
    cyclicCutoff_le_cyclicSector Ω _
      (normalizedLoweringWord_mem_cyclicCutoff Ω mu _ (R := (H : ℤ)) (by
        rw [canonicalWord_height]; exact_mod_cast k.val.property))⟩, by
    change normalizedLoweringWord Ω mu (canonicalWord k.val.val) ∈ cyclicHeightSpace Ω H
    rw [normalizedLoweringWord_eq_scale]
    exact Submodule.smul_mem _ _ (Submodule.subset_span
      ⟨canonicalWord k.val.val, (canonicalWord_height _).trans k.property, rfl⟩)⟩

theorem span_canonicalHeightVector_eq_top (Ω : TensorRegister n (Fin d))
    (mu : Fin d → ℕ) (H : ℕ)
    (hgap : ∀ a : PositiveRoot d, 0 < (mu a.val.1 : ℝ) - mu a.val.2) :
    Submodule.span ℂ (Set.range (canonicalHeightVector Ω mu H)) = ⊤ := by
  apply (Submodule.span_range_subtype_eq_top_iff (sectorHeightSpace Ω H) _).mpr
  apply (Submodule.map_injective_of_injective (cyclicSector Ω).injective_subtype)
  rw [Submodule.map_span]
  have hs : (sectorHeightSpace Ω H).map (cyclicSector Ω).subtype = cyclicHeightSpace Ω H := by
    rw [sectorHeightSpace, Submodule.map_comap_eq]
    rw [Submodule.range_subtype, inf_eq_right]
    exact (cyclicHeightSpace_le_cutoff Ω H).trans (cyclicCutoff_le_cyclicSector Ω _)
  rw [hs]
  simp only [← Set.range_comp, Function.comp_def]
  change Submodule.span ℂ (Set.range (fun k : ExactHeightOccupation d H =>
    normalizedLoweringWord Ω mu (canonicalWord k.val.val))) = _
  rw [span_normalizedLoweringWord_eq Ω mu hgap, cyclicHeightSpace_eq_span_canonical]
  congr 1
  ext x
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨k.val, k.property, rfl⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨⟨k,hk⟩, rfl⟩

def canonicalHeightBasis (Ω : TensorRegister n (Fin d)) (mu : Fin d → ℕ) (H : ℕ)
    (hgap : ∀ a : PositiveRoot d, 0 < (mu a.val.1 : ℝ) - mu a.val.2)
    (hli : LinearIndependent ℂ (fun k : HeightOccupation d H =>
      normalizedLoweringWord Ω mu (canonicalWord k.val))) :
    Module.Basis (ExactHeightOccupation d H) ℂ (sectorHeightSpace Ω H) :=
  Module.Basis.mk
    (LinearIndependent.of_comp (v := canonicalHeightVector Ω mu H)
      ((cyclicSector Ω).subtype.comp (sectorHeightSpace Ω H).subtype)
      (hli.comp (fun k : ExactHeightOccupation d H => k.val) Subtype.val_injective))
    (span_canonicalHeightVector_eq_top Ω mu H hgap).ge

@[simp] theorem canonicalHeightBasis_coe (Ω : TensorRegister n (Fin d))
    (mu : Fin d → ℕ) (H : ℕ)
    (hgap : ∀ a : PositiveRoot d, 0 < (mu a.val.1 : ℝ) - mu a.val.2)
    (hli : LinearIndependent ℂ (fun k : HeightOccupation d H =>
      normalizedLoweringWord Ω mu (canonicalWord k.val))) (k : ExactHeightOccupation d H) :
    ((canonicalHeightBasis Ω mu H hgap hli k : cyclicSector Ω) : TensorRegister n (Fin d)) =
      normalizedLoweringWord Ω mu (canonicalWord k.val.val) := by
  rw [canonicalHeightBasis, Module.Basis.mk_apply]
  rfl

end Cloning.TensorLie
