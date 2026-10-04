import Cloning.TensorSchurMultiplicityBranching

/-! Orthogonal refinement of physical highest-sector lists by one particle. -/
noncomputable section
open scoped BigOperators InnerProductSpace
namespace Cloning.TensorLie
open Cloning.PCT
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
variable {n m d : ℕ}

theorem tensorJoin_add_left (x y : TensorRegister n (Fin d))
    (z : TensorRegister m (Fin d)) : tensorJoin (x + y) z = tensorJoin x z + tensorJoin y z := by
  ext w
  simp [tensorJoin_apply, add_mul]

theorem tensorProductSector_mono_left {P R : Submodule ℂ (TensorRegister n (Fin d))}
    (h : P ≤ R) (Q : Submodule ℂ (TensorRegister m (Fin d))) :
    tensorProductSector P Q ≤ tensorProductSector R Q := by
  apply Submodule.span_le.mpr
  rintro _ ⟨x, hx, y, hy, rfl⟩
  exact tensorJoin_mem_tensorProductSector R Q (h hx) hy

theorem tensorProductSector_sup_left (P R : Submodule ℂ (TensorRegister n (Fin d)))
    (Q : Submodule ℂ (TensorRegister m (Fin d))) :
    tensorProductSector (P ⊔ R) Q = tensorProductSector P Q ⊔ tensorProductSector R Q := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨x, hx, y, hy, rfl⟩
    obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.mp hx
    rw [tensorJoin_add_left]
    exact Submodule.add_mem _
      ((show tensorProductSector P Q ≤ tensorProductSector P Q ⊔ tensorProductSector R Q from le_sup_left)
        (tensorJoin_mem_tensorProductSector P Q hu hy))
      ((show tensorProductSector R Q ≤ tensorProductSector P Q ⊔ tensorProductSector R Q from le_sup_right)
        (tensorJoin_mem_tensorProductSector R Q hv hy))
  · exact sup_le (tensorProductSector_mono_left le_sup_left Q)
      (tensorProductSector_mono_left le_sup_right Q)

theorem tensorProductSector_bot_left (Q : Submodule ℂ (TensorRegister m (Fin d))) :
    tensorProductSector (⊥ : Submodule ℂ (TensorRegister n (Fin d))) Q = ⊥ := by
  apply bot_unique
  apply Submodule.span_le.mpr
  rintro _ ⟨x, hx, y, _, rfl⟩
  have hx0 : x = 0 := hx
  simp [hx0]

theorem tensorProductSector_top_one :
    tensorProductSector (⊤ : Submodule ℂ (TensorRegister n (Fin d)))
      (⊤ : Submodule ℂ (TensorRegister 1 (Fin d))) = ⊤ := by
  apply top_unique
  intro x _
  rw [mem_tensorProductSector_top_iff]
  intro r
  exact Submodule.mem_top

/-- Orthogonality of the first physical factors implies orthogonality of their
literal tensor-product subspaces, irrespective of the final factor. -/
theorem tensorProductSector_isOrtho_left
    {P R : Submodule ℂ (TensorRegister n (Fin d))} (h : P ⟂ R)
    (Q S : Submodule ℂ (TensorRegister m (Fin d))) :
    tensorProductSector P Q ⟂ tensorProductSector R S := by
  apply Submodule.isOrtho_span.mpr
  rintro _ ⟨x, hx, y, _, rfl⟩ _ ⟨u, hu, v, _, rfl⟩
  rw [tensorJoin_inner, h.inner_eq hx hu, zero_mul]

theorem physicalSectorListSpan_append (L K : List (PhysicalHighestTensor n d)) :
    physicalSectorListSpan (L ++ K) = physicalSectorListSpan L ⊔ physicalSectorListSpan K := by
  induction L with
  | nil => simp [physicalSectorListSpan]
  | cons H L ih => simp [physicalSectorListSpan, ih, sup_assoc]

/-- The full one-particle refinement is the literal old span tensored with the
whole new physical register. -/
theorem fundamentalRefinement_span (L : List (PhysicalHighestTensor n d)) :
    physicalSectorListSpan (L.flatMap fundamentalBranchList) =
      tensorProductSector (physicalSectorListSpan L)
        (⊤ : Submodule ℂ (TensorRegister 1 (Fin d))) := by
  induction L with
  | nil => simp [physicalSectorListSpan, tensorProductSector_bot_left]
  | cons H L ih =>
      rw [List.flatMap_cons, physicalSectorListSpan_append, fundamentalBranchList_span, ih,
        physicalSectorListSpan, tensorProductSector_sup_left]

theorem fundamentalRefinement_orthogonal (L : List (PhysicalHighestTensor n d))
    (hL : L.Pairwise (fun H K => H.sector ⟂ K.sector)) :
    (L.flatMap fundamentalBranchList).Pairwise (fun H K => H.sector ⟂ K.sector) := by
  apply List.pairwise_flatMap.mpr
  refine ⟨fun H _ => fundamentalBranchList_orthogonal H, ?_⟩
  apply hL.imp
  intro H K hHK A hA B hB
  exact ((tensorProductSector_isOrtho_left hHK
    (⊤ : Submodule ℂ (TensorRegister 1 (Fin d))) ⊤).mono_left
      (fundamentalBranchList_sector_le H hA)).mono_right
      (fundamentalBranchList_sector_le K hB)

end Cloning.TensorLie
