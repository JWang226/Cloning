import Cloning.TensorSchurMultiplicityRefinement

/-! A full physical Schur decomposition constructed recursively along all
addable one-box branches, starting with the actual empty register. -/
noncomputable section
open scoped BigOperators InnerProductSpace
namespace Cloning.TensorLie
open Cloning.PCT
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

/-- The unique empty physical tensor, with the zero partition. -/
def emptyPhysicalHighest (d : ℕ) : PhysicalHighestTensor 0 d where
  weight := fun _ => 0
  weight_antitone := fun _ _ _ => le_rfl
  weight_sum := by simp
  vector := registerBasis (Fin 0 → Fin d) Fin.elim0
  norm_one := (registerBasis _).orthonormal.norm_eq_one _
  cartan := by intro a; simp [collectiveGenerator]
  raising := by intro a b _; simp [collectiveGenerator]

@[simp] theorem emptyPhysicalHighest_weight (d : ℕ) :
    (emptyPhysicalHighest d).weight = fun _ => 0 := rfl

/-- The zero-particle sector is the entire one-dimensional empty register. -/
theorem emptyPhysicalHighest_sector (d : ℕ) : (emptyPhysicalHighest d).sector = ⊤ := by
  apply top_unique
  intro x _
  have he : x = x Fin.elim0 • (emptyPhysicalHighest d).vector := by
    ext w
    have hw : w = Fin.elim0 := funext (fun i => Fin.elim0 i)
    subst w
    simp [emptyPhysicalHighest, registerBasis_apply, lp.single_apply]
  rw [he]
  exact Submodule.smul_mem _ _ (emptyPhysicalHighest d).vector_mem

/-- The actual list of physical copies, obtained by refining every old copy
through every addable row exactly once. -/
def recursivePhysicalDecomposition : (n d : ℕ) → List (PhysicalHighestTensor n d)
  | 0, d => [emptyPhysicalHighest d]
  | n + 1, d => (recursivePhysicalDecomposition n d).flatMap fundamentalBranchList

@[simp] theorem recursivePhysicalDecomposition_zero (d : ℕ) :
    recursivePhysicalDecomposition 0 d = [emptyPhysicalHighest d] := rfl

@[simp] theorem recursivePhysicalDecomposition_succ (n d : ℕ) :
    recursivePhysicalDecomposition (n + 1) d =
      (recursivePhysicalDecomposition n d).flatMap fundamentalBranchList := rfl

/-- Pairwise orthogonality is retained by the actual physical one-box refinement. -/
theorem recursivePhysicalDecomposition_orthogonal (n d : ℕ) :
    (recursivePhysicalDecomposition n d).Pairwise (fun H K => H.sector ⟂ K.sector) := by
  induction n with
  | zero => simp
  | succ n ih => exact fundamentalRefinement_orthogonal _ ih

/-- No physical summand is omitted at any tensor length. -/
theorem recursivePhysicalDecomposition_span (n d : ℕ) :
    physicalSectorListSpan (recursivePhysicalDecomposition n d) = ⊤ := by
  induction n with
  | zero => simp [physicalSectorListSpan, emptyPhysicalHighest_sector]
  | succ n ih =>
      rw [recursivePhysicalDecomposition_succ, fundamentalRefinement_span, ih,
        tensorProductSector_top_one]

/-- Finite direct-sum form of the exact exhaustive recursive decomposition. -/
theorem recursivePhysicalDecomposition_is_decomposition (n d : ℕ) :
    OrthogonalFamily ℂ
      (fun i : Fin (recursivePhysicalDecomposition n d).length =>
        ((recursivePhysicalDecomposition n d).get i).sector)
      (fun i => ((recursivePhysicalDecomposition n d).get i).sector.subtypeₗᵢ) ∧
      (⨆ i : Fin (recursivePhysicalDecomposition n d).length,
        ((recursivePhysicalDecomposition n d).get i).sector) = ⊤ := by
  exact ⟨physicalSectorList_orthogonalFamily _ (recursivePhysicalDecomposition_orthogonal n d),
    (physicalSectorListSpan_eq_iSup _).symm.trans (recursivePhysicalDecomposition_span n d)⟩

end Cloning.TensorLie
