import Cloning.TensorFundamentalBranchingExistence
import Cloning.TensorSchurDecompositionFundamental
import Cloning.TensorSchurDecompositionHighest

/-! Complete actual one-box branching data, chosen only after constructive existence. -/
noncomputable section
open scoped BigOperators InnerProductSpace
namespace Cloning.TensorLie
open YoungGeneral
set_option maxHeartbeats 800000
variable {n d : ℕ}

/-- Each actual irreducible copy branches once at every addable row. -/
structure FundamentalBranchData (H : PhysicalHighestTensor n d) where
  copies : List (PhysicalHighestTensor (n + 1) d)
  rows : Fin copies.length ↪ Fin d
  labels : ∀ i, (copies.get i).weight = addBox H.weight (rows i)
  orthogonal : copies.Pairwise (fun A B => A.sector ⟂ B.sector)
  span_eq : physicalSectorListSpan copies = tensorProductSector H.sector
    (⊤ : Submodule ℂ (TensorRegister 1 (Fin d)))
  row_range : ∀ r, Antitone (addBox H.weight r) ↔ ∃ i, rows i = r

theorem fundamentalBranchData_nonempty (H : PhysicalHighestTensor n d) :
    Nonempty (FundamentalBranchData H) := by
  obtain ⟨L, rows, hlabels, horth, hspan⟩ :=
    exists_fundamental_multiplicityFree_decomposition H.vector H.weight H.norm_one H.cartan H.raising
  refine ⟨⟨L, rows, hlabels, horth, hspan, ?_⟩⟩
  intro r
  apply fundamental_decomposition_row_coverage H.vector H.weight L rows hlabels hspan
  intro s hs
  obtain ⟨x, hxmem, hx0, hxweight, hxraise⟩ := exists_fundamental_highest_of_addable
    H.vector H.weight H.norm_one H.cartan H.raising H.weight_antitone s hs
  exact ⟨x, ⟨hxmem, hxweight, hxraise⟩, hx0⟩

/-- Fixed concrete physical branching data for each physical highest copy. -/
def fundamentalBranchData (H : PhysicalHighestTensor n d) : FundamentalBranchData H :=
  Classical.choice (fundamentalBranchData_nonempty H)

def fundamentalBranchList (H : PhysicalHighestTensor n d) :
    List (PhysicalHighestTensor (n + 1) d) := (fundamentalBranchData H).copies

theorem fundamentalBranchList_orthogonal (H : PhysicalHighestTensor n d) :
    (fundamentalBranchList H).Pairwise (fun A B => A.sector ⟂ B.sector) :=
  (fundamentalBranchData H).orthogonal

theorem fundamentalBranchList_span (H : PhysicalHighestTensor n d) :
    physicalSectorListSpan (fundamentalBranchList H) = tensorProductSector H.sector
      (⊤ : Submodule ℂ (TensorRegister 1 (Fin d))) := (fundamentalBranchData H).span_eq

theorem fundamentalBranchList_sector_le (H : PhysicalHighestTensor n d)
    {K : PhysicalHighestTensor (n + 1) d} (hK : K ∈ fundamentalBranchList H) :
    K.sector ≤ tensorProductSector H.sector (⊤ : Submodule ℂ (TensorRegister 1 (Fin d))) := by
  rw [← fundamentalBranchList_span H]
  exact physicalSector_le_listSpan hK

end Cloning.TensorLie
