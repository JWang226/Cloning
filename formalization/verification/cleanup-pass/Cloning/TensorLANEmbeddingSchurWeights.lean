import Cloning.TensorLANEmbeddingBlocks
import Cloning.TensorLANEmbeddingCellProtocol

/-! The actual copy probabilities and their exact affine-lattice pushforward. -/
noncomputable section
open scoped BigOperators Topology Classical InnerProductSpace NNReal ENNReal
open MeasureTheory Filter
namespace Cloning.TensorLAN
open Cloning.YoungHyperplane Cloning.TensorLie Cloning.InfiniteTraceClass Cloning.Hybrid
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

/-- The probabilities of the individual actual physical Schur copies. -/
def physicalCopyPMF (N d : ℕ) (p : Fin d → ℝ)
    (hp : ∀ a, 0 ≤ p a) (hs : ∑ a, p a = 1) : PMF (SchurCopy N d) :=
  PMF.ofFintype (fun i => ENNReal.ofReal (((recursivePhysicalDecomposition N d).get i).character p)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => PhysicalHighestTensor.character_nonneg _ _),
      sum_physical_characters (recursivePhysicalDecomposition N d)
        (recursivePhysicalDecomposition_is_decomposition N d).1
        (recursivePhysicalDecomposition_is_decomposition N d).2 p hp,
      hs, one_pow, ENNReal.ofReal_one])

@[simp] theorem physicalCopyPMF_toReal (N d : ℕ) (p : Fin d → ℝ)
    (hp : ∀ a, 0 ≤ p a) (hs : ∑ a, p a = 1) (i : SchurCopy N d) :
    (physicalCopyPMF N d p hp hs i).toReal =
      ((recursivePhysicalDecomposition N d).get i).character p := by
  simp only [physicalCopyPMF, PMF.ofFintype_apply,
    ENNReal.toReal_ofReal (PhysicalHighestTensor.character_nonneg _ _)]

/-- The physical partition measurement is literally the grouping of its
actual copy probabilities. -/
theorem tensorYoungPMF_eq_map_copies (N d : ℕ) (p : Fin d → ℝ)
    (hp : ∀ a, 0 ≤ p a) (hs : ∑ a, p a = 1) :
    tensorYoungPMF N d p hp hs =
      (physicalCopyPMF N d p hp hs).map
        (fun i => ((recursivePhysicalDecomposition N d).get i).shape) := by
  ext mu
  rw [tensorYoungPMF, physicalYoungPMF, PMF.ofFintype_apply, PMF.map_apply, tsum_fintype]
  unfold physicalLabelMass
  rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => by
    split_ifs
    · exact PhysicalHighestTensor.character_nonneg _ _
    · exact le_rfl)]
  apply Finset.sum_congr rfl
  intro i _
  simp only [physicalCopyPMF, PMF.ofFintype_apply]
  simp only [eq_comm (a := mu), PhysicalHighestTensor.shape_eq_iff]
  split_ifs <;> simp

@[simp] theorem schurCopyLattice_eq_shapeLattice (N d : ℕ) (i : SchurCopy N (d+1)) :
    schurCopyLattice N d i =
      shapeLattice d N ((recursivePhysicalDecomposition N (d+1)).get i).shape := by
  apply Subtype.ext
  funext a
  symm
  exact shapeLattice_apply d N _ ((recursivePhysicalDecomposition N (d+1)).get i).weight_sum a

/-- The normalized law driving the literal fixed-reference cells is exactly
the genuine copy instrument's pushforward. -/
theorem tensorYoungLatticePMF_eq_map_copies (N d : ℕ) (p : Fin (d+1) → ℝ)
    (hp : ∀ a, 0 ≤ p a) (hs : ∑ a, p a = 1) :
    tensorYoungLatticePMF d N p hp hs =
      (physicalCopyPMF N (d+1) p hp hs).map (schurCopyLattice N d) := by
  rw [tensorYoungLatticePMF, tensorYoungPMF_eq_map_copies, PMF.map_comp]
  congr 1
  funext i
  exact (schurCopyLattice_eq_shapeLattice N d i).symm

/-- Exact affine-label probability, including zero mass at every label that
has no physical copy. -/
theorem tensorYoungLatticePMF_toReal_eq_sum_copies (N d : ℕ) (p : Fin (d+1) → ℝ)
    (hp : ∀ a, 0 ≤ p a) (hs : ∑ a, p a = 1) (mu : Lattice d (N : ℤ)) :
    (tensorYoungLatticePMF d N p hp hs mu).toReal =
      ∑ i : SchurCopy N (d+1), if schurCopyLattice N d i = mu then
        ((recursivePhysicalDecomposition N (d+1)).get i).character p else 0 := by
  rw [tensorYoungLatticePMF_eq_map_copies, PMF.map_apply, tsum_fintype,
    ENNReal.toReal_sum (by
      intro i _
      split_ifs
      · exact (physicalCopyPMF N (d+1) p hp hs).apply_ne_top i
      · exact ENNReal.zero_ne_top)]
  apply Finset.sum_congr rfl
  intro i _
  simp only [eq_comm (a := mu)]
  split_ifs <;> simp

end Cloning.TensorLAN
