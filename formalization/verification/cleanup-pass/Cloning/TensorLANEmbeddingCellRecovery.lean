import Cloning.TensorLANEmbeddingSelectorRecovery
import Cloning.TensorLANEmbeddingMixtureError

/-! Exact recovery of physical copy probabilities after classical smoothing
and quantization in the fixed whitening chart. -/
noncomputable section
open scoped BigOperators Topology Classical InnerProductSpace
open MeasureTheory Filter
namespace Cloning.TensorLAN
open Cloning.YoungHyperplane Cloning.TensorLie Cloning.PCTJointGaussianWhitening
open Cloning.Hybrid Cloning.InfiniteTraceClass Cloning.PCT
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
variable {d : ℕ}
local instance (n d : ℕ) : FiniteDimensional ℂ (TensorRegister n (Fin d)) :=
  (registerBasis (Fin n → Fin d)).toOrthonormalBasis.toBasis.finiteDimensional_of_finite

variable (p : Fin (d+1) → ℝ) (hp : ∀ a, 0 < p a)
    (b : OrthonormalBasis (Fin (d+1)) ℝ (EuclideanSpace ℝ (Fin (d+1))))
    (hb : b 0 = sqrtSpectrum p)

def physicalLabelDensity (N : ℕ) (r : Fin (d+1) → ℝ) : (Fin d → ℝ) → ℝ :=
  fun y => ∑ i : SchurCopy N (d+1),
    ((recursivePhysicalDecomposition N (d+1)).get i).character r *
      physicalCellDensity p hp b hb N i y

theorem physicalLabelDensity_integrable (N : ℕ) (r : Fin (d+1) → ℝ) :
    Integrable (physicalLabelDensity p hp b hb N r) :=
  integrable_finset_sum _ (fun i _ => (physicalCellDensity_integrable p hp b hb N i).const_mul _)

theorem physicalLabelDensity_nonneg (N : ℕ) (r : Fin (d+1) → ℝ) (y : Fin d → ℝ) :
    0 ≤ physicalLabelDensity p hp b hb N r y :=
  Finset.sum_nonneg fun i _ => mul_nonneg (PhysicalHighestTensor.character_nonneg _ _)
    (physicalCellDensity_nonneg p hp b hb N i y)

theorem physicalLabelDensity_integral (N : ℕ) (r : Fin (d+1) → ℝ)
    (hr : ∀ a, 0 ≤ r a) (hs : ∑ a, r a = 1) :
    ∫ y, physicalLabelDensity p hp b hb N r y = 1 := by
  change (∫ y, ∑ i : SchurCopy N (d+1),
    ((recursivePhysicalDecomposition N (d+1)).get i).character r *
      physicalCellDensity p hp b hb N i y) = 1
  rw [integral_finset_sum _
    (fun i _ => (physicalCellDensity_integrable p hp b hb N i).const_mul _)]
  simp_rw [integral_const_mul, physicalCellDensity_integral, mul_one]
  rw [sum_physical_characters _ (recursivePhysicalDecomposition_is_decomposition N (d+1)).1
    (recursivePhysicalDecomposition_is_decomposition N (d+1)).2 r hr, hs, one_pow]

theorem physicalLabelDensity_eq_whitened (N : ℕ) (hN : 0 < N)
    (r : Fin (d+1) → ℝ) (hr : ∀ a, 0 ≤ r a) (hs : ∑ a, r a = 1) :
    physicalLabelDensity p hp b hb N r =
      whiteningDensity (rootWhitening p hp b hb) (fixedBaseYoungDensity d N p r hr hs) := by
  funext y
  exact sum_copy_physicalCellDensity N d hN p hp b hb r hr hs y

theorem physicalLabelDensity_selector_integral (N : ℕ) (hN : 0 < N)
    (r : Fin (d+1) → ℝ) (hr : ∀ a, 0 ≤ r a) (hs : ∑ a, r a = 1)
    (i : Option (SchurCopy N (d+1))) :
    (∫ y, uniformLabelSelector (schurCopyLattice N d) (physicalCellQuantizer p hp b hb N) i y *
      physicalLabelDensity p hp b hb N r y) =
      i.elim 0 (fun i => ((recursivePhysicalDecomposition N (d+1)).get i).character r) := by
  apply uniformLabelSelector_recovers _ _ (physicalCellQuantizer_measurable p hp b hb N)
    _ (physicalLabelDensity_integrable p hp b hb N r)
    (physicalLabelDensity_integral p hp b hb N r hr hs)
  · rw [sum_physical_characters _ (recursivePhysicalDecomposition_is_decomposition N (d+1)).1
      (recursivePhysicalDecomposition_is_decomposition N (d+1)).2 r hr, hs, one_pow]
  · exact physicalCopy_character_eq_of_lattice_eq N d r
  · intro a
    rw [physicalLabelDensity_eq_whitened p hp b hb N hN r hr hs,
      binMass_physicalCellQuantizer N d hN p hp b hb r hr hs,
      tensorYoungLatticePMF_toReal_eq_sum_copies]

/-- Smoothing the physical Young law and then reading the actual selector
recovers every copy with precisely its physical character probability. -/
theorem physicalCellReverse_prepare_physicalLabelDensity (N R : ℕ) (hN : 0 < N)
    (r : Fin (d+1) → ℝ) (hr : ∀ a, 0 ≤ r a) (hs : ∑ a, r a = 1)
    (A : TraceClass (RootFock (d+1))) :
    (physicalCellReverse p hp b hb N R).map
      (prepareL1 (physicalLabelDensity p hp b hb N r)
        (physicalLabelDensity_integrable p hp b hb N r) A) =
      ∑ i : SchurCopy N (d+1),
        (((recursivePhysicalDecomposition N (d+1)).get i).character r : ℂ) •
          (fockToCopy N (d+1) R i).toLinearMap A := by
  rw [physicalCellReverse, schurReverse, HybridToQuantum.finiteSelector_apply]
  have hi (i : Option (SchurCopy N (d+1))) : Integrable (fun y =>
      uniformLabelSelector (schurCopyLattice N d) (physicalCellQuantizer p hp b hb N) i y *
        physicalLabelDensity p hp b hb N r y) := by
    exact (physicalLabelDensity_integrable p hp b hb N r).bdd_mul
      ((uniformLabelSelector_measurable _ _ (physicalCellQuantizer_measurable p hp b hb N) i).aestronglyMeasurable)
      (Eventually.of_forall (finiteSelector_weight_bound _
        (uniformLabelSelector_nonneg _ _) (uniformLabelSelector_sum _ _) i))
  simp_rw [weightedL1Integral_prepare _ _ _ _ _ (hi _),
    physicalLabelDensity_selector_integral p hp b hb N hN r hr hs]
  rw [Fintype.sum_option]
  simp only [Option.elim_none, Option.elim_some, Complex.ofReal_zero, zero_smul, map_zero,
    zero_add, copyReverseWithFallback, map_smul]

end Cloning.TensorLAN
