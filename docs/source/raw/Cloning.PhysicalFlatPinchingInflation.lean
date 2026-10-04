import Cloning.PhysicalFlatPinching
import Cloning.TensorFlatProjectorRankLaw

/-! An actual positive Schur-diagonal majorant for ordered tensor states.
At a rank-flat spectrum its coefficient is exactly r^(-n) on the supported
partitions and zero on all remaining physical copies. -/
noncomputable section
open scoped BigOperators InnerProductSpace Classical ComplexOrder Matrix
namespace Cloning.PhysicalFlatConverse
open Cloning.PCT Cloning.TensorLie Cloning.TensorLAN Cloning.InfiniteTraceClass
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
set_option synthInstance.maxHeartbeats 200000
local instance (n d : ℕ) : FiniteDimensional ℂ (TensorRegister n (Fin d)) :=
  (registerBasis (Fin n → Fin d)).toOrthonormalBasis.toBasis.finiteDimensional_of_finite

def copyIdentity {n d : ℕ} (H : PhysicalHighestTensor n d) : TraceClass H.CanonicalSector :=
  TraceClass.ofOperator 1 (isTraceClass_of_finiteDimensional _)

theorem copyIdentity_nonneg {n d : ℕ} (H : PhysicalHighestTensor n d) : 0 ≤ (copyIdentity H).1 :=
  (ContinuousLinearMap.nonneg_iff_isPositive _).mpr ContinuousLinearMap.isPositive_one

theorem copyIdentity_trace {n d : ℕ} (H : PhysicalHighestTensor n d) :
    traceCLM (copyIdentity H) = (partitionDimension H.weight H.weight_antitone : ℂ) := by
  change trace (1 : H.CanonicalSector →L[ℂ] H.CanonicalSector) _ = _
  rw [trace_eq_linearMap_trace_of_finiteDimensional]
  exact LinearMap.trace_id ℂ _

def inflatedTensor (n d : ℕ) (p : Fin d → ℝ) : TraceClass (TensorRegister n (Fin d)) :=
  ∑ i : SchurCopy n d,
    ((∏ a, p a ^ ((recursivePhysicalDecomposition n d).get i).weight a : ℝ) : ℂ) •
      conjugationLinearMap ((recursivePhysicalDecomposition n d).get i).canonicalEmbedding.toContinuousLinearMap
        (copyIdentity ((recursivePhysicalDecomposition n d).get i))

theorem inflatedTensor_nonneg (n d : ℕ) (p : Fin d → ℝ) (hp : ∀ a, 0 ≤ p a) :
    0 ≤ (inflatedTensor n d p).1 := by
  change 0 ≤ inclusionCLM (∑ i : SchurCopy n d, _)
  rw [map_sum]
  apply Finset.sum_nonneg
  intro i _
  rw [map_smul]
  apply smul_nonneg
  · exact_mod_cast Finset.prod_nonneg (fun a _ => pow_nonneg (hp a) _)
  · exact conjugationLinearMap_nonneg _ _ (copyIdentity_nonneg _)

theorem inflatedTensor_trace (n d : ℕ) (p : Fin d → ℝ) :
    traceCLM (inflatedTensor n d p) =
      ((∑ i : SchurCopy n d,
        (∏ a, p a ^ ((recursivePhysicalDecomposition n d).get i).weight a) *
          (partitionDimension ((recursivePhysicalDecomposition n d).get i).weight
            ((recursivePhysicalDecomposition n d).get i).weight_antitone : ℝ)) : ℂ) := by
  simp only [inflatedTensor, map_sum, map_smul, conjugationLinearMap_isometry_trace,
    copyIdentity_trace, smul_eq_mul, Complex.ofReal_sum, Complex.ofReal_mul]
  rfl

/-- The genuine diagonal tensor block is dominated by its highest eigenvalue
times the identity on its actual canonical sector. -/
theorem canonicalTensorWeight_le_highest_identity {n d : ℕ} (H : PhysicalHighestTensor n d)
    (p : Fin d → ℝ) (hp : ∀ a, 0 ≤ p a) (hord : Antitone p) :
    (canonicalTensorWeight H (Matrix.diagonal (fun a => (p a : ℂ)))).1 ≤
      (((∏ a, p a ^ H.weight a : ℝ) : ℂ) • copyIdentity H).1 := by
  let T := H.canonicalTensorOperator (Matrix.diagonal (fun a => (p a : ℂ)))
  let c : ℝ := ∏ a, p a ^ H.weight a
  have hc : 0 ≤ c := Finset.prod_nonneg (fun a _ => pow_nonneg (hp a) _)
  have hT : 0 ≤ T := sectorGibbsOperator_nonneg _ _
    (partitionHighestTensor_cartan _ _) (partitionHighestTensor_raising_zero _ _) p hp
  have hn : ‖T‖ ≤ c := by
    apply ContinuousLinearMap.opNorm_le_bound _ hc
    intro x
    exact tensorOperator_diagonal_norm_le_on_cyclicSector
      (partitionHighestTensor H.weight H.weight_antitone) H.weight
      (partitionHighestTensor_cartan _ _) p hp hord x.property
  have hb := (CStarAlgebra.norm_le_iff_le_algebraMap T hc hT).mp hn
  simpa only [Algebra.algebraMap_eq_smul_one, Complex.real_smul] using hb

/-- An operator inequality for the literal full tensor register, derived
copy by copy from the actual highest-weight norm bound. -/
theorem matrixTensorPower_le_inflatedTensor (n d : ℕ) (p : Fin d → ℝ)
    (hp : ∀ a, 0 ≤ p a) (hord : Antitone p) :
    (matrixTensorPower (Matrix.diagonal (fun a => (p a : ℂ))) n).1 ≤ (inflatedTensor n d p).1 := by
  rw [matrixTensorPower_eq_sum_canonical_blocks (recursivePhysicalDecomposition n d)
    (recursivePhysicalDecomposition_is_decomposition n d).1
    (recursivePhysicalDecomposition_is_decomposition n d).2]
  change inclusionCLM (∑ i : SchurCopy n d, _) ≤ inclusionCLM (∑ i : SchurCopy n d, _)
  rw [map_sum, map_sum]
  apply Finset.sum_le_sum
  intro i _
  have h := canonicalTensorWeight_le_highest_identity ((recursivePhysicalDecomposition n d).get i) p hp hord
  have hh := conjugationLinearMap_nonneg
    ((recursivePhysicalDecomposition n d).get i).canonicalEmbedding.toContinuousLinearMap
    ((((∏ a, p a ^ ((recursivePhysicalDecomposition n d).get i).weight a : ℝ) : ℂ) •
      copyIdentity ((recursivePhysicalDecomposition n d).get i)) -
      canonicalTensorWeight ((recursivePhysicalDecomposition n d).get i) (Matrix.diagonal (fun a => (p a : ℂ))))
    (by exact sub_nonneg.mpr h)
  exact sub_nonneg.mp (by simpa only [map_sub, map_smul] using hh)

/-- Rank-flat inflation is a physical positive operator and dominates the
literal rank-flat tensor input, including the zero-fold tensor. -/
def flatInflatedInput (n r k : ℕ) : TraceClass (TensorRegister n (Fin (r+k))) :=
  inflatedTensor n (r+k) (rankFlatSpectrum r k)

theorem flatInflatedInput_nonneg (n r k : ℕ) : 0 ≤ (flatInflatedInput n r k).1 :=
  inflatedTensor_nonneg n (r+k) _ (rankFlatSpectrum_nonneg r k)

theorem rankFlatTensor_le_flatInflatedInput (n r k : ℕ) :
    (matrixTensorPower (Matrix.diagonal (fun a => (rankFlatSpectrum r k a : ℂ))) n).1 ≤
      (flatInflatedInput n r k).1 :=
  matrixTensorPower_le_inflatedTensor n (r+k) _ (rankFlatSpectrum_nonneg r k)
    (rankFlatSpectrum_antitone r k)

end Cloning.PhysicalFlatConverse
