import Cloning.TensorSchurDecompositionIsometry
import Cloning.TensorCartanCoordinates
import Cloning.TensorGibbsState
import Mathlib.Analysis.InnerProductSpace.Trace

/-! Literal physical traces of the full tensor-power decomposition. -/
noncomputable section
open scoped BigOperators InnerProductSpace
namespace Cloning.TensorLie
open Cloning.PCT
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {n d : ℕ}

local instance (n d : ℕ) : FiniteDimensional ℂ (TensorRegister n (Fin d)) :=
  (registerBasis (Fin n → Fin d)).toOrthonormalBasis.toBasis.finiteDimensional_of_finite

variable (L : List (PhysicalHighestTensor n d))

abbrev PhysicalSchurBasisIndex := Σ i : Fin L.length,
  PartitionIndex (L.get i).weight (L.get i).weight_antitone

def physicalSchurBasisVector (a : PhysicalSchurBasisIndex L) : TensorRegister n (Fin d) :=
  (L.get a.1).canonicalEmbedding
    (partitionBasis (L.get a.1).weight (L.get a.1).weight_antitone a.2)

variable (hL : OrthogonalFamily ℂ (fun i : Fin L.length => (L.get i).sector)
  (fun i => (L.get i).sector.subtypeₗᵢ))
  (hspan : (⨆ i : Fin L.length, (L.get i).sector) = ⊤)

include hL in
theorem physicalSchurBasisVector_orthonormal :
    Orthonormal ℂ (physicalSchurBasisVector L) := by
  classical
  rw [orthonormal_iff_ite]
  rintro ⟨i, a⟩ ⟨j, b⟩
  by_cases hij : i = j
  · subst j
    change ⟪(L.get i).canonicalEmbedding _, (L.get i).canonicalEmbedding _⟫_ℂ = _
    rw [LinearIsometry.inner_map_map]
    simpa using orthonormal_iff_ite.mp
      (partitionBasis (L.get i).weight (L.get i).weight_antitone).orthonormal a b
  · have hab : (⟨i, a⟩ : PhysicalSchurBasisIndex L) ≠ ⟨j, b⟩ := by
      intro he
      exact hij (congrArg Sigma.fst he)
    rw [if_neg hab]
    exact (canonicalSectorFamily_orthogonal L hL) hij _ _

include hL hspan in
theorem physicalSchurBasisVector_spans :
    ⊤ ≤ Submodule.span ℂ (Set.range (physicalSchurBasisVector L)) := by
  intro x _
  have hx := (physicalSchurIsometry_symm_apply L hL hspan
    (physicalSchurIsometry L hL hspan x)).symm
  rw [LinearIsometryEquiv.symm_apply_apply] at hx
  rw [← hx]
  apply Submodule.sum_mem
  intro i _
  let b := partitionBasis (L.get i).weight (L.get i).weight_antitone
  rw [← b.sum_repr ((physicalSchurIsometry L hL hspan x) i), map_sum]
  apply Submodule.sum_mem
  intro j _
  rw [map_smul]
  apply Submodule.smul_mem
  exact Submodule.subset_span ⟨⟨i, j⟩, rfl⟩

def physicalSchurBasis : OrthonormalBasis (PhysicalSchurBasisIndex L) ℂ
    (TensorRegister n (Fin d)) :=
  OrthonormalBasis.mk (physicalSchurBasisVector_orthonormal L hL)
    (physicalSchurBasisVector_spans L hL hspan)

@[simp] theorem physicalSchurBasis_apply (a : PhysicalSchurBasisIndex L) :
    physicalSchurBasis L hL hspan a = physicalSchurBasisVector L a := by
  exact congrFun (OrthonormalBasis.coe_mk _ _) a

include hL hspan in
/-- The trace of every actual tensor power is the sum of the traces of its
canonical physical irreducible blocks, counted with their actual copies. -/
theorem trace_tensorOperator_eq_sum_blocks (X : Matrix (Fin d) (Fin d) ℂ) :
    LinearMap.trace ℂ (TensorRegister n (Fin d)) (tensorOperator n X).toLinearMap =
      ∑ i : Fin L.length, LinearMap.trace ℂ (L.get i).CanonicalSector
        ((L.get i).canonicalTensorOperator X).toLinearMap := by
  rw [LinearMap.trace_eq_sum_inner _ (physicalSchurBasis L hL hspan)]
  simp only [physicalSchurBasis_apply, PhysicalSchurBasisIndex, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro i _
  rw [LinearMap.trace_eq_sum_inner _ (partitionBasis (L.get i).weight (L.get i).weight_antitone)]
  apply Finset.sum_congr rfl
  intro j _
  change ⟪(L.get i).canonicalEmbedding _, tensorOperator n X ((L.get i).canonicalEmbedding _)⟫_ℂ = _
  rw [← PhysicalHighestTensor.canonicalEmbedding_tensorOperator,
    LinearIsometry.inner_map_map]
  rfl

/-- The full physical diagonal tensor trace, including the zero-fold tensor. -/
theorem trace_tensorOperator_diagonal (D : Fin d → ℂ) :
    LinearMap.trace ℂ (TensorRegister n (Fin d))
      (tensorOperator n (Matrix.diagonal D)).toLinearMap = (∑ a, D a) ^ n := by
  rw [LinearMap.trace_eq_sum_inner _ (registerBasis (Fin n → Fin d)).toOrthonormalBasis]
  have he : ∀ w : Fin n → Fin d,
      ⟪(registerBasis (Fin n → Fin d)).toOrthonormalBasis w,
        (tensorOperator n (Matrix.diagonal D)).toLinearMap
          ((registerBasis (Fin n → Fin d)).toOrthonormalBasis w)⟫_ℂ = ∏ t, D (w t) := by
    intro w
    simp only [HilbertBasis.coe_toOrthonormalBasis]
    change ⟪registerBasis (Fin n → Fin d) w,
      tensorOperator n (Matrix.diagonal D) (registerBasis (Fin n → Fin d) w)⟫_ℂ = _
    rw [tensorOperator_diagonal_basis, inner_smul_right]
    have hh := orthonormal_iff_ite.mp (registerBasis (Fin n → Fin d)).orthonormal w w
    simp only [ite_true] at hh
    rw [hh, mul_one]
  simp only [he]
  rw [← Fintype.prod_sum (fun (_ : Fin n) a => D a)]
  simp

namespace PhysicalHighestTensor

def character (H : PhysicalHighestTensor n d) (p : Fin d → ℝ) : ℝ :=
  sectorPartitionFunction (partitionHighestTensor H.weight H.weight_antitone) H.weight
    (partitionHighestTensor_cartan H.weight H.weight_antitone)
    (partitionHighestTensor_raising_zero H.weight H.weight_antitone) p

theorem character_nonneg (H : PhysicalHighestTensor n d) (p : Fin d → ℝ) :
    0 ≤ H.character p := norm_nonneg _

theorem character_eq_trace (H : PhysicalHighestTensor n d) (p : Fin d → ℝ)
    (hp : ∀ a, 0 ≤ p a) :
    H.character p = (LinearMap.trace ℂ H.CanonicalSector
      (H.canonicalTensorOperator (Matrix.diagonal (fun a => (p a : ℂ)))).toLinearMap).re :=
  sectorPartitionFunction_eq_linearMapTrace _ _ _ _ p hp

end PhysicalHighestTensor

include hL hspan in
theorem sum_physical_characters (p : Fin d → ℝ) (hp : ∀ a, 0 ≤ p a) :
    ∑ i : Fin L.length, (L.get i).character p = (∑ a, p a) ^ n := by
  have ht := trace_tensorOperator_eq_sum_blocks L hL hspan
    (Matrix.diagonal (fun a => (p a : ℂ)))
  rw [trace_tensorOperator_diagonal] at ht
  have hr := congrArg Complex.re ht
  simp only [Complex.re_sum, ← Complex.ofReal_sum, ← Complex.ofReal_pow, Complex.ofReal_re] at hr
  rw [hr]
  exact Finset.sum_congr rfl (fun i _ => PhysicalHighestTensor.character_eq_trace _ p hp)

end Cloning.TensorLie
