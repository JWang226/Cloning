import Cloning.TensorSchurDecomposition
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Lp.LpEquiv

/-! A complete physical tensor decomposition as an exact Hilbert-sum isometry. -/
noncomputable section
open scoped BigOperators InnerProductSpace
namespace Cloning.TensorLie
open Cloning.PCT
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {n d : ℕ}

local instance : FiniteDimensional ℂ (TensorRegister n (Fin d)) :=
  (registerBasis (Fin n → Fin d)).toOrthonormalBasis.toBasis.finiteDimensional_of_finite

namespace PhysicalHighestTensor

abbrev CanonicalSector (H : PhysicalHighestTensor n d) :=
  cyclicSector (partitionHighestTensor H.weight H.weight_antitone)

def canonicalEmbedding (H : PhysicalHighestTensor n d) : H.CanonicalSector →ₗᵢ[ℂ] TensorRegister n (Fin d) :=
  H.sector.subtypeₗᵢ.comp H.canonicalIsometry.toLinearIsometry

theorem range_canonicalEmbedding (H : PhysicalHighestTensor n d) :
    LinearMap.range H.canonicalEmbedding.toLinearMap = H.sector := by
  ext x
  constructor
  · rintro ⟨v, rfl⟩
    exact (H.canonicalIsometry v).property
  · intro hx
    refine ⟨H.canonicalIsometry.symm ⟨x, hx⟩, ?_⟩
    change (H.canonicalIsometry (H.canonicalIsometry.symm ⟨x, hx⟩) : TensorRegister n (Fin d)) = x
    rw [LinearIsometryEquiv.apply_symm_apply]

def canonicalTensorOperator (H : PhysicalHighestTensor n d) (X : Matrix (Fin d) (Fin d) ℂ) :
    H.CanonicalSector →L[ℂ] H.CanonicalSector :=
  cyclicTensorOperator (partitionHighestTensor H.weight H.weight_antitone)
    (fun a => (H.weight a : ℂ)) (partitionHighestTensor_cartan H.weight H.weight_antitone)
    (partitionHighestTensor_raising_zero H.weight H.weight_antitone) X

theorem canonicalEmbedding_tensorOperator (H : PhysicalHighestTensor n d)
    (X : Matrix (Fin d) (Fin d) ℂ) (x : H.CanonicalSector) :
    H.canonicalEmbedding (H.canonicalTensorOperator X x) = tensorOperator n X (H.canonicalEmbedding x) := by
  exact congrArg (fun y : H.sector => (y : TensorRegister n (Fin d)))
    (H.canonicalIsometry_tensorOperator X x)

end PhysicalHighestTensor

variable (L : List (PhysicalHighestTensor n d))

abbrev CanonicalSectorSum := lp (fun i : Fin L.length => (L.get i).CanonicalSector) 2

theorem canonicalSectorFamily_orthogonal
    (hL : OrthogonalFamily ℂ (fun i : Fin L.length => (L.get i).sector)
      (fun i => (L.get i).sector.subtypeₗᵢ)) :
    OrthogonalFamily ℂ (fun i : Fin L.length => (L.get i).CanonicalSector)
      (fun i => (L.get i).canonicalEmbedding) := by
  intro i j hij x y
  exact hL hij ((L.get i).canonicalIsometry x) ((L.get j).canonicalIsometry y)

def canonicalSectorHilbertSum
    (hL : OrthogonalFamily ℂ (fun i : Fin L.length => (L.get i).sector)
      (fun i => (L.get i).sector.subtypeₗᵢ))
    (hspan : (⨆ i : Fin L.length, (L.get i).sector) = ⊤) :
    IsHilbertSum ℂ (fun i : Fin L.length => (L.get i).CanonicalSector)
      (fun i => (L.get i).canonicalEmbedding) := by
  apply IsHilbertSum.mk (canonicalSectorFamily_orthogonal L hL)
  simp only [PhysicalHighestTensor.range_canonicalEmbedding, hspan]
  exact Submodule.le_topologicalClosure _

/-- The full physical register is unitarily equivalent to the finite Hilbert
sum of its canonical partition copies. Repeated labels are retained. -/
def physicalSchurIsometry
    (hL : OrthogonalFamily ℂ (fun i : Fin L.length => (L.get i).sector)
      (fun i => (L.get i).sector.subtypeₗᵢ))
    (hspan : (⨆ i : Fin L.length, (L.get i).sector) = ⊤) :
    TensorRegister n (Fin d) ≃ₗᵢ[ℂ] CanonicalSectorSum L :=
  (canonicalSectorHilbertSum L hL hspan).linearIsometryEquiv

theorem physicalSchurIsometry_symm_apply
    (hL : OrthogonalFamily ℂ (fun i : Fin L.length => (L.get i).sector)
      (fun i => (L.get i).sector.subtypeₗᵢ))
    (hspan : (⨆ i : Fin L.length, (L.get i).sector) = ⊤) (x : CanonicalSectorSum L) :
    (physicalSchurIsometry L hL hspan).symm x =
      ∑ i : Fin L.length, (L.get i).canonicalEmbedding (x i) := by
  rw [physicalSchurIsometry, IsHilbertSum.linearIsometryEquiv_symm_apply, tsum_fintype]

/-- The exact diagonal block action on the finite sum of partition copies. -/
def physicalSchurBlockOperator (X : Matrix (Fin d) (Fin d) ℂ) :
    CanonicalSectorSum L →ₗ[ℂ] CanonicalSectorSum L where
  toFun x := ⟨fun i => (L.get i).canonicalTensorOperator X (x i), Memℓp.all _⟩
  map_add' x y := by
    apply lp.ext
    funext i
    change (L.get i).canonicalTensorOperator X (x i + y i) = _
    exact map_add _ _ _
  map_smul' c x := by
    apply lp.ext
    funext i
    change (L.get i).canonicalTensorOperator X (c • x i) = _
    exact map_smul _ _ _

@[simp] theorem physicalSchurBlockOperator_apply (X : Matrix (Fin d) (Fin d) ℂ)
    (x : CanonicalSectorSum L) (i : Fin L.length) :
    physicalSchurBlockOperator L X x i = (L.get i).canonicalTensorOperator X (x i) := rfl

/-- Exact block diagonalization of every literal tensor power, not only of
unitaries or positive matrices. -/
theorem physicalSchurIsometry_intertwines
    (hL : OrthogonalFamily ℂ (fun i : Fin L.length => (L.get i).sector)
      (fun i => (L.get i).sector.subtypeₗᵢ))
    (hspan : (⨆ i : Fin L.length, (L.get i).sector) = ⊤)
    (X : Matrix (Fin d) (Fin d) ℂ) (x : TensorRegister n (Fin d)) :
    physicalSchurIsometry L hL hspan (tensorOperator n X x) =
      physicalSchurBlockOperator L X (physicalSchurIsometry L hL hspan x) := by
  apply (physicalSchurIsometry L hL hspan).symm.injective
  rw [LinearIsometryEquiv.symm_apply_apply, physicalSchurIsometry_symm_apply]
  simp only [physicalSchurBlockOperator_apply, PhysicalHighestTensor.canonicalEmbedding_tensorOperator,
    ← map_sum]
  rw [← physicalSchurIsometry_symm_apply L hL hspan, LinearIsometryEquiv.symm_apply_apply]

/-- One fixed exhaustive decomposition, obtained from the proved finite
orthogonal splitting theorem. -/
def tensorDecompositionList (n d : ℕ) : List (PhysicalHighestTensor n d) :=
  Classical.choose (exists_tensor_cyclic_decomposition n d)

theorem tensorDecompositionList_orthogonal (n d : ℕ) :
    OrthogonalFamily ℂ
      (fun i : Fin (tensorDecompositionList n d).length => ((tensorDecompositionList n d).get i).sector)
      (fun i => ((tensorDecompositionList n d).get i).sector.subtypeₗᵢ) :=
  (Classical.choose_spec (exists_tensor_cyclic_decomposition n d)).1

theorem tensorDecompositionList_spans (n d : ℕ) :
    (⨆ i : Fin (tensorDecompositionList n d).length, ((tensorDecompositionList n d).get i).sector) = ⊤ :=
  (Classical.choose_spec (exists_tensor_cyclic_decomposition n d)).2

def tensorSchurTransform (n d : ℕ) :
    TensorRegister n (Fin d) ≃ₗᵢ[ℂ] CanonicalSectorSum (tensorDecompositionList n d) :=
  physicalSchurIsometry (tensorDecompositionList n d)
    (tensorDecompositionList_orthogonal n d) (tensorDecompositionList_spans n d)

theorem tensorSchurTransform_intertwines (X : Matrix (Fin d) (Fin d) ℂ)
    (x : TensorRegister n (Fin d)) :
    tensorSchurTransform n d (tensorOperator n X x) =
      physicalSchurBlockOperator (tensorDecompositionList n d) X (tensorSchurTransform n d x) :=
  physicalSchurIsometry_intertwines (tensorDecompositionList n d)
    (tensorDecompositionList_orthogonal n d) (tensorDecompositionList_spans n d) X x

end Cloning.TensorLie
