import Cloning.TensorCartanProduct
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! Actual orthonormal coordinates on the physical tensor-product subspace. -/
noncomputable section
open scoped BigOperators InnerProductSpace
namespace Cloning.TensorLie
open Cloning.PCT
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {n m d : ℕ}

@[simp] theorem tensorJoin_sum_left {ι : Type*} (s : Finset ι)
    (x : ι → TensorRegister n (Fin d)) (y : TensorRegister m (Fin d)) :
    tensorJoin (∑ i ∈ s, x i) y = ∑ i ∈ s, tensorJoin (x i) y := by
  ext w
  simp [tensorJoin_apply, lp.coeFn_sum, Finset.sum_mul]

@[simp] theorem tensorJoin_sum_right {ι : Type*} (s : Finset ι)
    (x : TensorRegister n (Fin d)) (y : ι → TensorRegister m (Fin d)) :
    tensorJoin x (∑ i ∈ s, y i) = ∑ i ∈ s, tensorJoin x (y i) := by
  ext w
  simp [tensorJoin_apply, lp.coeFn_sum, Finset.mul_sum]

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (P : Submodule ℂ (TensorRegister n (Fin d)))
    (Q : Submodule ℂ (TensorRegister m (Fin d)))
    (bP : OrthonormalBasis I ℂ P) (bQ : OrthonormalBasis J ℂ Q)

def productSectorFrame (ij : I × J) : tensorProductSector P Q :=
  ⟨tensorJoin (bP ij.1) (bQ ij.2),
    tensorJoin_mem_tensorProductSector P Q (bP ij.1).property (bQ ij.2).property⟩

@[simp] theorem productSectorFrame_coe (ij : I × J) :
    (productSectorFrame P Q bP bQ ij : TensorRegister (n + m) (Fin d)) =
      tensorJoin (bP ij.1) (bQ ij.2) := rfl

theorem productSectorFrame_orthonormal : Orthonormal ℂ (productSectorFrame P Q bP bQ) := by
  rw [orthonormal_iff_ite]
  intro i j
  change ⟪tensorJoin (bP i.1 : TensorRegister n (Fin d)) (bQ i.2 : TensorRegister m (Fin d)),
    tensorJoin (bP j.1 : TensorRegister n (Fin d)) (bQ j.2 : TensorRegister m (Fin d))⟫_ℂ = _
  rw [tensorJoin_inner]
  change ⟪bP i.1, bP j.1⟫_ℂ * ⟪bQ i.2, bQ j.2⟫_ℂ = _
  rw [orthonormal_iff_ite.mp bP.orthonormal, orthonormal_iff_ite.mp bQ.orthonormal]
  by_cases h1 : i.1 = j.1 <;> by_cases h2 : i.2 = j.2 <;>
    simp [h1, h2, Prod.ext_iff]

theorem tensorJoin_basis_expansion (x : P) (y : Q) :
    tensorJoin (x : TensorRegister n (Fin d)) (y : TensorRegister m (Fin d)) =
      ∑ i : I, ∑ j : J, (bP.repr x i * bQ.repr y j) •
        tensorJoin (bP i) (bQ j) := by
  have hx := congrArg (fun z : P => (z : TensorRegister n (Fin d))) (bP.sum_repr x)
  have hy := congrArg (fun z : Q => (z : TensorRegister m (Fin d))) (bQ.sum_repr y)
  simp only [Submodule.coe_sum, Submodule.coe_smul] at hx hy
  conv_lhs => rw [← hx, ← hy]
  simp only [tensorJoin_sum_left, tensorJoin_sum_right, tensorJoin_smul_left,
    tensorJoin_smul_right, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp only [mul_comm]

/-- Every literal product of sector vectors lies in the span of the product
orthonormal frame, by finite expansions in the two actual sector bases. -/
theorem productSectorFrame_spans :
    ⊤ ≤ Submodule.span ℂ (Set.range (productSectorFrame P Q bP bQ)) := by
  let S := Submodule.span ℂ (Set.range (productSectorFrame P Q bP bQ))
  let T := S.map (tensorProductSector P Q).subtype
  have hT : tensorProductSector P Q ≤ T := by
    apply Submodule.span_le.mpr
    rintro z ⟨x, hx, y, hy, rfl⟩
    rw [tensorJoin_basis_expansion P Q bP bQ ⟨x, hx⟩ ⟨y, hy⟩]
    apply T.sum_mem
    intro i hi
    apply T.sum_mem
    intro j hj
    apply T.smul_mem
    exact ⟨productSectorFrame P Q bP bQ (i, j),
      Submodule.subset_span (Set.mem_range_self (i, j)), rfl⟩
  intro x _
  obtain ⟨y, hy, he⟩ := hT x.property
  have hxy : y = x := Subtype.ext he
  rw [← hxy]
  exact hy

/-- An actual complete orthonormal basis of the physical product subspace. -/
def productSectorBasis : OrthonormalBasis (I × J) ℂ (tensorProductSector P Q) :=
  OrthonormalBasis.mk (productSectorFrame_orthonormal P Q bP bQ)
    (productSectorFrame_spans P Q bP bQ)

@[simp] theorem productSectorBasis_apply (ij : I × J) :
    productSectorBasis P Q bP bQ ij = productSectorFrame P Q bP bQ ij := by
  simp [productSectorBasis]

end Cloning.TensorLie
