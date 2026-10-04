import Cloning.TensorFlatProjectorRestriction

/-! Tensor products of actual sector isometries on the literal product subspaces. -/
noncomputable section
open scoped BigOperators InnerProductSpace
namespace Cloning.TensorLie
open Cloning.PCT
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
local instance (n d : ℕ) : FiniteDimensional ℂ (TensorRegister n (Fin d)) :=
  (registerBasis (Fin n → Fin d)).toOrthonormalBasis.toBasis.finiteDimensional_of_finite
variable {n m n' m' d d' : ℕ}
variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
variable (P : Submodule ℂ (TensorRegister n (Fin d))) (Q : Submodule ℂ (TensorRegister m (Fin d)))
    (P' : Submodule ℂ (TensorRegister n' (Fin d'))) (Q' : Submodule ℂ (TensorRegister m' (Fin d')))
    (bP : OrthonormalBasis I ℂ P) (bQ : OrthonormalBasis J ℂ Q)
    (f : P →ₗᵢ[ℂ] P') (g : Q →ₗᵢ[ℂ] Q')

def productIsometryFrame (ij : I × J) : tensorProductSector P' Q' :=
  ⟨tensorJoin (f (bP ij.1)) (g (bQ ij.2)),
    tensorJoin_mem_tensorProductSector P' Q' (f (bP ij.1)).property (g (bQ ij.2)).property⟩

theorem productIsometryFrame_orthonormal :
    Orthonormal ℂ (productIsometryFrame P Q P' Q' bP bQ f g) := by
  rw [orthonormal_iff_ite]
  intro i j
  change ⟪tensorJoin (f (bP i.1) : TensorRegister n' (Fin d')) (g (bQ i.2) : TensorRegister m' (Fin d')),
    tensorJoin (f (bP j.1) : TensorRegister n' (Fin d')) (g (bQ j.2) : TensorRegister m' (Fin d'))⟫_ℂ = _
  rw [tensorJoin_inner]
  change ⟪f (bP i.1), f (bP j.1)⟫_ℂ * ⟪g (bQ i.2), g (bQ j.2)⟫_ℂ = _
  rw [f.inner_map_map, g.inner_map_map,
    orthonormal_iff_ite.mp bP.orthonormal, orthonormal_iff_ite.mp bQ.orthonormal]
  by_cases hi : i.1 = j.1 <;> by_cases hj : i.2 = j.2 <;> simp [hi,hj,Prod.ext_iff]

/-- The Hilbert tensor product of two supplied genuine sector isometries. -/
def productSectorIsometry : tensorProductSector P Q →ₗᵢ[ℂ] tensorProductSector P' Q' :=
  (productIsometryFrame_orthonormal P Q P' Q' bP bQ f g).orthogonalFamily.linearIsometry.comp
    (((productSectorBasis P Q bP bQ).repr.trans
      (registerBasis (I×J)).toOrthonormalBasis.repr.symm).toLinearIsometry)

@[simp] theorem productSectorIsometry_basis (ij : I × J) :
    productSectorIsometry P Q P' Q' bP bQ f g (productSectorBasis P Q bP bQ ij) =
      productIsometryFrame P Q P' Q' bP bQ f g ij := by
  have he : ((productSectorBasis P Q bP bQ).repr.trans
      (registerBasis (I×J)).toOrthonormalBasis.repr.symm) (productSectorBasis P Q bP bQ ij) =
        registerBasis (I×J) ij := by
    apply (registerBasis (I×J)).toOrthonormalBasis.repr.injective
    simp only [LinearIsometryEquiv.trans_apply, LinearIsometryEquiv.apply_symm_apply]
    rw [OrthonormalBasis.repr_self, ← HilbertBasis.coe_toOrthonormalBasis,
      OrthonormalBasis.repr_self]
  change (productIsometryFrame_orthonormal P Q P' Q' bP bQ f g).orthogonalFamily.linearIsometry
    (((productSectorBasis P Q bP bQ).repr.trans
      (registerBasis (I×J)).toOrthonormalBasis.repr.symm) (productSectorBasis P Q bP bQ ij)) = _
  rw [he, registerBasis_apply, OrthogonalFamily.linearIsometry_apply_single]
  exact one_smul ℂ _

/-- Its action on literal product vectors is exactly the product of the maps. -/
theorem productSectorIsometry_tensorJoin (x : P) (y : Q) :
    (productSectorIsometry P Q P' Q' bP bQ f g
      ⟨tensorJoin x y,tensorJoin_mem_tensorProductSector P Q x.property y.property⟩ :
        TensorRegister (n'+m') (Fin d')) = tensorJoin (f x) (g y) := by
  have hs : (⟨tensorJoin x y,tensorJoin_mem_tensorProductSector P Q x.property y.property⟩ :
      tensorProductSector P Q) =
      ∑ i : I, ∑ j : J, (bP.repr x i * bQ.repr y j) • productSectorBasis P Q bP bQ (i,j) := by
    apply Subtype.ext
    simpa only [Submodule.coe_sum, Submodule.coe_smul, productSectorBasis_apply,
      productSectorFrame_coe] using tensorJoin_basis_expansion P Q bP bQ x y
  have ht : tensorJoin (f x : TensorRegister n' (Fin d')) (g y : TensorRegister m' (Fin d')) =
      ∑ i : I, ∑ j : J, (bP.repr x i * bQ.repr y j) •
        tensorJoin (f (bP i) : TensorRegister n' (Fin d')) (g (bQ j) : TensorRegister m' (Fin d')) := by
    have hx := congrArg (fun z : P' => (z : TensorRegister n' (Fin d')))
      (congrArg f (bP.sum_repr x))
    have hy := congrArg (fun z : Q' => (z : TensorRegister m' (Fin d')))
      (congrArg g (bQ.sum_repr y))
    simp only [map_sum, map_smul, Submodule.coe_sum, Submodule.coe_smul] at hx hy
    conv_lhs => rw [← hx, ← hy]
    simp only [tensorJoin_sum_left, tensorJoin_sum_right, tensorJoin_smul_left,
      tensorJoin_smul_right, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp only [mul_comm]
  rw [hs, ht]
  simp only [map_sum, map_smul, productSectorIsometry_basis, Submodule.coe_sum,
    Submodule.coe_smul, productIsometryFrame]

end Cloning.TensorLie
