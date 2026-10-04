import Cloning.TensorRankOneDimension
import Cloning.PCTPhysicalWerner
import Cloning.GeneralSymmetricDimension
import Cloning.TensorLieHighestWeight

/-! The literal one-row cyclic tensor sector is exactly the physical symmetric subspace. -/
noncomputable section
open scoped BigOperators InnerProductSpace
namespace Cloning.TensorLie
open Cloning.PCT Cloning.TensorCloning Cloning.GeneralSymmetricOccupation
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

local instance {n d : ℕ} : FiniteDimensional ℂ (TensorRegister n (Fin d)) :=
  (registerBasis (Fin n → Fin d)).toOrthonormalBasis.toBasis.finiteDimensional_of_finite

theorem physicalSymmetric_generator_invariant {n d : ℕ}
    (a b : Fin d) {x : TensorRegister n (Fin d)} (hx : x ∈ physicalSymmetric n) :
    collectiveGenerator n a b x ∈ physicalSymmetric n := by
  intro w σ
  simp only [collectiveGenerator_apply,Function.comp_apply]
  have he (t : Fin n) : Function.update (w ∘ σ) t b =
      (Function.update w (σ t) b) ∘ σ := by
    exact (Function.update_comp_eq_of_injective w σ.injective t b).symm
  calc
    (∑ t, if w (σ t)=a then x (Function.update (fun i => w (σ i)) t b) else 0) =
      ∑ t, if w (σ t)=a then x (Function.update w (σ t) b) else 0 := by
        apply Finset.sum_congr rfl
        intro t _
        change (if w (σ t)=a then x (Function.update (w ∘ σ) t b) else 0)=_
        rw [he,hx]
    _ = _ := Equiv.sum_comp σ (fun t => if w t=a then x (Function.update w t b) else 0)

theorem highestTensor_mem_physicalSymmetric (n d : ℕ) :
    highestTensor n d ∈ physicalSymmetric n := by
  intro w σ
  have he : w ∘ σ = (fun _ => (0 : Fin (d+1))) ↔ w=(fun _ => 0) := by
    constructor
    · intro h
      funext i
      have hh := congrFun h (σ.symm i)
      simpa only [Function.comp_apply,Equiv.apply_symm_apply] using hh
    · intro h; subst w; rfl
  simp [highestTensor,registerBasis_apply,lp.single_apply,Pi.single_apply,he,eq_comm]

theorem cyclicSector_highestTensor_le_symmetric (n d : ℕ) :
    cyclicSector (highestTensor n d) ≤ physicalSymmetric n := by
  apply Submodule.span_le.mpr
  rintro x ⟨w,rfl⟩
  induction w with
  | nil => exact highestTensor_mem_physicalSymmetric n d
  | cons a w ih => exact physicalSymmetric_generator_invariant a.val.2 a.val.1 ih

theorem physicalSymmetric_finrank (n d : ℕ) :
    Module.finrank ℂ (physicalSymmetric (C := Fin (d+1)) n)=(n+d).choose d := by
  have hr : (isometry n (d+1)).toLinearMap.range=physicalSymmetric n := isometry_range n (d+1)
  rw [← hr,LinearMap.finrank_range_of_inj (isometry n (d+1)).injective,
    Module.finrank_eq_card_basis (registerBasis (Occupation n (d+1))).toOrthonormalBasis.toBasis,
    occupation_card]

theorem cyclicSector_highestTensor_eq_physicalSymmetric (n d : ℕ) :
    cyclicSector (highestTensor n d)=physicalSymmetric n := by
  apply Submodule.eq_of_le_of_finrank_eq (cyclicSector_highestTensor_le_symmetric n d)
  rw [physicalSymmetric_finrank]
  have hw (a : Fin (d+1)) : collectiveGenerator n a a (highestTensor n d)=
      (oneRowPartition n d a : ℂ) • highestTensor n d := by
    simpa only [oneRowPartition,Nat.cast_ite,Nat.cast_zero] using highestTensor_cartan n d a
  have h := physicalSector_finrank_eq_dimensionProduct (highestTensor n d) (oneRowPartition n d)
    (highestTensor_norm n d) hw (highestTensor_raising_zero n d)
  rw [dimensionProduct_oneRow] at h
  exact_mod_cast h

end Cloning.TensorLie
