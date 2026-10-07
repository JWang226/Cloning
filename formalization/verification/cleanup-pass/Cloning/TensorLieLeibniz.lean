import Cloning.TensorLieFiltration

/-! Literal matrix-unit action on tensor vectors and the collective Leibniz identity. -/

noncomputable section
open scoped BigOperators InnerProductSpace
namespace Cloning.TensorLie
open Cloning.PCT
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {A : Type*} [Fintype A] [DecidableEq A] {n : ℕ}

/-- One tensor-slot matrix unit acts on precisely its one-particle factor. -/
theorem slotGenerator_tensorVector (t : Fin n) (a b : A)
    (v : Fin n → Register A) :
    slotGenerator t a b (tensorVector v) =
      tensorVector (Function.update v t
        (InnerProductSpace.rankOne ℂ (registerBasis A a) (registerBasis A b) (v t))) := by
  ext w
  rw [slotGenerator_apply, tensorVector_apply, tensorVector_apply]
  let T := InnerProductSpace.rankOne ℂ (registerBasis A a) (registerBasis A b) (v t)
  have hleft : (∏ j : Fin n, v j (Function.update w t b j)) =
      v t b * ∏ j ∈ Finset.univ.erase t, v j (w j) := by
    rw [← Finset.mul_prod_erase Finset.univ
      (fun j => v j (Function.update w t b j)) (Finset.mem_univ t)]
    simp only [Function.update_self]
    congr 1
    apply Finset.prod_congr rfl
    intro j hj
    rw [Function.update_of_ne (Finset.mem_erase.mp hj).1]
  have hright : (∏ j : Fin n, Function.update v t T j (w j)) =
      T (w t) * ∏ j ∈ Finset.univ.erase t, v j (w j) := by
    rw [← Finset.mul_prod_erase Finset.univ
      (fun j => Function.update v t T j (w j)) (Finset.mem_univ t)]
    simp only [Function.update_self]
    congr 1
    apply Finset.prod_congr rfl
    intro j hj
    rw [Function.update_of_ne (Finset.mem_erase.mp hj).1]
  rw [hleft, hright]
  dsimp only [T]
  simp only [InnerProductSpace.rankOne_apply, registerBasis_apply, register_inner_single,
    lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, lp.single_apply, Pi.single_apply]
  by_cases h : w t = a <;> simp [h]

/-- The actual collective generator is the finite tensor Leibniz sum. -/
theorem collectiveGenerator_tensorVector (a b : A) (v : Fin n → Register A) :
    collectiveGenerator n a b (tensorVector v) =
      ∑ t : Fin n, tensorVector (Function.update v t
        (InnerProductSpace.rankOne ℂ (registerBasis A a) (registerBasis A b) (v t))) := by
  simp only [collectiveGenerator, ContinuousLinearMap.sum_apply, slotGenerator_tensorVector]

end Cloning.TensorLie

