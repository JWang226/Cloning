import Cloning.TensorLieLeibniz
import Mathlib.LinearAlgebra.Alternating.Basic

/-! Actual antisymmetric tensors and the matrix-unit action on their factors. -/
noncomputable section
open scoped BigOperators InnerProductSpace ComplexOrder
namespace Cloning.TensorLie
open Cloning.PCT
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {A : Type*} [Fintype A] [DecidableEq A] {n : ℕ}

private theorem tensorVector_update_apply [DecidableEq (Fin n)] (v : Fin n → Register A) (i : Fin n)
    (x : Register A) (w : Fin n → A) :
    tensorVector (Function.update v i x) w =
      x (w i) * ∏ j ∈ Finset.univ.erase i, v j (w j) := by
  rw [tensorVector_apply, ← Finset.mul_prod_erase Finset.univ
    (fun j => Function.update v i x j (w j)) (Finset.mem_univ i)]
  simp only [Function.update_self]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  rw [Function.update_of_ne (Finset.mem_erase.mp hj).1]

/-- The literal product of one-particle coefficients, packaged multilinearly. -/
def tensorMultilinear (n : ℕ) :
    MultilinearMap ℂ (fun _ : Fin n => Register A) (TensorRegister n A) where
  toFun := tensorVector
  map_update_add' v i x y := by
    ext w
    simp only [tensorVector_update_apply, lp.coeFn_add, Pi.add_apply, add_mul]
  map_update_smul' v i c x := by
    ext w
    simp only [tensorVector_update_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, mul_assoc]

@[simp] theorem tensorMultilinear_apply (v : Fin n → Register A) :
    tensorMultilinear n v = tensorVector v := rfl

/-- Unnormalized antisymmetric tensor, with every sign and permutation explicit. -/
def wedgeTensor (n : ℕ) : (Register A) [⋀^Fin n]→ₗ[ℂ] TensorRegister n A :=
  (tensorMultilinear n).alternatization

theorem wedgeTensor_apply (v : Fin n → Register A) :
    wedgeTensor n v = ∑ σ : Equiv.Perm (Fin n),
      Equiv.Perm.sign σ • tensorVector (fun i => v (σ i)) := by
  simp [wedgeTensor, MultilinearMap.alternatization_apply,
    MultilinearMap.domDomCongr_apply]

/-- The collective tensor action is the alternating Leibniz sum. -/
theorem collectiveGenerator_wedgeTensor (a b : A) (v : Fin n → Register A) :
    collectiveGenerator n a b (wedgeTensor n v) =
      ∑ i : Fin n, wedgeTensor n (Function.update v i
        (InnerProductSpace.rankOne ℂ (registerBasis A a) (registerBasis A b) (v i))) := by
  rw [wedgeTensor_apply, map_sum]
  simp only [map_zsmul_unit, collectiveGenerator_tensorVector, Finset.smul_sum]
  simp_rw [wedgeTensor_apply]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro σ _
  conv_rhs => rw [← Equiv.sum_comp σ]
  apply Finset.sum_congr rfl
  intro i _
  congr 2
  funext j
  by_cases h : j = i
  · subst j; simp
  · simp [Function.update_of_ne h, Function.update_of_ne (σ.injective.ne h)]

@[simp] theorem tensorVector_basis (f : Fin n → A) :
    tensorVector (fun i => registerBasis A (f i)) = registerBasis (Fin n → A) f := by
  ext w
  simp only [tensorVector_apply, registerBasis_apply, lp.single_apply, Pi.single_apply]
  by_cases h : w = f
  · subst w; simp
  · rw [if_neg h]
    obtain ⟨i, hi⟩ : ∃ i, w i ≠ f i := by
      by_contra hn
      exact h (funext (fun i => not_not.mp (not_exists.mp hn i)))
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

/-- Injective factors have an explicit nonzero coefficient, including the empty tensor. -/
theorem wedgeTensor_basis_coefficient (f : Fin n ↪ A) :
    wedgeTensor n (fun i => registerBasis A (f i)) f = 1 := by
  rw [wedgeTensor_apply]
  simp only [tensorVector_basis, lp.coeFn_sum, Finset.sum_apply]
  rw [Finset.sum_eq_single (Equiv.refl (Fin n))]
  · simp [registerBasis_apply]
  · intro σ _ hσ
    have hf : (fun i => f (σ i)) ≠ f := by
      intro he
      apply hσ
      apply Equiv.ext
      intro i
      exact f.injective (congrFun he i)
    simp [registerBasis_apply, lp.single_apply, hf, Ne.symm hf, Units.smul_def]
  · simp

theorem wedgeTensor_basis_ne_zero (f : Fin n ↪ A) :
    wedgeTensor n (fun i => registerBasis A (f i)) ≠ 0 := by
  intro h
  have hh := wedgeTensor_basis_coefficient f
  rw [h] at hh
  simpa using hh

@[simp] theorem matrixUnit_basis (a b c : A) :
    InnerProductSpace.rankOne ℂ (registerBasis A a) (registerBasis A b)
      (registerBasis A c) = if b = c then registerBasis A a else 0 := by
  rw [InnerProductSpace.rankOne_apply,
    orthonormal_iff_ite.mp (registerBasis A).orthonormal]
  split_ifs <;> simp_all

end Cloning.TensorLie
