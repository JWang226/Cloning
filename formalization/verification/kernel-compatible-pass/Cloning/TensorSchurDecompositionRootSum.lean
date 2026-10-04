import Cloning.TensorSchurDecompositionRadialTrace

/-! Exact diagonal and positive-root decomposition of the Casimir trace. -/
noncomputable section
open scoped BigOperators InnerProductSpace
namespace Cloning.TensorLie
open MvPolynomial
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
variable {n d : ℕ}

theorem sum_positiveRoot {M : Type*} [AddCommMonoid M] (f : Fin d → Fin d → M) :
    (∑ r : PositiveRoot d, f r.val.1 r.val.2) =
      ∑ a : Fin d, ∑ b : Fin d, if a < b then f a b else 0 := by
  classical
  rw [← Fintype.sum_prod_type (fun r : Fin d × Fin d => if r.1 < r.2 then f r.1 r.2 else 0)]
  rw [← Finset.sum_filter]
  exact (Finset.sum_subtype (Finset.univ.filter (fun r : Fin d × Fin d => r.1 < r.2))
    (by intro r; simp) (fun r => f r.1 r.2)).symm

theorem sum_matrix_eq_diagonal_add_roots {M : Type*} [AddCommMonoid M]
    (f : Fin d → Fin d → M) :
    (∑ a, ∑ b, f a b) = (∑ a, f a a) +
      ∑ r : PositiveRoot d, (f r.val.1 r.val.2 + f r.val.2 r.val.1) := by
  classical
  have hp (a b : Fin d) : f a b =
      (if a = b then f a b else 0) +
        ((if a < b then f a b else 0) + (if b < a then f a b else 0)) := by
    rcases lt_trichotomy a b with h | h | h
    · simp [h, ne_of_lt h, not_lt.mpr h.le]
    · simp [h]
    · simp [h, ne_of_gt h, not_lt.mpr h.le]
  calc
    _ = (∑ a, f a a) +
        ((∑ a, ∑ b, if a < b then f a b else 0) +
          (∑ a, ∑ b, if b < a then f a b else 0)) := by
      conv_lhs => arg 2; ext a; arg 2; ext b; rw [hp a b]
      simp only [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    _ = _ := by
      rw [Finset.sum_comm (f := fun a b : Fin d => if b < a then f a b else 0)]
      simp only [← sum_positiveRoot, Finset.sum_add_distrib]

theorem tensorWeightTrace_casimir_decomposition
    (T : TensorRegister n (Fin d) →L[ℂ] TensorRegister n (Fin d)) :
    tensorWeightTrace (collectiveCasimir n d * T) =
      (∑ a : Fin d, X a * pderiv a (X a * pderiv a (tensorWeightTrace T))) +
      ∑ r : PositiveRoot d,
        (tensorWeightTrace (collectiveGenerator n r.val.1 r.val.2 *
            collectiveGenerator n r.val.2 r.val.1 * T) +
          tensorWeightTrace (collectiveGenerator n r.val.2 r.val.1 *
            collectiveGenerator n r.val.1 r.val.2 * T)) := by
  simp only [collectiveCasimir, Finset.sum_mul, map_sum]
  rw [sum_matrix_eq_diagonal_add_roots]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  rw [euler_tensorWeightTrace, euler_tensorWeightTrace, ← mul_assoc]

end Cloning.TensorLie
