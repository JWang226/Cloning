import Cloning.TensorCyclicSectorTensorPower
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Matrix.Normed

/-! Literal transvection actions commute with every collective-generator commutant. -/
noncomputable section
open scoped BigOperators InnerProductSpace Matrix Matrix.Norms.Elementwise
namespace Cloning.TensorLie
open Cloning.PCT Cloning.PCTPurificationChannel
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {n d : ℕ}

private theorem slotMatrix_product (t : Fin n) (a b : Fin d)
    (w v : Fin n → Fin d) :
    (∏ j ∈ Finset.univ.erase t, (1 : Matrix (Fin d) (Fin d) ℂ) (w j) (v j)) *
        Matrix.single a b (1 : ℂ) (w t) (v t) = slotMatrix t a b w v := by
  by_cases h : w t = a ∧ v = Function.update w t b
  · rcases h with ⟨ha, rfl⟩
    rw [slotMatrix, if_pos ⟨ha, rfl⟩]
    have hp : (∏ j ∈ Finset.univ.erase t,
        (1 : Matrix (Fin d) (Fin d) ℂ) (w j) (Function.update w t b j)) = 1 := by
      apply Finset.prod_eq_one
      intro j hj
      rw [Function.update_of_ne (Finset.mem_erase.mp hj).1]
      simp
    simp [hp, ha]
  · rw [slotMatrix, if_neg h]
    by_cases ha : w t = a
    · by_cases hb : v t = b
      · have hv : ∃ j, j ≠ t ∧ w j ≠ v j := by
          by_contra hn
          push_neg at hn
          apply h
          refine ⟨ha, funext (fun j => ?_)⟩
          by_cases hj : j = t
          · subst j
            simpa using hb
          · simpa [Function.update_of_ne hj] using (hn j hj).symm
        obtain ⟨j, hj, hwv⟩ := hv
        have hp : (∏ k ∈ Finset.univ.erase t,
            (1 : Matrix (Fin d) (Fin d) ℂ) (w k) (v k)) = 0 :=
          Finset.prod_eq_zero (i := j) (by simp [hj]) (by simp [Matrix.one_apply, hwv])
        rw [hp, zero_mul]
      · simp [Matrix.single, ha, hb, Ne.symm hb]
    · simp [Matrix.single, ha, Ne.symm ha]

/-- At the identity, the derivative of a physical tensor transvection is the
literal collective matrix unit. -/
theorem tensorOperator_transvection_hasDerivAt_zero (a b : Fin d) :
    HasDerivAt (fun z : ℂ => tensorOperator n (Matrix.transvection a b z))
      (collectiveGenerator n a b) 0 := by
  have hm : HasDerivAt (fun z : ℂ => tensorPower n (Matrix.transvection a b z))
      (∑ t : Fin n, slotMatrix t a b) 0 := by
    apply hasDerivAt_pi.mpr
    intro w
    apply hasDerivAt_pi.mpr
    intro v
    have hd (j : Fin n) : HasDerivAt
        (fun z : ℂ => Matrix.transvection a b z (w j) (v j))
        (Matrix.single a b (1 : ℂ) (w j) (v j)) 0 := by
      by_cases ha : a = w j <;> by_cases hb : b = v j <;>
        simp only [Matrix.transvection, Matrix.add_apply, Matrix.single, Matrix.of_apply, ha, hb,
          and_self, true_and, false_and, and_false, ite_true, ite_false, add_zero]
      · exact (hasDerivAt_id (0 : ℂ)).const_add _
      all_goals exact hasDerivAt_const _ _
    have hh := HasDerivAt.fun_finset_prod (fun j (_ : j ∈ (Finset.univ : Finset (Fin n))) => hd j)
    convert hh using 1
    simp only [Matrix.transvection_zero, smul_eq_mul, Matrix.sum_apply]
    exact Finset.sum_congr rfl (fun t _ => (slotMatrix_product t a b w v).symm)
  have hh := (registerMatrixCLM (I := Fin n → Fin d)).hasFDerivAt.comp_hasDerivAt (0 : ℂ) hm
  simpa only [tensorOperator, map_sum, registerMatrixCLM_apply, collectiveGenerator,
    slotGenerator] using hh

/-- The transvection path differentiates by left multiplication by the actual
collective generator. -/
theorem tensorOperator_transvection_hasDerivAt (a b : Fin d) (hab : a ≠ b) (z : ℂ) :
    HasDerivAt (fun s : ℂ => tensorOperator n (Matrix.transvection a b s))
      (collectiveGenerator n a b * tensorOperator n (Matrix.transvection a b z)) z := by
  have h0 := (tensorOperator_transvection_hasDerivAt_zero (n := n) a b).mul_const
    (tensorOperator n (Matrix.transvection a b z))
  have hz := (show HasDerivAt _ _ (z - z) by simpa using h0).comp_sub_const z z
  simpa only [← tensorOperator_mul, Matrix.transvection_mul_transvection_same a b hab,
    sub_add_cancel] using hz

/-- The same derivative can be written with the generator on the right. -/
theorem tensorOperator_transvection_hasDerivAt_right (a b : Fin d) (hab : a ≠ b) (z : ℂ) :
    HasDerivAt (fun s : ℂ => tensorOperator n (Matrix.transvection a b s))
      (tensorOperator n (Matrix.transvection a b z) * collectiveGenerator n a b) z := by
  have h0 := (tensorOperator_transvection_hasDerivAt_zero (n := n) a b).const_mul
    (tensorOperator n (Matrix.transvection a b z))
  have hz := (show HasDerivAt _ _ (z - z) by simpa using h0).comp_sub_const z z
  have hs (x : ℂ) : z + (x - z) = x := by ring
  simpa only [← tensorOperator_mul, Matrix.transvection_mul_transvection_same a b hab, hs] using hz

/-- A matrix-unit commutant commutes with the corresponding literal tensor
transvection, with no representation-integration premise. -/
theorem tensorOperator_transvection_commutes
    (T : TensorRegister n (Fin d) →L[ℂ] TensorRegister n (Fin d))
    (a b : Fin d) (hab : a ≠ b)
    (hT : T * collectiveGenerator n a b = collectiveGenerator n a b * T) (z : ℂ) :
    T * tensorOperator n (Matrix.transvection a b z) =
      tensorOperator n (Matrix.transvection a b z) * T := by
  let F (s : ℂ) := tensorOperator n (Matrix.transvection a b (-s)) * T *
    tensorOperator n (Matrix.transvection a b s)
  have hd (s : ℂ) : HasDerivAt F 0 s := by
    have hbase := tensorOperator_transvection_hasDerivAt_right (n := n) a b hab (-s)
    have hminus := (show HasDerivAt _ _ (0 - s) by simpa using hbase).comp_const_sub 0 s
    simp only [zero_sub] at hminus
    have hplus := tensorOperator_transvection_hasDerivAt (n := n) a b hab s
    have hh := (hminus.mul_const T).mul hplus
    convert hh using 1
    simp only [neg_mul]
    rw [mul_assoc (tensorOperator n (Matrix.transvection a b (-s)))
      (collectiveGenerator n a b) T, ← hT]
    noncomm_ring
  have hc : F z = F 0 := is_const_of_deriv_eq_zero
    (fun s => (hd s).differentiableAt) (fun s => (hd s).deriv) z 0
  have hcancel : tensorOperator n (Matrix.transvection a b z) *
      tensorOperator n (Matrix.transvection a b (-z)) = 1 := by
    rw [← tensorOperator_mul, Matrix.transvection_mul_transvection_same a b hab,
      add_neg_cancel, Matrix.transvection_zero, tensorOperator_one]
  have hh := congrArg (fun S => tensorOperator n (Matrix.transvection a b z) * S) hc
  simpa only [F, neg_zero, Matrix.transvection_zero, tensorOperator_one, one_mul,
    mul_one, ← mul_assoc, hcancel] using hh

end Cloning.TensorLie
