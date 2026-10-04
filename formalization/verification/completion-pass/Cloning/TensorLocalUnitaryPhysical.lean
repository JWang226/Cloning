import Cloning.TensorLocalUnitaryGenerator
import Cloning.TensorCyclicSectorTransvection
import Mathlib.Analysis.CStarAlgebra.Matrix

/-! The exponential of the actual collective infinitesimal action equals the
literal tensor power of the one-particle exponential. -/
noncomputable section
open scoped BigOperators InnerProductSpace Matrix Topology
open NormedSpace Filter
namespace Cloning.TensorLocalUnitary
open Cloning.TensorLie Cloning.PCT Cloning.PCTPurificationChannel
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
variable {n d : ℕ}

open scoped Matrix.Norms.L2Operator in
local instance : NormedAlgebra ℚ (Matrix (Fin d) (Fin d) ℂ) :=
  NormedAlgebra.restrictScalars ℚ ℂ _

local instance : NormedAlgebra ℚ (TensorRegister n (Fin d) →L[ℂ] TensorRegister n (Fin d)) :=
  NormedAlgebra.restrictScalars ℚ ℂ _

open scoped Matrix.Norms.L2Operator in
def matrixExpPath (Y : Matrix (Fin d) (Fin d) ℂ) (z : ℂ) := exp (z • Y)

open scoped Matrix.Norms.L2Operator in
private def entryCLM (a b : Fin d) : Matrix (Fin d) (Fin d) ℂ →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap {
    toFun := fun X => X a b
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

open scoped Matrix.Norms.L2Operator in
theorem matrixExpPath_entry_hasDerivAt_zero (Y : Matrix (Fin d) (Fin d) ℂ) (a b : Fin d) :
    HasDerivAt (fun z : ℂ => matrixExpPath Y z a b) (Y a b) 0 := by
  have h := (entryCLM a b).hasFDerivAt.comp_hasDerivAt (0 : ℂ)
    (hasDerivAt_exp_smul_const Y (0 : ℂ))
  simpa [matrixExpPath, entryCLM] using h

@[simp] theorem matrixExpPath_zero (Y : Matrix (Fin d) (Fin d) ℂ) : matrixExpPath Y 0 = 1 := by
  simp [matrixExpPath]

open scoped Matrix.Norms.L2Operator in
theorem matrixExpPath_add (Y : Matrix (Fin d) (Fin d) ℂ) (z s : ℂ) :
    matrixExpPath Y (z+s) = matrixExpPath Y z * matrixExpPath Y s := by
  rw [matrixExpPath, add_smul]
  exact exp_add_of_commute ((Commute.refl Y).smul_left z |>.smul_right s)

/-- The collective action of an arbitrary one-particle matrix, on the complete
physical tensor register. -/
def collectiveMatrix (Y : Matrix (Fin d) (Fin d) ℂ) :
    TensorRegister n (Fin d) →L[ℂ] TensorRegister n (Fin d) :=
  ∑ a, ∑ b, Y a b • collectiveGenerator n a b

open scoped Matrix.Norms.Elementwise

private theorem slotMatrix_product (t : Fin n) (a b : Fin d) (w v : Fin n → Fin d) :
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

private theorem slotMatrix_sum (Y : Matrix (Fin d) (Fin d) ℂ)
    (t : Fin n) (w v : Fin n → Fin d) :
    (∏ j ∈ Finset.univ.erase t, (1 : Matrix (Fin d) (Fin d) ℂ) (w j) (v j)) *
        Y (w t) (v t) = ∑ a, ∑ b, Y a b * slotMatrix t a b w v := by
  rw [show Y (w t) (v t) = ∑ a, ∑ b,
      Y a b * Matrix.single a b (1 : ℂ) (w t) (v t) by
        simp [Matrix.single, Matrix.of_apply, ite_and]]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [← slotMatrix_product]
  ring

/-- Differentiating the literal tensor exponential at zero yields the actual
sum of one-slot matrix-unit generators. -/
theorem tensorOperator_matrixExpPath_hasDerivAt_zero (Y : Matrix (Fin d) (Fin d) ℂ) :
    HasDerivAt (fun z : ℂ => tensorOperator n (matrixExpPath Y z))
      (collectiveMatrix (n := n) Y) 0 := by
  have hm : HasDerivAt (fun z : ℂ => tensorPower n (matrixExpPath Y z))
      (∑ t : Fin n, ∑ a, ∑ b, Y a b • slotMatrix t a b) 0 := by
    apply hasDerivAt_pi.mpr
    intro w
    apply hasDerivAt_pi.mpr
    intro v
    have hh := HasDerivAt.fun_finset_prod
      (fun j (_ : j ∈ (Finset.univ : Finset (Fin n))) =>
        matrixExpPath_entry_hasDerivAt_zero Y (w j) (v j))
    convert hh using 1
    simp only [matrixExpPath_zero, smul_eq_mul, Matrix.sum_apply, Matrix.smul_apply]
    exact Finset.sum_congr rfl (fun t _ => (slotMatrix_sum Y t w v).symm)
  have hh := (registerMatrixCLM (I := Fin n → Fin d)).hasFDerivAt.comp_hasDerivAt (0 : ℂ) hm
  convert hh using 1
  simp only [collectiveMatrix, collectiveGenerator, tensorOperator, map_sum, map_smul,
    registerMatrixCLM_apply, slotGenerator, Finset.smul_sum]
  exact (Finset.sum_comm.trans (Finset.sum_congr rfl (fun _ _ => Finset.sum_comm))).symm

/-- The complete physical tensor path solves the collective-generator equation. -/
theorem tensorOperator_matrixExpPath_hasDerivAt (Y : Matrix (Fin d) (Fin d) ℂ) (z : ℂ) :
    HasDerivAt (fun s : ℂ => tensorOperator n (matrixExpPath Y s))
      (collectiveMatrix (n := n) Y * tensorOperator n (matrixExpPath Y z)) z := by
  have h0 := (tensorOperator_matrixExpPath_hasDerivAt_zero (n := n) Y).mul_const
    (tensorOperator n (matrixExpPath Y z))
  have hz := (show HasDerivAt _ _ (z-z) by simpa using h0).comp_sub_const z z
  simpa only [← tensorOperator_mul, ← matrixExpPath_add, sub_add_cancel] using hz

/-- Exact integration of the collective Lie action, on the full tensor space. -/
theorem tensorOperator_matrixExpPath (Y : Matrix (Fin d) (Fin d) ℂ) (z : ℂ) :
    tensorOperator n (matrixExpPath Y z) = exp (z • collectiveMatrix (n := n) Y) := by
  let A := collectiveMatrix (n := n) Y
  let F (s : ℂ) := exp ((-s) • A) * tensorOperator n (matrixExpPath Y s)
  have hd (s : ℂ) : HasDerivAt F 0 s := by
    have hbase := hasDerivAt_exp_smul_const A (-s)
    have hminus := (show HasDerivAt _ _ (0-s) by simpa using hbase).comp_const_sub 0 s
    simp only [zero_sub] at hminus
    have hplus := tensorOperator_matrixExpPath_hasDerivAt (n := n) Y s
    have hh := hminus.mul hplus
    convert hh using 1
    dsimp [A]
    simp only [neg_smul]
    noncomm_ring
  have hc : F z = F 0 := is_const_of_deriv_eq_zero
    (fun s => (hd s).differentiableAt) (fun s => (hd s).deriv) z 0
  have hcancel : exp (z • A) * exp ((-z) • A) = 1 := by
    rw [neg_smul, ← exp_add_of_commute (Commute.refl (z • A)).neg_right,
      add_neg_cancel, exp_zero]
  have hh := congrArg (fun S => exp (z • A) * S) hc
  simpa only [F, neg_zero, zero_smul, exp_zero, matrixExpPath_zero,
    tensorOperator_one, one_mul, mul_one, ← mul_assoc, hcancel] using hh

open scoped Matrix.Norms.L2Operator in
/-- The literal tensor power of a matrix exponential is the exponential of its
actual sum of one-slot generators. No representation-integration premise. -/
theorem tensorOperator_exp (Y : Matrix (Fin d) (Fin d) ℂ) :
    tensorOperator n (exp Y) = exp (collectiveMatrix (n := n) Y) := by
  simpa only [matrixExpPath, one_smul] using tensorOperator_matrixExpPath (n := n) Y 1

end Cloning.TensorLocalUnitary
