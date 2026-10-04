import Cloning.InfiniteCompletelyPositive
import Cloning.InfiniteFidelityWeighted

/-! An attaining positive block witness for actual trace-class root fidelity. -/

namespace Cloning.InfiniteFidelity

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped ComplexOrder InnerProductSpace BigOperators
open InfiniteTraceClass InfiniteTraceClass.HilbertSchmidt

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The canonical self-adjoint two-by-two operator block. -/
def fidelityBlock (A B X : TraceClass H) : Fin 2 → Fin 2 → TraceClass H :=
  fun i j => if i = 0 then (if j = 0 then A else X)
    else (if j = 0 then TraceClass.adjoint X else B)

lemma contraction_quadratic_nonneg (U : H →L[ℂ] H) (hU : ‖U‖ ≤ 1) (x y : H) :
    0 ≤ ⟪x, x⟫_ℂ + ⟪x, (star U) y⟫_ℂ + (⟪y, U x⟫_ℂ + ⟪y, y⟫_ℂ) := by
  have hnorm : ‖U x‖ ≤ ‖x‖ := by
    calc
      ‖U x‖ ≤ ‖U‖ * ‖x‖ := U.le_opNorm x
      _ ≤ 1 * ‖x‖ := mul_le_mul_of_nonneg_right hU (norm_nonneg x)
      _ = ‖x‖ := one_mul _
  have hs : 0 ≤ ‖x‖ ^ 2 - ‖U x‖ ^ 2 :=
    sub_nonneg.mpr ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 hnorm)
  have heq : ⟪x, x⟫_ℂ + ⟪x, (star U) y⟫_ℂ + (⟪y, U x⟫_ℂ + ⟪y, y⟫_ℂ) =
      ⟪U x + y, U x + y⟫_ℂ + ((‖x‖ ^ 2 - ‖U x‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_add_left, inner_add_right, inner_add_right]
    simp only [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right,
      inner_self_eq_norm_sq_to_K, RCLike.ofReal_eq_complex_ofReal]
    push_cast
    ring
  rw [heq]
  have hp : 0 ≤ ⟪U x + y, U x + y⟫_ℂ := by
    simp only [inner_self_eq_norm_sq_to_K, RCLike.ofReal_eq_complex_ofReal,
      ← Complex.ofReal_pow, Complex.nonneg_iff, Complex.ofReal_re, Complex.ofReal_im]
    exact ⟨sq_nonneg _, trivial⟩
  exact add_nonneg hp (by exact_mod_cast hs)

lemma contractionWitness_traceClass {A B : H →L[ℂ] H} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hTA : IsTraceClass A) (hTB : IsTraceClass B) (U : H →L[ℂ] H) :
    IsTraceClass (CFC.sqrt A * star U * CFC.sqrt B) :=
  isTraceClass_mul_of_isHilbertSchmidt
    (isHilbertSchmidt_mul_right (isHilbertSchmidt_sqrt hA hTA))
    (isHilbertSchmidt_sqrt hB hTB)

def contractionWitness (A B : TraceClass H) (hA : 0 ≤ A.1) (hB : 0 ≤ B.1)
    (U : H →L[ℂ] H) : TraceClass H :=
  TraceClass.ofOperator (CFC.sqrt A.1 * star U * CFC.sqrt B.1)
    (contractionWitness_traceClass hA hB A.2 B.2 U)

lemma contractionWitness_blockPositive (A B : TraceClass H) (hA : 0 ≤ A.1) (hB : 0 ≤ B.1)
    (U : H →L[ℂ] H) (hU : ‖U‖ ≤ 1) :
    BlockPositive (fidelityBlock A B (contractionWitness A B hA hB U)) := by
  intro x
  have hsA : IsSelfAdjoint (CFC.sqrt A.1) := .of_nonneg (CFC.sqrt_nonneg A.1)
  have hsB : IsSelfAdjoint (CFC.sqrt B.1) := .of_nonneg (CFC.sqrt_nonneg B.1)
  have hdA : ⟪x 0, A.1 (x 0)⟫_ℂ = ⟪CFC.sqrt A.1 (x 0), CFC.sqrt A.1 (x 0)⟫_ℂ := by
    conv_lhs => rw [← CFC.sqrt_mul_sqrt_self A.1 hA]
    exact (hsA.isSymmetric (x 0) (CFC.sqrt A.1 (x 0))).symm
  have hdB : ⟪x 1, B.1 (x 1)⟫_ℂ = ⟪CFC.sqrt B.1 (x 1), CFC.sqrt B.1 (x 1)⟫_ℂ := by
    conv_lhs => rw [← CFC.sqrt_mul_sqrt_self B.1 hB]
    exact (hsB.isSymmetric (x 1) (CFC.sqrt B.1 (x 1))).symm
  have hcross : ⟪x 0, (CFC.sqrt A.1 * star U * CFC.sqrt B.1) (x 1)⟫_ℂ =
      ⟪CFC.sqrt A.1 (x 0), star U (CFC.sqrt B.1 (x 1))⟫_ℂ := by
    exact (hsA.isSymmetric (x 0) (star U (CFC.sqrt B.1 (x 1)))).symm
  have hstar : star (CFC.sqrt A.1 * star U * CFC.sqrt B.1) =
      CFC.sqrt B.1 * U * CFC.sqrt A.1 := by
    simp only [star_mul, star_star, hsA.star_eq, hsB.star_eq, mul_assoc]
  have hcross' : ⟪x 1, star (CFC.sqrt A.1 * star U * CFC.sqrt B.1) (x 0)⟫_ℂ =
      ⟪CFC.sqrt B.1 (x 1), U (CFC.sqrt A.1 (x 0))⟫_ℂ := by
    rw [hstar]
    exact (hsB.isSymmetric (x 1) (U (CFC.sqrt A.1 (x 0)))).symm
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  simp only [Fin.sum_univ_two, fidelityBlock, Fin.isValue, h10, ↓reduceIte,
    contractionWitness, TraceClass.adjoint, TraceClass.ofOperator_coe]
  rw [hdA, hdB, hcross, hcross']
  exact contraction_quadratic_nonneg U hU _ _

/-- The polar factor determines a concrete attaining block witness. -/
def polarWitness (A B : TraceClass H) (hA : 0 ≤ A.1) (hB : 0 ≤ B.1) : TraceClass H :=
  contractionWitness A B hA hB (Polar.polarFactor (CFC.sqrt B.1 * CFC.sqrt A.1))

lemma polarWitness_blockPositive (A B : TraceClass H) (hA : 0 ≤ A.1) (hB : 0 ≤ B.1) :
    BlockPositive (fidelityBlock A B (polarWitness A B hA hB)) :=
  contractionWitness_blockPositive A B hA hB _ (Polar.polarFactor_opNorm_le _)

lemma polarWitness_trace (A B : TraceClass H) (hA : 0 ≤ A.1) (hB : 0 ≤ B.1) :
    (traceCLM (polarWitness A B hA hB)).re = fidelity A.1 B.1 hA hB A.2 B.2 := by
  let T := CFC.sqrt B.1 * CFC.sqrt A.1
  let U := Polar.polarFactor T
  have hR := isHilbertSchmidt_sqrt hA A.2
  have hS : IsHilbertSchmidt (star U * CFC.sqrt B.1) :=
    isHilbertSchmidt_mul_left (isHilbertSchmidt_sqrt hB B.2)
  have hcycle := trace_mul_cycle_hilbertSchmidt hR hS
  have hfactor : (star U * CFC.sqrt B.1) * CFC.sqrt A.1 = CFC.abs T := by
    rw [mul_assoc]
    exact Polar.star_polarFactor_mul_self T
  have hTC := sqrt_product_traceClass hB hA B.2 A.2
  have htrace : (traceCLM (polarWitness A B hA hB)).re =
      (trace (CFC.abs T) (isTraceClass_abs hTC)).re := by
    change (trace (CFC.sqrt A.1 * star U * CFC.sqrt B.1) _).re = _
    have h := congrArg Complex.re hcycle
    simpa only [hfactor, mul_assoc] using h
  rw [htrace, trace_re_eq_traceNorm (CFC.abs_nonneg T), traceNorm_abs]
  exact fidelity_comm hB hA B.2 A.2

lemma exists_fidelityBlock_witness (A B : TraceClass H) (hA : 0 ≤ A.1) (hB : 0 ≤ B.1) :
    ∃ X : TraceClass H, BlockPositive (fidelityBlock A B X) ∧
      (traceCLM X).re = fidelity A.1 B.1 hA hB A.2 B.2 :=
  ⟨polarWitness A B hA hB, polarWitness_blockPositive A B hA hB,
    polarWitness_trace A B hA hB⟩

end
end Cloning.InfiniteFidelity
