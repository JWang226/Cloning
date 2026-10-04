import Cloning.InfiniteTraceClassSeries
import Cloning.CoherentCoefficients

/-!
# Trace-norm continuity of actual infinite-dimensional pure states

Every rank-one operator is trace class with trace norm `‖x‖ * ‖y‖`.
The standard two-term expansion of the difference of vector projectors gives
trace-norm continuity, and hence the concrete binomial coefficient vectors
converge to their coherent Poisson projector in the trace-class Banach space.
The physical symmetric-tensor occupation embedding is not constructed here.
-/

noncomputable section

open scoped ComplexOrder InnerProductSpace Topology
open Filter

namespace Cloning.InfiniteTraceClass

set_option backward.isDefEq.respectTransparency false

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
theorem rankOne_mul_self_right (x y : H) :
    InnerProductSpace.rankOne ℂ x y * InnerProductSpace.rankOne ℂ y y =
      ((‖y‖ ^ 2 : ℝ) : ℂ) • InnerProductSpace.rankOne ℂ x y := by
  rw [ContinuousLinearMap.mul_def, InnerProductSpace.rankOne_comp_rankOne]
  congr 1
  simpa only [Complex.ofReal_pow] using inner_self_eq_norm_sq_to_K (𝕜 := ℂ) y

/-- General rank-one operators, including nonpositive ones, are trace class. -/
theorem isTraceClass_rankOne (x y : H) : IsTraceClass (InnerProductSpace.rankOne ℂ x y) := by
  by_cases hy : y = 0
  · subst y
    simpa using (isTraceClass_zero (H := H))
  have hy0 : ‖y‖ ≠ 0 := norm_ne_zero_iff.mpr hy
  have hc : ((‖y‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast pow_ne_zero 2 hy0
  have hprod : IsTraceClass
      (InnerProductSpace.rankOne ℂ x y * InnerProductSpace.rankOne ℂ y y) := by
    simpa only [mul_one] using
      (isTraceClass_mul_mul (A := InnerProductSpace.rankOne ℂ x y) (B := 1)
        (isTraceClass_rankOne_self y))
  rw [rankOne_mul_self_right] at hprod
  have h := isTraceClass_smul (((‖y‖ ^ 2 : ℝ) : ℂ)⁻¹) hprod
  simpa only [smul_smul, inv_mul_cancel₀ hc, one_smul] using h

/-- The true trace norm of a rank-one operator equals the product of the
Hilbert norms, with no finite-dimensional assumption. -/
theorem traceNorm_rankOne (x y : H) :
    traceNorm (InnerProductSpace.rankOne ℂ x y) (isTraceClass_rankOne x y) = ‖x‖ * ‖y‖ := by
  apply le_antisymm
  · by_cases hy : y = 0
    · subst y
      simp [traceNorm_zero]
    have hysq : 0 < ‖y‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hy)
    have hprod : IsTraceClass
        (InnerProductSpace.rankOne ℂ x y * InnerProductSpace.rankOne ℂ y y * 1) :=
      isTraceClass_mul_mul (A := InnerProductSpace.rankOne ℂ x y) (B := 1)
        (isTraceClass_rankOne_self y)
    have hle := traceNorm_mul_mul_le (isTraceClass_rankOne_self y) hprod
    have hnorm1 : ‖(1 : H →L[ℂ] H)‖ ≤ 1 :=
      ContinuousLinearMap.opNorm_le_bound _ zero_le_one (by intro z; simp)
    have hle' : traceNorm
        (InnerProductSpace.rankOne ℂ x y * InnerProductSpace.rankOne ℂ y y * 1) hprod ≤
        ‖x‖ * ‖y‖ * ‖y‖ ^ 2 := by
      apply hle.trans
      rw [InnerProductSpace.norm_rankOne, traceNorm_rankOne_self]
      exact mul_le_of_le_one_right (by positivity) hnorm1
    have heq : InnerProductSpace.rankOne ℂ x y * InnerProductSpace.rankOne ℂ y y * 1 =
        ((‖y‖ ^ 2 : ℝ) : ℂ) • InnerProductSpace.rankOne ℂ x y := by
      rw [mul_one, rankOne_mul_self_right]
    rw [traceNorm_transport heq hprod, traceNorm_smul _ (isTraceClass_rankOne x y),
      Complex.norm_of_nonneg (sq_nonneg _)] at hle'
    nlinarith
  · simpa only [InnerProductSpace.norm_rankOne] using
      opNorm_le_traceNorm (isTraceClass_rankOne x y)

/-- A general rank-one operator bundled in the trace-class Banach space. -/
def rankOneOperator (x y : H) : TraceClass H :=
  TraceClass.ofOperator (InnerProductSpace.rankOne ℂ x y) (isTraceClass_rankOne x y)

theorem norm_rankOneOperator (x y : H) : ‖rankOneOperator x y‖ = ‖x‖ * ‖y‖ :=
  traceNorm_rankOne x y

theorem vectorProjector_sub_eq (x y : H) :
    vectorProjector x - vectorProjector y =
      rankOneOperator (x - y) x + rankOneOperator y (x - y) := by
  apply Subtype.ext
  change InnerProductSpace.rankOne ℂ x x - InnerProductSpace.rankOne ℂ y y =
    InnerProductSpace.rankOne ℂ (x - y) x + InnerProductSpace.rankOne ℂ y (x - y)
  ext z
  simp only [ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.add_apply, InnerProductSpace.rankOne_apply,
    inner_sub_left, sub_smul, smul_sub]
  abel

/-- The standard pure-state trace-distance bound holds on any complex Hilbert
space. The norm on the left is the genuine trace norm. -/
theorem norm_vectorProjector_sub_le (x y : H) :
    ‖vectorProjector x - vectorProjector y‖ ≤ (‖x‖ + ‖y‖) * ‖x - y‖ := by
  rw [vectorProjector_sub_eq]
  calc
    _ ≤ ‖rankOneOperator (x - y) x‖ + ‖rankOneOperator y (x - y)‖ := norm_add_le _ _
    _ = _ := by rw [norm_rankOneOperator, norm_rankOneOperator]; ring

theorem vectorProjector_tendsto {α : Type*} {l : Filter α} {x : α → H} {y : H}
    (hx : Tendsto x l (𝓝 y)) :
    Tendsto (fun i => vectorProjector (x i)) l (𝓝 (vectorProjector y)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun i => norm_nonneg _)
    (fun i => norm_vectorProjector_sub_le (x i) y)
  simpa using (hx.norm.add_const ‖y‖).mul
    ((hx.sub_const y).norm)

/-- The concrete coherent-product coefficient states converge in genuine
infinite-dimensional trace norm. -/
theorem coherent_product_projector_tendsto (t : ℝ) (ht : 0 ≤ t) :
    Tendsto (fun L => vectorProjector (CoherentCoefficients.productVector t ht L)) atTop
      (𝓝 (vectorProjector (CoherentCoefficients.coherentVector t ht))) :=
  vectorProjector_tendsto (CoherentCoefficients.productVector_tendsto_coherentVector t ht)

end Cloning.InfiniteTraceClass
