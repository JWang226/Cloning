import Cloning.HybridProduct
import Cloning.InfiniteFidelityRegularized
import Cloning.InfiniteTraceClassPairing

/-!
# Weighted hybrid fidelity bound

This is the continuous classical–quantum inequality in Appendix C. The output
is an arbitrary positive operator-valued integrable density, the target is the
actual field `g(y) T`, and the bounded positive witness may have no bounded
inverse. Its inverse moment is controlled through genuine bounded regularizations.
-/
noncomputable section
open scoped ComplexOrder InnerProductSpace Topology
open MeasureTheory Filter Cloning.InfiniteTraceClass Cloning.InfiniteFidelity
namespace Cloning.Hybrid
set_option backward.isDefEq.respectTransparency false
variable {Ω H : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The real trace of a trace-class operator against a bounded witness. -/
def witnessMoment (A : TraceClass H) (W : H →L[ℂ] H) : ℝ :=
  (tracePairingCLM A W).re

lemma witnessMoment_nonneg (A : PositiveTraceClass H) {W : H →L[ℂ] H} (hW : 0 ≤ W) :
    0 ≤ witnessMoment A.1 W :=
  trace_re_mul_nonneg_of_nonneg_left_traceClass A.2 hW A.1.2

lemma witnessMoment_real_smul (a : ℝ) (A : TraceClass H) (W : H →L[ℂ] H) :
    witnessMoment ((a : ℂ) • A) W = a * witnessMoment A W := by
  simp only [witnessMoment, map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

namespace PositiveField

/-- The pointwise weighted bound for the actual product target density. -/
theorem rootFidelity_product_sq_le (R : PositiveField (H := H) μ)
    (g : Ω → ℝ) (hg : Integrable g μ) (hgn : ∀ x, 0 ≤ g x) (T : DensityState H)
    {W : H →L[ℂ] H} (hW : 0 ≤ W) {M : ℝ} (hM : 0 ≤ M)
    (hInv : ∀ ε : ℝ, 0 < ε →
      witnessMoment (TraceClass.ofOperator T.op T.traceClass)
        (CFC.rpow (regularizedWeight W ε) (-1)) ≤ M) (x : Ω) :
    PositiveTraceClass.rootFidelity (R.value x) ((product g hg hgn T).value x) ^ 2 ≤
      witnessMoment (R.value x).1 W * (g x * M) := by
  apply fidelity_sq_le_of_regularized_inverse_moment (R.value x).2
    ((product g hg hgn T).value x).2 hW (R.value x).1.2
    ((product g hg hgn T).value x).1.2 (mul_nonneg (hgn x) hM)
  intro ε hε
  change witnessMoment ((product g hg hgn T).value x).1
    (CFC.rpow (regularizedWeight W ε) (-1)) ≤ g x * M
  rw [product_value, witnessMoment_real_smul]
  exact mul_le_mul_of_nonneg_left (hInv ε hε) (hgn x)

/-- Appendix C's weighted hybrid fidelity inequality for general measurable
positive weights and arbitrary trace-class quantum output densities.
The two integrability premises express precisely the finiteness of its RHS. -/
theorem rootFidelity_sq_le_weighted_product (R : PositiveField (H := H) μ)
    (g : Ω → ℝ) (hg : Integrable g μ) (hgn : ∀ x, 0 ≤ g x) (T : DensityState H)
    {W : H →L[ℂ] H} (hW : 0 ≤ W) {M : ℝ} (hM : 0 ≤ M)
    (hInv : ∀ ε : ℝ, 0 < ε →
      witnessMoment (TraceClass.ofOperator T.op T.traceClass)
        (CFC.rpow (regularizedWeight W ε) (-1)) ≤ M)
    (χ : Ω → ℝ) (hχ : ∀ x, 0 < χ x)
    (hweighted : Integrable (fun x => χ x * witnessMoment (R.value x).1 W) μ)
    (hclassical : Integrable (fun x => g x / χ x) μ) :
    R.rootFidelity (product g hg hgn T) ^ 2 ≤
      (∫ x, χ x * witnessMoment (R.value x).1 W ∂μ) *
      (∫ x, g x / χ x ∂μ) * M := by
  let f : Ω → ℝ := fun x => χ x * witnessMoment (R.value x).1 W
  let k : Ω → ℝ := fun x => g x / χ x
  have hfn (x : Ω) : 0 ≤ f x := mul_nonneg (hχ x).le (witnessMoment_nonneg _ hW)
  have hkn (x : Ω) : 0 ≤ k x := div_nonneg (hgn x) (hχ x).le
  have hip := integrable_sqrt_mul_sqrt hweighted hclassical hfn hkn
  have hpoint (x : Ω) :
      PositiveTraceClass.rootFidelity (R.value x) ((product g hg hgn T).value x) ≤
        Real.sqrt (f x) * Real.sqrt (k x) * Real.sqrt M := by
    have hsq := rootFidelity_product_sq_le R g hg hgn T hW hM hInv x
    have heq : f x * k x * M = witnessMoment (R.value x).1 W * (g x * M) := by
      dsimp [f, k]
      field_simp [ne_of_gt (hχ x)]
    have hsqrt : (Real.sqrt (f x) * Real.sqrt (k x) * Real.sqrt M) ^ 2 =
        witnessMoment (R.value x).1 W * (g x * M) := by
      rw [mul_pow, mul_pow, Real.sq_sqrt (hfn x), Real.sq_sqrt (hkn x), Real.sq_sqrt hM]
      exact heq
    have hpos := mul_nonneg (mul_nonneg (Real.sqrt_nonneg (f x))
      (Real.sqrt_nonneg (k x))) (Real.sqrt_nonneg M)
    nlinarith [PositiveTraceClass.rootFidelity_nonneg (R.value x) ((product g hg hgn T).value x)]
  have hroot : R.rootFidelity (product g hg hgn T) ≤
      Real.sqrt (∫ x, f x ∂μ) * Real.sqrt (∫ x, k x ∂μ) * Real.sqrt M := by
    calc
      R.rootFidelity (product g hg hgn T) ≤
          ∫ x, (Real.sqrt (f x) * Real.sqrt (k x) * Real.sqrt M) ∂μ :=
        integral_mono (R.integrable_rootFidelity _) (hip.mul_const _) hpoint
      _ = (∫ x, Real.sqrt (f x) * Real.sqrt (k x) ∂μ) * Real.sqrt M := integral_mul_const _ _
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (integral_sqrt_mul_sqrt_le hweighted hclassical hfn hkn) (Real.sqrt_nonneg M)
  have hfint : 0 ≤ ∫ x, f x ∂μ := integral_nonneg (fun x => hfn x)
  have hkint : 0 ≤ ∫ x, k x ∂μ := integral_nonneg (fun x => hkn x)
  have hsquared := (sq_le_sq₀ (R.rootFidelity_nonneg _) (by positivity)).mpr hroot
  simpa only [mul_pow, Real.sq_sqrt hfint, Real.sq_sqrt hkint, Real.sq_sqrt hM] using hsquared

end PositiveField
end Cloning.Hybrid
