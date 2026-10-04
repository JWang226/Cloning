import Cloning.InfiniteFidelityWeighted

/-! Removing a strictly-positive regularization from the weighted fidelity inequality.
The inverse moment assumption concerns actual bounded CFC inverse operators for every positive
regularization. No unbounded operator or inverse is silently treated as bounded. -/

namespace Cloning.InfiniteFidelity

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped ComplexOrder InnerProductSpace
open InfiniteTraceClass

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def regularizedWeight (W : H →L[ℂ] H) (ε : ℝ) : H →L[ℂ] H := W + ε • 1

lemma regularizedWeight_strictlyPositive {W : H →L[ℂ] H} (hW : 0 ≤ W)
    {ε : ℝ} (hε : 0 < ε) : IsStrictlyPositive (regularizedWeight W ε) :=
  IsStrictlyPositive.nonneg_add hW (isStrictlyPositive_one.smul hε)

lemma trace_regularizedWeight {A W : H →L[ℂ] H} (hTA : IsTraceClass A) (ε : ℝ) :
    trace (A * regularizedWeight W ε)
      (isTraceClass_mul_mul (A := 1) (B := regularizedWeight W ε) hTA) =
      trace (A * W) (isTraceClass_mul_mul (A := 1) (B := W) hTA) +
        (ε : ℂ) * trace A hTA := by
  have hAW : IsTraceClass (A * W) := isTraceClass_mul_mul (A := 1) (B := W) hTA
  have h := trace_add hAW (isTraceClass_smul (ε : ℂ) hTA)
  rw [trace_smul] at h
  simpa only [regularizedWeight, mul_add, Algebra.mul_smul_comm, mul_one,
    Complex.coe_smul] using h

lemma fidelity_sq_le_positive_weight {A B W : H →L[ℂ] H}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hTA : IsTraceClass A) (hTB : IsTraceClass B)
    (hW : IsStrictlyPositive W) :
    fidelity A B hA hB hTA hTB ^ 2 ≤
      (trace (A * W) (isTraceClass_mul_mul (A := 1) (B := W) hTA)).re *
      (trace (B * CFC.rpow W (-1))
        (isTraceClass_mul_mul (A := 1) (B := CFC.rpow W (-1)) hTB)).re := by
  have hleft := trace_re_mul_nonneg_of_nonneg_left_traceClass hA hW.nonneg hTA
  have hright := trace_re_mul_nonneg_of_nonneg_left_traceClass hB
    (show 0 ≤ CFC.rpow W (-1) from CFC.rpow_nonneg) hTB
  have h := (sq_le_sq₀ (fidelity_nonneg hA hB hTA hTB)
    (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).2
    (fidelity_le_positive_weight hA hB hTA hTB hW)
  simpa only [mul_pow, Real.sq_sqrt hleft, Real.sq_sqrt hright] using h

/-- A uniform bound on regularized inverse moments suffices for the unregularized witness
bound, even when `W` itself has no bounded inverse. -/
lemma fidelity_sq_le_of_regularized_inverse_moment {A B W : H →L[ℂ] H}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hW : 0 ≤ W)
    (hTA : IsTraceClass A) (hTB : IsTraceClass B) {M : ℝ} (hM : 0 ≤ M)
    (hInv : ∀ ε : ℝ, 0 < ε →
      (trace (B * CFC.rpow (regularizedWeight W ε) (-1))
        (isTraceClass_mul_mul (A := 1)
          (B := CFC.rpow (regularizedWeight W ε) (-1)) hTB)).re ≤ M) :
    fidelity A B hA hB hTA hTB ^ 2 ≤
      (trace (A * W) (isTraceClass_mul_mul (A := 1) (B := W) hTA)).re * M := by
  have htrA : 0 ≤ (trace A hTA).re := trace_re_nonneg hA hTA
  have htrW := trace_re_mul_nonneg_of_nonneg_left_traceClass hA hW hTA
  apply le_of_forall_pos_le_add
  intro δ hδ
  let ε : ℝ := δ / ((trace A hTA).re * M + 1)
  have hden : 0 < (trace A hTA).re * M + 1 := by positivity
  have hε : 0 < ε := div_pos hδ hden
  have hbound := fidelity_sq_le_positive_weight hA hB hTA hTB
    (regularizedWeight_strictlyPositive hW hε)
  have ht := congrArg Complex.re (trace_regularizedWeight (W := W) hTA ε)
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero] at ht
  rw [ht] at hbound
  have hbound' := hbound.trans (mul_le_mul_of_nonneg_left (hInv ε hε)
    (add_nonneg htrW (mul_nonneg hε.le htrA)))
  have hsmall : ε * ((trace A hTA).re * M) ≤ δ := by
    calc
      ε * ((trace A hTA).re * M) ≤ ε * ((trace A hTA).re * M + 1) := by
        gcongr
        exact le_add_of_nonneg_right zero_le_one
      _ = δ := div_mul_cancel₀ δ (ne_of_gt hden)
  nlinarith

end
end Cloning.InfiniteFidelity
