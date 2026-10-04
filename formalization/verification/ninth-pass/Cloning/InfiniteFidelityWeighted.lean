import Cloning.InfiniteFidelity

/-! Weighted Cauchy–Schwarz bounds for root fidelity of actual infinite-dimensional
trace-class operators. Bounded inverse factors are genuine operators, not assumed fidelity laws. -/

namespace Cloning.InfiniteFidelity

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped ComplexOrder InnerProductSpace
open InfiniteTraceClass InfiniteTraceClass.HilbertSchmidt

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma trace_re_star_mul_self {R : H →L[ℂ] H} (hR : IsHilbertSchmidt R)
    {w : Set H} (b : HilbertBasis w ℂ H) :
    (trace (star R * R) (isTraceClass_star_mul_self_of_isHilbertSchmidt hR)).re =
      ∑' i : w, ‖R (b i)‖ ^ 2 := by
  rw [trace_re_eq_traceNorm (star_mul_self_nonneg R), traceNorm_eq_of_hilbertBasis _ b,
    CFC.abs_of_nonneg _ (star_mul_self_nonneg R)]
  apply tsum_congr
  intro i
  simp only [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.mul_def,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right,
    inner_self_eq_norm_sq_to_K]
  norm_cast

lemma trace_re_mul_star_self {R : H →L[ℂ] H} (hR : IsHilbertSchmidt R)
    {w : Set H} (b : HilbertBasis w ℂ H) :
    (trace (R * star R) (isTraceClass_mul_star_of_isHilbertSchmidt hR)).re =
      ∑' i : w, ‖R (b i)‖ ^ 2 := by
  have h := trace_re_star_mul_self (isHilbertSchmidt_star hR) b
  simp only [star_star] at h
  rw [h]
  exact (hasSum_norm_sq_apply_eq_adjoint b b
    (summable_norm_sq_apply_of_hilbertBasis w b hR)).tsum_eq

lemma trace_mul_cycle_hilbertSchmidt {R S : H →L[ℂ] H}
    (hR : IsHilbertSchmidt R) (hS : IsHilbertSchmidt S) :
    trace (R * S) (isTraceClass_mul_of_isHilbertSchmidt hR hS) =
      trace (S * R) (isTraceClass_mul_of_isHilbertSchmidt hS hR) := by
  obtain ⟨w, b, _⟩ := exists_hilbertBasis ℂ H
  rw [trace_eq_of_hilbertBasis _ b, trace_eq_of_hilbertBasis _ b]
  exact tsum_diagonal_mul_eq_tsum_diagonal_swap b b hR hS

/-- Hilbert–Schmidt factorization with an inserted bounded right inverse. This formulation
also handles nonscalar weights and avoids any finite-dimensional inverse convention. -/
lemma fidelity_le_weighted_sandwiches {A B C D : H →L[ℂ] H}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hTA : IsTraceClass A) (hTB : IsTraceClass B)
    (hCD : C * D = 1) :
    fidelity A B hA hB hTA hTB ≤
      Real.sqrt (trace (star C * A * C) (isTraceClass_mul_mul hTA)).re *
      Real.sqrt (trace (D * B * star D) (isTraceClass_mul_mul hTB)).re := by
  obtain ⟨w, b, _⟩ := exists_hilbertBasis ℂ H
  have hR : IsHilbertSchmidt (CFC.sqrt A * C) :=
    isHilbertSchmidt_mul_right (isHilbertSchmidt_sqrt hA hTA)
  have hS : IsHilbertSchmidt (D * CFC.sqrt B) :=
    isHilbertSchmidt_mul_left (isHilbertSchmidt_sqrt hB hTB)
  have hRS := isTraceClass_mul_of_isHilbertSchmidt hR hS
  have hfactor : (CFC.sqrt A * C) * (D * CFC.sqrt B) = CFC.sqrt A * CFC.sqrt B := by
    simp only [mul_assoc, ← mul_assoc C D, hCD, one_mul]
  have hstarA : star (CFC.sqrt A) = CFC.sqrt A :=
    (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg A)).star_eq
  have hstarB : star (CFC.sqrt B) = CFC.sqrt B :=
    (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg B)).star_eq
  have hRprod : star (CFC.sqrt A * C) * (CFC.sqrt A * C) = star C * A * C := by
    simp only [star_mul, hstarA, mul_assoc]
    rw [← mul_assoc (CFC.sqrt A), CFC.sqrt_mul_sqrt_self A hA]
  have hSprod : (D * CFC.sqrt B) * star (D * CFC.sqrt B) = D * B * star D := by
    simp only [star_mul, hstarB, mul_assoc]
    rw [← mul_assoc (CFC.sqrt B), CFC.sqrt_mul_sqrt_self B hB]
  have hRsum : (∑' i : w, ‖(CFC.sqrt A * C) (b i)‖ ^ 2) =
      (trace (star C * A * C) (isTraceClass_mul_mul hTA)).re := by
    have h := trace_re_star_mul_self hR b
    simpa only [hRprod] using h.symm
  have hSsum : (∑' i : w, ‖(D * CFC.sqrt B) (b i)‖ ^ 2) =
      (trace (D * B * star D) (isTraceClass_mul_mul hTB)).re := by
    have h := trace_re_mul_star_self hS b
    simpa only [hSprod] using h.symm
  have hbound := traceNorm_mul_le_of_isHilbertSchmidt hR hS hRS b
  simpa only [hfactor, hRsum, hSsum] using hbound

lemma fidelity_le_unit_weight {A B : H →L[ℂ] H}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hTA : IsTraceClass A) (hTB : IsTraceClass B)
    (U : (H →L[ℂ] H)ˣ) :
    fidelity A B hA hB hTA hTB ≤
      Real.sqrt (trace (star (U : H →L[ℂ] H) * A * (U : H →L[ℂ] H))
        (isTraceClass_mul_mul hTA)).re *
      Real.sqrt (trace ((↑U⁻¹ : H →L[ℂ] H) * B * star (↑U⁻¹ : H →L[ℂ] H))
        (isTraceClass_mul_mul hTB)).re :=
  fidelity_le_weighted_sandwiches hA hB hTA hTB U.val_inv

lemma trace_sandwich_cycle {A : H →L[ℂ] H} (hTA : IsTraceClass A)
    (C : H →L[ℂ] H) :
    trace (star C * A * C) (isTraceClass_mul_mul hTA) =
      trace (A * (C * star C))
        (isTraceClass_mul_mul (A := 1) (B := C * star C) hTA) := by
  have hAC : IsTraceClass (A * C) := isTraceClass_mul_mul (A := 1) (B := C) hTA
  have h := trace_mul_cycle (A := star C) hAC
  simpa only [mul_assoc] using h

lemma trace_re_mul_nonneg_of_nonneg_left_traceClass {A B : H →L[ℂ] H}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hTA : IsTraceClass A) :
    0 ≤ (trace (A * B) (isTraceClass_mul_mul (A := 1) (B := B) hTA)).re := by
  have h := trace_sandwich_cycle hTA (CFC.sqrt B)
  have hstarB : star (CFC.sqrt B) = CFC.sqrt B :=
    (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg B)).star_eq
  simp only [hstarB, CFC.sqrt_mul_sqrt_self B hB] at h
  rw [← h]
  apply trace_re_nonneg
  simpa only [hstarB] using star_left_conjugate_nonneg hA (CFC.sqrt B)

/-- The weighted fidelity bound in cyclic form. -/
lemma fidelity_le_weighted_traces {A B C D : H →L[ℂ] H}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hTA : IsTraceClass A) (hTB : IsTraceClass B)
    (hCD : C * D = 1) :
    fidelity A B hA hB hTA hTB ≤
      Real.sqrt (trace (A * (C * star C))
        (isTraceClass_mul_mul (A := 1) (B := C * star C) hTA)).re *
      Real.sqrt (trace (B * (star D * D))
        (isTraceClass_mul_mul (A := 1) (B := star D * D) hTB)).re := by
  have h := fidelity_le_weighted_sandwiches hA hB hTA hTB hCD
  have hBcycle := trace_sandwich_cycle hTB (star D)
  simp only [star_star] at hBcycle
  rwa [trace_sandwich_cycle hTA C, hBcycle] at h

/-- For a strictly positive bounded weight `W`, CFC inverse powers are its genuine bounded
inverse. This is the infinite-dimensional weighted witness inequality. -/
lemma fidelity_le_positive_weight {A B W : H →L[ℂ] H}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hTA : IsTraceClass A) (hTB : IsTraceClass B)
    (hW : IsStrictlyPositive W) :
    fidelity A B hA hB hTA hTB ≤
      Real.sqrt (trace (A * W) (isTraceClass_mul_mul (A := 1) (B := W) hTA)).re *
      Real.sqrt (trace (B * CFC.rpow W (-1))
        (isTraceClass_mul_mul (A := 1) (B := CFC.rpow W (-1)) hTB)).re := by
  have hCD : CFC.sqrt W * CFC.rpow W (-(1 / 2 : ℝ)) = 1 := by
    rw [CFC.sqrt_eq_rpow]
    exact CFC.rpow_mul_rpow_neg (1 / 2 : ℝ) hW.isUnit hW.nonneg
  have hC : CFC.sqrt W * star (CFC.sqrt W) = W := by
    rw [(IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg W)).star_eq]
    exact CFC.sqrt_mul_sqrt_self W hW.nonneg
  have hD : star (CFC.rpow W (-(1 / 2 : ℝ))) * CFC.rpow W (-(1 / 2 : ℝ)) =
      CFC.rpow W (-1) := by
    have hDstar : star (CFC.rpow W (-(1 / 2 : ℝ))) = CFC.rpow W (-(1 / 2 : ℝ)) :=
      (IsSelfAdjoint.of_nonneg (show 0 ≤ CFC.rpow W (-(1 / 2 : ℝ)) from
        CFC.rpow_nonneg)).star_eq
    rw [hDstar]
    calc
      _ = CFC.rpow W (-(1 / 2 : ℝ) + -(1 / 2 : ℝ)) :=
        (CFC.rpow_add (x := -(1 / 2 : ℝ)) (y := -(1 / 2 : ℝ)) hW.isUnit).symm
      _ = CFC.rpow W (-1) := by norm_num
  have h := fidelity_le_weighted_traces hA hB hTA hTB hCD
  simpa only [hC, hD] using h

end
end Cloning.InfiniteFidelity
