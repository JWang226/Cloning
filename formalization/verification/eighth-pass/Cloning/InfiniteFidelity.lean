import Cloning.InfiniteTraceClassPositive
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order

/-! Root fidelity of actual positive trace-class operators on an arbitrary complete complex
Hilbert space. All norms and traces are the analytic trace-class quantities. -/

namespace Cloning.InfiniteFidelity

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped ComplexOrder InnerProductSpace
open InfiniteTraceClass InfiniteTraceClass.HilbertSchmidt

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma sqrt_product_traceClass {A B : H →L[ℂ] H} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hTA : IsTraceClass A) (hTB : IsTraceClass B) :
    IsTraceClass (CFC.sqrt A * CFC.sqrt B) :=
  isTraceClass_mul_of_isHilbertSchmidt (isHilbertSchmidt_sqrt hA hTA)
    (isHilbertSchmidt_sqrt hB hTB)

/-- The root fidelity `‖√A √B‖₁`, with its trace-class domain made explicit. -/
def fidelity (A B : H →L[ℂ] H) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hTA : IsTraceClass A) (hTB : IsTraceClass B) : ℝ :=
  traceNorm (CFC.sqrt A * CFC.sqrt B) (sqrt_product_traceClass hA hB hTA hTB)

lemma fidelity_nonneg {A B : H →L[ℂ] H} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hTA : IsTraceClass A) (hTB : IsTraceClass B) :
    0 ≤ fidelity A B hA hB hTA hTB := traceNorm_nonneg _ _

lemma fidelity_le_sqrt_mul_sqrt {A B : H →L[ℂ] H} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hTA : IsTraceClass A) (hTB : IsTraceClass B) :
    fidelity A B hA hB hTA hTB ≤
      Real.sqrt (trace A hTA).re * Real.sqrt (trace B hTB).re := by
  obtain ⟨w, b, _⟩ := exists_hilbertBasis ℂ H
  have h := traceNorm_mul_le_of_isHilbertSchmidt
    (isHilbertSchmidt_sqrt hA hTA) (isHilbertSchmidt_sqrt hB hTB)
    (sqrt_product_traceClass hA hB hTA hTB) b
  rwa [tsum_sqrt_norm_sq_eq_trace_re hA hTA b,
    tsum_sqrt_norm_sq_eq_trace_re hB hTB b] at h

lemma fidelity_sq_le_trace_mul {A B : H →L[ℂ] H} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hTA : IsTraceClass A) (hTB : IsTraceClass B) :
    fidelity A B hA hB hTA hTB ^ 2 ≤ (trace A hTA).re * (trace B hTB).re := by
  have h := (sq_le_sq₀ (fidelity_nonneg hA hB hTA hTB)
    (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).2
    (fidelity_le_sqrt_mul_sqrt hA hB hTA hTB)
  simpa only [mul_pow, Real.sq_sqrt (trace_re_nonneg hA hTA),
    Real.sq_sqrt (trace_re_nonneg hB hTB)] using h

lemma fidelity_self {A : H →L[ℂ] H} (hA : 0 ≤ A) (hTA : IsTraceClass A) :
    fidelity A A hA hA hTA hTA = (trace A hTA).re := by
  simp only [fidelity, CFC.sqrt_mul_sqrt_self A hA, trace_re_eq_traceNorm hA hTA]

lemma fidelity_comm {A B : H →L[ℂ] H} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hTA : IsTraceClass A) (hTB : IsTraceClass B) :
    fidelity A B hA hB hTA hTB = fidelity B A hB hA hTB hTA := by
  have h := traceNorm_star (sqrt_product_traceClass hA hB hTA hTB)
  have hstarA : star (CFC.sqrt A) = CFC.sqrt A :=
    (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg A)).star_eq
  have hstarB : star (CFC.sqrt B) = CFC.sqrt B :=
    (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg B)).star_eq
  simpa only [star_mul, hstarA, hstarB] using h.symm

lemma abs_sqrt_product {A B : H →L[ℂ] H} (hA : 0 ≤ A) :
    CFC.abs (CFC.sqrt A * CFC.sqrt B) =
      CFC.sqrt (CFC.sqrt B * A * CFC.sqrt B) := by
  have hstarA : star (CFC.sqrt A) = CFC.sqrt A :=
    (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg A)).star_eq
  have hstarB : star (CFC.sqrt B) = CFC.sqrt B :=
    (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg B)).star_eq
  simp only [CFC.abs, star_mul, hstarA, hstarB, mul_assoc]
  rw [← mul_assoc (CFC.sqrt A), CFC.sqrt_mul_sqrt_self A hA]

lemma sqrt_sandwich_traceClass {A B : H →L[ℂ] H} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hTA : IsTraceClass A) (hTB : IsTraceClass B) :
    IsTraceClass (CFC.sqrt (CFC.sqrt B * A * CFC.sqrt B)) := by
  rw [← abs_sqrt_product hA]
  exact isTraceClass_abs (sqrt_product_traceClass hA hB hTA hTB)

lemma fidelity_eq_trace_sqrt_sandwich {A B : H →L[ℂ] H} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hTA : IsTraceClass A) (hTB : IsTraceClass B) :
    fidelity A B hA hB hTA hTB =
      (trace (CFC.sqrt (CFC.sqrt B * A * CFC.sqrt B))
        (sqrt_sandwich_traceClass hA hB hTA hTB)).re := by
  rw [trace_re_eq_traceNorm (CFC.sqrt_nonneg (CFC.sqrt B * A * CFC.sqrt B))
    (sqrt_sandwich_traceClass hA hB hTA hTB)]
  exact (traceNorm_abs (sqrt_product_traceClass hA hB hTA hTB)).symm.trans
    (traceNorm_transport (abs_sqrt_product hA)
      (isTraceClass_abs (sqrt_product_traceClass hA hB hTA hTB)))

lemma fidelity_mono_left {A C B : H →L[ℂ] H} (hA : 0 ≤ A) (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hTA : IsTraceClass A) (hTC : IsTraceClass C) (hTB : IsTraceClass B) (hAC : A ≤ C) :
    fidelity A B hA hB hTA hTB ≤ fidelity C B hC hB hTC hTB := by
  rw [fidelity_eq_trace_sqrt_sandwich hA hB hTA hTB,
    fidelity_eq_trace_sqrt_sandwich hC hB hTC hTB]
  apply trace_re_mono
  apply CFC.sqrt_le_sqrt
  have h := star_left_conjugate_nonneg (sub_nonneg.mpr hAC) (CFC.sqrt B)
  have hstarB : star (CFC.sqrt B) = CFC.sqrt B :=
    (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg B)).star_eq
  rw [hstarB, mul_sub, sub_mul] at h
  exact sub_nonneg.mp h

/-- A dimension-independent perturbation bound in the Hilbert–Schmidt distance between
square roots. The estimate is proved directly from the trace norm and Hilbert–Schmidt Hölder. -/
lemma fidelity_continuity_left_roots {A C B : H →L[ℂ] H}
    (hA : 0 ≤ A) (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hTA : IsTraceClass A) (hTC : IsTraceClass C) (hTB : IsTraceClass B)
    {w : Set H} (b : HilbertBasis w ℂ H) :
    |fidelity A B hA hB hTA hTB - fidelity C B hC hB hTC hTB| ≤
      Real.sqrt (∑' i : w, ‖(CFC.sqrt A - CFC.sqrt C) (b i)‖ ^ 2) *
        Real.sqrt (trace B hTB).re := by
  have hroot := isHilbertSchmidt_sub (isHilbertSchmidt_sqrt hA hTA)
    (isHilbertSchmidt_sqrt hC hTC)
  have hBroot := isHilbertSchmidt_sqrt hB hTB
  have hp := isTraceClass_mul_of_isHilbertSchmidt hroot hBroot
  have hd : IsTraceClass (CFC.sqrt A * CFC.sqrt B - CFC.sqrt C * CFC.sqrt B) := by
    simpa only [sub_mul] using hp
  have hnorm := abs_traceNorm_sub_le (sqrt_product_traceClass hA hB hTA hTB)
    (sqrt_product_traceClass hC hB hTC hTB) hd
  have hbound := traceNorm_mul_le_of_isHilbertSchmidt hroot hBroot hp b
  rw [tsum_sqrt_norm_sq_eq_trace_re hB hTB b] at hbound
  exact hnorm.trans (by simpa only [sub_mul] using hbound)

/-- Fidelity of normalized, positive analytic density operators. -/
def stateFidelity (ρ σ : DensityState H) : ℝ :=
  fidelity ρ.op σ.op ρ.positive σ.positive ρ.traceClass σ.traceClass

lemma stateFidelity_nonneg (ρ σ : DensityState H) : 0 ≤ stateFidelity ρ σ :=
  fidelity_nonneg ρ.positive σ.positive ρ.traceClass σ.traceClass

lemma stateFidelity_le_one (ρ σ : DensityState H) : stateFidelity ρ σ ≤ 1 := by
  have h := fidelity_le_sqrt_mul_sqrt ρ.positive σ.positive ρ.traceClass σ.traceClass
  simpa only [ρ.trace_one, σ.trace_one, Complex.one_re, Real.sqrt_one, one_mul] using h

@[simp] lemma stateFidelity_self (ρ : DensityState H) : stateFidelity ρ ρ = 1 := by
  exact (fidelity_self ρ.positive ρ.traceClass).trans (by rw [ρ.trace_one, Complex.one_re])

lemma stateFidelity_comm (ρ σ : DensityState H) : stateFidelity ρ σ = stateFidelity σ ρ :=
  fidelity_comm ρ.positive σ.positive ρ.traceClass σ.traceClass

end
end Cloning.InfiniteFidelity
