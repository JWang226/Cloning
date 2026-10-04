import Cloning.InfiniteFidelityBlockFactorization

/-! Actual normalization of positive finite mixtures, with a unit fallback
only when their total mass is zero. -/
noncomputable section
open scoped BigOperators ComplexOrder Classical
namespace Cloning.Hybrid.PositiveTraceClass
open Cloning.InfiniteTraceClass Cloning.InfiniteFidelityHilbertSum
set_option backward.isDefEq.respectTransparency false
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {I : Type*} [Fintype I]

theorem norm_finiteMixture (q : I → ℝ) (hq : ∀ i, 0 ≤ q i)
    (A : I → PositiveTraceClass H) :
    ‖(finiteMixture q hq A).1‖ = ∑ i, q i * ‖(A i).1‖ := by
  rw [positive_norm_eq_trace]
  simp only [finiteMixture_val, map_sum, map_smul, Complex.re_sum, smul_eq_mul,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  apply Finset.sum_congr rfl
  intro i hi
  rw [positive_norm_eq_trace]

def normalized (A fallback : PositiveTraceClass H) : PositiveTraceClass H :=
  if h : 0 < ‖A.1‖ then scale ⟨‖A.1‖⁻¹, inv_nonneg.mpr (norm_nonneg _)⟩ A else fallback

theorem norm_normalized (A fallback : PositiveTraceClass H) (hf : ‖fallback.1‖ = 1) :
    ‖(normalized A fallback).1‖ = 1 := by
  by_cases h : 0 < ‖A.1‖
  · rw [normalized, dif_pos h, norm_scale]
    exact inv_mul_cancel₀ (ne_of_gt h)
  · simpa only [normalized, dif_neg h] using hf

theorem scale_normalized (A fallback : PositiveTraceClass H) :
    scale ⟨‖A.1‖, norm_nonneg _⟩ (normalized A fallback) = A := by
  apply Subtype.ext
  by_cases h : 0 < ‖A.1‖
  · simp only [normalized, dif_pos h, scale, smul_smul]
    change ((‖A.1‖ : ℂ) * (‖A.1‖⁻¹ : ℝ)) • A.1 = A.1
    rw [← Complex.ofReal_mul, mul_inv_cancel₀ (ne_of_gt h), Complex.ofReal_one, one_smul]
  · have hz : ‖A.1‖ = 0 := le_antisymm (le_of_not_gt h) (norm_nonneg _)
    have hA : A.1 = 0 := norm_eq_zero.mp hz
    change (‖A.1‖ : ℂ) • (normalized A fallback).1 = A.1
    rw [hz, Complex.ofReal_zero, zero_smul, hA]

theorem normalized_finiteMixture_of_pos
    (q : I → ℝ) (hq : ∀ i, 0 ≤ q i) (A : I → PositiveTraceClass H)
    (hA : ∀ i, ‖(A i).1‖ = 1) (fallback : PositiveTraceClass H)
    (hs : 0 < ∑ i, q i) :
    normalized (finiteMixture q hq A) fallback =
      finiteMixture (fun i ↦ q i / ∑ a, q a)
        (fun i ↦ div_nonneg (hq i) hs.le) A := by
  have hn : ‖(finiteMixture q hq A).1‖ = ∑ i, q i := by
    simp only [norm_finiteMixture, hA, mul_one]
  rw [normalized, dif_pos (hn ▸ hs)]
  apply Subtype.ext
  change ((‖(finiteMixture q hq A).1‖⁻¹ : ℝ) : ℂ) • (finiteMixture q hq A).1 = _
  rw [hn]
  simp only [finiteMixture_val, Finset.smul_sum, smul_smul]
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  simp only [Complex.ofReal_div, Complex.ofReal_inv, Complex.ofReal_mul, div_eq_mul_inv, mul_comm]

theorem normalized_mixture_weights_sum
    (q : I → ℝ) (hs : 0 < ∑ i, q i) : ∑ i, q i / ∑ a, q a = 1 := by
  rw [← Finset.sum_div, div_self (ne_of_gt hs)]

end Cloning.Hybrid.PositiveTraceClass
