import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Cauchy–Schwarz for square roots of integrable densities on arbitrary
measure spaces, including infinite Lebesgue measures. -/
noncomputable section
open MeasureTheory Filter
namespace Cloning.Hybrid
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

lemma sqrt_mul_sqrt_le_half_add {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt a * Real.sqrt b ≤ (a + b) / 2 := by
  have h := sq_nonneg (Real.sqrt a - Real.sqrt b)
  nlinarith [Real.sq_sqrt ha, Real.sq_sqrt hb]

lemma integrable_sqrt_mul_sqrt {f g : Ω → ℝ} (hf : Integrable f μ)
    (hg : Integrable g μ) (hfn : ∀ x, 0 ≤ f x) (hgn : ∀ x, 0 ≤ g x) :
    Integrable (fun x => Real.sqrt (f x) * Real.sqrt (g x)) μ := by
  apply ((hf.add hg).div_const 2).mono'
    ((Real.continuous_sqrt.comp_aestronglyMeasurable hf.aestronglyMeasurable).mul
      (Real.continuous_sqrt.comp_aestronglyMeasurable hg.aestronglyMeasurable))
  exact Eventually.of_forall fun x => by
    dsimp only [Pi.mul_apply, Pi.add_apply]
    rw [Real.norm_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))]
    exact sqrt_mul_sqrt_le_half_add (hfn x) (hgn x)

lemma memLp_two_sqrt {f : Ω → ℝ} (hf : Integrable f μ) (hfn : ∀ x, 0 ≤ f x) :
    MemLp (fun x => Real.sqrt (f x)) 2 μ := by
  apply (memLp_two_iff_integrable_sq
    (Real.continuous_sqrt.comp_aestronglyMeasurable hf.aestronglyMeasurable)).mpr
  simpa only [Real.sq_sqrt (hfn _)] using hf

/-- Integral Cauchy–Schwarz directly in the form required for hybrid fidelity. -/
theorem integral_sqrt_mul_sqrt_le {f g : Ω → ℝ} (hf : Integrable f μ)
    (hg : Integrable g μ) (hfn : ∀ x, 0 ≤ f x) (hgn : ∀ x, 0 ≤ g x) :
    (∫ x, Real.sqrt (f x) * Real.sqrt (g x) ∂μ) ≤
      Real.sqrt (∫ x, f x ∂μ) * Real.sqrt (∫ x, g x ∂μ) := by
  have hpq : (2 : ℝ).HolderConjugate 2 := by
    apply Real.holderConjugate_iff.mpr
    norm_num
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg hpq
    (Eventually.of_forall fun x => Real.sqrt_nonneg (f x))
    (Eventually.of_forall fun x => Real.sqrt_nonneg (g x))
    (by simpa using memLp_two_sqrt hf hfn)
    (by simpa using memLp_two_sqrt hg hgn)
  simpa only [Real.rpow_two, Real.sq_sqrt (hfn _), Real.sq_sqrt (hgn _),
    ← Real.sqrt_eq_rpow] using h

end Cloning.Hybrid
