import Cloning.PCTProjectorPurityGaussianSingle

/-! The exact finite-dimensional Gaussian cross moment responsible for the
projector-purity correction, derived from the actual circular product law. -/
noncomputable section
open scoped Topology BigOperators
open MeasureTheory
namespace Cloning.PCTProjectorPurity
open Cloning.CoherentGaussianMixture Cloning.MultimodeCoherentGaussianMixture
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 150000

lemma cross_re_le_energy (z w : ℂ) :
    4*z.re*w.re≤2*(‖z‖^2+‖w‖^2) := by
  rw [←Complex.normSq_eq_norm_sq,←Complex.normSq_eq_norm_sq,Complex.normSq_apply,
    Complex.normSq_apply]
  nlinarith [sq_nonneg (z.re-w.re),sq_nonneg z.im,sq_nonneg w.im]

lemma cross_exp_le_energy (s : ℕ) (zw : (Fin s → ℂ) × (Fin s → ℂ)) :
    Real.exp (4*∑i,(zw.1 i).re*(zw.2 i).re)≤
      Real.exp (2*((∑i,‖zw.1 i‖^2)+(∑i,‖zw.2 i‖^2))) := by
  apply Real.exp_le_exp.mpr
  rw [Finset.mul_sum,mul_add,Finset.mul_sum,Finset.mul_sum,←Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  simpa only [mul_add,mul_assoc] using cross_re_le_energy (zw.1 i) (zw.2 i)

/-- Joint integrability is established before using Fubini. -/
theorem integrable_exp_re_cross (s : ℕ) {δ : ℝ} (hδ : 0<δ) (hδ2 : δ<1/2) :
    Integrable (fun zw : (Fin s → ℂ) × (Fin s → ℂ) =>
      Real.exp (4*∑i,(zw.1 i).re*(zw.2 i).re))
      ((gaussianProductMeasure (fun _ : Fin s => δ)).prod
        (gaussianProductMeasure (fun _ : Fin s => δ))) := by
  apply (integrable_exp_energy_pair s hδ 2 (by linarith)).mono'
  · exact (by fun_prop : Continuous (fun zw : (Fin s → ℂ) × (Fin s → ℂ) =>
      Real.exp (4*∑i,(zw.1 i).re*(zw.2 i).re))).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun zw => by
      rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
      exact cross_exp_le_energy s zw)

lemma integral_exp_re_cross_inner (s : ℕ) {δ : ℝ} (hδ : 0<δ) (z : Fin s → ℂ) :
    (∫w : Fin s → ℂ,Real.exp (4*∑i,(z i).re*(w i).re)
      ∂gaussianProductMeasure (fun _ => δ))=
      ∏i,Real.exp (4*δ*(z i).re^2) := by
  letI := gaussianMeasure_probability hδ
  simp only [Finset.mul_sum,Real.exp_sum,gaussianProductMeasure]
  rw [integral_fintype_prod_eq_prod (fun i : Fin s => fun x : ℂ => Real.exp (4*((z i).re*x.re)))]
  apply Finset.prod_congr rfl
  intro i _
  rw [show (fun x : ℂ => Real.exp (4*((z i).re*x.re)))=
      (fun x : ℂ => Real.exp ((4*(z i).re)*x.re)) by funext; congr 1; ring,
    integral_exp_re hδ]
  congr 1
  ring

/-- The circular Gaussian product cross moment, with every variance and
normalization factor derived explicitly. -/
theorem integral_exp_re_cross (s : ℕ) {δ : ℝ} (hδ : 0<δ) (hδ2 : δ<1/2) :
    (∫zw : (Fin s → ℂ) × (Fin s → ℂ),
      Real.exp (4*∑i,(zw.1 i).re*(zw.2 i).re)
      ∂((gaussianProductMeasure (fun _ : Fin s => δ)).prod
        (gaussianProductMeasure (fun _ : Fin s => δ))))=
      (1-4*δ^2)^(-(s : ℝ)/2) := by
  letI := gaussianMeasure_probability hδ
  letI := gaussianProductMeasure_probability (fun _ : Fin s => hδ)
  rw [integral_prod _ (integrable_exp_re_cross s hδ hδ2)]
  simp_rw [integral_exp_re_cross_inner s hδ]
  rw [gaussianProductMeasure,integral_fintype_prod_eq_prod (fun _ : Fin s => fun x : ℂ => Real.exp (4*δ*x.re^2))]
  have ht : (4*δ)*δ<1 := by nlinarith
  simp only [integral_exp_re_sq hδ (4*δ) ht,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  have hb : 0<1-4*δ^2 := by nlinarith
  rw [show 1-4*δ*δ=1-4*δ^2 by ring,inv_pow,Real.sqrt_eq_rpow,
    ←Real.rpow_mul_natCast hb.le,←Real.rpow_neg hb.le]
  congr 1
  ring

end Cloning.PCTProjectorPurity
