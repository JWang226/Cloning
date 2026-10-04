import Cloning.WeylGaussianTwistedConvolution
import Cloning.MultimodeCoherentGaussianMixture

/-! Exponential energy moments of the actual circular Gaussian tangent law.
These provide the integrable domination required by the purity limit. -/
noncomputable section
open scoped BigOperators Topology
open MeasureTheory
namespace Cloning.PCTProjectorPurity
open Cloning.CoherentGaussianMixture Cloning.MultimodeCoherentGaussianMixture
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 150000

lemma integral_gaussianMeasure_real (δ : ℝ) (hδ : 0<δ) (f : ℂ → ℝ) :
    (∫z,f z ∂gaussianMeasure δ)=∫z,gaussianDensity δ z*f z := by
  rw [gaussianMeasure,integral_withDensity_eq_integral_toReal_smul
    (continuous_gaussianDensity δ).measurable.ennreal_ofReal
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (gaussianDensity_pos hδ _).le,smul_eq_mul]

/-- Exact one-coordinate energy moment, throughout its true integrability
range, including negative exponential weights. -/
theorem integral_exp_norm_sq {δ : ℝ} (hδ : 0<δ) (t : ℝ) (ht : t*δ<1) :
    (∫z : ℂ,Real.exp (t*‖z‖^2) ∂gaussianMeasure δ)=(1-t*δ)⁻¹ := by
  have hq : 0<δ⁻¹-t := by
    have := (lt_div_iff₀ hδ).2 ht
    simpa only [one_div] using sub_pos.mpr this
  rw [integral_gaussianMeasure_real δ hδ]
  have he (z : ℂ) : gaussianDensity δ z*Real.exp (t*‖z‖^2)=
      (Real.pi*δ)⁻¹*Real.exp (-(δ⁻¹-t)*‖z‖^2) := by
    unfold gaussianDensity
    rw [div_eq_mul_inv,mul_right_comm,←Real.exp_add,mul_comm]
    congr 1
    congr 1
    ring
  simp_rw [he]
  rw [integral_const_mul,Cloning.MultimodeCoherent.integral_gaussian_single hq]
  have hd : δ≠0 := hδ.ne'
  have ht0 : 1-t*δ≠0 := (sub_pos.mpr ht).ne'
  have hq0 : δ⁻¹-t≠0 := hq.ne'
  field_simp
  <;> ring

theorem integrable_exp_norm_sq {δ : ℝ} (hδ : 0<δ) (t : ℝ) (ht : t*δ<1) :
    Integrable (fun z : ℂ => Real.exp (t*‖z‖^2)) (gaussianMeasure δ) := by
  apply Integrable.of_integral_ne_zero
  rw [integral_exp_norm_sq hδ t ht]
  exact inv_ne_zero (sub_pos.mpr ht).ne'

/-- Exact multimode energy moment, derived from the literal product measure. -/
theorem integral_exp_energy (s : ℕ) {δ : ℝ} (hδ : 0<δ) (t : ℝ) (ht : t*δ<1) :
    (∫z : Fin s → ℂ,Real.exp (t*∑i,‖z i‖^2)
      ∂gaussianProductMeasure (fun _ => δ))=((1-t*δ)⁻¹)^s := by
  letI := gaussianMeasure_probability hδ
  simp only [Finset.mul_sum,Real.exp_sum,gaussianProductMeasure]
  rw [integral_fintype_prod_eq_prod (fun _ : Fin s => fun z : ℂ => Real.exp (t*‖z‖^2))]
  simp only [integral_exp_norm_sq hδ t ht,Finset.prod_const,Finset.card_univ,Fintype.card_fin]

theorem integrable_exp_energy (s : ℕ) {δ : ℝ} (hδ : 0<δ) (t : ℝ) (ht : t*δ<1) :
    Integrable (fun z : Fin s → ℂ => Real.exp (t*∑i,‖z i‖^2))
      (gaussianProductMeasure (fun _ => δ)) := by
  apply Integrable.of_integral_ne_zero
  rw [integral_exp_energy s hδ t ht]
  exact pow_ne_zero s (inv_ne_zero (sub_pos.mpr ht).ne')

/-- The two-variable domination used for projector purity is integrable. -/
theorem integrable_exp_energy_pair (s : ℕ) {δ : ℝ} (hδ : 0<δ) (t : ℝ) (ht : t*δ<1) :
    Integrable (fun zw : (Fin s → ℂ) × (Fin s → ℂ) =>
      Real.exp (t*((∑i,‖zw.1 i‖^2)+(∑i,‖zw.2 i‖^2))))
      ((gaussianProductMeasure (fun _ : Fin s => δ)).prod
        (gaussianProductMeasure (fun _ : Fin s => δ))) := by
  have hh := (integrable_exp_energy s hδ t ht).mul_prod (integrable_exp_energy s hδ t ht)
  simpa only [mul_add,Real.exp_add] using hh

end Cloning.PCTProjectorPurity
