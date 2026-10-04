import Cloning.PCTProjectorPurityDomination
import Cloning.PCTProjectorPurityGaussianEnergy
import Cloning.PCTFlatGaussianCrossMoment

/-! Dominated convergence for the actual flat PCT tensor-mixture purity.
The exact finite-particle kernel, global envelope and Gaussian limit have
all been derived before the integral limit is taken. -/
noncomputable section
open scoped BigOperators Topology Matrix ComplexOrder InnerProductSpace
open Filter MeasureTheory
namespace Cloning.PCTProjectorPurity
open Cloning.PCT Cloning.PCTReducedGaussian Cloning.PCTPhysicalState
open Cloning.PCTLocalChart Cloning.PCTGaussianCovariance Cloning.YoungGeneral
open Cloning.MultimodeCoherentGaussianMixture
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 180000
variable {r s : ℕ}

lemma small_variance_mul {δ : ℝ} (hr : 2≤r) (hδ : 0<δ)
    (hδr : δ<1/(2*(r:ℝ))) : (2*(r:ℝ))*δ<1 := by
  have hrR : (0:ℝ)<r := by exact_mod_cast (show 0<r by omega)
  have hh := (lt_div_iff₀ (by positivity : 0<2*(r:ℝ))).mp hδr
  nlinarith

lemma small_variance_half {δ : ℝ} (hr : 2≤r) (hδ : 0<δ)
    (hδr : δ<1/(2*(r:ℝ))) : δ<1/2 := by
  have hh := small_variance_mul hr hδ hδr
  have hrR : (2:ℝ)≤r := by exact_mod_cast hr
  nlinarith

lemma integrable_particle_purity_kernel (hr : 2≤r)
    (u : OrthonormalBasis (Fin (s+1)) ℂ (Register (Fin r×Fin r)))
    (hu : u 0=coefficientVector (schmidtCoefficients (flatSpectrum r)))
    {δ : ℝ} (hδ : 0<δ) (hδr : δ<1/(2*(r:ℝ))) (L : ℕ) :
    Integrable (fun zw : (Fin s→ℂ)×(Fin s→ℂ) =>
      ((r:ℝ)*(Matrix.trace (particle u zw.1 L*particle u zw.2 L)).re)^L)
      ((gaussianProductMeasure (fun _ : Fin s => δ)).prod
        (gaussianProductMeasure (fun _ : Fin s => δ))) := by
  apply (integrable_exp_energy_pair s hδ (2*r) (small_variance_mul hr hδ hδr)).mono'
    (continuous_particle_purity_kernel u L).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun zw => by
    rw [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (particle_overlap_nonneg (by omega) u zw.1 zw.2 L) L)]
    exact particle_purity_kernel_le_energy hr u hu zw.1 zw.2 L)

/-- The literal normalized matrix-overlap power has the derived scaled-purity
limit. No covariance, moment or local-limit premise appears. -/
theorem particle_purity_integral_tendsto (hr : 2≤r)
    (u : OrthonormalBasis (Fin (s+1)) ℂ (Register (Fin r×Fin r)))
    (hu : u 0=coefficientVector (schmidtCoefficients (flatSpectrum r)))
    {δ : ℝ} (hδ : 0<δ) (hδr : δ<1/(2*(r:ℝ))) :
    Tendsto (fun L : ℕ => ∫zw : (Fin s→ℂ)×(Fin s→ℂ),
      ((r:ℝ)*(Matrix.trace (particle u zw.1 L*particle u zw.2 L)).re)^L
      ∂((gaussianProductMeasure (fun _ : Fin s => δ)).prod
        (gaussianProductMeasure (fun _ : Fin s => δ))))
      atTop (𝓝 ((1-4*δ^2)^(-(s:ℝ)/2))) := by
  have hH0 := Cloning.PCTFlatGaussianCross.schmidt_reference_hermitian u _ hu
  have hv := Cloning.PCTFlatGaussianCross.flat_cross_integral u hH0 r (by omega)
    hδ (small_variance_half hr hδ hδr)
  have he : (∫zw : (Fin s→ℂ)×(Fin s→ℂ),
      Real.exp ((r:ℝ)*(Matrix.trace (tangent u zw.1*tangent u zw.2)).re)
      ∂((gaussianProductMeasure (fun _ : Fin s => δ)).prod
        (gaussianProductMeasure (fun _ : Fin s => δ))))=
      (1-4*δ^2)^(-(s:ℝ)/2) := by
    have hp : flatSpectrum r=(fun _ : Fin r => (r:ℝ)⁻¹) := by
      funext i
      simp only [flatSpectrum,one_div]
    simpa only [tangent,hp] using hv
  rw [←he]
  apply tendsto_integral_of_dominated_convergence
    (fun zw : (Fin s→ℂ)×(Fin s→ℂ) =>
      Real.exp (2*(r:ℝ)*(GeneralCoherent.energy zw.1+GeneralCoherent.energy zw.2)))
    (fun L => (continuous_particle_purity_kernel u L).aestronglyMeasurable)
    (integrable_exp_energy_pair s hδ (2*r) (small_variance_mul hr hδ hδr))
  · intro L
    exact Filter.Eventually.of_forall (fun zw => by
      rw [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg
        (particle_overlap_nonneg (by omega) u zw.1 zw.2 L) L)]
      exact particle_purity_kernel_le_energy hr u hu zw.1 zw.2 L)
  · exact Filter.Eventually.of_forall (fun zw => particle_purity_kernel_tendsto
      (by omega) u hu zw.1 zw.2)

/-- Iterated-integral form used by the exact finite tensor-mixture identity. -/
theorem particle_purity_iterated_integral_tendsto (hr : 2≤r)
    (u : OrthonormalBasis (Fin (s+1)) ℂ (Register (Fin r×Fin r)))
    (hu : u 0=coefficientVector (schmidtCoefficients (flatSpectrum r)))
    {δ : ℝ} (hδ : 0<δ) (hδr : δ<1/(2*(r:ℝ))) :
    Tendsto (fun L : ℕ => ∫z,∫w,
      ((r:ℝ)*(Matrix.trace (particle u z L*particle u w L)).re)^L
      ∂gaussianProductMeasure (fun _ : Fin s => δ)
      ∂gaussianProductMeasure (fun _ : Fin s => δ))
      atTop (𝓝 ((1-4*δ^2)^(-(s:ℝ)/2))) := by
  letI := gaussianProductMeasure_probability (fun _ : Fin s => hδ)
  apply (particle_purity_integral_tendsto hr u hu hδ hδr).congr
  intro L
  exact integral_prod _ (integrable_particle_purity_kernel hr u hu hδ hδr L)

end Cloning.PCTProjectorPurity
