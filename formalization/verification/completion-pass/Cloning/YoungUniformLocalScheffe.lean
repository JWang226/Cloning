import Cloning.YoungUniformLocalGaussian

/-! Scheffé convergence and continuity of the actual normalized covariance
Gaussian. These are used to pass from derived local estimates to global L¹. -/

noncomputable section
open scoped BigOperators Topology Classical
open MeasureTheory Filter
namespace Cloning.YoungHyperplane
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

/-- Scheffé's lemma for real nonnegative densities on an arbitrary measure
space, proved using domination of the minimum by the limiting density. -/
theorem density_scheffe {X : Type*} [MeasurableSpace X] (ν : Measure X)
    (f : ℕ → X → ℝ) (g : X → ℝ) (hf : ∀ n, Integrable (f n) ν)
    (hg : Integrable g ν) (hf0 : ∀ n x, 0 ≤ f n x) (hg0 : ∀ x, 0 ≤ g x)
    (hmass : ∀ n, (∫ x, f n x ∂ν) = ∫ x, g x ∂ν)
    (hpoint : ∀ᵐ x ∂ν, Tendsto (fun n ↦ f n x) atTop (𝓝 (g x))) :
    Tendsto (fun n ↦ ∫ x, |f n x - g x| ∂ν) atTop (𝓝 0) := by
  have hminint n : Integrable (fun x ↦ min (f n x) (g x)) ν := (hf n).inf hg
  have hmin : Tendsto (fun n ↦ ∫ x, min (f n x) (g x) ∂ν) atTop (𝓝 (∫ x, g x ∂ν)) := by
    apply tendsto_integral_of_dominated_convergence g
      (fun n ↦ (hminint n).aestronglyMeasurable) hg
    · intro n
      exact ae_of_all ν fun x ↦ by
        rw [Real.norm_eq_abs, abs_of_nonneg (le_min (hf0 n x) (hg0 x))]
        exact min_le_right _ _
    · filter_upwards [hpoint] with x hx
      simpa using hx.min (tendsto_const_nhds (x := g x))
  have heq n : (∫ x, |f n x - g x| ∂ν) =
      2 * (∫ x, g x ∂ν) - 2 * (∫ x, min (f n x) (g x) ∂ν) := by
    have hid : (fun x ↦ |f n x - g x|) = fun x ↦ f n x + g x - 2 * min (f n x) (g x) := by
      funext x
      by_cases h : f n x ≤ g x
      · rw [min_eq_left h, abs_of_nonpos (sub_nonpos.mpr h)]; ring
      · rw [min_eq_right (le_of_not_ge h), abs_of_nonneg (sub_nonneg.mpr (le_of_not_ge h))]; ring
    rw [hid]
    erw [integral_sub ((hf n).add hg) ((hminint n).const_mul 2),
      integral_add (hf n) hg, integral_const_mul, hmass]
    ring
  simp_rw [heq]
  simpa using ((tendsto_const_nhds (x := 2 * (∫ x, g x ∂ν))).sub (hmin.const_mul 2))

/-- Continuity of the explicit normalized Gaussian along moving positive
spectra and moving root-space points. -/
theorem covarianceGaussian_tendsto (d : ℕ) (p : ℕ → Fin (d + 1) → ℝ)
    (p₀ : Fin (d + 1) → ℝ) (hp : ∀ n, ∑ i, p n i = 1) (hp₀ : ∑ i, p₀ i = 1)
    (hp0 : ∀ n i, 0 < p n i) (hp₀0 : ∀ i, 0 < p₀ i)
    (hlim : ∀ i, Tendsto (fun n ↦ p n i) atTop (𝓝 (p₀ i)))
    (x : ℕ → rootSpace d) (x₀ : rootSpace d)
    (hx : ∀ i, Tendsto (fun n ↦ (x n).1 i) atTop (𝓝 (x₀.1 i))) :
    Tendsto (fun n ↦ covarianceGaussian d (p n) (hp n) (x n)) atTop
      (𝓝 (covarianceGaussian d p₀ hp₀ x₀)) := by
  have hlog := tendsto_finset_sum Finset.univ (fun i _ ↦
    (Real.continuousAt_log (hp₀0 i).ne').tendsto.comp (hlim i))
  have hquad := tendsto_finset_sum Finset.univ (fun i _ ↦
    ((hx i).pow 2).div (hlim i) (hp₀0 i).ne')
  simp_rw [covarianceGaussian_eq_exp d _ _ (hp0 _) _, covarianceGaussian_eq_exp d _ _ hp₀0 _]
  exact Real.continuous_exp.continuousAt.tendsto.comp
    ((tendsto_const_nhds.sub (hlog.const_mul (1 / 2))).sub (hquad.const_mul (1 / 2)))

/-- Parameter continuity in L¹ is derived from normalization and pointwise
continuity, with no common-eigenbasis or density-domination premise. -/
theorem covarianceGaussian_l1_tendsto (d : ℕ) (p : ℕ → Fin (d + 1) → ℝ)
    (p₀ : Fin (d + 1) → ℝ) (hp : ∀ n, ∑ i, p n i = 1) (hp₀ : ∑ i, p₀ i = 1)
    (hp0 : ∀ n i, 0 < p n i) (hp₀0 : ∀ i, 0 < p₀ i)
    (hlim : ∀ i, Tendsto (fun n ↦ p n i) atTop (𝓝 (p₀ i))) :
    Tendsto (fun n ↦ ∫ x, |covarianceGaussian d (p n) (hp n) x -
      covarianceGaussian d p₀ hp₀ x| ∂volume) atTop (𝓝 0) := by
  apply density_scheffe volume (fun n ↦ covarianceGaussian d (p n) (hp n))
    (covarianceGaussian d p₀ hp₀)
    (fun n ↦ integrable_covarianceGaussian d (p n) (hp n) (hp0 n))
    (integrable_covarianceGaussian d p₀ hp₀ hp₀0)
    (fun n ↦ covarianceGaussian_nonneg d (p n) (hp n))
    (covarianceGaussian_nonneg d p₀ hp₀)
  · intro n
    rw [integral_covarianceGaussian d _ _ (hp0 n), integral_covarianceGaussian d _ _ hp₀0]
  · exact ae_of_all volume fun x ↦ covarianceGaussian_tendsto d p p₀ hp hp₀ hp0 hp₀0 hlim
      (fun _ ↦ x) x (fun _ ↦ tendsto_const_nhds)

end Cloning.YoungHyperplane
