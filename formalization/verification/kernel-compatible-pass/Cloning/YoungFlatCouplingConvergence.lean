import Cloning.YoungFlatCouplingEvents

/-! Vanishing bad-event mass for couplings of two densities with the same L¹
limit. Quantizers and finite label spaces may vary with the sample size. -/
noncomputable section
open scoped BigOperators Topology Classical
open MeasureTheory Filter
namespace Cloning.YoungFlatCoupling
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

theorem l1_between_le (f g h : X → ℝ) (hf : Integrable f μ)
    (hg : Integrable g μ) (hh : Integrable h μ) :
    (∫ x, |f x-g x| ∂μ) ≤ (∫ x, |f x-h x| ∂μ) + ∫ x, |g x-h x| ∂μ := by
  erw [← integral_add (hf.sub hh).abs (hg.sub hh).abs]
  apply integral_mono (hf.sub hg).abs ((hf.sub hh).abs.add (hg.sub hh).abs)
  intro x
  simpa only [abs_sub_comm (h x) (g x)] using abs_sub_le (f x) (h x) (g x)

theorem overlap_event_le_limit (f g h : X → ℝ)
    (hf : Integrable f μ) (hg : Integrable g μ) (hh : Integrable h μ)
    (P : X → Prop) (hP : MeasurableSet {x | P x}) :
    (∫ x, if P x then min (f x) (g x) else 0 ∂μ) ≤
      (∫ x, if P x then h x else 0 ∂μ) + ∫ x, |f x-h x| ∂μ := by
  have hi : Integrable (fun x => if P x then min (f x) (g x) else 0) μ :=
    (show Integrable (fun x => min (f x) (g x)) μ from hf.inf hg).indicator hP
  have hj : Integrable (fun x => if P x then h x else 0) μ := hh.indicator hP
  erw [← integral_add hj (hf.sub hh).abs]
  apply integral_mono hi (hj.add (hf.sub hh).abs)
  intro x
  simp only [Pi.add_apply, Pi.sub_apply]
  by_cases hx : P x
  · simp only [if_pos hx]
    have he := le_abs_self (f x-h x)
    have hm := min_le_left (f x) (g x)
    linarith
  · simp only [if_neg hx, zero_add]
    exact abs_nonneg _

theorem limit_bad_event_tendsto_zero (h : X → ℝ) (hh : Integrable h μ)
    (hh0 : ∀ x, 0 ≤ h x) (P : ℕ → X → Prop)
    (hP : ∀ N, MeasurableSet {x | P N x})
    (hgood : ∀ x, h x ≠ 0 → ∀ᶠ N in atTop, ¬P N x) :
    Tendsto (fun N => ∫ x, if P N x then h x else 0 ∂μ) atTop (𝓝 0) := by
  have hi N : Integrable (fun x => if P N x then h x else 0) μ := hh.indicator (hP N)
  have ht : Tendsto (fun N => ∫ x, if P N x then h x else 0 ∂μ) atTop
      (𝓝 (∫ _x : X, (0 : ℝ) ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence h (fun N => (hi N).aestronglyMeasurable) hh
    · intro N
      apply ae_of_all
      intro x
      by_cases hx : P N x
      · simp only [if_pos hx, Real.norm_eq_abs, abs_of_nonneg (hh0 x), le_refl]
      · simp only [if_neg hx, norm_zero]; exact hh0 x
    · apply ae_of_all
      intro x
      by_cases hx : h x = 0
      · simp only [hx, ite_self]
        exact tendsto_const_nhds
      · apply tendsto_const_nhds.congr'
        filter_upwards [hgood x hx] with N hN
        simp only [if_neg hN]
  simpa only [integral_zero] using ht

end Cloning.YoungFlatCoupling
