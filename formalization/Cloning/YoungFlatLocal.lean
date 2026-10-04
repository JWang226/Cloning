import Cloning.YoungFlatCells
import Cloning.YoungUniformLocalScheffe

/-! The actual flat Young law has a continuous Vandermonde-squared local limit. -/
noncomputable section
open scoped BigOperators Topology Classical
open Filter MeasureTheory
namespace Cloning.YoungFlat
open Cloning.TensorLie Cloning.YoungHyperplane Cloning.YoungGeneral Cloning.YoungMultinomial
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000

def flatDensity (d N : ℕ) : rootSpace d → ℝ :=
  tensorYoungDensity d N (flatSpectrum (d+1))
    (fun _ ↦ by unfold flatSpectrum; positivity) (flatSpectrum_sum _ (by omega))

/-- Positive-part Vandermonde form of the Gaussian density on the ordered chamber. -/
def limitDensity (d : ℕ) (x : rootSpace d) : ℝ :=
  covarianceGaussian d (flatSpectrum (d+1)) (flatSpectrum_sum _ (by omega)) x *
    vandermondeFactor (fun i ↦ x.1 i)

theorem flatDensity_nonneg (d N : ℕ) (x : rootSpace d) : 0 ≤ flatDensity d N x :=
  tensorYoungDensity_nonneg _ _ _ _ _ _

theorem integral_flatDensity (d N : ℕ) (hN : 0 < N) : (∫ x, flatDensity d N x) = 1 :=
  integral_tensorYoungDensity d N hN _ _ _

theorem integrable_flatDensity (d N : ℕ) (hN : 0 < N) : Integrable (flatDensity d N) :=
  integrable_tensorYoungDensity d N hN _ _ _

theorem limitDensity_nonneg (d : ℕ) (x : rootSpace d) : 0 ≤ limitDensity d x :=
  mul_nonneg (covarianceGaussian_nonneg _ _ _ _) (vandermondeFactor_nonneg (by omega) _)

/-- Local convergence also allows moving points and includes chamber walls. -/
theorem flatDensity_moving_tendsto (d : ℕ) (n : ℕ → ℕ)
    (hn : Tendsto n atTop atTop) (hn0 : ∀ k, 0 < n k)
    (x : ℕ → rootSpace d) (x₀ : rootSpace d)
    (hx : ∀ i, Tendsto (fun k ↦ (x k).1 i) atTop (𝓝 (x₀.1 i))) :
    Tendsto (fun k ↦ flatDensity d (n k) (x k)) atTop (𝓝 (limitDensity d x₀)) := by
  let p := flatSpectrum (d+1)
  have hp : ∑ i, p i = 1 := flatSpectrum_sum _ (by omega)
  have hp0 i : 0 < p i := by dsimp [p, flatSpectrum]; positivity
  let μ := fun k ↦ sampleShape d (n k) p (x k)
  let c := fun k ↦ sampleCenter d (n k) p (sampleLabel d (n k) p (x k))
  have hv := eventually_flat_sampleShape_valid d n hn x x₀ hx
  have hc i : Tendsto (fun k ↦ (c k).1 i) atTop (𝓝 (x₀.1 i)) :=
    sampleCenter_moving_tendsto d n hn (fun _ ↦ p) (fun _ ↦ hp) x x₀ hx i
  have hb : ∀ᶠ k in atTop, ∀ i, |(c k).1 i| ≤ ‖x₀‖+1 := by
    apply eventually_all.mpr
    intro i
    filter_upwards [(hc i).eventually (Metric.ball_mem_nhds _ (by norm_num : (0:ℝ)<1))] with k hk
    have hxbound : |x₀.1 i| ≤ ‖x₀‖ := by simpa using PiLp.norm_apply_le x₀.1 i
    have ha := abs_add_le ((c k).1 i-x₀.1 i) (x₀.1 i)
    simp only [Metric.mem_ball, Real.dist_eq] at hk
    rw [sub_add_cancel] at ha
    linarith
  have hm : Tendsto (fun k ↦ multinomialMass (n k) p (fun i ↦ (μ k i).val) /
      gaussianMass (n k) p (fun i ↦ (c k).1 i)) atTop (𝓝 1) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    obtain ⟨N₀, hN₀⟩ := uniform_multinomial_local_limit (ι := Fin (d+1))
      (1/((d+1 : ℕ) : ℝ)) (‖x₀‖+1) (by positivity) (by positivity) ε hε
    filter_upwards [hb, hv, hn.eventually (eventually_ge_atTop N₀)] with k hbk hvk hnk
    rw [Real.dist_eq]
    exact hN₀ (n k) hnk p (fun i ↦ (c k).1 i) (fun i ↦ (μ k i).val)
      (fun _ ↦ le_rfl) hp (c k).2 hbk
      (shape_count_from_cell d (n k) (hn0 k) p hp (x k) (μ k) hvk.1 hvk.2)
  have hcorr : Tendsto (fun k ↦ positiveCorrection (fun i ↦ (μ k i).val)) atTop
      (𝓝 (vandermondeFactor (fun i ↦ x₀.1 i))) := by
    apply (scaledCorrection_tendsto (by omega : 0<d+1)
      (fun k ↦ (Real.sqrt (n k : ℝ))⁻¹) (inv_sqrt_nat_tendsto_zero.comp hn)
      (fun k i ↦ (c k).1 i) (fun i ↦ x₀.1 i) hc).congr'
    filter_upwards [hv] with k hk
    exact (positiveCorrection_eq_scaled (hn0 k) (fun i ↦ (μ k i).val)
      (fun i ↦ (c k).1 i)
      (shape_count_from_cell d (n k) (hn0 k) p hp (x k) (μ k) hk.1 hk.2)).symm
  have hmass : Tendsto (fun k ↦ (tensorFlatYoungPMF (n k) (d+1) (by omega) (μ k)).toReal /
      gaussianMass (n k) p (fun i ↦ (c k).1 i)) atTop
      (𝓝 (vandermondeFactor (fun i ↦ x₀.1 i))) := by
    have hh := hm.mul hcorr
    simp only [one_mul] at hh
    apply hh.congr'
    filter_upwards [hv] with k hk
    rw [tensorFlatYoungPMF_eq_multinomial d (n k) (μ k) hk.1]
    ring
  have hg := covarianceGaussian_tendsto d (fun _ ↦ p) p (fun _ ↦ hp) hp
    (fun _ ↦ hp0) hp0 (fun _ ↦ tendsto_const_nhds) c x₀ hc
  have ht := hmass.mul hg
  rw [mul_comm] at ht
  apply ht.congr'
  filter_upwards [hv] with k hk
  have hxcell : x k ∈ sampleCell d (n k) p (shapeLattice d (n k) (μ k)) := by
    rw [hk.2]
    exact mem_sampleCell_sampleLabel d (n k) p (x k)
  change _ = tensorYoungDensity d (n k) p _ hp (x k)
  rw [tensorYoungDensity_eq_on_cell d (n k) (hn0 k) p _ hp (μ k) hk.1 (x k) hxcell,
    ← scaled_gaussianMass_eq_covarianceGaussian d (n k) (hn0 k) p hp hp0 (c k)]
  change (tensorFlatYoungPMF (n k) (d+1) (by omega) (μ k)).toReal /
      gaussianMass (n k) p (fun i ↦ (c k).1 i) *
      ((Real.sqrt (n k : ℝ)^d / Real.sqrt ((d : ℝ)+1))*gaussianMass (n k) p (fun i ↦ (c k).1 i)) = _
  have hg0 : gaussianMass (n k) p (fun i ↦ (c k).1 i) ≠ 0 := Real.exp_ne_zero _
  change _ = (Real.sqrt (n k : ℝ)^d / Real.sqrt ((d : ℝ)+1))*
    (tensorFlatYoungPMF (n k) (d+1) (by omega) (μ k)).toReal
  field_simp

end Cloning.YoungFlat
