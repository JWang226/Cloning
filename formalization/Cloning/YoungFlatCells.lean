import Cloning.YoungFlatCorrection
import Cloning.YoungUniformLocalSampleShape

/-! Moving-point flat cells satisfy the exact finite label constraints. -/
noncomputable section
open scoped BigOperators Topology Classical
open Filter
namespace Cloning.YoungFlat
open Cloning.YoungHyperplane Cloning.YoungGeneral
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

theorem sampleCenter_moving_tendsto (d : ℕ) (n : ℕ → ℕ) (hn : Tendsto n atTop atTop)
    (p : ℕ → Fin (d+1) → ℝ) (hp : ∀ k, ∑ i, p k i = 1)
    (x : ℕ → rootSpace d) (x₀ : rootSpace d)
    (hx : ∀ i, Tendsto (fun k ↦ (x k).1 i) atTop (𝓝 (x₀.1 i))) (i : Fin (d+1)) :
    Tendsto (fun k ↦ (sampleCenter d (n k) (p k) (sampleLabel d (n k) (p k) (x k))).1 i)
      atTop (𝓝 (x₀.1 i)) := by
  have herr : Tendsto (fun k ↦
      (sampleCenter d (n k) (p k) (sampleLabel d (n k) (p k) (x k))).1 i-(x k).1 i)
      atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _) ?_
      ((sample_mesh_tendsto_zero d).comp hn)
    filter_upwards [hn.eventually (eventually_gt_atTop 0)] with k hk
    simpa only [Real.norm_eq_abs, Int.cast_natCast] using
      sampleCenter_coordinate_distance d (n k) (by exact_mod_cast hk) (p k) (hp k)
        (sampleLabel d (n k) (p k) (x k)) (x k)
        (mem_sampleCell_sampleLabel d (n k) (p k) (x k)) i
  simpa only [sub_add_cancel, zero_add] using herr.add (hx i)

theorem sampleLabel_flat_moving_ratio (d : ℕ) (n : ℕ → ℕ) (hn : Tendsto n atTop atTop)
    (x : ℕ → rootSpace d) (x₀ : rootSpace d)
    (hx : ∀ i, Tendsto (fun k ↦ (x k).1 i) atTop (𝓝 (x₀.1 i))) (i : Fin (d+1)) :
    Tendsto (fun k ↦ ((sampleLabel d (n k) (flatSpectrum (d+1)) (x k)).1 i : ℝ)/(n k : ℝ))
      atTop (𝓝 (1/((d+1 : ℕ) : ℝ))) := by
  have hc := (sampleCenter_moving_tendsto d n hn (fun _ ↦ flatSpectrum (d+1))
    (fun _ ↦ flatSpectrum_sum (d+1) (by omega)) x x₀ hx i).mul
      (Cloning.YoungMultinomial.inv_sqrt_nat_tendsto_zero.comp hn)
  have ht := hc.const_add (1/((d+1 : ℕ) : ℝ))
  simp only [mul_zero, add_zero] at ht
  apply ht.congr'
  filter_upwards [hn.eventually (eventually_gt_atTop 0)] with k hk
  rw [lattice_ratio_eq_center d (n k) hk _ (flatSpectrum_sum _ (by omega))]
  rfl

/-- Flat labels need positivity for finite completion; no strict spectral gaps are used. -/
theorem eventually_flat_sampleShape_valid (d : ℕ) (n : ℕ → ℕ) (hn : Tendsto n atTop atTop)
    (x : ℕ → rootSpace d) (x₀ : rootSpace d)
    (hx : ∀ i, Tendsto (fun k ↦ (x k).1 i) atTop (𝓝 (x₀.1 i))) :
    ∀ᶠ k in atTop,
      (∑ i, (sampleShape d (n k) (flatSpectrum (d+1)) (x k) i).val) = n k ∧
      shapeLattice d (n k) (sampleShape d (n k) (flatSpectrum (d+1)) (x k)) =
        sampleLabel d (n k) (flatSpectrum (d+1)) (x k) := by
  have hp : ∀ᶠ k in atTop, ∀ i,
      0 < ((sampleLabel d (n k) (flatSpectrum (d+1)) (x k)).1 i : ℝ)/(n k : ℝ) :=
    eventually_all.mpr fun i ↦ (sampleLabel_flat_moving_ratio d n hn x x₀ hx i).eventually
      (eventually_gt_nhds (by positivity))
  filter_upwards [hp, hn.eventually (eventually_gt_atTop 0)] with k hk hn0
  have hnR : (0 : ℝ) < n k := by exact_mod_cast hn0
  have hpos i : 0 ≤ (sampleLabel d (n k) (flatSpectrum (d+1)) (x k)).1 i := by
    exact_mod_cast ((div_pos_iff_of_pos_right hnR).mp (hk i)).le
  exact ⟨sampleShape_sum d (n k) _ (x k) hpos, shapeLattice_sampleShape d (n k) _ (x k) hpos⟩

theorem shape_count_from_cell (d N : ℕ) (hN : 0 < N)
    (p : Fin (d+1) → ℝ) (hp : ∑ i, p i = 1) (x : rootSpace d)
    (μ : Shape (d+1) N) (hs : ∑ i, (μ i).val = N)
    (he : shapeLattice d N μ = sampleLabel d N p x) (i : Fin (d+1)) :
    ((μ i).val : ℝ) = N*(p i+
      (sampleCenter d N p (sampleLabel d N p x)).1 i/Real.sqrt (N : ℝ)) := by
  have hc := shapeLattice_apply d N μ hs i
  rw [he] at hc
  have hcast : ((sampleLabel d N p x).1 i : ℝ) = ((μ i).val : ℝ) := by exact_mod_cast hc
  have ht := lattice_ratio_eq_center d N hN p hp (sampleLabel d N p x) i
  rw [hcast] at ht
  exact ((div_eq_iff (by positivity : (N : ℝ) ≠ 0)).mp ht).trans (mul_comm _ _)

end Cloning.YoungFlat
