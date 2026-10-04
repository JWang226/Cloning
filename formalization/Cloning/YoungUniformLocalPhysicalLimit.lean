import Cloning.YoungUniformLocalCharacter
import Cloning.YoungUniformLocalSampleShape
import Cloning.YoungUniformLocalDensity
import Cloning.YoungUniformLocalScheffe

/-! The actual smoothed physical Young law has the Gaussian local limit.
This combines proved Stirling estimates, physical multiplicities, physical
sector trace asymptotics and exact affine cell geometry. -/

noncomputable section
open scoped BigOperators Topology Classical
open Filter MeasureTheory
namespace Cloning.YoungHyperplane
open Cloning.TensorLie Cloning.YoungGeneral Cloning.YoungMultinomial
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

private theorem shape_count_from_cell (d N : ℕ) (hN : 0 < N)
    (p : Fin (d + 1) → ℝ) (hp : ∑ i, p i = 1) (x : rootSpace d)
    (μ : Shape (d + 1) N) (hs : ∑ i, (μ i).val = N)
    (he : shapeLattice d N μ = sampleLabel d N p x) (i : Fin (d + 1)) :
    ((μ i).val : ℝ) = N * (p i +
      (sampleCenter d N p (sampleLabel d N p x)).1 i / Real.sqrt (N : ℝ)) := by
  have hc := shapeLattice_apply d N μ hs i
  rw [he] at hc
  have hcast : ((sampleLabel d N p x).1 i : ℝ) = ((μ i).val : ℝ) := by exact_mod_cast hc
  have ht := lattice_ratio_eq_center d N hN p hp (sampleLabel d N p x) i
  rw [hcast] at ht
  have hh := (div_eq_iff (by positivity : (N : ℝ) ≠ 0)).mp ht
  exact hh.trans (mul_comm _ _)

/-- Pointwise Gaussian convergence for actual smoothed physical Schur laws,
including moving spectra and arbitrary divergent sample-size subsequences. -/
theorem tensorYoungDensity_tendsto (d : ℕ) (n : ℕ → ℕ)
    (hn : Tendsto n atTop atTop) (hn0 : ∀ k, 0 < n k)
    (p : ℕ → Fin (d + 1) → ℝ) (hp : ∀ k, ∑ i, p k i = 1)
    (hp0 : ∀ k i, 0 < p k i) (p₀ : Fin (d + 1) → ℝ) (hs₀ : ∑ i, p₀ i = 1)
    (hp₀ : ∀ i, 0 < p₀ i) (hord : StrictAnti p₀)
    (hlim : ∀ i, Tendsto (fun k ↦ p k i) atTop (𝓝 (p₀ i))) (x : rootSpace d) :
    Tendsto (fun k ↦ tensorYoungDensity d (n k) (p k) (fun i ↦ (hp0 k i).le) (hp k) x)
      atTop (𝓝 (covarianceGaussian d p₀ hs₀ x)) := by
  let μ := fun k ↦ sampleShape d (n k) (p k) x
  let c := fun k ↦ sampleCenter d (n k) (p k) (sampleLabel d (n k) (p k) x)
  have hv := eventually_sampleShape_valid d n hn p hp p₀ hp₀ hord hlim x
  have hμratio i : Tendsto (fun k ↦ ((μ k i).val : ℝ) / (n k : ℝ)) atTop (𝓝 (p₀ i)) :=
    sampleShape_ratio_tendsto d n hn p hp p₀ hp₀ hord hlim x i
  obtain ⟨a, ha, hpa, _⟩ := YoungCompatibility.compact_spectra_positive_gap
    ({p₀} : Set (Fin (d + 1) → ℝ)) isCompact_singleton
    (by intro q hq; have he : q = p₀ := Set.mem_singleton_iff.mp hq; simpa [he] using hp₀)
    (by intro q hq; have he : q = p₀ := Set.mem_singleton_iff.mp hq; simpa [he] using hord)
  have hpa0 i : a ≤ p₀ i := hpa p₀ (by simp) i
  have hpbound : ∀ᶠ k in atTop, ∀ i, a / 2 ≤ p k i :=
    eventually_all.mpr fun i ↦ ((hlim i).eventually
      (eventually_gt_nhds (show a / 2 < p₀ i by linarith [hpa0 i]))).mono fun _ h ↦ h.le
  have hcbound : ∀ᶠ k in atTop, ∀ i, |(c k).1 i| ≤ ‖x‖ + 1 := by
    have hm := ((sample_mesh_tendsto_zero d).comp hn).eventually
      (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))
    filter_upwards [hm] with k hk i
    have hxcoord j : |x.1 j| ≤ ‖x‖ := by simpa using PiLp.norm_apply_le x.1 j
    have hh := sampleCenter_coordinate_bound d (n k) (by exact_mod_cast hn0 k)
      (p k) (hp k) (sampleLabel d (n k) (p k) x) x
      (mem_sampleCell_sampleLabel d (n k) (p k) x) ‖x‖ hxcoord i
    simp only [Int.cast_natCast] at hh
    exact hh.trans (by dsimp at hk; linarith)
  have hm : Tendsto (fun k ↦ multinomialMass (n k) (p k) (fun i ↦ (μ k i).val) /
      gaussianMass (n k) (p k) (fun i ↦ (c k).1 i)) atTop (𝓝 1) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    obtain ⟨N₀, hN₀⟩ := uniform_multinomial_local_limit (ι := Fin (d + 1))
      (a / 2) (‖x‖ + 1) (by positivity) (by positivity) ε hε
    filter_upwards [hpbound, hcbound, hv, hn.eventually (eventually_ge_atTop N₀)] with k hpk hck hvk hnk
    rw [Real.dist_eq]
    exact hN₀ (n k) hnk (p k) (fun i ↦ (c k).1 i) (fun i ↦ (μ k i).val)
      hpk (hp k) (c k).2 hck
      (shape_count_from_cell d (n k) (hn0 k) (p k) (hp k) x (μ k) hvk.2.1 hvk.2.2)
  have hc := tableauCorrection_tendsto (fun k i ↦ (μ k i).val) n p₀
    (fun i ↦ (hp₀ i).ne') hn hμratio
  have hz := physicalSectorCharacter_div_highest_tendsto n hn (fun k i ↦ (μ k i).val)
    (hv.mono fun _ h ↦ h.1) p p₀ hp₀ hord hlim hμratio
  have hprob : Tendsto (fun k ↦
      (tensorYoungPMF (n k) (d + 1) (p k) (fun i ↦ (hp0 k i).le) (hp k) (μ k)).toReal /
        gaussianMass (n k) (p k) (fun i ↦ (c k).1 i)) atTop (𝓝 1) := by
    have ht := (hm.mul hc).mul hz
    rw [one_mul, mul_inv_cancel₀ (spectralCorrection_pos p₀ hp₀ hord).ne'] at ht
    apply ht.congr'
    filter_upwards [hv] with k hk
    exact (tensorYoungPMF_div_gaussianMass (d + 1) (n k) (p k) (fun i ↦ (c k).1 i)
      (hp0 k) (hp k) (μ k) hk.1 hk.2.1).symm
  have hg := covarianceGaussian_tendsto d p p₀ hp hs₀ hp0 hp₀ hlim c x
    (fun i ↦ sampleLabel_center_tendsto d n hn p hp x i)
  have ht := hprob.mul hg
  simp only [one_mul] at ht
  apply ht.congr'
  filter_upwards [hv] with k hk
  have hxcell : x ∈ sampleCell d (n k) (p k) (shapeLattice d (n k) (μ k)) := by
    rw [hk.2.2]
    exact mem_sampleCell_sampleLabel d (n k) (p k) x
  rw [tensorYoungDensity_eq_on_cell d (n k) (hn0 k) (p k) (fun i ↦ (hp0 k i).le)
    (hp k) (μ k) hk.2.1 x hxcell,
    ← scaled_gaussianMass_eq_covarianceGaussian d (n k) (hn0 k) (p k) (hp k) (hp0 k) (c k)]
  have hg0 : gaussianMass (n k) (p k) (fun i ↦ (c k).1 i) ≠ 0 := Real.exp_ne_zero _
  field_simp

end Cloning.YoungHyperplane
