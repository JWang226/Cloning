import Cloning.CountMultinomialDensity
import Cloning.YoungUniformLocalScheffe

/-! Conditional count central limits for moving multinomial parameters at the flat base. -/
noncomputable section
open scoped BigOperators Topology Classical
open Filter MeasureTheory
namespace Cloning.CountMultinomial
open Cloning.YoungGeneral Cloning.YoungHyperplane Cloning.YoungFlat Cloning.YoungMultinomial
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000

theorem sampleCenter_change_probability (d N : ℕ) (hN : 0<N)
    (p q : Fin (d+1) → ℝ) (hp : ∑ i, p i=1) (hq : ∑ i, q i=1)
    (μ : Lattice d (N : ℤ)) (i : Fin (d+1)) :
    (sampleCenter d N p μ).1 i=(sampleCenter d N q μ).1 i-
      Real.sqrt (N : ℝ)*(p i-q i) := by
  rw [sampleCenter_apply d N p hp, sampleCenter_apply d N q hq]
  simp only [Int.cast_natCast]
  have hn : Real.sqrt (N : ℝ)≠0 := by positivity
  have hs := Real.sq_sqrt (Nat.cast_nonneg N)
  field_simp
  linear_combination (p i-q i)*hs

/-- The local count CLT is proved from the factorial mass, at every shifted point. -/
theorem density_moving_tendsto_of_positive (d : ℕ) (n : ℕ → ℕ)
    (hn : Tendsto n atTop atTop) (hn0 : ∀ k, 0<n k)
    (p : ℕ → Fin (d+1) → ℝ) (hp : ∀ k i, 0≤p k i) (hs : ∀ k, ∑ i, p k i=1)
    (hp0 : ∀ k i, 0<p k i)
    (hlim : ∀ i, Tendsto (fun k ↦ p k i) atTop (𝓝 (flatSpectrum (d+1) i)))
    (h : rootSpace d)
    (hshift : ∀ i, Tendsto (fun k ↦ Real.sqrt (n k : ℝ)*(p k i-flatSpectrum (d+1) i))
      atTop (𝓝 (h.1 i)))
    (x : rootSpace d) :
    Tendsto (fun k ↦ density d (n k) (p k) (hp k) (hs k) x) atTop
      (𝓝 (covarianceGaussian d (flatSpectrum (d+1)) (flatSpectrum_sum _ (by omega)) (x-h))) := by
  let p₀ := flatSpectrum (d+1)
  have hp₀ : ∑ i, p₀ i=1 := flatSpectrum_sum _ (by omega)
  have hp₀0 i : 0<p₀ i := by dsimp [p₀,flatSpectrum]; positivity
  let μ := fun k ↦ sampleShape d (n k) p₀ x
  let c := fun k ↦ sampleCenter d (n k) (p k) (sampleLabel d (n k) p₀ x)
  have hv := eventually_flat_sampleShape_valid d n hn (fun _ ↦ x) x (fun _ ↦ tendsto_const_nhds)
  have hc i : Tendsto (fun k ↦ (c k).1 i) atTop (𝓝 ((x-h).1 i)) := by
    have hh := (sampleLabel_center_tendsto d n hn (fun _ ↦ p₀) (fun _ ↦ hp₀) x i).sub (hshift i)
    apply hh.congr'
    exact Eventually.of_forall fun k ↦ (sampleCenter_change_probability d (n k) (hn0 k)
      (p k) p₀ (hs k) hp₀ _ i).symm
  have hpa : ∀ᶠ k in atTop, ∀ i, (1/((d+1 : ℕ) : ℝ))/2 ≤ p k i := by
    apply eventually_all.mpr
    intro i
    exact (hlim i).eventually (eventually_ge_nhds (by change (1/((d+1 : ℕ) : ℝ))/2 < 1/((d+1 : ℕ) : ℝ); exact half_lt_self (hp₀0 i)))
  have hb : ∀ᶠ k in atTop, ∀ i, |(c k).1 i| ≤ ‖x-h‖+1 := by
    apply eventually_all.mpr
    intro i
    filter_upwards [(hc i).eventually (Metric.ball_mem_nhds _ (by norm_num : (0:ℝ)<1))] with k hk
    have hbound : |(x-h).1 i| ≤ ‖x-h‖ := by simpa using PiLp.norm_apply_le (x-h).1 i
    have ha := abs_add_le ((c k).1 i-(x-h).1 i) ((x-h).1 i)
    simp only [Metric.mem_ball, Real.dist_eq] at hk
    rw [sub_add_cancel] at ha
    linarith
  have hcount k (hvk : (∑ i, (μ k i).val)=n k ∧ shapeLattice d (n k) (μ k)=sampleLabel d (n k) p₀ x) i :
      ((μ k i).val : ℝ)=n k*(p k i+(c k).1 i/Real.sqrt (n k : ℝ)) := by
    have he := shapeLattice_apply d (n k) (μ k) hvk.1 i
    rw [hvk.2] at he
    have her : ((sampleLabel d (n k) p₀ x).1 i : ℝ)=((μ k i).val : ℝ) := by exact_mod_cast he
    have hh := lattice_ratio_eq_center d (n k) (hn0 k) (p k) (hs k) (sampleLabel d (n k) p₀ x) i
    rw [her] at hh
    exact ((div_eq_iff (by exact_mod_cast (hn0 k).ne' : (n k : ℝ)≠0)).mp hh).trans (mul_comm _ _)
  have hm : Tendsto (fun k ↦ multinomialMass (n k) (p k) (fun i ↦ (μ k i).val)/
      gaussianMass (n k) (p k) (fun i ↦ (c k).1 i)) atTop (𝓝 1) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    obtain ⟨N₀,hN₀⟩ := uniform_multinomial_local_limit (ι := Fin (d+1))
      ((1/((d+1 : ℕ) : ℝ))/2) (‖x-h‖+1) (by positivity) (by positivity) ε hε
    filter_upwards [hpa,hb,hv,hn.eventually (eventually_ge_atTop N₀)] with k hpak hbk hvk hnk
    rw [Real.dist_eq]
    exact hN₀ (n k) hnk (p k) (fun i ↦ (c k).1 i) (fun i ↦ (μ k i).val)
      hpak (hs k) (c k).2 hbk (hcount k hvk)
  have hg := covarianceGaussian_tendsto d p p₀ hs hp₀ hp0 hp₀0 hlim c (x-h) hc
  have hh := hm.mul hg
  simp only [one_mul] at hh
  apply hh.congr'
  filter_upwards [hv] with k hk
  have hx : x∈sampleCell d (n k) p₀ (shapeLattice d (n k) (μ k)) := by
    rw [hk.2]
    exact mem_sampleCell_sampleLabel d (n k) p₀ x
  rw [density_eq_on_cell d (n k) (hn0 k) (p k) (hp k) (hs k) (μ k) hk.1 x hx,
    ← scaled_gaussianMass_eq_covarianceGaussian d (n k) (hn0 k) (p k) (hs k) (hp0 k) (c k)]
  have hg0 : gaussianMass (n k) (p k) (fun i ↦ (c k).1 i)≠0 := Real.exp_ne_zero _
  field_simp

end Cloning.CountMultinomial
