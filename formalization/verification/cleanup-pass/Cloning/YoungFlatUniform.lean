import Cloning.YoungFlatLocal

/-! Compact-uniform flat Young local convergence, including every chamber wall. -/
noncomputable section
open scoped BigOperators Topology Classical
open Filter MeasureTheory
namespace Cloning.YoungFlat
open Cloning.YoungHyperplane Cloning.YoungGeneral
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

theorem continuous_limitDensity (d : ℕ) : Continuous (limitDensity d) := by
  have hcoords : Continuous (fun x : rootSpace d ↦ fun i ↦ x.1 i) :=
    continuous_pi fun i ↦ (PiLp.continuous_apply 2 _ i).comp continuous_subtype_val
  apply Continuous.mul ?_ ((continuous_vandermondeFactor (d+1)).comp hcoords)
  unfold covarianceGaussian GaussianAffinity.productDensity
  apply continuous_finset_prod
  intro i _
  have hi := (PiLp.continuous_apply 2 _ i).comp
    (covarianceEigenbasis d (flatSpectrum (d+1)) (flatSpectrum_sum _ (by omega))).repr.continuous
  unfold GaussianAffinity.density
  exact (Real.continuous_exp.comp ((hi.pow 2).const_mul _)).const_mul _

/-- Genuine locally uniform flat-spectrum convergence is derived from moving-point CLT. -/
theorem uniform_flatDensity_on_compact (d : ℕ) (K : Set (rootSpace d)) (hK : IsCompact K)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ x ∈ K, |flatDensity d N x-limitDensity d x| < ε := by
  by_contra h
  push_neg at h
  have hbad k := h (max k 1)
  choose n hn x hxK hb using hbad
  obtain ⟨x₀, hx₀K, φ, hφ, hconv⟩ := hK.tendsto_subseq hxK
  have hnlim : Tendsto n atTop atTop :=
    tendsto_atTop_mono (fun k ↦ (le_max_left k 1).trans (hn k)) tendsto_id
  have hn0 k : 0 < n (φ k) := by have h := hn (φ k); omega
  have hx i : Tendsto (fun k ↦ (x (φ k)).1 i) atTop (𝓝 (x₀.1 i)) :=
    ((PiLp.continuous_apply 2 _ i).comp continuous_subtype_val).continuousAt.tendsto.comp hconv
  have hf := flatDensity_moving_tendsto d (fun k ↦ n (φ k))
    (hnlim.comp hφ.tendsto_atTop) hn0 (fun k ↦ x (φ k)) x₀ hx
  have hg := (continuous_limitDensity d).continuousAt.tendsto.comp hconv
  have hh := (hf.sub hg).abs
  simp only [sub_self, abs_zero] at hh
  obtain ⟨k, hk⟩ := (hh.eventually (gt_mem_nhds hε)).exists
  exact (not_lt_of_ge (hb (φ k))) hk

/-- Local L¹ convergence on each compact set is a consequence, not a hypothesis. -/
theorem flatDensity_l1_on_compact (d : ℕ) (K : Set (rootSpace d)) (hK : IsCompact K) :
    Tendsto (fun N ↦ ∫ x in K, |flatDensity d N x-limitDensity d x|) atTop (𝓝 0) := by
  have hg := (continuous_limitDensity d).continuousOn.integrableOn_compact (μ := volume) hK
  have hvol : volume K ≠ ⊤ := hK.measure_ne_top
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let δ := ε/(volume.real K+1)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨N₀, hN₀⟩ := uniform_flatDensity_on_compact d K hK δ hδ
  filter_upwards [eventually_ge_atTop (max N₀ 1)] with N hN
  have hn0 : 0 < N := by omega
  have hb : (∫ x in K, |flatDensity d N x-limitDensity d x|) ≤ δ*volume.real K := by
    have hi := ((integrable_flatDensity d N hn0).integrableOn.sub hg).abs
    calc
      _ ≤ ∫ _x in K, δ := by
        apply setIntegral_mono_on hi (integrableOn_const hvol) hK.measurableSet
        intro x hx
        exact (hN₀ N (by omega) x hx).le
      _ = _ := by rw [setIntegral_const]; simp only [smul_eq_mul]; ring
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (integral_nonneg (fun _ ↦ abs_nonneg _))]
  apply hb.trans_lt
  have hv : 0 ≤ volume.real K := ENNReal.toReal_nonneg
  dsimp [δ]
  have hden : 0 < volume.real K+1 := by positivity
  rw [div_mul_eq_mul_div, div_lt_iff₀ hden]
  nlinarith

end Cloning.YoungFlat
