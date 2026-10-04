import Cloning.YoungFlatTightness
import Cloning.YoungFlatIntegrability

/-! Normalization and full L¹ convergence of the physical flat Young laws. -/
noncomputable section
open scoped BigOperators Topology Classical
open MeasureTheory Filter
namespace Cloning.YoungFlat
open Cloning.YoungHyperplane
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000

/-- No Mehta integral is assumed: exact physical normalization and tightness normalize the limit. -/
theorem integral_limitDensity (d : ℕ) : (∫ x, limitDensity d x) = 1 := by
  apply le_antisymm (integral_limitDensity_le_one d)
  by_contra hh
  have hgap : 0 < 1-∫ x, limitDensity d x := sub_pos.mpr (lt_of_not_ge hh)
  let ε : ℝ := (1-∫ x, limitDensity d x)/3
  have hε : 0 < ε := by dsimp [ε]; positivity
  obtain ⟨K,hK,hKtail⟩ := flatDensity_tight d ε hε
  have hlocal := (flatDensity_l1_on_compact d K hK).eventually (gt_mem_nhds hε)
  obtain ⟨N, hN, hnear⟩ := ((eventually_ge_atTop 1).and hlocal).exists
  have hN0 : 0 < N := lt_of_lt_of_le Nat.zero_lt_one hN
  have hf := integrable_flatDensity d N hN0
  have hg := integrable_limitDensity d
  have hdiff : |(∫ x in K, flatDensity d N x)-(∫ x in K, limitDensity d x)| < ε := by
    rw [← integral_sub hf.integrableOn hg.integrableOn]
    exact abs_integral_le_integral_abs.trans_lt hnear
  have hsplit := integral_add_compl hK.measurableSet hf
  rw [integral_flatDensity d N hN0] at hsplit
  have hgK : (∫ x in K, limitDensity d x) ≤ ∫ x, limitDensity d x :=
    setIntegral_le_integral hg (ae_of_all _ (limitDensity_nonneg d))
  have htail := hKtail N hN0
  have hd := (abs_lt.mp hdiff).2
  dsimp [ε] at hd htail
  linarith

/-- The actual finite physical Young laws converge globally in L¹ to the explicit
ordered Vandermonde-squared Gaussian density. -/
theorem flatDensity_l1_tendsto (d : ℕ) :
    Tendsto (fun N : ℕ ↦ ∫ x, |flatDensity d N x-limitDensity d x|) atTop (𝓝 0) := by
  apply (tendsto_add_atTop_iff_nat 1).mp
  have hn : Tendsto (fun N : ℕ ↦ N+1) atTop atTop :=
    tendsto_atTop_mono (fun n ↦ Nat.le_succ n) tendsto_id
  exact density_scheffe volume (fun N ↦ flatDensity d (N+1)) (limitDensity d)
    (fun N ↦ integrable_flatDensity d (N+1) (Nat.succ_pos N))
    (integrable_limitDensity d) (fun N ↦ flatDensity_nonneg d (N+1))
    (limitDensity_nonneg d)
    (fun N ↦ (integral_flatDensity d (N+1) (Nat.succ_pos N)).trans (integral_limitDensity d).symm)
    (ae_of_all _ fun x ↦ flatDensity_moving_tendsto d (fun N ↦ N+1) hn
      (fun N ↦ Nat.succ_pos N) (fun _ ↦ x) x (fun _ ↦ tendsto_const_nhds))

end Cloning.YoungFlat
