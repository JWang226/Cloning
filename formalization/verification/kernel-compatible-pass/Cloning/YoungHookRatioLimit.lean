import Cloning.YoungHookRatio
import Mathlib.Analysis.SpecificLimits.Basic

/-! The exact tableau correction converges along arbitrary sequences with a
positive limiting spectrum. No local limit approximation is a premise. -/
noncomputable section
open scoped BigOperators Classical Topology
open Filter

namespace Cloning.YoungGeneral

def spectralCorrection {d : ℕ} (p : Fin d → ℝ) : ℝ :=
  ∏ i : Fin d, ∏ j ∈ Finset.Ioi i, (1 - p j / p i)

theorem tableauCorrection_tendsto {d : ℕ} (μ : ℕ → Fin d → ℕ)
    (N : ℕ → ℕ) (p : Fin d → ℝ) (hp : ∀ i, p i ≠ 0)
    (hN : Tendsto N atTop atTop)
    (hμ : ∀ i, Tendsto (fun n ↦ (μ n i : ℝ) / (N n : ℝ)) atTop (𝓝 (p i))) :
    Tendsto (fun n ↦ tableauCorrection (μ n)) atTop (𝓝 (spectralCorrection p)) := by
  simp only [tableauCorrection_eq_pair_ratios, spectralCorrection]
  apply tendsto_finset_prod
  intro i _
  apply tendsto_finset_prod
  intro j _
  have hnreal : Tendsto (fun n ↦ (N n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hN
  have hzero : Tendsto (fun n ↦ ((j.val : ℝ) - (i.val : ℝ)) / (N n : ℝ))
      atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using
      (tendsto_inv_atTop_zero.comp hnreal).const_mul ((j.val : ℝ) - (i.val : ℝ))
  have hlim := ((hμ i).sub (hμ j) |>.add hzero).div ((hμ i).add hzero)
    (show p i + 0 ≠ 0 by simpa using hp i)
  have hval : (p i - p j + 0) / (p i + 0) = 1 - p j / p i := by
    simp only [add_zero]
    rw [sub_div, div_self (hp i)]
  rw [hval] at hlim
  apply hlim.congr'
  filter_upwards [hN.eventually (eventually_gt_atTop 0)] with n hn
  have hn0 : (N n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  dsimp only [Pi.div_apply]
  rw [← sub_div, ← add_div, ← add_div,
    div_div_div_cancel_right₀ hn0]
  congr 1 <;> ring

end Cloning.YoungGeneral
