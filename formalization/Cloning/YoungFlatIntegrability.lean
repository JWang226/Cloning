import Cloning.YoungFlatUniform

/-! Fatou's inequality gives integrability of the actual flat limiting density. -/
noncomputable section
open scoped BigOperators Topology Classical ENNReal
open Filter MeasureTheory
namespace Cloning.YoungFlat
open Cloning.YoungHyperplane
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

theorem lintegral_limitDensity_le_one (d : ℕ) :
    (∫⁻ x, ENNReal.ofReal (limitDensity d x)) ≤ 1 := by
  have hn : Tendsto (fun n : ℕ ↦ n+1) atTop atTop :=
    tendsto_atTop_mono (fun n ↦ Nat.le_succ n) tendsto_id
  have hpoint (x : rootSpace d) :
      Filter.liminf (fun n ↦ ENNReal.ofReal (flatDensity d (n+1) x)) atTop =
        ENNReal.ofReal (limitDensity d x) :=
    (ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      (flatDensity_moving_tendsto d (fun n ↦ n+1) hn (fun n ↦ Nat.succ_pos n)
        (fun _ ↦ x) x (fun _ ↦ tendsto_const_nhds))).liminf_eq
  have hint (n : ℕ) : (∫⁻ x, ENNReal.ofReal (flatDensity d (n+1) x)) = 1 := by
    rw [← ofReal_integral_eq_lintegral_ofReal (integrable_flatDensity d (n+1) (by omega))
      (ae_of_all _ (flatDensity_nonneg d (n+1))), integral_flatDensity d (n+1) (by omega),
      ENNReal.ofReal_one]
  have hh := lintegral_liminf_le' (fun n ↦
    ENNReal.measurable_ofReal.comp_aemeasurable (integrable_flatDensity d (n+1) (by omega)).aemeasurable)
  simp only [Function.comp_apply, hpoint, hint, liminf_const] at hh
  exact hh

theorem integrable_limitDensity (d : ℕ) : Integrable (limitDensity d) := by
  refine ⟨(continuous_limitDensity d).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ (limitDensity_nonneg d))]
  exact (lintegral_limitDensity_le_one d).trans_lt (by simp)

theorem integral_limitDensity_le_one (d : ℕ) : (∫ x, limitDensity d x) ≤ 1 := by
  have hh := lintegral_limitDensity_le_one d
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_limitDensity d)
    (ae_of_all _ (limitDensity_nonneg d)), ← ENNReal.ofReal_one] at hh
  exact (ENNReal.ofReal_le_ofReal_iff (by norm_num : (0 : ℝ) ≤ 1)).mp hh

end Cloning.YoungFlat
