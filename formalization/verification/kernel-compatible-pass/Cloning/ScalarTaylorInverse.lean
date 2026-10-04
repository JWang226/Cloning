import Cloning.ScalarTaylorRemainder
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Asymptotics.Lemmas

/-! Inverting a simple zero with a cubic Taylor remainder retains the linear
big-O error in the resulting Laurent expansion. -/
noncomputable section
open scoped Topology
open Filter Set Asymptotics
namespace Cloning.ScalarTaylor
set_option backward.isDefEq.respectTransparency false

theorem inverse_remainder {f : ℝ → ℝ} {α β : ℝ} (hα : α ≠ 0)
    (hf0 : f 0=0) (hf : HasDerivAt f α 0)
    (hrem : (fun x => f x-α*x-β*x^2) =O[𝓝 (0:ℝ)] (fun x => x^3)) :
    (fun x => (f x)⁻¹-(α*x)⁻¹+β/α^2)
      =O[𝓝[≠] (0:ℝ)] (fun x => x) := by
  let L := 𝓝[≠] (0:ℝ)
  have hid : Tendsto (fun x : ℝ => x) L (𝓝 0) := nhdsWithin_le_nhds
  have hq : Tendsto (fun x : ℝ => f x/x) L (𝓝 α) := by
    simpa [hf0, smul_eq_mul, div_eq_mul_inv, mul_comm] using hf.tendsto_slope_zero
  have hw : Tendsto (fun x : ℝ => -1+(β/α)*x) L (𝓝 (-1)) := by
    simpa using (hid.const_mul (β/α)).const_add (-1)
  let R : ℝ → ℝ := fun x => f x-α*x-β*x^2
  let N : ℝ → ℝ := fun x => (-1+(β/α)*x)*R x+(β^2/α)*x^3
  have hR : R =O[L] (fun x => x^3) := hrem.mono nhdsWithin_le_nhds
  have hN : N =O[L] (fun x => x^3) := by
    have hh₁ : (fun x => (-1+(β/α)*x)*R x) =O[L] (fun x => x^3) := by
      simpa only [one_mul] using (hw.isBigO_one ℝ).mul hR
    have hh := hh₁.add
      (isBigO_const_mul_self (β^2/α) (fun x : ℝ => x^3) L)
    simpa [N, one_mul] using hh
  have hscaled := ((hN.mul ((hq.inv₀ hα).isBigO_one ℝ)).const_mul_left α⁻¹).mul
    (isBigO_refl (fun x : ℝ => (x^2)⁻¹) L)
  have hright (x : ℝ) : (x^3*1)*(x^2)⁻¹=x := by
    by_cases hx : x=0
    · simp [hx]
    · field_simp
  have hs : (fun x => α⁻¹*(N x*(f x/x)⁻¹)*(x^2)⁻¹) =O[L] (fun x => x) := by
    simpa only [hright] using hscaled
  apply hs.congr' ?_ (Eventually.of_forall (fun _ => rfl))
  have hx : ∀ᶠ x : ℝ in L, x≠0 := self_mem_nhdsWithin
  have hqne : ∀ᶠ x : ℝ in L, f x/x ≠ 0 := hq.eventually_ne hα
  filter_upwards [hx,hqne] with x hx hqne
  have hfx : f x≠0 := by intro h; exact hqne (by simp [h])
  dsimp [N,R]
  field_simp
  <;> ring

end Cloning.ScalarTaylor
