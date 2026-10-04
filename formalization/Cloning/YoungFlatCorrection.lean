import Cloning.YoungFlatMass

/-! A continuous positive-part Vandermonde correction, including collision boundaries. -/
noncomputable section
open scoped BigOperators Topology Classical
open Filter
namespace Cloning.YoungFlat
open Cloning.TensorLie
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

/-- The continuous chamber factor in the flat local limit. -/
def vandermondeFactor {r : ℕ} (x : Fin r → ℝ) : ℝ :=
  ∏ a : PositiveRoot r, (max (x a.val.1-x a.val.2) 0)^2 /
    ((1/(r : ℝ))*((a.val.2.val : ℝ)-a.val.1.val))

/-- The exact correction expressed at mesh `t=1/sqrt N`. -/
def scaledCorrection {r : ℕ} (t : ℝ) (x : Fin r → ℝ) : ℝ :=
  ∏ a : PositiveRoot r,
    (max (x a.val.1-x a.val.2+((a.val.2.val : ℝ)-a.val.1.val)*t) 0)^2 /
    ((1/(r : ℝ)+x a.val.1*t+((a.val.2.val : ℝ)-a.val.1.val)*t^2)*
      ((a.val.2.val : ℝ)-a.val.1.val))

theorem positiveCorrection_eq_scaled {r N : ℕ} (hN : 0 < N) (μ : Fin r → ℕ) (x : Fin r → ℝ)
    (hc : ∀ i, (μ i : ℝ) = N*(1/(r : ℝ)+x i/Real.sqrt (N : ℝ))) :
    positiveCorrection μ = scaledCorrection (Real.sqrt (N : ℝ))⁻¹ x := by
  have hn : (N : ℝ) ≠ 0 := by positivity
  have hs : Real.sqrt (N : ℝ) ≠ 0 := by positivity
  have hsq : Real.sqrt (N : ℝ)^2 = (N : ℝ) := Real.sq_sqrt (Nat.cast_nonneg N)
  apply Finset.prod_congr rfl
  intro a _
  let gap : ℝ := a.val.2.val-a.val.1.val
  have hnumer : ((μ a.val.1 : ℝ)-μ a.val.2+a.val.2.val-a.val.1.val)/Real.sqrt (N : ℝ) =
      x a.val.1-x a.val.2+gap*(Real.sqrt (N : ℝ))⁻¹ := by
    rw [hc, hc]
    dsimp [gap]
    field_simp
    ring_nf
    simp only [hsq]
    <;> ring
  have hdenom : ((μ a.val.1 : ℝ)+a.val.2.val-a.val.1.val)/(N : ℝ) =
      1/(r : ℝ)+x a.val.1*(Real.sqrt (N : ℝ))⁻¹+gap*((Real.sqrt (N : ℝ))⁻¹)^2 := by
    rw [hc]
    dsimp [gap]
    field_simp
    ring_nf
    simp only [hsq]
    <;> ring
  change (max ((μ a.val.1 : ℝ)-μ a.val.2+a.val.2.val-a.val.1.val) 0)^2 /
      (((μ a.val.1 : ℝ)+a.val.2.val-a.val.1.val)*gap) = _
  rw [← hnumer, ← hdenom, ← zero_div (Real.sqrt (N : ℝ)),
    max_div_div_right (Real.sqrt_nonneg _), div_pow, hsq]
  field_simp
  simp only [zero_div]
  rfl

theorem scaledCorrection_tendsto {r : ℕ} (hr : 0 < r)
    (t : ℕ → ℝ) (ht : Tendsto t atTop (𝓝 0)) (x : ℕ → Fin r → ℝ) (x₀ : Fin r → ℝ)
    (hx : ∀ i, Tendsto (fun n ↦ x n i) atTop (𝓝 (x₀ i))) :
    Tendsto (fun n ↦ scaledCorrection (t n) (x n)) atTop (𝓝 (vandermondeFactor x₀)) := by
  apply tendsto_finset_prod
  intro a _
  have hg : 0 < (a.val.2.val : ℝ)-a.val.1.val := by
    exact sub_pos.mpr (by exact_mod_cast Fin.lt_def.mp a.property)
  have hrR : 0 < (r : ℝ) := by exact_mod_cast hr
  have hh := ((((hx a.val.1).sub (hx a.val.2)).add
    (ht.const_mul ((a.val.2.val : ℝ)-a.val.1.val))).max (tendsto_const_nhds (x := (0 : ℝ)))).pow 2
  have hd := (((tendsto_const_nhds (x := 1/(r : ℝ))).add ((hx a.val.1).mul ht)).add
    ((ht.pow 2).const_mul ((a.val.2.val : ℝ)-a.val.1.val))).mul_const
      ((a.val.2.val : ℝ)-a.val.1.val)
  simpa only [mul_zero, add_zero, zero_pow (by omega : 2 ≠ 0)] using
    hh.div hd (by simpa using (show (1/(r : ℝ))*((a.val.2.val : ℝ)-a.val.1.val) ≠ 0 by positivity))

theorem continuous_vandermondeFactor (r : ℕ) : Continuous (@vandermondeFactor r) := by
  unfold vandermondeFactor
  apply continuous_finset_prod
  intro a _
  exact (((continuous_apply a.val.1).sub (continuous_apply a.val.2)).max continuous_const).pow 2 |>.div_const _

theorem vandermondeFactor_nonneg {r : ℕ} (hr : 0 < r) (x : Fin r → ℝ) :
    0 ≤ vandermondeFactor x := by
  apply Finset.prod_nonneg
  intro a _
  have hg : 0 < (a.val.2.val : ℝ)-a.val.1.val := by
    exact sub_pos.mpr (by exact_mod_cast Fin.lt_def.mp a.property)
  exact div_nonneg (sq_nonneg _) (mul_nonneg (by positivity) hg.le)

end Cloning.YoungFlat
