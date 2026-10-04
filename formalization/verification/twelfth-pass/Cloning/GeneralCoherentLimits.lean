import Cloning.GeneralCoherentCoordinates
import Cloning.GeneralCoherentConvergence

/-! Moving-parameter coherent limits of actual normalized finite-dimensional
tensor products in every finite number of excitation modes. -/
noncomputable section
open scoped BigOperators InnerProductSpace Topology
open Filter
namespace Cloning.GeneralCoherent
open GeneralSymmetricOccupation
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

def factorialProduct {s : ℕ} (k : Fin s → ℕ) : ℝ := ∏ i, ((k i).factorial : ℝ)
theorem factorialProduct_pos {s : ℕ} (k : Fin s → ℕ) : 0 < factorialProduct k := by
  apply Finset.prod_pos
  intro i hi
  exact_mod_cast Nat.factorial_pos (k i)

theorem scaled_multiplicity {L s : ℕ} (k : Fin s → ℕ) (hk : (∑ i, k i) ≤ L) :
    (multiplicity (fromExcitation k hk) : ℝ) / (L : ℝ) ^ (∑ i, k i) =
      ((L.choose (∑ i, k i) : ℝ) * (1 / L) ^ (∑ i, k i)) *
        ((∑ i, k i).factorial : ℝ) / factorialProduct k := by
  have hm : (multiplicity (fromExcitation k hk) : ℝ) * factorialProduct k =
      (L.choose (∑ i, k i) : ℝ) * ((∑ i, k i).factorial : ℝ) := by
    unfold factorialProduct
    exact_mod_cast multiplicity_fromExcitation_mul k hk
  have he := (eq_div_iff (factorialProduct_pos k).ne').mpr hm
  rw [he]
  ring

theorem productVector_coefficients {s : ℕ} (z : Fin s → ℂ) (L : ℕ)
    (k : Fin s → ℕ) (hk : (∑ i, k i) ≤ L) :
    productVector z L k =
      (Real.sqrt (((L.choose (∑ i, k i) : ℝ) * (1 / L) ^ (∑ i, k i)) *
        ((∑ i, k i).factorial : ℝ) / factorialProduct k) : ℂ) *
      (∏ i, z i ^ k i) / (Real.sqrt ((1 + energy z / L) ^ L) : ℂ) := by
  rw [productVector_apply_of_le z L k hk, oneParticle_occupation_product,
    excitation_fromExcitation, ← scaled_multiplicity k hk]
  have he := energy_nonneg z
  rw [Real.sqrt_div (Nat.cast_nonneg _), Thermal.sqrt_nat_pow (Nat.cast_nonneg L),
    Thermal.sqrt_nat_pow (by positivity : 0 ≤ 1 + energy z / L)]
  push_cast
  ring

theorem coherentVector_coefficients {s : ℕ} (z : Fin s → ℂ) (k : Fin s → ℕ) :
    MultimodeCoherent.coherentVector z k =
      (Real.exp (-energy z / 2) : ℂ) * (∏ i, z i ^ k i) /
        (Real.sqrt (factorialProduct k) : ℂ) := by
  rw [MultimodeCoherent.coherentVector_coefficients]
  simp only [Finset.prod_div_distrib, Finset.prod_mul_distrib]
  have he : (∏ i, Real.exp (-‖z i‖ ^ 2 / 2)) = Real.exp (-energy z / 2) := by
    rw [← Real.exp_sum]
    congr 1
    unfold energy
    rw [← Finset.sum_div, Finset.sum_neg_distrib]
  have hs : (∏ i, Real.sqrt ((k i).factorial : ℝ)) = Real.sqrt (factorialProduct k) := by
    exact (Real.sqrt_prod Finset.univ (fun i _ => Nat.cast_nonneg _)).symm
  rw [← Complex.ofReal_prod, ← Complex.ofReal_prod, he, hs]

/-- Energy is continuous even when excitation coordinates vanish. -/
theorem continuous_energy (s : ℕ) : Continuous (@energy s) := by
  unfold energy
  fun_prop

/-- The complex occupation coefficients converge while both sample size and
local amplitude vary. -/
theorem productVector_coefficient_moving_tendsto {s : ℕ}
    (L : ℕ → ℕ) (hL : Tendsto L atTop atTop) (z : ℕ → Fin s → ℂ)
    {w : Fin s → ℂ} (hz : Tendsto z atTop (𝓝 w)) (k : Fin s → ℕ) :
    Tendsto (fun n => productVector (z n) (L n) k) atTop
      (𝓝 (MultimodeCoherent.coherentVector w k)) := by
  have hn := (PoissonApproximation.tendsto_binomial_numerator 1 (∑ i, k i)).comp hL
  simp only [one_pow, Function.comp_def] at hn
  have hm := (hn.mul_const ((∑ i, k i).factorial : ℝ)).div_const (factorialProduct k)
  have heq : (1 / ((∑ i, k i).factorial : ℝ) * ((∑ i, k i).factorial : ℝ)) /
      factorialProduct k = 1 / factorialProduct k := by
    rw [one_div_mul_cancel (by exact_mod_cast (Nat.factorial_ne_zero (∑ i, k i))) ]
  rw [heq] at hm
  have hs := (Real.continuous_sqrt.tendsto _).comp hm
  have hp : Tendsto (fun n => ∏ i, z n i ^ k i) atTop (𝓝 (∏ i, w i ^ k i)) := by
    exact tendsto_finset_prod _ (fun i _ => ((continuous_apply i).tendsto w |>.comp hz).pow (k i))
  have he := (continuous_energy s).tendsto w |>.comp hz
  have hd := (Real.continuous_sqrt.tendsto _).comp
    (ComplexCoherent.moving_exponential L hL (fun n => energy (z n)) he
      (fun n => energy_nonneg (z n)))
  have hdc : (Real.sqrt (Real.exp (energy w)) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (Real.exp_pos _)).ne'
  have h := ((Complex.continuous_ofReal.tendsto _).comp hs |>.mul hp).div
    ((Complex.continuous_ofReal.tendsto _).comp hd) hdc
  have hlim : (Real.sqrt (1 / factorialProduct k) : ℂ) * (∏ i, w i ^ k i) /
      (Real.sqrt (Real.exp (energy w)) : ℂ) = MultimodeCoherent.coherentVector w k := by
    rw [coherentVector_coefficients, Real.sqrt_div (by norm_num), Real.sqrt_one,
      ← Real.exp_half]
    rw [show -energy w / 2 = -(energy w / 2) by ring, Real.exp_neg]
    push_cast
    ring
  rw [hlim] at h
  apply h.congr'
  filter_upwards [hL.eventually (eventually_ge_atTop (∑ i, k i))] with n hn
  exact (productVector_coefficients (z n) (L n) k hn).symm

/-- Norm convergence of the genuine padded physical tensor vectors with a
varying local parameter. -/
theorem productVector_moving_tendsto {s : ℕ}
    (L : ℕ → ℕ) (hL : Tendsto L atTop atTop) (z : ℕ → Fin s → ℂ)
    {w : Fin s → ℂ} (hz : Tendsto z atTop (𝓝 w)) :
    Tendsto (fun n => productVector (z n) (L n)) atTop
      (𝓝 (MultimodeCoherent.coherentVector w)) :=
  lp_tendsto_of_coefficients _ _ (fun n => productVector_norm (z n) (L n))
    (MultimodeCoherent.coherentVector_norm w)
    (productVector_coefficient_moving_tendsto L hL z hz)

end Cloning.GeneralCoherent
