import Cloning.WeylNumberKernel

/-! The exact ladder recurrence for derivatives of the physical Weyl kernel. -/
noncomputable section
open scoped InnerProductSpace Topology BigOperators
namespace Cloning.MultimodeCoherent
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

def rayNumberKernel (a z : ℂ) (k : ℕ) (t : ℂ) : ℂ :=
  Complex.exp (-(starRingEnd ℂ z * z) / 2 - t ^ 2 * (starRingEnd ℂ a * a) / 2 +
    t * (starRingEnd ℂ z * a)) * (starRingEnd ℂ z - t * starRingEnd ℂ a) ^ k /
      (Real.sqrt (k.factorial : ℝ) : ℂ)

theorem numberKernel_real_smul (a z : ℂ) (k : ℕ) (t : ℝ) :
    numberKernel (t • a) z k = rayNumberKernel a z k (t : ℂ) := by
  simp only [numberKernel, rayNumberKernel, Complex.real_smul, map_mul, Complex.conj_ofReal]
  congr 2
  ring

theorem sqrt_factorial_succ_complex (k : ℕ) :
    (Real.sqrt ((k+1).factorial : ℝ) : ℂ) =
      (Real.sqrt (k+1 : ℝ) : ℂ) * (Real.sqrt (k.factorial : ℝ) : ℂ) := by
  rw [Nat.factorial_succ, Nat.cast_mul, Real.sqrt_mul (by positivity), Complex.ofReal_mul]
  norm_cast

theorem sqrt_factorial_complex_ne_zero (k : ℕ) :
    (Real.sqrt (k.factorial : ℝ) : ℂ) ≠ 0 := by
  exact_mod_cast (ne_of_gt (Real.sqrt_pos.mpr (by positivity : (0 : ℝ) < k.factorial)))

theorem rayNumberKernel_hasDerivAt_raw (a z t : ℂ) (k : ℕ) :
    HasDerivAt (rayNumberKernel a z k)
      ((Complex.exp (-(starRingEnd ℂ z * z) / 2 - t ^ 2 * (starRingEnd ℂ a * a) / 2 +
          t * (starRingEnd ℂ z * a)) *
        (a * (starRingEnd ℂ z - t * starRingEnd ℂ a) *
            (starRingEnd ℂ z - t * starRingEnd ℂ a) ^ k -
          (k : ℂ) * (starRingEnd ℂ z - t * starRingEnd ℂ a) ^ (k-1) * starRingEnd ℂ a)) /
        (Real.sqrt (k.factorial : ℝ) : ℂ)) t := by
  have he := (((hasDerivAt_const t (-(starRingEnd ℂ z * z) / 2)).sub
    ((((hasDerivAt_id t).pow 2).mul_const (starRingEnd ℂ a * a)).div_const 2)).add
      ((hasDerivAt_id t).mul_const (starRingEnd ℂ z * a))).cexp
  have hp := ((hasDerivAt_const t (starRingEnd ℂ z)).sub
    ((hasDerivAt_id t).mul_const (starRingEnd ℂ a))).pow k
  convert (he.mul hp).div_const (Real.sqrt (k.factorial : ℝ) : ℂ) using 1 <;>
    simp only [rayNumberKernel, id_eq, Pi.sub_apply, Pi.add_apply, Pi.pow_apply] <;> ring

theorem sqrt_succ_factorial_ratio (k : ℕ) :
    (Real.sqrt (k+1 : ℝ) : ℂ) / (Real.sqrt ((k+1).factorial : ℝ) : ℂ) =
      1 / (Real.sqrt (k.factorial : ℝ) : ℂ) := by
  rw [sqrt_factorial_succ_complex]
  have h : (Real.sqrt (k+1 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Real.sqrt_pos.mpr (by positivity : (0 : ℝ) < k+1)))
  field_simp

theorem sqrt_pred_factorial_ratio (k : ℕ) :
    (Real.sqrt (k : ℝ) : ℂ) / (Real.sqrt ((k-1).factorial : ℝ) : ℂ) =
      (k : ℂ) / (Real.sqrt (k.factorial : ℝ) : ℂ) := by
  cases k with
  | zero => simp
  | succ k =>
    simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel]
    rw [sqrt_factorial_succ_complex]
    have hs : (Real.sqrt (k+1 : ℝ) : ℂ)^2 = (k+1 : ℂ) := by
      rw [← Complex.ofReal_pow, Real.sq_sqrt (by positivity)]
      push_cast
      rfl
    have hp : (Real.sqrt (k+1 : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (ne_of_gt (Real.sqrt_pos.mpr (by positivity : (0 : ℝ) < k+1)))
    apply (div_eq_div_iff (sqrt_factorial_complex_ne_zero k)
      (mul_ne_zero hp (sqrt_factorial_complex_ne_zero k))).mpr
    push_cast
    linear_combination (Real.sqrt (k.factorial : ℝ) : ℂ) * hs

theorem rayNumberKernel_hasDerivAt (a z t : ℂ) (k : ℕ) :
    HasDerivAt (rayNumberKernel a z k)
      (a * (Real.sqrt (k+1 : ℝ) : ℂ) * rayNumberKernel a z (k+1) t -
        starRingEnd ℂ a * (Real.sqrt (k : ℝ) : ℂ) * rayNumberKernel a z (k-1) t) t := by
  convert rayNumberKernel_hasDerivAt_raw a z t k using 1
  simp only [rayNumberKernel]
  generalize Complex.exp (-(starRingEnd ℂ z * z) / 2 - t ^ 2 * (starRingEnd ℂ a * a) / 2 +
      t * (starRingEnd ℂ z * a)) = E
  generalize starRingEnd ℂ z - t * starRingEnd ℂ a = b
  have hu := sqrt_succ_factorial_ratio k
  have hl := sqrt_pred_factorial_ratio k
  simp only [div_eq_mul_inv] at hu hl ⊢
  rw [pow_succ]
  linear_combination (a * E * b^(k+1)) * hu - (starRingEnd ℂ a * E * b^(k-1)) * hl

theorem numberKernel_ray_hasDerivAt (a z : ℂ) (k : ℕ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => numberKernel (s • a) z k)
      (a * (Real.sqrt (k+1 : ℝ) : ℂ) * numberKernel (t • a) z (k+1) -
        starRingEnd ℂ a * (Real.sqrt (k : ℝ) : ℂ) * numberKernel (t • a) z (k-1)) t := by
  simp_rw [numberKernel_real_smul]
  exact (rayNumberKernel_hasDerivAt a z (t : ℂ) k).comp_ofReal

end Cloning.MultimodeCoherent
