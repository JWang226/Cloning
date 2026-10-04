import Cloning.ComplexCoherent
import Mathlib.Analysis.SpecialFunctions.Exponential

/-! The actual complex coherent-vector inner-product kernel, computed from
its convergent Fock coefficients. No overlap formula is assumed. -/

noncomputable section
open scoped InnerProductSpace Topology BigOperators

namespace Cloning.ComplexCoherent

set_option backward.isDefEq.respectTransparency false

/-- The coefficient inner products are the terms of the complex exponential
series, including their normalization factors. -/
theorem coherentVector_coefficient_inner (z w : ℂ) (n : ℕ) :
    ⟪coherentVector z n, coherentVector w n⟫_ℂ =
      (Real.exp (-‖z‖ ^ 2 / 2) : ℂ) * (Real.exp (-‖w‖ ^ 2 / 2) : ℂ) *
        ((starRingEnd ℂ z * w) ^ n / (n.factorial : ℂ)) := by
  rw [RCLike.inner_apply, coherentVector_apply, coherentVector_apply]
  simp only [map_div₀, map_mul, map_pow, Complex.conj_ofReal]
  rw [div_mul_div_comm]
  have hs : (Real.sqrt (n.factorial : ℝ) : ℂ) *
      (Real.sqrt (n.factorial : ℝ) : ℂ) = (n.factorial : ℂ) := by
    exact_mod_cast Real.mul_self_sqrt (show (0 : ℝ) ≤ n.factorial by positivity)
  rw [hs, mul_pow]
  ring

/-- Exact overlap, first in factorized normalization form. -/
theorem inner_coherentVector_factorized (z w : ℂ) :
    ⟪coherentVector z, coherentVector w⟫_ℂ =
      (Real.exp (-‖z‖ ^ 2 / 2) : ℂ) * (Real.exp (-‖w‖ ^ 2 / 2) : ℂ) *
        Complex.exp (starRingEnd ℂ z * w) := by
  have hs : HasSum (fun n : ℕ => (starRingEnd ℂ z * w) ^ n / (n.factorial : ℂ))
      (Complex.exp (starRingEnd ℂ z * w)) := by
    rw [Complex.exp_eq_exp_ℂ]
    exact NormedSpace.expSeries_div_hasSum_exp _
  rw [lp.inner_eq_tsum]
  simp_rw [coherentVector_coefficient_inner]
  exact (hs.mul_left ((Real.exp (-‖z‖ ^ 2 / 2) : ℂ) *
    (Real.exp (-‖w‖ ^ 2 / 2) : ℂ))).tsum_eq

/-- The standard coherent-state kernel, proved for the actual ℓ² vectors. -/
theorem inner_coherentVector (z w : ℂ) :
    ⟪coherentVector z, coherentVector w⟫_ℂ =
      Complex.exp (((-(‖z‖ ^ 2 + ‖w‖ ^ 2) / 2 : ℝ) : ℂ) +
        starRingEnd ℂ z * w) := by
  rw [inner_coherentVector_factorized, Complex.ofReal_exp, Complex.ofReal_exp,
    ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  ring

end Cloning.ComplexCoherent
