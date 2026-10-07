import Cloning.TensorRootBounds
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Calculus.Taylor

/-! A vector-specific Taylor remainder for actual skew-adjoint exponentials.
The bound uses the iterated generator on the chosen vector, avoiding the
global generator norm that grows with the physical sample size. -/
noncomputable section
open scoped InnerProductSpace Topology BigOperators
open NormedSpace Filter
namespace Cloning.TensorLocalUnitary
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
local instance : NormedAlgebra ℝ (H →L[ℂ] H) := NormedAlgebra.restrictScalars ℝ ℂ _
local instance : NormedAlgebra ℚ (H →L[ℂ] H) := NormedAlgebra.restrictScalars ℚ ℝ _

def expOrbit (A : H →L[ℂ] H) (v : H) (t : ℝ) : H := exp (t • A) v

theorem expOrbit_hasDerivAt (A : H →L[ℂ] H) (v : H) (t : ℝ) :
    HasDerivAt (expOrbit A v) (expOrbit A (A v) t) t := by
  have h := ((ContinuousLinearMap.apply ℂ H v).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_exp_smul_const A t)
  simpa only [expOrbit, ContinuousLinearMap.coe_restrictScalars, ContinuousLinearMap.apply_apply,
    ContinuousLinearMap.mul_apply] using h

theorem expOrbit_iteratedDeriv (A : H →L[ℂ] H) (v : H) (m : ℕ) :
    iteratedDeriv m (expOrbit A v) = expOrbit A ((A ^ m) v) := by
  induction m with
  | zero => simp [expOrbit, iteratedDeriv_zero]
  | succ m ih =>
    rw [iteratedDeriv_succ, ih]
    funext t
    simpa only [pow_succ', ContinuousLinearMap.mul_apply] using
      (expOrbit_hasDerivAt A ((A^m) v) t).deriv

theorem expOrbit_contDiff (A : H →L[ℂ] H) (v : H) (m : ℕ) :
    ContDiff ℝ m (expOrbit A v) := by
  apply contDiff_nat_iff_iteratedDeriv.mpr
  constructor
  · intro j _
    rw [expOrbit_iteratedDeriv]
    exact (show Differentiable ℝ (expOrbit A ((A^j) v)) from
      fun t => (expOrbit_hasDerivAt A ((A^j) v) t).differentiableAt).continuous
  · intro j _
    rw [expOrbit_iteratedDeriv]
    exact fun t => (expOrbit_hasDerivAt A ((A^j) v) t).differentiableAt

theorem expOrbit_norm (A : H →L[ℂ] H) (hA : A.adjoint = -A) (v : H) (t : ℝ) :
    ‖expOrbit A v t‖ = ‖v‖ := by
  apply ContinuousLinearMap.norm_map_of_mem_unitary
  apply exp_mem_unitary_of_mem_skewAdjoint
  change star (t • A) = -(t • A)
  simp only [star_smul, star_trivial, ContinuousLinearMap.star_eq_adjoint, hA, smul_neg]

/-- Actual exponential versus its degree-m Taylor polynomial on one vector.
The only generator hypothesis is literal skew-adjointness; the bound is
`‖A^(m+1) v‖ / m!`, independent of the global operator norm. -/
theorem exp_taylor_vector_remainder
    (A : H →L[ℂ] H) (hA : A.adjoint = -A) (v : H) (m : ℕ) :
    ‖exp A v - ∑ j ∈ Finset.range (m+1), ((j.factorial : ℝ)⁻¹) • ((A^j) v)‖ ≤
      ‖(A^(m+1)) v‖ / m.factorial := by
  have hderiv (j : ℕ) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
      iteratedDerivWithin j (expOrbit A v) (Set.Icc (0 : ℝ) 1) t = expOrbit A ((A^j) v) t := by
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc zero_lt_one)
      (expOrbit_contDiff A v j).contDiffAt ht, expOrbit_iteratedDeriv]
  have h := taylor_mean_remainder_bound (f := expOrbit A v) (a := 0) (b := 1) (x := 1)
    (n := m) zero_le_one (expOrbit_contDiff A v (m+1)).contDiffOn
    (by simp) (C := ‖(A^(m+1)) v‖) (by
      intro t ht
      rw [hderiv (m+1) t ht, expOrbit_norm A hA])
  have hpoly : taylorWithinEval (expOrbit A v) m (Set.Icc (0 : ℝ) 1) 0 1 =
      ∑ j ∈ Finset.range (m+1), ((j.factorial : ℝ)⁻¹) • ((A^j) v) := by
    rw [taylor_within_apply]
    apply Finset.sum_congr rfl
    intro j hj
    rw [hderiv j 0 (by simp)]
    simp only [expOrbit, zero_smul, exp_zero, ContinuousLinearMap.one_apply,
      sub_zero, one_pow, mul_one]
  rw [hpoly] at h
  simpa only [expOrbit, one_smul, sub_zero, one_pow, mul_one] using h

end Cloning.TensorLocalUnitary
