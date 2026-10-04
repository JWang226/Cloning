import Cloning.WeylNumberDerivative
import Mathlib.Analysis.Calculus.Taylor

/-! Actual Weyl Taylor polynomials on the finite number-state domain. -/
noncomputable section
open scoped InnerProductSpace Topology BigOperators
namespace Cloning.MultimodeCoherent
open Cloning.MultimodeCoherentGaussianMixture
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {d : ℕ}

abbrev NumberCoefficients (d : ℕ) := (Fin d → ℕ) →₀ ℂ

def numberVector : NumberCoefficients d →ₗ[ℂ] Fock d :=
  Finsupp.linearCombination ℂ (numberBasis d)

@[simp] theorem numberVector_single (k : Fin d → ℕ) (c : ℂ) :
    numberVector (Finsupp.single k c) = c • numberBasis d k := by
  simp [numberVector]

def numberLadderCoefficients (a : Fin d → ℂ) (k : Fin d → ℕ) : NumberCoefficients d :=
  ∑ i, (Finsupp.single (Function.update k i (k i+1))
      (a i * (Real.sqrt (k i+1 : ℝ) : ℂ)) -
    Finsupp.single (Function.update k i (k i-1))
      (starRingEnd ℂ (a i) * (Real.sqrt (k i : ℝ) : ℂ)))

theorem numberVector_ladderCoefficients (a : Fin d → ℂ) (k : Fin d → ℕ) :
    numberVector (numberLadderCoefficients a k) = numberLadder a k := by
  simp [numberLadderCoefficients, numberLadder]

/-- The unbounded oscillator generator is used only on its invariant algebraic
finite-support domain, where every iterate is an actual finite sum. -/
def numberGenerator (a : Fin d → ℂ) : NumberCoefficients d →ₗ[ℂ] NumberCoefficients d :=
  Finsupp.linearCombination ℂ (numberLadderCoefficients a)

@[simp] theorem numberGenerator_single (a : Fin d → ℂ) (k : Fin d → ℕ) (c : ℂ) :
    numberGenerator a (Finsupp.single k c) = c • numberLadderCoefficients a k := by
  simp [numberGenerator]

theorem numberVector_generator (a : Fin d → ℂ) (c : NumberCoefficients d) :
    numberVector (numberGenerator a c) = ∑ k ∈ c.support, c k • numberLadder a k := by
  simp only [numberGenerator, Finsupp.linearCombination_apply, Finsupp.sum,
    map_sum, map_smul, numberVector_ladderCoefficients]

def numberOrbit (a : Fin d → ℂ) (c : NumberCoefficients d) (t : ℝ) : Fock d :=
  displacement (t • a) (numberVector c)

theorem numberOrbit_hasDerivAt (a : Fin d → ℂ) (c : NumberCoefficients d) (t : ℝ) :
    HasDerivAt (numberOrbit a c) (numberOrbit a (numberGenerator a c) t) t := by
  have h := HasDerivAt.fun_sum (u := c.support)
    (fun k _ => (displacement_number_hasDerivAt a k t).const_smul (c k))
  unfold numberOrbit
  rw [numberVector_generator]
  simpa only [numberVector, Finsupp.linearCombination_apply, Finsupp.sum,
    map_sum, map_smul, Pi.smul_apply] using h

def numberIterate (a : Fin d → ℂ) (c : NumberCoefficients d) : ℕ → NumberCoefficients d
  | 0 => c
  | m+1 => numberGenerator a (numberIterate a c m)

@[simp] theorem numberIterate_zero (a : Fin d → ℂ) (c : NumberCoefficients d) :
    numberIterate a c 0 = c := rfl

@[simp] theorem numberIterate_succ (a : Fin d → ℂ) (c : NumberCoefficients d) (m : ℕ) :
    numberIterate a c (m+1) = numberGenerator a (numberIterate a c m) := rfl

theorem numberOrbit_iteratedDeriv (a : Fin d → ℂ) (c : NumberCoefficients d) (m : ℕ) :
    iteratedDeriv m (numberOrbit a c) = numberOrbit a (numberIterate a c m) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [iteratedDeriv_succ, ih]
    funext t
    exact (numberOrbit_hasDerivAt a (numberIterate a c m) t).deriv

theorem numberOrbit_contDiff (a : Fin d → ℂ) (c : NumberCoefficients d) (m : ℕ) :
    ContDiff ℝ m (numberOrbit a c) := by
  apply contDiff_nat_iff_iteratedDeriv.mpr
  constructor
  · intro j _
    rw [numberOrbit_iteratedDeriv]
    exact (show Differentiable ℝ (numberOrbit a (numberIterate a c j)) from
      fun t => (numberOrbit_hasDerivAt a (numberIterate a c j) t).differentiableAt).continuous
  · intro j _
    rw [numberOrbit_iteratedDeriv]
    exact fun t => (numberOrbit_hasDerivAt a (numberIterate a c j) t).differentiableAt

theorem numberOrbit_norm (a : Fin d → ℂ) (c : NumberCoefficients d) (t : ℝ) :
    ‖numberOrbit a c t‖ = ‖numberVector c‖ := displacement_norm _ _

/-- A Taylor remainder for the actual constructed Weyl operator, with no
operator-norm boundedness assumption on the number-state generator. -/
theorem displacement_taylor_vector_remainder
    (a : Fin d → ℂ) (c : NumberCoefficients d) (m : ℕ) :
    ‖displacement a (numberVector c) -
      ∑ j ∈ Finset.range (m+1), ((j.factorial : ℝ)⁻¹) • numberVector (numberIterate a c j)‖ ≤
      ‖numberVector (numberIterate a c (m+1))‖ / m.factorial := by
  have hderiv (j : ℕ) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
      iteratedDerivWithin j (numberOrbit a c) (Set.Icc (0 : ℝ) 1) t =
        numberOrbit a (numberIterate a c j) t := by
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc zero_lt_one)
      (numberOrbit_contDiff a c j).contDiffAt ht, numberOrbit_iteratedDeriv]
  have h := taylor_mean_remainder_bound (f := numberOrbit a c) (a := 0) (b := 1) (x := 1)
    (n := m) zero_le_one (numberOrbit_contDiff a c (m+1)).contDiffOn
    (by simp) (C := ‖numberVector (numberIterate a c (m+1))‖) (by
      intro t ht
      rw [hderiv (m+1) t ht, numberOrbit_norm])
  have hpoly : taylorWithinEval (numberOrbit a c) m (Set.Icc (0 : ℝ) 1) 0 1 =
      ∑ j ∈ Finset.range (m+1), ((j.factorial : ℝ)⁻¹) • numberVector (numberIterate a c j) := by
    rw [taylor_within_apply]
    apply Finset.sum_congr rfl
    intro j hj
    rw [hderiv j 0 (by simp)]
    simp only [numberOrbit, zero_smul, displacement_zero, ContinuousLinearMap.id_apply,
      sub_zero, one_pow, mul_one]
  rw [hpoly] at h
  simpa only [numberOrbit, one_smul, sub_zero, one_pow, mul_one] using h

end Cloning.MultimodeCoherent
