import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.Instances.Nat

/-!
# Exact factorial mass and vanishing Stirling remainders

These identities concern the literal factorial multinomial mass. The residual
is obtained from Mathlib's proved Stirling formula.
-/

noncomputable section
open scoped BigOperators Topology
open Filter
namespace Cloning.YoungMultinomial

/-- The logarithmic Stirling residual. -/
def stirlingResidual (n : ℕ) : ℝ :=
  Real.log (Stirling.stirlingSeq n) - Real.log (Real.sqrt Real.pi)

theorem stirlingResidual_tendsto_zero : Tendsto stirlingResidual atTop (𝓝 0) := by
  simpa [stirlingResidual] using
    (Real.continuousAt_log (by positivity : Real.sqrt Real.pi ≠ 0)).tendsto.comp
      Stirling.tendsto_stirlingSeq_sqrt_pi |>.sub_const (Real.log (Real.sqrt Real.pi))

/-- Every coordinate that grows at least linearly has vanishing residual,
with no convergence assumption on its normalized count. -/
theorem stirlingResidual_tendsto_of_lower_bound (m : ℕ → ℕ) (a : ℝ) (ha : 0 < a)
    (hm : ∀ᶠ N : ℕ in atTop, a * (N : ℝ) ≤ (m N : ℝ)) :
    Tendsto (fun N ↦ stirlingResidual (m N)) atTop (𝓝 0) := by
  have hr : Tendsto (fun N ↦ (m N : ℝ)) atTop atTop :=
    tendsto_atTop_mono' atTop hm (tendsto_natCast_atTop_atTop.const_mul_atTop ha)
  exact stirlingResidual_tendsto_zero.comp (tendsto_natCast_atTop_iff.mp hr)

/-- The exact logarithmic factorial decomposition, for every positive count. -/
theorem log_factorial_eq (n : ℕ) (hn : 0 < n) :
    Real.log (n.factorial : ℝ) =
      ((n : ℝ) + 1 / 2) * Real.log n - n +
        1 / 2 * Real.log (2 * Real.pi) + stirlingResidual n := by
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have h := Stirling.log_stirlingSeq_formula n
  rw [Real.log_div hn0 (Real.exp_ne_zero 1), Real.log_exp,
    Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hn0] at h
  rw [stirlingResidual, Real.log_sqrt (by positivity),
    Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero]
  linarith

/-- The actual multinomial probability mass. -/
def multinomialMass {ι : Type*} [Fintype ι] (N : ℕ) (p : ι → ℝ) (μ : ι → ℕ) : ℝ :=
  (N.factorial : ℝ) * (∏ i, p i ^ μ i) / ∏ i, ((μ i).factorial : ℝ)

theorem multinomialMass_pos {ι : Type*} [Fintype ι] (N : ℕ)
    (p : ι → ℝ) (μ : ι → ℕ) (hp : ∀ i, 0 < p i) :
    0 < multinomialMass N p μ := by
  unfold multinomialMass
  exact div_pos (mul_pos (by positivity) (Finset.prod_pos fun i _ ↦ pow_pos (hp i) _))
    (Finset.prod_pos fun i _ ↦ by positivity)

/-- Exact logarithm of the factorial formula. -/
theorem log_multinomialMass {ι : Type*} [Fintype ι] (N : ℕ)
    (p : ι → ℝ) (μ : ι → ℕ) (hp : ∀ i, 0 < p i) :
    Real.log (multinomialMass N p μ) =
      Real.log (N.factorial : ℝ) + (∑ i, (μ i : ℝ) * Real.log (p i)) -
        ∑ i, Real.log ((μ i).factorial : ℝ) := by
  have hprod : (∏ i, p i ^ μ i) ≠ 0 := Finset.prod_ne_zero_iff.mpr
    (fun i _ ↦ pow_ne_zero _ (hp i).ne')
  rw [multinomialMass, Real.log_div (mul_ne_zero (by positivity) hprod) (by positivity),
    Real.log_mul (by positivity) hprod,
    Real.log_prod (fun i _ ↦ pow_ne_zero _ (hp i).ne'), Real.log_prod (fun i _ ↦ by positivity)]
  simp only [Real.log_pow]

/-- Fully expanded multinomial logarithm with a genuine vanishing Stirling
residual and no unproved asymptotic estimate. -/
theorem log_multinomialMass_stirling {ι : Type*} [Fintype ι] (N : ℕ)
    (p : ι → ℝ) (μ : ι → ℕ) (hp : ∀ i, 0 < p i)
    (hN : 0 < N) (hμ : ∀ i, 0 < μ i) (hsum : ∑ i, μ i = N) :
    Real.log (multinomialMass N p μ) =
      ((N : ℝ) + 1 / 2) * Real.log N -
      (∑ i, ((μ i : ℝ) + 1 / 2) * Real.log (μ i)) +
      (∑ i, (μ i : ℝ) * Real.log (p i)) +
      (1 - Fintype.card ι) / 2 * Real.log (2 * Real.pi) +
      stirlingResidual N - ∑ i, stirlingResidual (μ i) := by
  rw [log_multinomialMass N p μ hp, log_factorial_eq N hN]
  simp_rw [log_factorial_eq _ (hμ _)]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul]
  have hs : (∑ i, (μ i : ℝ)) = N := by exact_mod_cast hsum
  rw [hs]
  ring

end Cloning.YoungMultinomial
