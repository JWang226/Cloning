import Cloning.YoungMultinomialLocalEntropy
import Cloning.YoungMultinomialLocalStirling

/-!
# The multinomial local Gaussian approximation

The finite-count identities and the asymptotic estimates below concern the
literal multinomial mass, and the Gaussian logarithm is explicit.
-/

noncomputable section
open scoped BigOperators Topology
open Filter
namespace Cloning.YoungMultinomial

/-- Logarithm of the Gaussian approximation to one lattice probability.
The cell volume is accounted for when this mass is interpolated. -/
def gaussianLogMass {ι : Type*} [Fintype ι] (N : ℕ) (p x : ι → ℝ) : ℝ :=
  (1 - Fintype.card ι) / 2 * Real.log (2 * Real.pi * N) -
    1 / 2 * (∑ i, Real.log (p i)) - ∑ i, (x i) ^ 2 / (2 * p i)

def gaussianMass {ι : Type*} [Fintype ι] (N : ℕ) (p x : ι → ℝ) : ℝ :=
  Real.exp (gaussianLogMass N p x)

/-- Exact entropy representation of the literal multinomial mass. -/
theorem log_multinomialMass_entropy {ι : Type*} [Fintype ι]
    (N : ℕ) (p q : ι → ℝ) (μ : ι → ℕ) (hp : ∀ i, 0 < p i)
    (hN : 0 < N) (hq : ∀ i, 0 < q i) (hsum : ∑ i, q i = 1)
    (hcount : ∀ i, (μ i : ℝ) = N * q i) :
    Real.log (multinomialMass N p μ) =
      (1 - Fintype.card ι) / 2 * Real.log (2 * Real.pi * N) -
      1 / 2 * (∑ i, Real.log (q i)) -
      N * (∑ i, q i * Real.log (q i / p i)) +
      stirlingResidual N - ∑ i, stirlingResidual (μ i) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hμ : ∀ i, 0 < μ i := fun i ↦ by
    exact_mod_cast (hcount i ▸ mul_pos hn (hq i) : (0 : ℝ) < μ i)
  have hsμ : ∑ i, μ i = N := by
    have hr : (∑ i, (μ i : ℝ)) = N := by
      simp_rw [hcount]
      rw [← Finset.mul_sum, hsum, mul_one]
    exact_mod_cast hr
  rw [log_multinomialMass_stirling N p μ hp hN hμ hsμ]
  have hlogs i : Real.log (μ i : ℝ) = Real.log N + Real.log (q i) := by
    rw [hcount, Real.log_mul hn.ne' (hq i).ne']
  simp_rw [hlogs, hcount, Real.log_div (hq _).ne' (hp _).ne']
  rw [Real.log_mul (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero) hn.ne']
  have hterm i : ((N : ℝ) * q i + 1 / 2) * (Real.log N + Real.log (q i)) =
      (N : ℝ) * Real.log N * q i + 1 / 2 * Real.log N +
        N * (q i * Real.log (q i)) + 1 / 2 * Real.log (q i) := by ring
  simp_rw [hterm, mul_sub]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum, hsum, mul_one]
  simp_rw [mul_assoc (N : ℝ) _ (Real.log (p _)), ← Finset.mul_sum]
  ring

/-- Exact central-window log error, separated into an entropy error, a
smooth prefactor change, and the proved Stirling residual. -/
theorem central_log_error_eq {ι : Type*} [Fintype ι]
    (N : ℕ) (p x : ι → ℝ) (μ : ι → ℕ) (hp : ∀ i, 0 < p i)
    (hN : 0 < N) (hsum : ∑ i, p i = 1) (hzero : ∑ i, x i = 0)
    (hq : ∀ i, 0 < p i + x i / Real.sqrt N)
    (hcount : ∀ i, (μ i : ℝ) = N * (p i + x i / Real.sqrt N)) :
    Real.log (multinomialMass N p μ) - gaussianLogMass N p x =
      -(N * (∑ i, (p i + x i / Real.sqrt N) *
          Real.log ((p i + x i / Real.sqrt N) / p i)) -
        ∑ i, (x i) ^ 2 / (2 * p i)) -
      1 / 2 * (∑ i, Real.log ((p i + x i / Real.sqrt N) / p i)) +
      stirlingResidual N - ∑ i, stirlingResidual (μ i) := by
  have hs : (∑ i, (p i + x i / Real.sqrt N)) = 1 := by
    simp only [Finset.sum_add_distrib, div_eq_mul_inv, ← Finset.sum_mul, hsum,
      hzero, zero_mul, add_zero]
  rw [log_multinomialMass_entropy N p _ μ hp hN hq hs hcount, gaussianLogMass]
  simp_rw [Real.log_div (hq _).ne' (hp _).ne', Finset.sum_sub_distrib]
  ring

end Cloning.YoungMultinomial
