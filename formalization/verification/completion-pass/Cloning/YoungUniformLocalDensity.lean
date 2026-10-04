import Cloning.YoungUniformLocalGaussian
import Cloning.YoungUniformLocalMultinomial

/-! Exact agreement between Gaussian lattice masses and the normalized
Euclidean root-space Gaussian density. -/
noncomputable section
open scoped BigOperators Topology Classical
open MeasureTheory Filter
namespace Cloning.YoungHyperplane
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

/-- The actual cell-volume multiplier turns the explicit Gaussian mass into
the normalized covariance density, including every Jacobian factor. -/
theorem scaled_gaussianMass_eq_covarianceGaussian (d N : ℕ) (hN : 0 < N)
    (p : Fin (d + 1) → ℝ) (hp : ∑ i, p i = 1) (hp0 : ∀ i, 0 < p i)
    (x : rootSpace d) :
    (Real.sqrt (N : ℝ) ^ d / Real.sqrt ((d : ℝ) + 1)) *
      YoungMultinomial.gaussianMass N p (fun i ↦ x.1 i) = covarianceGaussian d p hp x := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hc : 0 < Real.sqrt (N : ℝ) ^ d / Real.sqrt ((d : ℝ) + 1) := by positivity
  rw [covarianceGaussian_eq_exp d p hp hp0 x]
  conv_lhs => rw [← Real.exp_log hc]
  rw [YoungMultinomial.gaussianMass, ← Real.exp_add]
  congr 1
  rw [Real.log_div (by positivity) (by positivity), Real.log_pow,
    Real.log_sqrt hn.le, Real.log_sqrt (by positivity)]
  simp only [YoungMultinomial.gaussianLogMass, Fintype.card_fin, Nat.cast_add, Nat.cast_one]
  rw [Real.log_mul (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero) hn.ne']
  simp only [div_mul_eq_div_mul_one_div, one_div]
  have hquad : (∑ i, (x.1 i) ^ 2 / 2 * (p i)⁻¹) =
      (1 / 2) * ∑ i, (x.1 i) ^ 2 / p i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hquad]
  ring

/-- A direct local central limit for the density values at lattice centers. -/
theorem uniform_multinomial_density_ratio (d : ℕ) (a R : ℝ) (ha : 0 < a) (hR : 0 ≤ R)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (p : Fin (d + 1) → ℝ) (hp : ∑ i, p i = 1)
      (hp0 : ∀ i, 0 < p i) (x : rootSpace d) (μ : Fin (d + 1) → ℕ),
      (∀ i, a ≤ p i) → (∀ i, |x.1 i| ≤ R) →
      (∀ i, (μ i : ℝ) = N * (p i + x.1 i / Real.sqrt N)) →
      |(Real.sqrt (N : ℝ) ^ d / Real.sqrt ((d : ℝ) + 1)) *
        YoungMultinomial.multinomialMass N p μ / covarianceGaussian d p hp x - 1| < ε := by
  obtain ⟨N₀, hN₀⟩ := YoungMultinomial.uniform_multinomial_local_limit
    (ι := Fin (d + 1)) a R ha hR ε hε
  refine ⟨max N₀ 1, ?_⟩
  intro N hN p hp hp0 x μ hpa hx hμ
  have hn : 0 < N := by omega
  have h := hN₀ N (le_trans (le_max_left _ _) hN) p (fun i ↦ x.1 i) μ hpa hp x.2 hx hμ
  have hc : (Real.sqrt (N : ℝ) ^ d / Real.sqrt ((d : ℝ) + 1)) ≠ 0 := by positivity
  rw [← scaled_gaussianMass_eq_covarianceGaussian d N hn p hp hp0 x, mul_div_mul_left _ _ hc]
  exact h

end Cloning.YoungHyperplane
