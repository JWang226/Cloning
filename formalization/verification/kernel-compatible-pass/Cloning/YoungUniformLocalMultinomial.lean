import Cloning.YoungMultinomialLocalLimit

/-!
# Epsilon-uniform multinomial local approximation

The estimates hold simultaneously for every positive spectrum with a common
lower bound and every lattice center in a fixed bounded window.
-/

noncomputable section
open scoped BigOperators Topology
open Filter
namespace Cloning.YoungMultinomial

/-- Genuine uniformity in both the spectrum and the central lattice point. -/
theorem uniform_multinomial_local_limit {ι : Type*} [Fintype ι]
    (a R : ℝ) (ha : 0 < a) (hR : 0 ≤ R) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (p x : ι → ℝ) (μ : ι → ℕ),
      (∀ i, a ≤ p i) → (∑ i, p i = 1) → (∑ i, x i = 0) →
      (∀ i, |x i| ≤ R) →
      (∀ i, (μ i : ℝ) = N * (p i + x i / Real.sqrt N)) →
      |multinomialMass N p μ / gaussianMass N p x - 1| < ε := by
  classical
  by_contra h
  push_neg at h
  choose n hn p x μ hp hs hz hx hc hb using h
  have hnlim : Tendsto n atTop atTop := tendsto_atTop_mono hn tendsto_id
  have ht := multinomialMass_div_gaussianMass_tendsto_one_subsequence
    n hnlim p x μ a R ha hR (Eventually.of_forall hp) (Eventually.of_forall hx) hs hz hc
  have he : ∀ᶠ k : ℕ in atTop,
      |multinomialMass (n k) (p k) (μ k) / gaussianMass (n k) (p k) (x k) - 1| < ε := by
    simpa only [Real.dist_eq] using (Metric.tendsto_nhds.mp ht ε hε)
  obtain ⟨k, hk⟩ := he.exists
  exact (not_lt_of_ge (hb k)) hk

end Cloning.YoungMultinomial
