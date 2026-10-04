import Cloning.YoungGeneralLimit
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Applying the proved tableau concentration to a Young-label PMF

The premise here is an exact pointwise identification with the concrete
`standardCount * schurPolynomial` formula.  No concentration, dimension,
moment, or vanishing-tail premise remains.  Constructing the Schur measurement
and proving this identification is a separate representation-theoretic task.
-/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace Cloning.YoungGeneral

def tailProbability {d N : ℕ} (P : PMF (Shape d N)) (p : Fin d → ℝ) (ε : ℝ) : ℝ :=
  ∑ μ : Shape d N,
    if ∃ i, (N : ℝ) * ε ≤ |((μ i).val : ℝ) - N * p i| then (P μ).toReal else 0

theorem tailProbability_eq_atypicalMass {d N : ℕ} (P : PMF (Shape d N))
    (p : Fin d → ℝ)
    (hformula : ∀ μ, (P μ).toReal = youngWeight N p (fun i ↦ (μ i).val)) (ε : ℝ) :
    tailProbability P p ε = atypicalMass N p ε := by
  classical
  unfold tailProbability
  simp_rw [hformula]
  have h := sum_youngWeight_mul N p (fun μ ↦
    if ∃ i, (N : ℝ) * ε ≤ |((μ i).val : ℝ) - N * p i| then (1 : ℝ) else 0)
  simpa only [mul_ite, mul_one, mul_zero, wordShape_val, atypicalMass] using h

/-- The finite Young PMF tail estimate requires only its exact tableau formula. -/
theorem tailProbability_le {d N : ℕ} (P : PMF (Shape d N)) (p : Fin d → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) (horder : Antitone p)
    (hformula : ∀ μ, (P μ).toReal = youngWeight N p (fun i ↦ (μ i).val))
    (ε : ℝ) (hε : 0 ≤ ε) (hε2 : ε ≤ 2) :
    tailProbability P p ε ≤
      ((N : ℝ) + 1) ^ (d * d) * (2 * d * Real.exp (-(N : ℝ) * ε ^ 2 / 4)) := by
  rw [tailProbability_eq_atypicalMass P p hformula]
  exact atypicalMass_le N p hp hs horder ε hε hε2

/-- Vanishing atypical mass uniformly for arbitrary moving ordered spectra. -/
theorem tailProbability_tendsto_zero {d : ℕ} (P : ∀ N, PMF (Shape d N))
    (p : ℕ → Fin d → ℝ) (hp : ∀ N i, 0 ≤ p N i) (hs : ∀ N, ∑ i, p N i = 1)
    (horder : ∀ N, Antitone (p N))
    (hformula : ∀ N μ, (P N μ).toReal = youngWeight N (p N) (fun i ↦ (μ i).val)) :
    Tendsto (fun N ↦ tailProbability (P N) (p N) (shrinkingRadius N)) atTop (𝓝 0) := by
  simp_rw [tailProbability_eq_atypicalMass _ _ (hformula _)]
  exact atypicalMass_tendsto_zero p hp hs horder

end Cloning.YoungGeneral
