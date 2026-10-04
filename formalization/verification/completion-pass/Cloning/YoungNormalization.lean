import Cloning.YoungRSKPieri
import Cloning.YoungNormalizationBranching
import Cloning.YoungGeneralPMF

/-!
# Normalization of the literal tableau formula and its actual PMF

The reversible finite-array Pieri bijection and standard-word branching
prove that the total tableau weight is `(∑ pᵢ)^N`. Thus a probability spectrum
defines a genuine Young-label PMF directly from `standardCount * schurPolynomial`.
Neither normalization nor a pointwise distribution identification is assumed.
-/

noncomputable section
open scoped BigOperators Classical Topology
open Filter
namespace Cloning.YoungGeneral

theorem totalTableauMass_succ_mul (d N : ℕ) (p : Fin d → ℝ) :
    totalTableauMass d (N + 1) p = totalTableauMass d N p * ∑ i, p i := by
  rw [totalTableauMass_succ, totalTableauMass_eq_standardSum]
  calc
    _ = weightedStandardSum N (fun μ => schurPolynomial N p μ * ∑ i, p i) := by
      apply weightedStandardSum_congr_on_shapes
      intro μ hμ hsum
      have hN : ∀ i, μ i ≤ N := fun i => by
        simpa only [hsum] using row_le_sum μ i
      calc
        _ = ∑ i : Fin d, schurPolynomial (N + 1) p (addBox μ i) := by
          apply Finset.sum_congr rfl
          intro i _
          by_cases hi : Antitone (addBox μ i)
          · simp only [if_pos hi]
          · simp only [if_neg hi, schurPolynomial_eq_zero_of_not_antitone (N + 1) p _ hi]
        _ = _ := schurPolynomial_pieri N p μ hμ hN
    _ = _ := by
      unfold weightedStandardSum
      simp only [ite_mul, zero_mul, Finset.sum_mul]

/-- Exact normalization polynomial in every alphabet size, including zero
probabilities and the empty alphabet. -/
theorem totalTableauMass_eq_pow (d N : ℕ) (p : Fin d → ℝ) :
    totalTableauMass d N p = (∑ i, p i) ^ N := by
  induction N with
  | zero => simp only [totalTableauMass_zero, pow_zero]
  | succ N ih => rw [totalTableauMass_succ_mul, ih, pow_succ]

theorem totalTableauMass_eq_one {d : ℕ} (N : ℕ) (p : Fin d → ℝ)
    (hs : ∑ i, p i = 1) : totalTableauMass d N p = 1 := by
  rw [totalTableauMass_eq_pow, hs, one_pow]

theorem sum_youngWeight_eq_one {d : ℕ} (N : ℕ) (p : Fin d → ℝ)
    (hs : ∑ i, p i = 1) :
    (∑ μ : Shape d N, youngWeight N p (fun i => (μ i).val)) = 1 :=
  totalTableauMass_eq_one N p hs

/-- The actual normalized tableau law, constructed from its proved finite
weights. -/
def tableauPMF {d : ℕ} (N : ℕ) (p : Fin d → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) : PMF (Shape d N) :=
  PMF.ofFintype (fun μ => ENNReal.ofReal (youngWeight N p (fun i => (μ i).val))) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun μ _ => youngWeight_nonneg N p hp _),
      sum_youngWeight_eq_one N p hs, ENNReal.ofReal_one])

@[simp] theorem tableauPMF_apply {d : ℕ} (N : ℕ) (p : Fin d → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) (μ : Shape d N) :
    tableauPMF N p hp hs μ = ENNReal.ofReal (youngWeight N p (fun i => (μ i).val)) := rfl

@[simp] theorem tableauPMF_toReal {d : ℕ} (N : ℕ) (p : Fin d → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) (μ : Shape d N) :
    (tableauPMF N p hp hs μ).toReal = youngWeight N p (fun i => (μ i).val) :=
  ENNReal.toReal_ofReal (youngWeight_nonneg N p hp _)

theorem tableauPMF_support {d : ℕ} (N : ℕ) (p : Fin d → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) (μ : Shape d N)
    (hμ : tableauPMF N p hp hs μ ≠ 0) :
    Antitone (fun i => (μ i).val) ∧ (∑ i, (μ i).val) = N := by
  apply youngWeight_support N p _
  intro hz
  apply hμ
  simp only [tableauPMF_apply, hz, ENNReal.ofReal_zero]

/-- The proved tail bound now applies to a constructed PMF, with no formula
identification hypothesis. -/
theorem tableauPMF_tailProbability_le {d : ℕ} (N : ℕ) (p : Fin d → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) (horder : Antitone p)
    (ε : ℝ) (hε : 0 ≤ ε) (hε2 : ε ≤ 2) :
    tailProbability (tableauPMF N p hp hs) p ε ≤
      ((N : ℝ) + 1) ^ (d * d) * (2 * d * Real.exp (-(N : ℝ) * ε ^ 2 / 4)) :=
  tailProbability_le _ p hp hs horder (tableauPMF_toReal N p hp hs) ε hε hε2

/-- Shrinking-window concentration for the actual PMFs, uniformly for moving
ordered spectra, including degeneracies. -/
theorem tableauPMF_tailProbability_tendsto_zero {d : ℕ} (p : ℕ → Fin d → ℝ)
    (hp : ∀ N i, 0 ≤ p N i) (hs : ∀ N, ∑ i, p N i = 1)
    (horder : ∀ N, Antitone (p N)) :
    Tendsto (fun N => tailProbability (tableauPMF N (p N) (hp N) (hs N))
      (p N) (shrinkingRadius N)) atTop (𝓝 0) :=
  tailProbability_tendsto_zero _ p hp hs horder (fun N => tableauPMF_toReal N _ _ _)

end Cloning.YoungGeneral
