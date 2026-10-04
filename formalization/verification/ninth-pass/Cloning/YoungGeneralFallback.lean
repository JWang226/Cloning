import Cloning.YoungGeneralPMF
import Cloning.YoungCompatibilityFallback

/-!
# General Young formula implies asymptotically negligible fallback

The input law is a genuine finite PMF with the exact tableau formula.  It is
bound to the existing physical-label rounding kernel.  The previous
vanishing-atypical-mass premise is replaced by the proved general-rank
concentration estimate.
-/

noncomputable section
open scoped BigOperators Topology Classical
open Filter

namespace Cloning.YoungGeneral
open YoungCompatibility

def integerShape {d N : ℕ} (μ : Shape d N) : Fin d → ℤ := fun i ↦ (μ i).val

theorem integerShape_isYoung {d N : ℕ} (P : PMF (Shape d N)) (p : Fin d → ℝ)
    (hformula : ∀ μ, (P μ).toReal = youngWeight N p (fun i ↦ (μ i).val))
    (μ : Shape d N) (hμ : (P μ).toReal ≠ 0) :
    IsYoung N (integerShape μ) := by
  have h := youngWeight_support N p (fun i ↦ (μ i).val) (by rwa [← hformula μ])
  refine ⟨fun i ↦ Int.natCast_nonneg _, ?_, ?_⟩
  · intro i j hij
    dsimp only [integerShape]
    exact_mod_cast h.1 hij
  · dsimp only [integerShape]
    exact_mod_cast h.2

/-- The PMF's entire bad-label mass is bounded by the explicitly proved
coordinate tail, including the partition-support condition. -/
theorem badMass_integerShape_le_tail {d N : ℕ} (P : PMF (Shape (d + 1) N))
    (p : Fin (d + 1) → ℝ)
    (hformula : ∀ μ, (P μ).toReal = youngWeight N p (fun i ↦ (μ i).val)) (ε : ℝ) :
    badMass P (fun μ ↦ Typical N p ε (integerShape μ)) ≤ tailProbability P p ε := by
  classical
  unfold badMass tailProbability
  rw [tsum_fintype]
  apply Finset.sum_le_sum
  intro μ _
  by_cases hz : (P μ).toReal = 0
  · simp [probability, hz]
  · have hyoung := integerShape_isYoung P p hformula μ hz
    by_cases ht : Typical N p ε (integerShape μ)
    · simp only [if_pos ht]
      positivity
    · have hex : ∃ i, (N : ℝ) * ε ≤ |((μ i).val : ℝ) - N * p i| := by
        by_contra hn
        push_neg at hn
        apply ht
        refine ⟨hyoung, fun i ↦ ?_⟩
        simpa only [integerShape, Int.cast_natCast] using (hn i).le
      simp [ht, hex, probability]

/-- General-rank disappearance of the actual fallback.  All statistical
assumptions are exact spectrum/formula identifications; there is no input
concentration or vanishing-error premise. -/
theorem tableau_fallback_errors_tendsto_zero {d : ℕ} (hd : 1 ≤ d)
    (K : Set (Fin (d + 1) → ℝ)) (hK : IsCompact K)
    (hpos : ∀ p ∈ K, ∀ i, 0 < p i) (hanti : ∀ p ∈ K, StrictAnti p)
    (m : ℕ → ℤ) (γn : ℕ → ℝ) (γ : ℝ) (hγ : 1 < γ)
    (hγn : Tendsto γn atTop (𝓝 γ))
    (hm : ∀ n, (m n : ℝ) = γn n * (n : ℝ))
    (p : ℕ → Fin (d + 1) → ℝ) (hp : ∀ n, p n ∈ K)
    (hs : ∀ n, ∑ i, p n i = 1)
    (P : ∀ N, PMF (Shape (d + 1) N)) (Q : ℕ → PMF (Fin (d + 1) → ℤ))
    (hformula : ∀ N μ, (P N μ).toReal = youngWeight N (p N) (fun i ↦ (μ i).val)) :
    Tendsto (fun n ↦ CountableScheffe.l1Distance
      (probability ((P n).bind (fun μ ↦ fallbackKernel (γn n) n (m n) (integerShape μ))))
      (probability ((P n).bind (fun μ ↦ rawKernel (γn n) (m n) (integerShape μ))))) atTop (𝓝 0) ∧
    Tendsto (fun n ↦ |CountableScheffe.affinity
      (probability ((P n).bind (fun μ ↦ fallbackKernel (γn n) n (m n) (integerShape μ))))
        (probability (Q n)) -
      CountableScheffe.affinity
        (probability ((P n).bind (fun μ ↦ rawKernel (γn n) (m n) (integerShape μ))))
        (probability (Q n))|) atTop (𝓝 0) := by
  have htail := tailProbability_tendsto_zero P p
    (fun n i ↦ (hpos (p n) (hp n) i).le) hs (fun n ↦ (hanti (p n) (hp n)).antitone) hformula
  have hbad : Tendsto (fun n ↦ badMass (P n)
      (fun μ ↦ Typical n (p n) (shrinkingRadius n) (integerShape μ))) atTop (𝓝 0) := by
    apply squeeze_zero (fun n ↦ badMass_nonneg _ _) (fun n ↦
      badMass_integerShape_le_tail (P n) (p n) (hformula n) _) htail
  have hbad2 := hbad.const_mul 2
  simp only [mul_zero] at hbad2
  obtain ⟨a, ha, hpK, hgap⟩ := compact_spectra_positive_gap K hK hpos hanti
  have hevent := eventually_rounding_support_compatible hd m γn shrinkingRadius γ a ha
    hγ hγn shrinkingRadius_tendsto_zero hm
  have heq : ∀ᶠ n : ℕ in atTop, ∀ μ : Shape (d + 1) n,
      Typical n (p n) (shrinkingRadius n) (integerShape μ) →
        fallbackKernel (γn n) n (m n) (integerShape μ) =
          rawKernel (γn n) (m n) (integerShape μ) := by
    filter_upwards [hevent] with n hn
    intro μ hμ
    apply fallbackKernel_eq_raw_of_support
    exact hn (p n) (hpK (p n) (hp n)) (hgap (p n) (hp n))
      (integerShape μ) hμ.1.2.2 hμ.2
  constructor
  · apply squeeze_zero' (Eventually.of_forall (fun n ↦ tsum_nonneg (fun _ ↦ abs_nonneg _)))
      (heq.mono (fun n hn ↦ bind_fallback_l1_bound (P n) _ _ _ hn)) hbad2
  · apply squeeze_zero' (Eventually.of_forall (fun n ↦ abs_nonneg _))
      (heq.mono (fun n hn ↦ bind_fallback_affinity_bound (P n) _ _ _ hn (Q n)))
    simpa only [Real.sqrt_zero] using hbad2.sqrt

end Cloning.YoungGeneral
