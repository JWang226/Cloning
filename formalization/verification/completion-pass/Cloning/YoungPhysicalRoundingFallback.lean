import Cloning.TensorSchurDecompositionConcentration
import Cloning.YoungGeneralFallback

/-! The actual physical Schur law makes the manuscript's fallback negligible. -/
noncomputable section
open scoped BigOperators Topology Classical
open Filter
namespace Cloning.YoungGeneral
open Cloning.TensorLie YoungCompatibility
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

/-- Every label with nonzero physical mass is an actual Young partition. -/
theorem tensorYoung_integerShape_isYoung {d N : ℕ} (p : Fin d → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1)
    (μ : Shape d N) (hμ : (tensorYoungPMF N d p hp hs μ).toReal ≠ 0) :
    IsYoung N (integerShape μ) := by
  have hvalid : Antitone (fun i ↦ (μ i).val) ∧ (∑ i, (μ i).val) = N := by
    by_contra hh
    have hz : tensorYoungPMF N d p hp hs μ = 0 :=
      physicalYoungPMF_eq_zero_of_not_partition _ _ _ _ _ _ μ (not_and_or.mp hh)
    exact hμ (by simp [hz])
  refine ⟨fun i ↦ Int.natCast_nonneg _, ?_, ?_⟩
  · intro i j hij
    dsimp only [integerShape]
    exact_mod_cast hvalid.1 hij
  · dsimp only [integerShape]
    exact_mod_cast hvalid.2

/-- Physical atypical probability is bounded by the proved concentration tail. -/
theorem tensorYoung_badMass_le_tail {d N : ℕ} (p : Fin (d + 1) → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) (ε : ℝ) :
    badMass (tensorYoungPMF N (d+1) p hp hs)
      (fun μ ↦ Typical N p ε (integerShape μ)) ≤
      tailProbability (tensorYoungPMF N (d+1) p hp hs) p ε := by
  unfold badMass tailProbability
  rw [tsum_fintype]
  apply Finset.sum_le_sum
  intro μ _
  by_cases hz : (tensorYoungPMF N (d+1) p hp hs μ).toReal = 0
  · simp [probability, hz]
  · have hyoung := tensorYoung_integerShape_isYoung p hp hs μ hz
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

/-- The actual physical input law has vanishing fallback error against any target law,
uniformly along every moving spectrum in a compact positive simple-spectrum set. -/
theorem tensorYoung_fallback_errors_tendsto_zero {d : ℕ} (hd : 1 ≤ d)
    (K : Set (Fin (d + 1) → ℝ)) (hK : IsCompact K)
    (hpos : ∀ p ∈ K, ∀ i, 0 < p i) (hanti : ∀ p ∈ K, StrictAnti p)
    (m : ℕ → ℤ) (γn : ℕ → ℝ) (γ : ℝ) (hγ : 1 < γ)
    (hγn : Tendsto γn atTop (𝓝 γ))
    (hm : ∀ n, (m n : ℝ) = γn n * (n : ℝ))
    (p : ℕ → Fin (d + 1) → ℝ) (hp : ∀ n, p n ∈ K)
    (hs : ∀ n, ∑ i, p n i = 1) (Q : ℕ → PMF (Fin (d + 1) → ℤ)) :
    let P := fun n ↦ tensorYoungPMF n (d+1) (p n) (fun i ↦ (hpos _ (hp n) i).le) (hs n)
    Tendsto (fun n ↦ CountableScheffe.l1Distance
      (probability ((P n).bind (fun μ ↦ fallbackKernel (γn n) n (m n) (integerShape μ))))
      (probability ((P n).bind (fun μ ↦ rawKernel (γn n) (m n) (integerShape μ))))) atTop (𝓝 0) ∧
    Tendsto (fun n ↦ |CountableScheffe.affinity
      (probability ((P n).bind (fun μ ↦ fallbackKernel (γn n) n (m n) (integerShape μ))))
        (probability (Q n)) -
      CountableScheffe.affinity
        (probability ((P n).bind (fun μ ↦ rawKernel (γn n) (m n) (integerShape μ))))
        (probability (Q n))|) atTop (𝓝 0) := by
  dsimp only
  let P := fun n ↦ tensorYoungPMF n (d+1) (p n) (fun i ↦ (hpos _ (hp n) i).le) (hs n)
  have htail := tensorYoungPMF_tail_tendsto_zero p
    (fun n i ↦ (hpos (p n) (hp n) i).le) hs (fun n ↦ (hanti (p n) (hp n)).antitone)
  have hbad : Tendsto (fun n ↦ badMass (P n)
      (fun μ ↦ Typical n (p n) (shrinkingRadius n) (integerShape μ))) atTop (𝓝 0) := by
    apply squeeze_zero (fun n ↦ badMass_nonneg _ _) (fun n ↦
      tensorYoung_badMass_le_tail (p n) _ (hs n) _) htail
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
