import Cloning.TensorLocalUnitaryCompression

/-! Actual finite-degree physical displacement polynomials have the oscillator
limits after transport into the proved common complete cutoff frames. -/
noncomputable section
open scoped BigOperators InnerProductSpace Topology
open Filter
namespace Cloning.TensorLocalUnitary
open Cloning.TensorLie
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
variable {d : ℕ}

def wordCoordinates (mu : Fin d → ℕ) (hmu : Antitone mu) (Q : ℕ)
    (w : List (PositiveRoot d)) : CutoffIndex d Q → ℂ := fun i =>
  ⟪cutoffFrame (partitionHighestTensor mu hmu) mu Q i,
    normalizedLoweringWord (partitionHighestTensor mu hmu) mu w⟫_ℂ

def limitingWordCoordinates (Q : ℕ) (w : List (PositiveRoot d)) : CutoffIndex d Q → ℂ :=
  fun i => if (cutoffWord d Q i).Perm w then 1 else 0

variable (mu : ℕ → Fin d → ℕ) (hmu : ∀ N, Antitone (mu N))
    (δ : ℕ → ℝ) (hδ : Tendsto δ atTop atTop)
    (hgap : ∀ᶠ N in atTop, ∀ a : PositiveRoot d, δ N ≤ rootGap (mu N) a)
include hδ hgap

theorem wordCoordinates_tendsto (Q : ℕ) (w : List (PositiveRoot d)) :
    Tendsto (fun N => wordCoordinates (mu N) (hmu N) Q w)
      atTop (𝓝 (limitingWordCoordinates Q w)) := by
  apply tendsto_pi_nhds.mpr
  intro i
  apply varying_inner_tendsto_of_two_close
    (fun N => cutoffFrame (partitionHighestTensor (mu N) (hmu N)) (mu N) Q i)
    (fun N => cutoffRawFrame (partitionHighestTensor (mu N) (hmu N)) (mu N) Q i)
    (fun N => normalizedLoweringWord (partitionHighestTensor (mu N) (hmu N)) (mu N) w)
    (fun N => normalizedLoweringWord (partitionHighestTensor (mu N) (hmu N)) (mu N) w)
    1 1 _
  · exact partition_cutoffFrame_close mu hmu δ hδ hgap Q i
  · simp
  · exact partition_cutoffRawFrame_norm_tendsto mu hmu δ hδ hgap Q i
  · exact partition_normalizedWord_norm_tendsto mu hmu δ hδ hgap w
  · exact partition_normalized_gram_tendsto (fun a : PositiveRoot d => a)
      Function.injective_id mu hmu δ hδ hgap (cutoffWord d Q i) w

/-- Exact compression for physical generator powers up to any chosen finite
degree. Every membership and basis premise is proved from physical roots. -/
theorem physical_word_power_eventually_eq (z : ℕ → PositiveRoot d → ℂ)
    (R Q m : ℕ) (hQ : R+m*d ≤ Q) (w : List (PositiveRoot d))
    (hw : loweringHeight w ≤ R) :
    ∀ᶠ N in atTop, ∀ i : CutoffIndex d Q,
      ⟪cutoffFrame (partitionHighestTensor (mu N) (hmu N)) (mu N) Q i,
        (rootGenerator (n := ∑ j, mu N j) (mu N) (z N)^m)
          (normalizedLoweringWord (partitionHighestTensor (mu N) (hmu N)) (mu N) w)⟫_ℂ =
        ((physicalCutoffMatrix (mu N) (hmu N) Q (z N))^m).mulVec
          (wordCoordinates (mu N) (hmu N) Q w) i := by
  filter_upwards [partition_eventually_cutoffOrthonormalBasis mu hmu δ hδ hgap Q] with N hb
  obtain ⟨b, hb⟩ := hb
  have hx : normalizedLoweringWord (partitionHighestTensor (mu N) (hmu N)) (mu N) w ∈
      cyclicCutoff (partitionHighestTensor (mu N) (hmu N)) (R : ℤ) :=
    normalizedLoweringWord_mem_cyclicCutoff _ _ _ (by exact_mod_cast hw)
  have hm (r : ℕ) (hr : r < m) :
      (rootGenerator (n := ∑ j, mu N j) (mu N) (z N)^r)
        (normalizedLoweringWord (partitionHighestTensor (mu N) (hmu N)) (mu N) w) ∈
        cyclicCutoff (partitionHighestTensor (mu N) (hmu N)) (Q : ℤ) := by
    have hs := rootGenerator_pow_mem (partitionHighestTensor (mu N) (hmu N)) (mu N)
      (partitionHighestTensor_cartan (mu N) (hmu N))
      (partitionHighestTensor_raising_zero (mu N) (hmu N)) (z N) R r hx
    apply cyclicCutoff_nat_monotone _ _ hs
    exact (Nat.add_le_add_left (Nat.mul_le_mul_right d (Nat.le_of_lt hr)) R).trans hQ
  intro i
  have hh := inner_pow_eq_mulVec _ b (rootGenerator (mu N) (z N))
    (normalizedLoweringWord (partitionHighestTensor (mu N) (hmu N)) (mu N) w) m hm i
  have hM : ambientMatrix _ b (rootGenerator (mu N) (z N)) =
      physicalCutoffMatrix (mu N) (hmu N) Q (z N) := by
    ext j k
    simp only [ambientMatrix, physicalCutoffMatrix, hb]
  rw [hM] at hh
  simpa only [hb, wordCoordinates] using hh

/-- The literal physical generator powers converge to the finite oscillator
polynomial, with no assumed infinitesimal convergence or chart adapter. -/
theorem physical_word_power_tendsto (z : ℕ → PositiveRoot d → ℂ)
    (z₀ : PositiveRoot d → ℂ) (hz : Tendsto z atTop (𝓝 z₀))
    (R Q m : ℕ) (hQ : R+m*d ≤ Q) (w : List (PositiveRoot d))
    (hw : loweringHeight w ≤ R) (i : CutoffIndex d Q) :
    Tendsto (fun N =>
      ⟪cutoffFrame (partitionHighestTensor (mu N) (hmu N)) (mu N) Q i,
        (rootGenerator (n := ∑ j, mu N j) (mu N) (z N)^m)
          (normalizedLoweringWord (partitionHighestTensor (mu N) (hmu N)) (mu N) w)⟫_ℂ)
      atTop (𝓝 (((oscillatorCutoffMatrix Q z₀)^m).mulVec (limitingWordCoordinates Q w) i)) := by
  have hM := physicalCutoffMatrix_pow_tendsto mu hmu δ hδ hgap z z₀ hz Q m
  have hv := wordCoordinates_tendsto mu hmu δ hδ hgap Q w
  have hlim : Tendsto (fun N => ((physicalCutoffMatrix (mu N) (hmu N) Q (z N))^m).mulVec
      (wordCoordinates (mu N) (hmu N) Q w) i)
      atTop (𝓝 (((oscillatorCutoffMatrix Q z₀)^m).mulVec (limitingWordCoordinates Q w) i)) := by
    unfold Matrix.mulVec dotProduct
    apply tendsto_finset_sum
    intro j _
    exact ((tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hM i) j).mul (tendsto_pi_nhds.mp hv j))
  apply hlim.congr'
  filter_upwards [physical_word_power_eventually_eq mu hmu δ hδ hgap z R Q m hQ w hw] with N hN
  exact (hN i).symm

end Cloning.TensorLocalUnitary
