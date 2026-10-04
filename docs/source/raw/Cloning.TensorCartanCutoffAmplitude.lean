import Cloning.TensorCartanCutoffMatrixLimit
import Cloning.TensorCartanOccupationAmplitude

/-! The actual complete orthonormal cutoff matrices have the explicit
product-binomial oscillator limit. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace Cloning.TensorLie
variable {d : ℕ}

theorem cartanCutoffFrameMatrixElement_tendsto_product_amplitude
    (mu nu : ℕ → Fin d → ℕ) (hmu : ∀ N, Antitone (mu N)) (hnu : ∀ N, Antitone (nu N))
    (δmu δnu : ℕ → ℝ) (hδmu : Tendsto δmu atTop atTop) (hδnu : Tendsto δnu atTop atTop)
    (hmuGap : ∀ᶠ N in atTop, ∀ a : PositiveRoot d, δmu N ≤ rootGap (mu N) a)
    (hnuGap : ∀ᶠ N in atTop, ∀ a : PositiveRoot d, δnu N ≤ rootGap (nu N) a)
    (t : PositiveRoot d → ℝ) (ht0 : ∀ a, 0 ≤ t a) (ht1 : ∀ a, t a ≤ 1)
    (ht : ∀ a, Tendsto (fun N => rootFraction (mu N) (nu N) a) atTop (𝓝 (t a)))
    (R : ℕ) (i j k : CutoffIndex d R)
    (hcount : ∀ a, (cutoffWord d R j).count a + (cutoffWord d R k).count a =
      (cutoffWord d R i).count a) :
    Tendsto (fun N => cartanCutoffFrameMatrixElement (mu N) (nu N) (hmu N) (hnu N) R i j k)
      atTop (𝓝 ((∏ a : PositiveRoot d,
        Cloning.Occupation.splitAmplitude ((cutoffWord d R i).count a)
          ((cutoffWord d R j).count a) (t a) : ℝ) : ℂ)) := by
  rw [← occupationSplitMatrixElement_eq_product_amplitude t ht0 ht1 _ _ _ hcount]
  exact cartanCutoffFrameMatrixElement_tendsto mu nu hmu hnu δmu δnu hδmu hδnu
    hmuGap hnuGap t ht R i j k

theorem cartanCutoffFrameMatrixElement_tendsto_zero_of_incompatible
    (mu nu : ℕ → Fin d → ℕ) (hmu : ∀ N, Antitone (mu N)) (hnu : ∀ N, Antitone (nu N))
    (δmu δnu : ℕ → ℝ) (hδmu : Tendsto δmu atTop atTop) (hδnu : Tendsto δnu atTop atTop)
    (hmuGap : ∀ᶠ N in atTop, ∀ a : PositiveRoot d, δmu N ≤ rootGap (mu N) a)
    (hnuGap : ∀ᶠ N in atTop, ∀ a : PositiveRoot d, δnu N ≤ rootGap (nu N) a)
    (t : PositiveRoot d → ℝ)
    (ht : ∀ a, Tendsto (fun N => rootFraction (mu N) (nu N) a) atTop (𝓝 (t a)))
    (R : ℕ) (i j k : CutoffIndex d R)
    (hcount : ¬ ∀ a, (cutoffWord d R j).count a + (cutoffWord d R k).count a =
      (cutoffWord d R i).count a) :
    Tendsto (fun N => cartanCutoffFrameMatrixElement (mu N) (nu N) (hmu N) (hnu N) R i j k)
      atTop (𝓝 0) := by
  rw [← occupationSplitMatrixElement_eq_zero t _ _ _ hcount]
  exact cartanCutoffFrameMatrixElement_tendsto mu nu hmu hnu δmu δnu hδmu hδnu
    hmuGap hnuGap t ht R i j k

end Cloning.TensorLie
