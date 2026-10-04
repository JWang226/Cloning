import Cloning.MatrixDiscardLabel
import Cloning.MatrixChannelFidelity
import Cloning.MatrixFidelityScaling

/-!
# Joint concavity from a concrete label-discarding channel

Data processing and the proved direct-sum identity imply superadditivity on
pairs of positive matrices. Independently weighted mixtures give the usual
strong concavity bound; equal weights give joint concavity.
-/

noncomputable section
open scoped BigOperators Matrix MatrixOrder ComplexOrder
open Matrix
namespace Cloning.MatrixFidelity

set_option backward.isDefEq.respectTransparency false

variable {ι n : Type*} [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n]

/-- Summing matching positive blocks can only increase their total fidelity. -/
theorem fidelity_sum_le (A B : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).PosSemidef) (hB : ∀ i, (B i).PosSemidef) :
    ∑ i, fidelity (A i) (B i) ≤ fidelity (∑ i, A i) (∑ i, B i) := by
  have h := fidelity_data_processing Cloning.Channels.discardLabelChannel
    (blockDiagonal'_posSemidef A hA) (blockDiagonal'_posSemidef B hB)
  change fidelity (blockDiagonal' A) (blockDiagonal' B) ≤
    fidelity (Cloning.Channels.discardLabelMap (blockDiagonal' A))
      (Cloning.Channels.discardLabelMap (blockDiagonal' B)) at h
  simpa only [fidelity_blockDiagonal' A B hA hB,
    Cloning.Channels.discardLabelMap_blockDiagonal'] using h

/-- Strong concavity with two independent nonnegative families of weights;
normalization of the weights is not required. -/
theorem fidelity_strong_concavity (A B : ι → Matrix n n ℂ) (p q : ι → ℝ)
    (hA : ∀ i, (A i).PosSemidef) (hB : ∀ i, (B i).PosSemidef)
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i) :
    ∑ i, Real.sqrt (p i) * Real.sqrt (q i) * fidelity (A i) (B i) ≤
      fidelity (∑ i, p i • A i) (∑ i, q i • B i) := by
  have h := fidelity_sum_le (fun i => p i • A i) (fun i => q i • B i)
    (fun i => (hA i).smul (hp i)) (fun i => (hB i).smul (hq i))
  simpa only [fidelity_smul _ _ _ _ (hp _) (hq _) (hA _) (hB _)] using h

/-- Joint concavity for finite mixtures, including weights of arbitrary mass. -/
theorem fidelity_joint_concavity (A B : ι → Matrix n n ℂ) (w : ι → ℝ)
    (hA : ∀ i, (A i).PosSemidef) (hB : ∀ i, (B i).PosSemidef)
    (hw : ∀ i, 0 ≤ w i) :
    ∑ i, w i * fidelity (A i) (B i) ≤
      fidelity (∑ i, w i • A i) (∑ i, w i • B i) := by
  simpa only [Real.mul_self_sqrt (hw _)] using
    fidelity_strong_concavity A B w w hA hB hw hw

end Cloning.MatrixFidelity
