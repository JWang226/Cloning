import Cloning.TensorCloningChannel
import Cloning.TensorLANEmbeddingSchurWeights
import Cloning.TensorLANEmbeddingTypical

/-! The exact actual-copy law inherits the proved physical Young concentration.
These are genuine Schur-copy probabilities, without a character-law premise. -/
noncomputable section
open scoped BigOperators Classical Topology ENNReal
open Filter
namespace Cloning.TensorCloning
open Cloning.TensorLie Cloning.TensorLAN Cloning.YoungGeneral
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

theorem tensorYoungPMF_sum_eq_copies (n d : ℕ) (p : Fin d → ℝ)
    (hp : ∀ a, 0 ≤ p a) (hs : ∑ a, p a = 1) (f : Shape d n → ℝ) :
    (∑ μ : Shape d n, (tensorYoungPMF n d p hp hs μ).toReal * f μ) =
      ∑ i : SchurCopy n d, knownCopyWeight n d p i * f ((recursivePhysicalDecomposition n d).get i).shape := by
  have he (μ : Shape d n) : (tensorYoungPMF n d p hp hs μ).toReal =
      ∑ i : SchurCopy n d, if ((recursivePhysicalDecomposition n d).get i).shape = μ then
        knownCopyWeight n d p i else 0 := by
    rw [tensorYoungPMF_eq_map_copies, PMF.map_apply, tsum_fintype,
      ENNReal.toReal_sum (by
        intro i _
        split_ifs
        · exact (physicalCopyPMF n d p hp hs).apply_ne_top i
        · exact ENNReal.zero_ne_top)]
    apply Finset.sum_congr rfl
    intro i _
    simp only [eq_comm (a := μ)]
    split_ifs <;> simp [knownCopyWeight]
  simp_rw [he, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp only [ite_mul, zero_mul]
  simp

def copyTypical (n d : ℕ) (p : Fin d → ℝ) (i : SchurCopy n d) : Prop :=
  TypicalLabel n p ((recursivePhysicalDecomposition n d).get i).weight

def copyBadMass (n d : ℕ) (p : Fin d → ℝ) : ℝ :=
  ∑ i : SchurCopy n d, if copyTypical n d p i then 0 else knownCopyWeight n d p i

theorem copyBadMass_nonneg (n d : ℕ) (p : Fin d → ℝ) : 0 ≤ copyBadMass n d p := by
  apply Finset.sum_nonneg
  intro i _
  split_ifs
  · exact le_rfl
  · exact knownCopyWeight_nonneg n d p i

theorem copyBadMass_eq_tail (n d : ℕ) (p : Fin d → ℝ)
    (hp : ∀ a, 0 ≤ p a) (hs : ∑ a, p a = 1) :
    copyBadMass n d p = tailProbability (tensorYoungPMF n d p hp hs) p (shrinkingRadius n) := by
  have he := tensorYoungPMF_sum_eq_copies n d p hp hs (fun μ =>
    if ∃ a, (n : ℝ)*shrinkingRadius n ≤ |((μ a).val : ℝ)-n*p a| then 1 else 0)
  simp only [mul_ite, mul_one, mul_zero] at he
  rw [tailProbability, he]
  apply Finset.sum_congr rfl
  intro i _
  have hh : copyTypical n d p i ↔
      ¬ ∃ a, (n : ℝ)*shrinkingRadius n ≤
        |((((recursivePhysicalDecomposition n d).get i).shape a).val : ℝ)-n*p a| := by
    simp only [copyTypical, TypicalLabel, not_exists, not_le, PhysicalHighestTensor.shape]
  rw [hh]
  split_ifs <;> simp_all

/-- Copy probabilities concentrate for every moving ordered spectrum. -/
theorem copyBadMass_tendsto_zero {d : ℕ} (p : ℕ → Fin d → ℝ)
    (hp : ∀ n a, 0 ≤ p n a) (hs : ∀ n, ∑ a, p n a = 1)
    (horder : ∀ n, Antitone (p n)) :
    Tendsto (fun n => copyBadMass n d (p n)) atTop (𝓝 0) := by
  simp_rw [copyBadMass_eq_tail _ _ _ (hp _) (hs _)]
  exact tensorYoungPMF_tail_tendsto_zero p hp hs horder

/-- Arbitrary divergent sample subsequences retain the actual physical tail
estimate, with no restriction on the growth rate. -/
theorem copyBadMass_fixed_tendsto_zero {d : ℕ} (p : Fin d → ℝ)
    (hp : ∀ a, 0 ≤ p a) (hs : ∑ a, p a = 1) (horder : Antitone p)
    (n : ℕ → ℕ) (hn : Tendsto n atTop atTop) :
    Tendsto (fun k => copyBadMass (n k) d p) atTop (𝓝 0) :=
  (copyBadMass_tendsto_zero (fun _ => p) (fun _ => hp) (fun _ => hs) (fun _ => horder)).comp hn

end Cloning.TensorCloning
