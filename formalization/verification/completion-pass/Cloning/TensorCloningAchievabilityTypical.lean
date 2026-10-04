import Cloning.TensorCloningAchievabilityMixture
import Cloning.TensorCloningAchievabilityProbability

/-! Finite probability losses for retaining typical pairs in the actual
known-spectrum protocol. -/
noncomputable section
open scoped BigOperators Classical Topology
open Filter
namespace Cloning.TensorCloning
open Cloning.TensorLie Cloning.TensorLAN Cloning.YoungGeneral
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

def jointTypical (n m d : ℕ) (p : Fin d → ℝ) (ij : SchurCopy n d × SchurCopy m d) : Prop :=
  copyTypical n d p ij.1 ∧ copyTypical m d p ij.2

def jointBadMass (n m d : ℕ) (p : Fin d → ℝ) : ℝ :=
  ∑ ij : SchurCopy n d × SchurCopy m d,
    if jointTypical n m d p ij then 0 else jointCopyWeight n m d p ij

theorem jointBadMass_nonneg (n m d : ℕ) (p : Fin d → ℝ) : 0 ≤ jointBadMass n m d p := by
  apply Finset.sum_nonneg
  intro ij _
  split_ifs
  · exact le_rfl
  · exact jointCopyWeight_nonneg n m d p ij

/-- The product-copy law loses at most the sum of its two actual atypical
marginal masses. -/
theorem jointBadMass_le (n m d : ℕ) (p : Fin d → ℝ)
    (hp : ∀ a, 0 ≤ p a) (hs : ∑ a, p a = 1) :
    jointBadMass n m d p ≤ copyBadMass n d p + copyBadMass m d p := by
  calc
    _ ≤ ∑ ij : SchurCopy n d × SchurCopy m d,
        ((if copyTypical n d p ij.1 then 0 else knownCopyWeight n d p ij.1) * knownCopyWeight m d p ij.2 +
        knownCopyWeight n d p ij.1 * (if copyTypical m d p ij.2 then 0 else knownCopyWeight m d p ij.2)) := by
      apply Finset.sum_le_sum
      intro ij _
      dsimp only [jointTypical, jointCopyWeight]
      by_cases hi : copyTypical n d p ij.1 <;> by_cases hj : copyTypical m d p ij.2 <;>
        simp [hi, hj] <;>
        nlinarith [mul_nonneg (knownCopyWeight_nonneg n d p ij.1) (knownCopyWeight_nonneg m d p ij.2)]
    _ = copyBadMass n d p + copyBadMass m d p := by
      rw [Fintype.sum_prod_type]
      simp_rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      rw [knownCopyWeight_sum m d p hp hs]
      simp only [mul_one]
      rw [← Finset.sum_mul, knownCopyWeight_sum n d p hp hs, one_mul]
      rfl

theorem jointBadMass_tendsto_zero {d : ℕ} (p : Fin d → ℝ)
    (hp : ∀ a, 0 ≤ p a) (hs : ∑ a, p a = 1) (horder : Antitone p)
    (n m : ℕ → ℕ) (hn : Tendsto n atTop atTop) (hm : Tendsto m atTop atTop) :
    Tendsto (fun k => jointBadMass (n k) (m k) d p) atTop (𝓝 0) := by
  have hh := (copyBadMass_fixed_tendsto_zero p hp hs horder n hn).add
    (copyBadMass_fixed_tendsto_zero p hp hs horder m hm)
  simp only [zero_add] at hh
  exact squeeze_zero (fun k => jointBadMass_nonneg _ _ _ _) (fun k => jointBadMass_le _ _ _ p hp hs) hh

private theorem weighted_lower_of_good {ι : Type*} [Fintype ι]
    (q f : ι → ℝ) (hq : ∀ i, 0 ≤ q i) (hs : ∑ i, q i = 1)
    (hf : ∀ i, 0 ≤ f i) (good : ι → Prop) (c η : ℝ) (hc : c ≤ 1) (hη : 0 ≤ η)
    (hgood : ∀ i, good i → c-η ≤ f i) :
    c-η-(∑ i, if good i then 0 else q i) ≤ ∑ i, q i*f i := by
  have hpoint (i : ι) : (c-η)*q i - (if good i then 0 else q i) ≤ q i*f i := by
    by_cases hi : good i
    · rw [if_pos hi, sub_zero]
      nlinarith [hgood i hi, hq i]
    · rw [if_neg hi]
      nlinarith [hq i, hf i]
  have hh := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hpoint i)
  simpa only [Finset.sum_sub_distrib, ← Finset.mul_sum, hs, mul_one] using hh

/-- Finite global lower bound after retaining typical source/target copies.
All probability terms are actual physical Schur probabilities. -/
theorem knownSpectrumChannel_payoff_lower_typical {d : ℕ} (n m : ℕ)
    (p : SimpleSpectrum (d+1)) (U : unitary (Matrix (Fin (d+1)) (Fin (d+1)) ℂ))
    (c η : ℝ) (hc : c ≤ 1) (hη : 0 ≤ η)
    (hgood : ∀ ij : SchurCopy n (d+1) × SchurCopy m (d+1), jointTypical n m (d+1) p.eigenvalue ij →
      c-η ≤ transitionFidelity n m (d+1) p.eigenvalue p.positive U ij.1 ij.2) :
    c-η-copyBadMass n (d+1) p.eigenvalue-copyBadMass m (d+1) p.eigenvalue ≤
      spectrumPayoff n m (knownSpectrumChannel n m (d+1) p.eigenvalue
        (fun a => (p.positive a).le) p.normalized) p U := by
  have hh := weighted_lower_of_good (jointCopyWeight n m (d+1) p.eigenvalue)
    (fun ij => transitionFidelity n m (d+1) p.eigenvalue p.positive U ij.1 ij.2)
    (jointCopyWeight_nonneg n m (d+1) p.eigenvalue)
    (jointCopyWeight_sum n m (d+1) p.eigenvalue (fun a => (p.positive a).le) p.normalized)
    (fun ij => transitionFidelity_nonneg n m (d+1) p.eigenvalue p.positive U ij.1 ij.2)
    (jointTypical n m (d+1) p.eigenvalue) c η hc hη hgood
  have ht := knownSpectrumChannel_payoff_lower n m p U
  have hm := jointBadMass_le n m (d+1) p.eigenvalue (fun a => (p.positive a).le) p.normalized
  change c-η-jointBadMass n m (d+1) p.eigenvalue ≤ _ at hh
  linarith

end Cloning.TensorCloning
