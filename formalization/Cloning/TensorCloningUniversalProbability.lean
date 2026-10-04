import Cloning.TensorCloningUniversalMixture
import Cloning.TensorCloningAchievabilityProbability

/-! The actual universal transition table loses exactly the source Young tail
when retaining typical source copies and positive-probability transitions. -/
noncomputable section
open scoped BigOperators Classical Topology
namespace Cloning.TensorCloning
open Cloning.TensorLie Cloning.TensorLAN Cloning.YoungCompatibility Filter
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

def universalKeep (n m d : ℕ) (p : Fin (d+1) → ℝ)
    (i : SchurCopy n (d+1)) (j : SchurCopy m (d+1)) : Prop :=
  copyTypical n (d+1) p i ∧ 0 < probability (universalCopyPMF n m d i) j

theorem universal_discarded_mass (n m d : ℕ) (p : Fin (d+1) → ℝ) :
    (∑ ij : SchurCopy n (d+1) × SchurCopy m (d+1),
      if universalKeep n m d p ij.1 ij.2 then 0 else universalJointWeight n m d p ij.1 ij.2) =
      copyBadMass n (d+1) p := by
  rw [Fintype.sum_prod_type]
  unfold copyBadMass
  apply Finset.sum_congr rfl
  intro i hi
  by_cases ht : copyTypical n (d+1) p i
  · rw [if_pos ht]
    apply Finset.sum_eq_zero
    intro j hj
    by_cases hp : 0 < probability (universalCopyPMF n m d i) j
    · simp [universalKeep, ht, hp]
    · have hz : probability (universalCopyPMF n m d i) j = 0 :=
        le_antisymm (le_of_not_gt hp) ENNReal.toReal_nonneg
      simp [universalKeep, ht, hp, universalJointWeight, hz]
  · simp only [universalKeep, ht, false_and, if_false, universalJointWeight, ← Finset.mul_sum]
    have hs : (∑ j, probability (universalCopyPMF n m d i) j) = 1 := by
      simpa only [tsum_fintype] using tsum_probability (universalCopyPMF n m d i)
    rw [hs, mul_one]

theorem universalKeep_label_support (n m d : ℕ) (p : Fin (d+1) → ℝ)
    (i : SchurCopy n (d+1)) (j : SchurCopy m (d+1))
    (h : universalKeep n m d p i j) :
    fallbackKernel ((m : ℝ)/(n : ℝ)) n m (integerCopyLabel n d i) (integerCopyLabel m d j) ≠ 0 := by
  have hj : universalCopyPMF n m d i j ≠ 0 := by
    intro hz
    have hh := h.2
    simp [probability, hz] at hh
  have hm : (universalCopyPMF n m d i).map (integerCopyLabel m d) (integerCopyLabel m d j) ≠ 0 :=
    (PMF.mem_support_map_iff _ _ _).mpr ⟨j, hj, rfl⟩
  simpa only [universalCopyPMF_label] using hm

theorem universal_discarded_mass_tendsto_zero {d : ℕ}
    (p : ℕ → Fin (d+1) → ℝ) (hp : ∀ n a, 0 ≤ p n a)
    (hs : ∀ n, ∑ a, p n a = 1) (horder : ∀ n, Antitone (p n)) (m : ℕ → ℕ) :
    Tendsto (fun n ↦ ∑ ij : SchurCopy n (d+1) × SchurCopy (m n) (d+1),
      if universalKeep n (m n) d (p n) ij.1 ij.2 then 0 else
        universalJointWeight n (m n) d (p n) ij.1 ij.2) atTop (𝓝 0) := by
  simp_rw [universal_discarded_mass]
  exact copyBadMass_tendsto_zero p hp hs horder

end Cloning.TensorCloning
