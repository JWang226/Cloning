import Cloning.YoungUniformLocalLabels

/-! Finite physical Young labels for the actual rescaled cell of a point.
The finite completion agrees with the full affine label eventually, as proved
from positivity and the strict limiting spectrum. -/

noncomputable section
open scoped BigOperators Topology Classical
open Filter
namespace Cloning.YoungHyperplane
open Cloning.YoungGeneral
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

def sampleShape (d N : ℕ) (p : Fin (d + 1) → ℝ) (x : rootSpace d) : Shape (d + 1) N :=
  fun i ↦ ⟨min ((sampleLabel d N p x).1 i).toNat N, Nat.lt_succ_of_le (min_le_right _ _)⟩

theorem sampleLabel_toNat_sum (d N : ℕ) (p : Fin (d + 1) → ℝ) (x : rootSpace d)
    (hpos : ∀ i, 0 ≤ (sampleLabel d N p x).1 i) :
    (∑ i, ((sampleLabel d N p x).1 i).toNat) = N := by
  have h : (∑ i, (((sampleLabel d N p x).1 i).toNat : ℤ)) = (N : ℤ) := by
    simp_rw [Int.toNat_of_nonneg (hpos _)]
    exact (sampleLabel d N p x).2
  exact_mod_cast h

theorem sampleShape_apply (d N : ℕ) (p : Fin (d + 1) → ℝ) (x : rootSpace d)
    (hpos : ∀ i, 0 ≤ (sampleLabel d N p x).1 i) (i : Fin (d + 1)) :
    (sampleShape d N p x i).val = ((sampleLabel d N p x).1 i).toNat := by
  have h := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) ↦
    Nat.zero_le (((sampleLabel d N p x).1 j).toNat)) (Finset.mem_univ i)
  rw [sampleLabel_toNat_sum d N p x hpos] at h
  exact min_eq_left h

theorem sampleShape_cast (d N : ℕ) (p : Fin (d + 1) → ℝ) (x : rootSpace d)
    (hpos : ∀ i, 0 ≤ (sampleLabel d N p x).1 i) (i : Fin (d + 1)) :
    ((sampleShape d N p x i).val : ℤ) = (sampleLabel d N p x).1 i := by
  rw [sampleShape_apply d N p x hpos i, Int.toNat_of_nonneg (hpos i)]

theorem sampleShape_sum (d N : ℕ) (p : Fin (d + 1) → ℝ) (x : rootSpace d)
    (hpos : ∀ i, 0 ≤ (sampleLabel d N p x).1 i) :
    (∑ i, (sampleShape d N p x i).val) = N := by
  simp_rw [sampleShape_apply d N p x hpos]
  exact sampleLabel_toNat_sum d N p x hpos

theorem shapeLattice_sampleShape (d N : ℕ) (p : Fin (d + 1) → ℝ) (x : rootSpace d)
    (hpos : ∀ i, 0 ≤ (sampleLabel d N p x).1 i) :
    shapeLattice d N (sampleShape d N p x) = sampleLabel d N p x := by
  apply Subtype.ext
  funext i
  rw [shapeLattice_apply d N _ (sampleShape_sum d N p x hpos), sampleShape_cast d N p x hpos]

theorem sampleShape_antitone (d N : ℕ) (p : Fin (d + 1) → ℝ) (x : rootSpace d)
    (hpos : ∀ i, 0 ≤ (sampleLabel d N p x).1 i)
    (hanti : Antitone (sampleLabel d N p x).1) :
    Antitone (fun i ↦ (sampleShape d N p x i).val) := by
  intro i j hij
  have h := hanti hij
  rw [← sampleShape_cast d N p x hpos j, ← sampleShape_cast d N p x hpos i] at h
  exact_mod_cast h

/-- The finite physical shape eventually is exactly the full cell label and
satisfies every physical partition constraint. -/
theorem eventually_sampleShape_valid (d : ℕ) (n : ℕ → ℕ) (hn : Tendsto n atTop atTop)
    (p : ℕ → Fin (d + 1) → ℝ) (hp : ∀ k, ∑ i, p k i = 1)
    (p₀ : Fin (d + 1) → ℝ) (hp₀ : ∀ i, 0 < p₀ i) (hord : StrictAnti p₀)
    (hlim : ∀ i, Tendsto (fun k ↦ p k i) atTop (𝓝 (p₀ i))) (x : rootSpace d) :
    ∀ᶠ k in atTop,
      Antitone (fun i ↦ (sampleShape d (n k) (p k) x i).val) ∧
      (∑ i, (sampleShape d (n k) (p k) x i).val) = n k ∧
      shapeLattice d (n k) (sampleShape d (n k) (p k) x) = sampleLabel d (n k) (p k) x := by
  filter_upwards [eventually_sampleLabel_partition d n hn p hp p₀ hp₀ hord hlim x] with k hk
  exact ⟨sampleShape_antitone d (n k) (p k) x hk.1 hk.2,
    sampleShape_sum d (n k) (p k) x hk.1, shapeLattice_sampleShape d (n k) (p k) x hk.1⟩

theorem sampleShape_ratio_tendsto (d : ℕ) (n : ℕ → ℕ) (hn : Tendsto n atTop atTop)
    (p : ℕ → Fin (d + 1) → ℝ) (hp : ∀ k, ∑ i, p k i = 1)
    (p₀ : Fin (d + 1) → ℝ) (hp₀ : ∀ i, 0 < p₀ i) (hord : StrictAnti p₀)
    (hlim : ∀ i, Tendsto (fun k ↦ p k i) atTop (𝓝 (p₀ i))) (x : rootSpace d)
    (i : Fin (d + 1)) :
    Tendsto (fun k ↦ ((sampleShape d (n k) (p k) x i).val : ℝ) / (n k : ℝ))
      atTop (𝓝 (p₀ i)) := by
  apply (sampleLabel_ratio_tendsto d n hn p hp p₀ hlim x i).congr'
  filter_upwards [eventually_sampleLabel_partition d n hn p hp p₀ hp₀ hord hlim x] with k hk
  congr 1
  exact_mod_cast (sampleShape_cast d (n k) (p k) x hk.1 i).symm

end Cloning.YoungHyperplane
