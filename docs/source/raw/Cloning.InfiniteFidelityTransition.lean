import Cloning.InfiniteFidelityFiniteMixture

/-! Finite transition bounds for actual trace-class root fidelity, including
an explicit square-root cost for discarding exceptional transitions. -/
noncomputable section
open scoped BigOperators Classical ComplexOrder
namespace Cloning.Hybrid.PositiveTraceClass
open Cloning.InfiniteTraceClass Cloning.InfiniteFidelity
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
variable {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [Fintype ι]

theorem finiteMixture_rootFidelity_lower_trimmed (q r : ι → ℝ)
    (hq : ∀ i, 0 ≤ q i) (hr : ∀ i, 0 ≤ r i) (hrsum : ∑ i, r i ≤ 1)
    (A B : ι → PositiveTraceClass H) (keep : ι → Prop) (c : ℝ)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hgood : ∀ i, keep i → c ≤ (A i).rootFidelity (B i)) :
    c * (∑ i, Real.sqrt (q i) * Real.sqrt (r i)) -
        Real.sqrt (∑ i, if keep i then 0 else q i) ≤
      (finiteMixture q hq A).rootFidelity (finiteMixture r hr B) := by
  let w : ι → ℝ := fun i ↦ Real.sqrt (q i) * Real.sqrt (r i)
  have hw (i : ι) : 0 ≤ w i := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hpoint (i : ι) : c * w i ≤ w i * (A i).rootFidelity (B i) +
      (if keep i then 0 else w i) := by
    by_cases hi : keep i
    · simp only [if_pos hi, add_zero]
      simpa only [mul_comm c] using mul_le_mul_of_nonneg_left (hgood i hi) (hw i)
    · simp only [if_neg hi]
      have hnon := mul_nonneg (hw i) (rootFidelity_nonneg (A i) (B i))
      have hle := mul_le_mul_of_nonneg_right hc1 (hw i)
      nlinarith
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) ↦ hpoint i)
  rw [← Finset.mul_sum, Finset.sum_add_distrib] at hsum
  have hbad : (∑ i, if keep i then 0 else w i) ≤
      Real.sqrt (∑ i, if keep i then 0 else q i) := by
    calc
      _ = ∑ i, Real.sqrt (if keep i then 0 else q i) * Real.sqrt (r i) := by
        apply Finset.sum_congr rfl
        intro i hi
        by_cases hk : keep i <;> simp [hk, w]
      _ ≤ Real.sqrt (∑ i, if keep i then 0 else q i) * Real.sqrt (∑ i, r i) :=
        Real.sum_sqrt_mul_sqrt_le Finset.univ (fun i ↦ by split_ifs; exact le_rfl; exact hq i) hr
      _ ≤ Real.sqrt (∑ i, if keep i then 0 else q i) * 1 :=
        mul_le_mul_of_nonneg_left (by simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hrsum)
          (Real.sqrt_nonneg _)
      _ = _ := mul_one _
  have hconc := finiteMixture_rootFidelity_lower q r hq hr A B
  change (∑ i, w i * (A i).rootFidelity (B i)) ≤ _ at hconc
  change c * (∑ i, w i) - _ ≤ _
  linarith

/-- Adding positive mass to either argument can only increase root fidelity. -/
theorem rootFidelity_mono_left (A C B : PositiveTraceClass H)
    (hAC : inclusionCLM A.1 ≤ inclusionCLM C.1) : A.rootFidelity B ≤ C.rootFidelity B :=
  fidelity_mono_left A.2 C.2 B.2 A.1.2 C.1.2 B.1.2 hAC

theorem rootFidelity_mono_right (A B D : PositiveTraceClass H)
    (hBD : inclusionCLM B.1 ≤ inclusionCLM D.1) : A.rootFidelity B ≤ A.rootFidelity D := by
  rw [rootFidelity_comm A B, rootFidelity_comm A D]
  exact rootFidelity_mono_left B D A hBD

end Cloning.Hybrid.PositiveTraceClass
