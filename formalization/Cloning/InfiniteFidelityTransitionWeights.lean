import Cloning.InfiniteFidelityTransition

/-! Conditional reweighting of a finite transition table. It gives the exact
output-label affinity while preserving the target state up to positive mass. -/
noncomputable section
open scoped BigOperators Classical ComplexOrder
namespace Cloning.Hybrid.PositiveTraceClass
open Cloning.InfiniteTraceClass Cloning.InfiniteFidelity
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
variable {H ι κ : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [Fintype ι] [Fintype κ]

def transitionTargetWeight (q : ι → κ → ℝ) (t : κ → ℝ) (i : ι) (j : κ) : ℝ :=
  q i j * (t j / ∑ k, q k j)

theorem transitionTargetWeight_nonneg (q : ι → κ → ℝ) (t : κ → ℝ)
    (hq : ∀ i j, 0 ≤ q i j) (ht : ∀ j, 0 ≤ t j) (i : ι) (j : κ) :
    0 ≤ transitionTargetWeight q t i j :=
  mul_nonneg (hq i j) (div_nonneg (ht j) (Finset.sum_nonneg (fun k _ ↦ hq k j)))

theorem transitionTargetWeight_sum (q : ι → κ → ℝ) (t : κ → ℝ) (j : κ) :
    ∑ i, transitionTargetWeight q t i j = if (∑ i, q i j) = 0 then 0 else t j := by
  simp only [transitionTargetWeight, ← Finset.sum_mul]
  split_ifs with h
  · simp [h]
  · field_simp

theorem transitionTargetWeight_sum_le (q : ι → κ → ℝ) (t : κ → ℝ)
    (ht : ∀ j, 0 ≤ t j) (j : κ) : ∑ i, transitionTargetWeight q t i j ≤ t j := by
  rw [transitionTargetWeight_sum]
  split_ifs
  · exact ht j
  · exact le_rfl

theorem transitionTargetWeight_total_le (q : ι → κ → ℝ) (t : κ → ℝ)
    (ht : ∀ j, 0 ≤ t j) :
    (∑ z : ι × κ, transitionTargetWeight q t z.1 z.2) ≤ ∑ j, t j := by
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  exact Finset.sum_le_sum (fun j _ ↦ transitionTargetWeight_sum_le q t ht j)

theorem transitionTargetWeight_affinity (q : ι → κ → ℝ) (t : κ → ℝ)
    (hq : ∀ i j, 0 ≤ q i j) (ht : ∀ j, 0 ≤ t j) :
    (∑ z : ι × κ, Real.sqrt (q z.1 z.2) * Real.sqrt (transitionTargetWeight q t z.1 z.2)) =
      ∑ j, Real.sqrt (∑ i, q i j) * Real.sqrt (t j) := by
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  have he (i : ι) : Real.sqrt (q i j) * Real.sqrt (transitionTargetWeight q t i j) =
      q i j * Real.sqrt (t j / ∑ k, q k j) := by
    rw [transitionTargetWeight, Real.sqrt_mul (hq i j), ← mul_assoc, Real.mul_self_sqrt (hq i j)]
  simp_rw [he]
  rw [← Finset.sum_mul, Real.sqrt_div (ht j)]
  have hs : 0 ≤ ∑ i, q i j := Finset.sum_nonneg (fun i _ ↦ hq i j)
  by_cases hz : (∑ i, q i j) = 0
  · simp [hz]
  · have hr : Real.sqrt (∑ i, q i j) ≠ 0 := Real.sqrt_ne_zero'.mpr (lt_of_le_of_ne hs (Ne.symm hz))
    field_simp
    rw [Real.sq_sqrt hs]
    ring

theorem finiteMixture_mono_weights (q r : κ → ℝ) (hq : ∀ j, 0 ≤ q j)
    (hr : ∀ j, 0 ≤ r j) (hqr : ∀ j, q j ≤ r j) (B : κ → PositiveTraceClass H) :
    inclusionCLM (finiteMixture q hq B).1 ≤ inclusionCLM (finiteMixture r hr B).1 := by
  simp only [finiteMixture_val, map_sum, map_smul, Complex.coe_smul]
  exact Finset.sum_le_sum (fun j _ ↦ smul_le_smul_of_nonneg_right (hqr j) (B j).2)

theorem finiteMixture_product_right (r : ι → κ → ℝ) (hr : ∀ i j, 0 ≤ r i j)
    (B : κ → PositiveTraceClass H) :
    finiteMixture (fun z : ι × κ ↦ r z.1 z.2) (fun z ↦ hr z.1 z.2) (fun z ↦ B z.2) =
      finiteMixture (fun j ↦ ∑ i, r i j) (fun j ↦ Finset.sum_nonneg (fun i _ ↦ hr i j)) B := by
  apply Subtype.ext
  simp only [finiteMixture_val, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Complex.ofReal_sum, Finset.sum_smul]

/-- A global finite transition lower bound for arbitrary actual positive
trace-class states. The retained conditional fidelities need no orthogonal
support hypothesis; all normalization losses are explicit. -/
theorem transition_rootFidelity_lower (q : ι → κ → ℝ) (t : κ → ℝ)
    (hq : ∀ i j, 0 ≤ q i j) (ht : ∀ j, 0 ≤ t j) (htsum : ∑ j, t j ≤ 1)
    (A : ι → κ → PositiveTraceClass H) (B : κ → PositiveTraceClass H)
    (keep : ι → κ → Prop) (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hgood : ∀ i j, keep i j → c ≤ (A i j).rootFidelity (B j)) :
    c * (∑ j, Real.sqrt (∑ i, q i j) * Real.sqrt (t j)) -
      Real.sqrt (∑ z : ι × κ, if keep z.1 z.2 then 0 else q z.1 z.2) ≤
    (finiteMixture (fun z : ι × κ ↦ q z.1 z.2) (fun z ↦ hq z.1 z.2)
      (fun z ↦ A z.1 z.2)).rootFidelity (finiteMixture t ht B) := by
  have hr := transitionTargetWeight_nonneg q t hq ht
  have hl := finiteMixture_rootFidelity_lower_trimmed
    (fun z : ι × κ ↦ q z.1 z.2) (fun z : ι × κ ↦ transitionTargetWeight q t z.1 z.2)
    (fun z ↦ hq z.1 z.2) (fun z ↦ hr z.1 z.2)
    ((transitionTargetWeight_total_le q t ht).trans htsum)
    (fun z ↦ A z.1 z.2) (fun z ↦ B z.2) (fun z ↦ keep z.1 z.2) c hc0 hc1
    (fun z hz ↦ hgood z.1 z.2 hz)
  rw [transitionTargetWeight_affinity q t hq ht, finiteMixture_product_right] at hl
  exact hl.trans (rootFidelity_mono_right _ _ _ (finiteMixture_mono_weights _ _ _ ht
    (transitionTargetWeight_sum_le q t ht) B))

end Cloning.Hybrid.PositiveTraceClass
