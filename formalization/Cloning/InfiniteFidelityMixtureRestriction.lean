import Cloning.InfiniteFidelityMixtureNormalization

/-! Restricting a masked positive mixture to its actual retained component
type commutes exactly with normalization. -/
noncomputable section
open scoped BigOperators ComplexOrder Classical
namespace Cloning.Hybrid.PositiveTraceClass
open Cloning.InfiniteTraceClass
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 100000
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {I : Type*} [Fintype I]

def maskedWeight (q : I → ℝ) (P : I → Prop) (i : I) : ℝ := if P i then q i else 0

theorem maskedWeight_nonneg (q : I → ℝ) (hq : ∀ i, 0 ≤ q i) (P : I → Prop) :
    ∀ i, 0 ≤ maskedWeight q P i := by
  intro i
  unfold maskedWeight
  split_ifs
  · exact hq i
  · exact le_rfl

theorem maskedWeight_sum (q : I → ℝ) (P : I → Prop) :
    (∑ i, maskedWeight q P i) = ∑ i : {i // P i}, q i.val := by
  unfold maskedWeight
  rw [← Finset.sum_filter]
  exact Finset.sum_subtype _ (by simp) _

theorem finiteMixture_masked (q : I → ℝ) (hq : ∀ i, 0 ≤ q i) (P : I → Prop)
    (A : I → PositiveTraceClass H) :
    finiteMixture (maskedWeight q P) (maskedWeight_nonneg q hq P) A =
      finiteMixture (fun i : {i // P i} ↦ q i.val) (fun i ↦ hq i.val) (fun i ↦ A i.val) := by
  apply Subtype.ext
  simp only [finiteMixture_val, maskedWeight, apply_ite Complex.ofReal, Complex.ofReal_zero,
    ite_smul, zero_smul]
  rw [← Finset.sum_filter]
  exact Finset.sum_subtype _ (by simp) _

theorem normalized_masked_mixture_eq (q : I → ℝ) (hq : ∀ i, 0 ≤ q i) (P : I → Prop)
    (A : I → PositiveTraceClass H) (hA : ∀ i, ‖(A i).1‖ = 1)
    (fallback : PositiveTraceClass H) (hs : 0 < ∑ i : {i // P i}, q i.val) :
    normalized (finiteMixture (maskedWeight q P) (maskedWeight_nonneg q hq P) A) fallback =
      finiteMixture (fun i : {i // P i} ↦ q i.val / ∑ a : {i // P i}, q a.val)
        (fun i ↦ div_nonneg (hq i.val) hs.le) (fun i ↦ A i.val) := by
  calc
    _ = normalized (finiteMixture (fun i : {i // P i} ↦ q i.val)
        (fun i ↦ hq i.val) (fun i ↦ A i.val)) fallback :=
      congrArg (fun X : PositiveTraceClass H ↦ normalized X fallback) (finiteMixture_masked q hq P A)
    _ = _ := normalized_finiteMixture_of_pos (fun i : {i // P i} ↦ q i.val)
      (fun i ↦ hq i.val) (fun i ↦ A i.val) (fun i ↦ hA i.val) fallback hs

end Cloning.Hybrid.PositiveTraceClass
