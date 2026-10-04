import Cloning.InfiniteFidelityConcavity
import Cloning.HybridGaussianAttainmentFidelity

/-! Finite joint-mixture lower bounds for genuine trace-class root fidelity. -/
noncomputable section
open scoped BigOperators Classical ComplexOrder
namespace Cloning.Hybrid.PositiveTraceClass
open Cloning.InfiniteTraceClass Cloning.InfiniteFidelity
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
variable {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def finsetSum (s : Finset ι) (A : ι → PositiveTraceClass H) : PositiveTraceClass H :=
  ⟨∑ i ∈ s, (A i).1, by
    change 0 ≤ inclusionCLM (∑ i ∈ s, (A i).1)
    rw [map_sum]
    exact Finset.sum_nonneg (fun i hi ↦ (A i).2)⟩

@[simp] theorem finsetSum_val (s : Finset ι) (A : ι → PositiveTraceClass H) :
    (finsetSum s A).1 = ∑ i ∈ s, (A i).1 := rfl

/-- Finite superadditivity, with no orthogonality or support separation. -/
theorem sum_rootFidelity_le (s : Finset ι) (A B : ι → PositiveTraceClass H) :
    (∑ i ∈ s, (A i).rootFidelity (B i)) ≤ (finsetSum s A).rootFidelity (finsetSum s B) := by
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using rootFidelity_nonneg (finsetSum ∅ A) (finsetSum ∅ B)
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    apply (add_le_add (le_refl ((A i).rootFidelity (B i))) ih).trans
    have h := fidelity_weighted_joint_concavity (A i).1 (B i).1
      (finsetSum s A).1 (finsetSum s B).1 (A i).2 (B i).2 (finsetSum s A).2 (finsetSum s B).2
      1 1 (by norm_num) (by norm_num)
    simpa only [Complex.ofReal_one, one_smul, one_mul, rootFidelity, finsetSum,
      Finset.sum_insert hi] using h

variable [Fintype ι]

def finiteMixture (q : ι → ℝ) (hq : ∀ i, 0 ≤ q i) (A : ι → PositiveTraceClass H) :
    PositiveTraceClass H := finsetSum Finset.univ (fun i ↦ scale ⟨q i, hq i⟩ (A i))

@[simp] theorem finiteMixture_val (q : ι → ℝ) (hq : ∀ i, 0 ≤ q i) (A : ι → PositiveTraceClass H) :
    (finiteMixture q hq A).1 = ∑ i, (q i : ℂ) • (A i).1 := rfl

/-- Independent nonnegative weights on the two finite mixtures produce the
classical square-root affinity factors and the actual conditional fidelities. -/
theorem finiteMixture_rootFidelity_lower (q r : ι → ℝ)
    (hq : ∀ i, 0 ≤ q i) (hr : ∀ i, 0 ≤ r i) (A B : ι → PositiveTraceClass H) :
    (∑ i, (Real.sqrt (q i) * Real.sqrt (r i)) * (A i).rootFidelity (B i)) ≤
      (finiteMixture q hq A).rootFidelity (finiteMixture r hr B) := by
  simpa only [rootFidelity_scale] using sum_rootFidelity_le Finset.univ
    (fun i ↦ scale ⟨q i, hq i⟩ (A i)) (fun i ↦ scale ⟨r i, hr i⟩ (B i))

/-- Ordinary finite joint concavity on any collection of physical states. -/
theorem finiteMixture_rootFidelity_lower_same (q : ι → ℝ) (hq : ∀ i, 0 ≤ q i)
    (A B : ι → PositiveTraceClass H) :
    (∑ i, q i * (A i).rootFidelity (B i)) ≤
      (finiteMixture q hq A).rootFidelity (finiteMixture q hq B) := by
  simpa only [Real.mul_self_sqrt (hq _)] using finiteMixture_rootFidelity_lower q q hq hq A B

end Cloning.Hybrid.PositiveTraceClass
