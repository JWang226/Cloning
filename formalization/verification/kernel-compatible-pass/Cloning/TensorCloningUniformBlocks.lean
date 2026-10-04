import Cloning.TensorCloningBlockTrimming
import Cloning.TensorCloningRetainedUniversal

/-! The normalized actual physical output blocks are exactly the retained
conditional mixtures used in the proved compact-uniform limit. -/
noncomputable section
open scoped BigOperators InnerProductSpace ComplexOrder Classical Matrix
namespace Cloning.TensorCloning
open Cloning.PCT Cloning.TensorLie Cloning.TensorLAN Cloning.InfiniteTraceClass Cloning.Hybrid
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
local instance (n d : ℕ) : FiniteDimensional ℂ (TensorRegister n (Fin d)) :=
  (registerBasis (Fin n → Fin d)).toOrthonormalBasis.toBasis.finiteDimensional_of_finite

theorem retainedCopyWeight_sum (n m d : ℕ) (w : SchurCopy n d → SchurCopy m d → ℝ)
    (keep : SchurCopy n d → SchurCopy m d → Prop) (j : SchurCopy m d) :
    (∑ i,retainedCopyWeight n m d w keep i j) = ∑ i : {i // keep i j},w i.val j :=
  PositiveTraceClass.maskedWeight_sum (fun i => w i j) (fun i => keep i j)

theorem retainedCopyProbability_sum (n m d : ℕ) (w : SchurCopy n d → SchurCopy m d → ℝ)
    (keep : SchurCopy n d → SchurCopy m d → Prop) (j : SchurCopy m d)
    (hr : 0 < ∑ i : {i // keep i j},w i.val j) :
    (∑ i : {i // keep i j},w i.val j / ∑ a : {i // keep i j},w a.val j)=1 := by
  rw [← Finset.sum_div, div_self hr.ne']

theorem normalizedCopyBlock_rootFidelity_one (n m d : ℕ) (p : Fin d → ℝ) (hp : ∀ a, 0 < p a)
    (w : SchurCopy n d → SchurCopy m d → ℝ) (hw : ∀ i j, 0 ≤ w i j)
    (keep : SchurCopy n d → SchurCopy m d → Prop) (j : SchurCopy m d)
    (hr : 0 < ∑ i : {i // keep i j},w i.val j) :
    (normalizedCopyBlock n m d p hp 1 w hw keep j).rootFidelity
      (copySectorState ((recursivePhysicalDecomposition m d).get j) 1 p hp) =
    retainedCopyFidelity n m d p hp j (fun i => keep i j)
      (fun i : {i // keep i j} => w i.val j / ∑ a : {i // keep i j},w a.val j)
      (fun i => div_nonneg (hw i.val j) hr.le) := by
  rw [normalizedCopyBlock_eq_mixture n m d p hp 1 (by simp) w hw keep j hr, copySectorState_one_eq]
  simp only [copyTransitionState, copySectorState_one_eq]
  rfl

end Cloning.TensorCloning
