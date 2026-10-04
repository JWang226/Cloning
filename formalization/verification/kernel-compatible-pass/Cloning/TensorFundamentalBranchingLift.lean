import Cloning.TensorFundamentalBranchingSlices
import Cloning.TensorHighestGramIntertwiner
import Cloning.TensorCyclicSectorIrreducible

/-! Literal extension of a first-factor linear map by the final physical slot. -/
noncomputable section
open scoped BigOperators InnerProductSpace
namespace Cloning.TensorLie
open Cloning.PCT
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
variable {n m d : ℕ}
local instance (n d : ℕ) : FiniteDimensional ℂ (TensorRegister n (Fin d)) :=
  (registerBasis (Fin n → Fin d)).toOrthonormalBasis.toBasis.finiteDimensional_of_finite

/-- Apply an actual linear map on the first tensor factor and preserve the last slot. -/
def lastFactorLift (T : TensorRegister n (Fin d) →L[ℂ] TensorRegister m (Fin d)) :
    TensorRegister (n + 1) (Fin d) →L[ℂ] TensorRegister (m + 1) (Fin d) :=
  LinearMap.toContinuousLinearMap {
    toFun x := ⟨fun w => T (lastSlice (w (Fin.last m)) x) (Fin.init w), memℓp_gen (by
      simp only [ENNReal.toReal_ofNat]; exact (hasSum_fintype _).summable)⟩
    map_add' _ _ := by ext; simp
    map_smul' _ _ := by ext; simp }

@[simp] theorem lastSlice_lastFactorLift
    (T : TensorRegister n (Fin d) →L[ℂ] TensorRegister m (Fin d))
    (r : Fin d) (x : TensorRegister (n + 1) (Fin d)) :
    lastSlice r (lastFactorLift T x) = T (lastSlice r x) := by
  ext w
  change T (lastSlice ((Fin.snoc w r : Fin (m + 1) → Fin d) (Fin.last m)) x)
    (Fin.init (Fin.snoc w r : Fin (m + 1) → Fin d)) = _
  simp only [Fin.snoc_last, Fin.init_snoc]

/-- Expanding the final register shows that membership is exactly slice membership. -/
theorem mem_tensorProductSector_top_iff (P : Submodule ℂ (TensorRegister n (Fin d)))
    (x : TensorRegister (n + 1) (Fin d)) :
    x ∈ tensorProductSector P (⊤ : Submodule ℂ (TensorRegister 1 (Fin d))) ↔
      ∀ r, lastSlice r x ∈ P := by
  classical
  constructor
  · intro hx r; exact lastSlice_mem_tensorProductSector _ _ hx r
  · intro hx
    have he : x = ∑ r : Fin d, tensorJoin (lastSlice r x)
        (registerBasis (Fin 1 → Fin d) (fun _ => r)) := by
      apply lastSlice_ext
      intro r
      simp only [map_sum, lastSlice_tensorJoin, registerBasis_apply, lp.single_apply,
        Pi.single_apply]
      rw [Finset.sum_eq_single r]
      · simp
      · intro s _ hsr
        have hne : (fun _ : Fin 1 => r) ≠ (fun _ => s) := by
          intro he
          exact hsr (congrFun he 0).symm
        simp [hne]
      · simp
    rw [he]
    exact Submodule.sum_mem _ (fun r _ => Submodule.subset_span ⟨_, hx r, _, Submodule.mem_top, rfl⟩)

theorem lastFactorLift_mem (T : TensorRegister n (Fin d) →L[ℂ] TensorRegister m (Fin d))
    (Q : Submodule ℂ (TensorRegister m (Fin d))) (hT : ∀ x, T x ∈ Q)
    (x : TensorRegister (n + 1) (Fin d)) :
    lastFactorLift T x ∈ tensorProductSector Q (⊤ : Submodule ℂ (TensorRegister 1 (Fin d))) := by
  rw [mem_tensorProductSector_top_iff]
  intro r
  rw [lastSlice_lastFactorLift]
  exact hT _

/-- First-factor intertwining gives intertwining on the complete physical tensor product. -/
theorem lastFactorLift_intertwines
    (T : TensorRegister n (Fin d) →L[ℂ] TensorRegister m (Fin d))
    (hT : ∀ a b x, T (collectiveGenerator n a b x) = collectiveGenerator m a b (T x))
    (a b : Fin d) (x : TensorRegister (n + 1) (Fin d)) :
    lastFactorLift T (collectiveGenerator (n + 1) a b x) =
      collectiveGenerator (m + 1) a b (lastFactorLift T x) := by
  apply lastSlice_ext
  intro r
  simp only [lastSlice_lastFactorLift, lastSlice_generator, map_add, hT]
  split_ifs <;> simp

end Cloning.TensorLie
