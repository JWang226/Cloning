import Cloning.TensorFundamentalBranchingTransport
import Cloning.TensorFundamentalBranchingWedge
import Cloning.TensorFundamentalBranchingShape
import Cloning.TensorPartitionHighest

/-! Every addable fundamental branch exists in the literal physical tensor product.
A column wedge supplies a highest vector whose final-slot contraction survives the
actual orthogonal projection and canonical cyclic transport. -/
noncomputable section
open scoped BigOperators InnerProductSpace
namespace Cloning.TensorLie
open Cloning.PCT YoungGeneral
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
variable {n d : ℕ}

/-- Existence of every addable one-box branch, without any branching,
character, or dimension premise. -/
theorem exists_fundamental_highest_of_addable
    (Ω : TensorRegister n (Fin d)) (mu : Fin d → ℕ)
    (hΩnorm : ‖Ω‖ = 1)
    (hΩweight : ∀ a, collectiveGenerator n a a Ω = (mu a : ℂ) • Ω)
    (hΩraise : ∀ a b, a < b → collectiveGenerator n a b Ω = 0)
    (hmu : Antitone mu) (r : Fin d) (hr : Antitone (addBox mu r)) :
    ∃ x : TensorRegister (n + 1) (Fin d),
      x ∈ tensorProductSector (cyclicSector Ω) (⊤ : Submodule ℂ (TensorRegister 1 (Fin d))) ∧
      x ≠ 0 ∧
      (∀ a, collectiveGenerator (n + 1) a a x = (addBox mu r a : ℂ) • x) ∧
      (∀ a b, a < b → collectiveGenerator (n + 1) a b x = 0) := by
  let eta := removeInitialColumn mu r
  have heta : Antitone eta := removeInitialColumn_antitone mu hmu r hr
  let A := partitionHighestTensor eta heta
  have hAnorm : ‖A‖ = 1 := partitionHighestTensor_norm eta heta
  have hAweight := partitionHighestTensor_cartan eta heta
  have hAraise := partitionHighestTensor_raising_zero eta heta
  have hd : r.val ≤ d := Nat.le_of_lt r.isLt
  have hd' : r.val + 1 ≤ d := r.isLt
  let H := tensorJoin A (columnHighestTensor hd)
  have hHnorm : ‖H‖ = 1 := tensorJoin_norm_one _ _ hAnorm (columnHighestTensor_norm hd)
  have hHweight (a : Fin d) : collectiveGenerator ((∑ a, eta a) + r.val) a a H = (mu a : ℂ) • H := by
    have he := tensorJoin_cartan a A (columnHighestTensor hd) (eta a : ℂ)
      (if a.val < r.val then 1 else 0) (hAweight a) (columnHighestTensor_cartan hd a)
    have hc : (eta a : ℂ) + (if a.val < r.val then 1 else 0) = (mu a : ℂ) := by
      exact_mod_cast removeInitialColumn_add_indicator mu r hr a
    simpa only [hc] using he
  have hHraise (a b : Fin d) (hab : a < b) :
      collectiveGenerator ((∑ a, eta a) + r.val) a b H = 0 :=
    tensorJoin_raising_zero a b _ _ (hAraise a b hab) (columnHighestTensor_raising_zero hd a b hab)
  let T := projectedCyclicTransport H Ω (fun a => (mu a : ℂ))
    hHweight hΩweight hHraise hΩraise hHnorm hΩnorm
  have hT (a b : Fin d) (z : TensorRegister ((∑ a, eta a) + r.val) (Fin d)) :
      T (collectiveGenerator _ a b z) = collectiveGenerator n a b (T z) :=
    projectedCyclicTransport_intertwines H Ω _ hHweight hΩweight hHraise hΩraise hHnorm hΩnorm a b z
  have hTH : T H = Ω := projectedCyclicTransport_highest H Ω _ hHweight hΩweight hHraise hΩraise hHnorm hΩnorm
  let X := tensorJoin A (columnTensorRaw hd')
  let Y := lastFactorLift T X
  have hYmem : Y ∈ tensorProductSector (cyclicSector Ω) (⊤ : Submodule ℂ (TensorRegister 1 (Fin d))) :=
    lastFactorLift_mem T _
      (projectedCyclicTransport_mem H Ω _ hHweight hΩweight hHraise hΩraise hHnorm hΩnorm) X
  have hslice : lastSlice r Y = (‖columnTensorRaw hd‖ : ℂ) • Ω := by
    change lastSlice r (lastFactorLift T X) = _
    rw [lastSlice_lastFactorLift]
    change T (lastSlice (n := (∑ a, eta a) + r.val) r (tensorJoin (n := ∑ a, eta a) (m := r.val + 1) A (columnTensorRaw hd'))) = _
    rw [lastSlice_tensorJoin_last, lastSlice_columnTensorRaw]
    have hc : columnTensorRaw hd = (‖columnTensorRaw hd‖ : ℂ) • columnHighestTensor hd := by
      simpa only [columnHighestTensor, Complex.coe_smul] using
        (NormedSpace.norm_smul_normalize (columnTensorRaw hd)).symm
    conv_lhs => rw [hc, tensorJoin_smul_right, map_smul, hTH]
  have hYne : Y ≠ 0 := by
    intro hy
    have hc : (‖columnTensorRaw hd‖ : ℂ) ≠ 0 := by
      exact_mod_cast (norm_ne_zero_iff.mpr (columnTensorRaw_ne_zero hd))
    have hΩne : Ω ≠ 0 := by intro he; simp [he] at hΩnorm
    have he := hslice
    rw [hy, map_zero] at he
    exact (smul_ne_zero hc hΩne) he.symm
  refine ⟨Y, hYmem, hYne, ?_, ?_⟩
  · intro a
    have hX : collectiveGenerator ((∑ a, eta a) + r.val + 1) a a X = (addBox mu r a : ℂ) • X := by
      have he := tensorJoin_cartan a A (columnTensorRaw hd') (eta a : ℂ)
        (if a.val < r.val + 1 then 1 else 0) (hAweight a) (columnTensorRaw_cartan hd' a)
      have hc : (eta a : ℂ) + (if a.val < r.val + 1 then 1 else 0) = (addBox mu r a : ℂ) := by
        exact_mod_cast removeInitialColumn_add_succ_indicator mu r hr a
      simpa only [hc] using he
    change collectiveGenerator _ a a (lastFactorLift T X) = _
    rw [← lastFactorLift_intertwines T hT, hX, map_smul]
  · intro a b hab
    have hX : collectiveGenerator ((∑ a, eta a) + r.val + 1) a b X = 0 := tensorJoin_raising_zero a b _ _
      (hAraise a b hab) (columnTensorRaw_raising_zero hd' a b hab)
    change collectiveGenerator _ a b (lastFactorLift T X) = _
    rw [← lastFactorLift_intertwines T hT, hX, map_zero]

end Cloning.TensorLie
