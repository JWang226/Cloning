import Cloning.TensorWedge
import Mathlib.Analysis.Normed.Module.Normalize

/-! Concrete normalized highest tensors for individual antisymmetric columns. -/
noncomputable section
open scoped BigOperators InnerProductSpace ComplexOrder
namespace Cloning.TensorLie
open Cloning.PCT
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

/-- Initial-segment inclusion of a column's letters into the physical alphabet. -/
def columnLetters {h d : ℕ} (hd : h ≤ d) : Fin h ↪ Fin d :=
  ⟨fun i => ⟨i.val, lt_of_lt_of_le i.isLt hd⟩,
    fun _ _ he => Fin.ext (congrArg (fun x : Fin d => x.val) he)⟩

@[simp] theorem columnLetters_val {h d : ℕ} (hd : h ≤ d) (i : Fin h) :
    (columnLetters hd i).val = i.val := rfl

/-- The nonzero antisymmetrization of `|0> ⊗ … ⊗ |h-1>`. -/
def columnTensorRaw {h d : ℕ} (hd : h ≤ d) : TensorRegister h (Fin d) :=
  wedgeTensor h (fun i => registerBasis (Fin d) (columnLetters hd i))

theorem columnTensorRaw_ne_zero {h d : ℕ} (hd : h ≤ d) : columnTensorRaw hd ≠ 0 :=
  wedgeTensor_basis_ne_zero (columnLetters hd)

/-- Every physical raising matrix unit annihilates the antisymmetric column. -/
theorem columnTensorRaw_raising_zero {h d : ℕ} (hd : h ≤ d)
    (a b : Fin d) (hab : a < b) :
    collectiveGenerator h a b (columnTensorRaw hd) = 0 := by
  rw [columnTensorRaw, collectiveGenerator_wedgeTensor]
  apply Finset.sum_eq_zero
  intro i _
  rw [matrixUnit_basis]
  by_cases hbi : b = columnLetters hd i
  · rw [if_pos hbi]
    have ha : a.val < h := by
      have hb : b.val = i.val := congrArg Fin.val hbi
      exact lt_trans (show a.val < b.val from hab) (hb ▸ i.isLt)
    let j : Fin h := ⟨a.val, ha⟩
    have haj : columnLetters hd j = a := Fin.ext rfl
    have hij : i ≠ j := by
      intro he
      have hba : b = a := hbi.trans (congrArg (columnLetters hd) he |>.trans haj)
      exact (ne_of_lt hab) hba.symm
    apply (wedgeTensor h).map_eq_zero_of_eq (i := i) (j := j)
    · simp only [Function.update_self, Function.update_of_ne hij.symm, haj]
    · exact hij
  · rw [if_neg hbi, AlternatingMap.map_update_zero]

/-- The column contains each letter below its height exactly once. -/
theorem columnTensorRaw_cartan {h d : ℕ} (hd : h ≤ d) (a : Fin d) :
    collectiveGenerator h a a (columnTensorRaw hd) =
      (if a.val < h then (1 : ℂ) else 0) • columnTensorRaw hd := by
  rw [columnTensorRaw, collectiveGenerator_wedgeTensor]
  by_cases ha : a.val < h
  · rw [if_pos ha, one_smul]
    let i : Fin h := ⟨a.val, ha⟩
    have hai : a = columnLetters hd i := Fin.ext rfl
    rw [Finset.sum_eq_single i]
    · rw [matrixUnit_basis, if_pos hai, hai, Function.update_eq_self]
    · intro j _ hji
      have haj : a ≠ columnLetters hd j := by
        intro he
        exact hji ((columnLetters hd).injective (he.symm.trans hai))
      rw [matrixUnit_basis, if_neg haj, AlternatingMap.map_update_zero]
    · simp
  · rw [if_neg ha, zero_smul]
    apply Finset.sum_eq_zero
    intro i _
    have hai : a ≠ columnLetters hd i := by
      intro he
      exact ha ((congrArg Fin.val he) ▸ i.isLt)
    rw [matrixUnit_basis, if_neg hai, AlternatingMap.map_update_zero]

/-- A column vector with a proved, rather than postulated, unit norm. -/
def columnHighestTensor {h d : ℕ} (hd : h ≤ d) : TensorRegister h (Fin d) :=
  NormedSpace.normalize (columnTensorRaw hd)

theorem columnHighestTensor_norm {h d : ℕ} (hd : h ≤ d) :
    ‖columnHighestTensor hd‖ = 1 :=
  NormedSpace.norm_normalize (columnTensorRaw_ne_zero hd)

theorem columnHighestTensor_raising_zero {h d : ℕ} (hd : h ≤ d)
    (a b : Fin d) (hab : a < b) :
    collectiveGenerator h a b (columnHighestTensor hd) = 0 := by
  simp only [columnHighestTensor, NormedSpace.normalize,
    ContinuousLinearMap.map_smul_of_tower, columnTensorRaw_raising_zero hd a b hab, smul_zero]

theorem columnHighestTensor_cartan {h d : ℕ} (hd : h ≤ d) (a : Fin d) :
    collectiveGenerator h a a (columnHighestTensor hd) =
      (if a.val < h then (1 : ℂ) else 0) • columnHighestTensor hd := by
  simp only [columnHighestTensor, NormedSpace.normalize,
    ContinuousLinearMap.map_smul_of_tower, columnTensorRaw_cartan]
  exact smul_comm _ _ _

end Cloning.TensorLie
