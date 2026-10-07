import Cloning.TensorFlatProjectorDimensionLimit
import Cloning.YoungDimensionRatio

/-! Exact ambient/support dimension ratios for zero-padded physical partitions. -/
noncomputable section
open scoped BigOperators
namespace Cloning.TensorLie
open Cloning.WeylCharacter Cloning.YoungDimensionRatio
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {r k : ℕ}

def padPartition (mu : Fin r → ℕ) (k : ℕ) : Fin (r+k) → ℕ :=
  Fin.append mu (fun _ => 0)

@[simp] theorem padPartition_left (mu : Fin r → ℕ) (i : Fin r) :
    padPartition mu k (Fin.castAdd k i) = mu i := Fin.append_left ..

@[simp] theorem padPartition_right (mu : Fin r → ℕ) (j : Fin k) :
    padPartition mu k (Fin.natAdd r j) = 0 := Fin.append_right ..

theorem padPartition_antitone (mu : Fin r → ℕ) (hmu : Antitone mu) (k : ℕ) :
    Antitone (padPartition mu k) := by
  intro i j
  induction i using Fin.addCases with
  | left i =>
    induction j using Fin.addCases with
    | left j =>
      intro hij
      simpa only [padPartition_left] using hmu (show i ≤ j from hij)
    | right j => simp
  | right i =>
    induction j using Fin.addCases with
    | left j =>
      intro hij
      have hh : r+i.val ≤ j.val := hij
      omega
    | right j => simp

@[simp] theorem sum_padPartition (mu : Fin r → ℕ) (k : ℕ) :
    ∑ a, padPartition mu k a = ∑ a, mu a := by
  rw [Fin.sum_univ_add]
  simp

private theorem dimensionProduct_eq_allPairs {d : ℕ} (mu : Fin d → ℕ) :
    dimensionProduct mu = ∏ i : Fin d, ∏ j : Fin d,
      if i < j then ((mu i : ℝ)-mu j+j.val-i.val)/((j.val:ℝ)-i.val) else 1 := by
  rw [dimensionProduct_eq_pairProduct]
  apply Finset.prod_congr rfl
  intro i _
  rw [← Finset.prod_filter]
  congr 1
  ext j
  simp

private theorem zero_tail_factor (i j : Fin k) :
    (if Fin.natAdd r i < Fin.natAdd r j then
      (((0:ℕ):ℝ)-0+(Fin.natAdd r j).val-(Fin.natAdd r i).val) /
        (((Fin.natAdd r j).val:ℝ)-(Fin.natAdd r i).val) else 1) = 1 := by
  split_ifs with h
  · simp only [Nat.cast_zero, sub_zero, zero_add]
    apply div_self
    have hh : ((Fin.natAdd r i).val : ℝ) < (Fin.natAdd r j).val := by exact_mod_cast h
    linarith
  · rfl

/-- The physical Weyl product factors into support and crossing roots. -/
theorem dimensionProduct_padPartition (mu : Fin r → ℕ) (k : ℕ) :
    dimensionProduct (padPartition mu k) =
      dimensionProduct mu * dimensionRatio r k (fun i => (mu i : ℝ)) := by
  rw [dimensionProduct_eq_allPairs, Fin.prod_univ_add]
  simp_rw [Fin.prod_univ_add, padPartition_left, padPartition_right]
  have hcross (i : Fin r) (j : Fin k) : Fin.castAdd k i < Fin.natAdd r j := by
    change i.val < r+j.val
    omega
  have hback (i : Fin k) (j : Fin r) : ¬ Fin.natAdd r i < Fin.castAdd k j := by
    change ¬ r+i.val < j.val
    omega
  have hsame (i j : Fin r) : (Fin.castAdd k i < Fin.castAdd k j) ↔ i < j := Iff.rfl
  simp only [hsame, hcross, hback, if_true, if_false,
    zero_tail_factor, Finset.prod_const_one, one_mul, mul_one]
  simp only [Fin.val_castAdd]
  simp only [Nat.cast_zero]
  have htail : (∏ i : Fin k, ∏ j : Fin k,
      if Fin.natAdd r i < Fin.natAdd r j then
        ((0:ℝ)-0+(Fin.natAdd r j).val-(Fin.natAdd r i).val) /
          (((Fin.natAdd r j).val:ℝ)-(Fin.natAdd r i).val) else 1) = 1 := by
    apply Finset.prod_eq_one
    intro i _
    apply Finset.prod_eq_one
    intro j _
    simpa only [Nat.cast_zero] using zero_tail_factor (r := r) i j
  rw [htail, mul_one, Finset.prod_mul_distrib, dimensionProduct_eq_allPairs]
  congr 1
  unfold dimensionRatio
  rw [Fintype.prod_prod_type]
  apply Finset.prod_congr rfl
  intro i _
  apply Finset.prod_congr rfl
  intro j _
  simp only [Fin.val_castAdd, Fin.val_natAdd, Nat.cast_add, Nat.cast_zero, sub_zero,
    crossingGap]
  congr 1
  ring

/-- The ratio uses the actual ambient and support Hilbert-space dimensions. -/
theorem partitionDimension_pad_ratio (mu : Fin r → ℕ) (hmu : Antitone mu) (k : ℕ) :
    (partitionDimension (padPartition mu k) (padPartition_antitone mu hmu k) : ℝ) /
      (partitionDimension mu hmu : ℝ) = dimensionRatio r k (fun i => (mu i : ℝ)) := by
  rw [partitionDimension_eq_dimensionProduct, partitionDimension_eq_dimensionProduct,
    dimensionProduct_padPartition, mul_div_cancel_left₀ _ (dimensionProduct_pos mu hmu).ne']

end Cloning.TensorLie
