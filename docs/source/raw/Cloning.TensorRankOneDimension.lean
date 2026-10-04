import Cloning.WeylCharacterDimensionPhysical
import Cloning.TensorCloningKernel
import Mathlib.Data.Nat.Choose.Basic

/-! Exact dimensions of physical one-row cyclic sectors. -/
noncomputable section
open scoped BigOperators
namespace Cloning.TensorLie
open Cloning.WeylCharacter Cloning.TensorCloning
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

theorem dimensionProduct_oneRow (n d : ℕ) :
    dimensionProduct (oneRowPartition n d) = ((n+d).choose d : ℝ) := by
  rw [dimensionProduct_eq_pairProduct]
  have hall (i : Fin (d+1)) :
      (∏ j ∈ Finset.Ioi i,
        (((oneRowPartition n d i : ℝ)-oneRowPartition n d j+j.val-i.val)/((j.val:ℝ)-i.val))) =
      ∏ j : Fin (d+1), if i<j then
        (((oneRowPartition n d i : ℝ)-oneRowPartition n d j+j.val-i.val)/((j.val:ℝ)-i.val)) else 1 := by
    rw [← Finset.prod_filter]
    congr 1
    ext j
    simp
  simp_rw [hall]
  rw [Fin.prod_univ_succ]
  have htail : (∏ i : Fin d, ∏ j : Fin (d+1), if i.succ<j then
      (((oneRowPartition n d i.succ : ℝ)-oneRowPartition n d j+j.val-i.succ.val)/
        ((j.val:ℝ)-i.succ.val)) else 1)=1 := by
    apply Finset.prod_eq_one
    intro i _
    apply Finset.prod_eq_one
    intro j _
    split_ifs with hij
    · have hj : j ≠ 0 := by intro h; subst j; exact (not_lt_of_ge (Fin.zero_le _)) hij
      have hgap : (j.val:ℝ)-i.succ.val ≠ 0 := (sub_pos.mpr (by exact_mod_cast hij)).ne'
      simp only [oneRowPartition,if_neg (Fin.succ_ne_zero i),if_neg hj,Nat.cast_zero,
        sub_self,zero_add,div_self hgap]
    · rfl
  rw [htail,mul_one,Fin.prod_univ_succ]
  simp only [lt_self_iff_false,if_false,one_mul,Fin.succ_pos,if_true,
    oneRowPartition,if_true,Fin.succ_ne_zero,if_false,Nat.cast_zero,sub_zero,Fin.val_zero,
    Fin.val_succ,Nat.cast_add,Nat.cast_one]
  rw [Finset.prod_div_distrib]
  have hnum : (∏ j : Fin d, ((n:ℝ)+(j.val+1)))=((n+1).ascFactorial d : ℝ) := by
    rw [Nat.ascFactorial_eq_prod_range]
    simp only [Nat.cast_prod,Nat.cast_add,Nat.cast_one]
    rw [← Fin.prod_univ_eq_prod_range]
    apply Finset.prod_congr rfl
    intro j _
    ring
  have hden : (∏ j : Fin d, (j.val+1:ℝ))=(d.factorial:ℝ) := by
    rw [Nat.factorial_eq_prod_range_add_one]
    simp only [Nat.cast_prod,Nat.cast_add,Nat.cast_one]
    rw [← Fin.prod_univ_eq_prod_range]
  rw [hnum,hden,Nat.ascFactorial_eq_factorial_mul_choose,Nat.cast_mul]
  exact mul_div_cancel_left₀ _ (by exact_mod_cast Nat.factorial_ne_zero d)

theorem partitionDimension_oneRow (n d : ℕ) :
    partitionDimension (oneRowPartition n d) (oneRowPartition_antitone n d)=(n+d).choose d := by
  have h := partitionDimension_eq_dimensionProduct (oneRowPartition n d) (oneRowPartition_antitone n d)
  rw [dimensionProduct_oneRow] at h
  exact_mod_cast h

end Cloning.TensorLie
