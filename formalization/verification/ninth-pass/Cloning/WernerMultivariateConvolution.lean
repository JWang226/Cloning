import Cloning.WernerNormalization
import Cloning.WernerDimensionIdentity

/-! The multivariate negative-binomial convolution supplying the exact
partial-trace balance of the symmetric projector. -/
namespace Cloning.Occupation
open scoped BigOperators
open Finset

private theorem list_choose_convolution (s r : ℕ) (a : Fin (s + 1) → ℕ) :
    ((List.Nat.antidiagonalTuple (s + 1) r).map
      (fun b => ∏ i, (b i + a i).choose (a i))).sum =
      (r + (∑ i, a i) + s).choose ((∑ i, a i) + s) := by
  induction s generalizing r with
  | zero => simp
  | succ s ih =>
    rw [List.Nat.antidiagonalTuple, List.map_flatMap, List.flatMap_def, List.sum_flatten]
    simp only [List.map_map, Function.comp_def]
    have hprod (t : ℕ) (b : Fin (s + 1) → ℕ) :
        (∏ i : Fin (s + 1 + 1), ((Fin.cons t b : Fin (s + 1 + 1) → ℕ) i + a i).choose (a i)) =
          (t + a 0).choose (a 0) * ∏ i, (b i + a i.succ).choose (a i.succ) := by
      rw [Fin.prod_univ_succ]
      rfl
    simp_rw [hprod, List.sum_map_mul_left, ih]
    simp only [List.Nat.antidiagonal, List.map_map, Function.comp_def]
    rw [← List.sum_toFinset _ List.nodup_range]
    simp only [List.toFinset_range]
    convert choose_convolution (a 0) ((∑ i : Fin (s + 1), a i.succ) + s) r using 1 <;>
      simp [Fin.sum_univ_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- Convolution over actual occupation vectors with a fixed total. -/
theorem multivariate_choose_convolution (s r : ℕ) (a : Fin (s + 1) → ℕ) :
    (∑ b ∈ Finset.Nat.antidiagonalTuple (s + 1) r,
      ∏ i, (b i + a i).choose (a i)) =
      (r + (∑ i, a i) + s).choose ((∑ i, a i) + s) := by
  have heq : (∑ b ∈ Finset.Nat.antidiagonalTuple (s + 1) r,
      ∏ i, (b i + a i).choose (a i)) =
      ((List.Nat.antidiagonalTuple (s + 1) r).map
        (fun b => ∏ i, (b i + a i).choose (a i))).sum := rfl
  rw [heq]
  exact list_choose_convolution s r a

/-- The same convolution in the form used for added occupation numbers. -/
theorem multivariate_choose_added (s r : ℕ) (a : Fin (s + 1) → ℕ) :
    (∑ b ∈ Finset.Nat.antidiagonalTuple (s + 1) r,
      ∏ i, (a i + b i).choose (b i)) =
      ((∑ i, a i) + r + s).choose r := by
  have he (b : Fin (s + 1) → ℕ) : (∏ i, (a i + b i).choose (b i)) =
      ∏ i, (b i + a i).choose (a i) := by
    apply prod_congr rfl
    intro i hi
    simpa [Nat.add_comm] using (Nat.choose_symm_add (a := a i) (b := b i)).symm
  simp_rw [he]
  rw [multivariate_choose_convolution]
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    (Nat.choose_symm_add (a := (∑ i, a i) + s) (b := r))

/-- The scalar balance factor is the ratio of the symmetric dimensions. -/
theorem werner_balance_dimension_identity (n r s : ℕ) :
    ((n + r + s).choose (n + s) : ℝ) / ((n + r).choose n : ℝ) =
      ((n + r + s).choose s : ℝ) / ((n + s).choose s : ℝ) := by
  have ha : ((n + s).choose s : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (Nat.le_add_left s n)).ne'
  have hb : ((n + r).choose n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (Nat.le_add_right n r)).ne'
  have hid : ((n + r + s).choose (n + s) : ℝ) * ((n + s).choose s : ℝ) =
      ((n + r + s).choose s : ℝ) * ((n + r).choose n : ℝ) := by
    exact_mod_cast (by simpa using
      (Nat.choose_mul (n := n + r + s) (k := n + s) (s := s) (Nat.le_add_left s n)))
  exact (div_eq_div_iff hb ha).mpr hid

end Cloning.Occupation
