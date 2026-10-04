import Cloning.CloningValueComparisonMonotone
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.BigOperators.Intervals

/-! Concrete simple spectra with every eigenvalue ratio tending to zero. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace Cloning.ValueComparison
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false

def geometricNormalizer (d : ℕ) (t : ℝ) : ℝ := ∑i : Fin d, t^i.val

theorem geometricNormalizer_pos {d : ℕ} (hd : 1≤d) {t : ℝ} (ht : 0<t) :
    0<geometricNormalizer d t := by
  apply Finset.sum_pos
  · intro i _
    exact pow_pos ht _
  · exact ⟨⟨0,by omega⟩,Finset.mem_univ _⟩

def geometricSpectrum (d : ℕ) (hd : 1≤d) (t : ℝ) (ht0 : 0<t) (ht1 : t<1) :
    SimpleSpectrum d where
  eigenvalue i := t^i.val/geometricNormalizer d t
  positive i := div_pos (pow_pos ht0 _) (geometricNormalizer_pos hd ht0)
  strictAnti := by
    intro i j hij
    exact (div_lt_div_iff_of_pos_right (geometricNormalizer_pos hd ht0)).mpr
      (pow_lt_pow_right_of_lt_one₀ ht0 ht1 hij)
  normalized := by
    rw [←Finset.sum_div]
    exact div_self (geometricNormalizer_pos hd ht0).ne'

theorem geometricSpectrum_ratio (d : ℕ) (hd : 1≤d) (t : ℝ) (ht0 : 0<t)
    (ht1 : t<1) (ij : PairIndex d) :
    (geometricSpectrum d hd t ht0 ht1).ratio ij = t^(ij.val.2.val-ij.val.1.val) := by
  dsimp [SimpleSpectrum.ratio,geometricSpectrum]
  rw [div_div_div_cancel_right₀ (geometricNormalizer_pos hd ht0).ne']
  exact (pow_sub₀ t ht0.ne' (Nat.le_of_lt ij.property)).symm

def geometricSequence (d : ℕ) (hd : 1≤d) (n : ℕ) : SimpleSpectrum d :=
  geometricSpectrum d hd ((1/2:ℝ)^(n+1)) (pow_pos (by norm_num) _)
    (pow_lt_one₀ (by norm_num) (by norm_num) (by omega))

theorem geometricSequence_ratio_tendsto (d : ℕ) (hd : 1≤d) (ij : PairIndex d) :
    Tendsto (fun n => (geometricSequence d hd n).ratio ij) atTop (𝓝 0) := by
  have ht : Tendsto (fun n : ℕ => (1/2:ℝ)^(n+1)) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ)≤1/2)
      (by norm_num : (1/2:ℝ)<1)).comp (tendsto_add_atTop_nat 1)
  have hpos : 0 < ij.val.2.val - ij.val.1.val := Nat.sub_pos_of_lt ij.property
  simpa only [geometricSequence,geometricSpectrum_ratio,zero_pow (Nat.ne_of_gt hpos)] using
    ht.pow (ij.val.2.val-ij.val.1.val)

/-- Counting each unordered pair once, without assuming a mode enumeration. -/
theorem pairIndex_card (d : ℕ) : Fintype.card (PairIndex d)*2=d*(d-1) := by
  let e : PairIndex d ≃ Σj : Fin d, Fin j.val :=
    { toFun := fun ij => ⟨ij.val.2,⟨ij.val.1.val,ij.property⟩⟩
      invFun := fun ji => ⟨(⟨ji.2.val,lt_trans ji.2.isLt ji.1.isLt⟩,ji.1),ji.2.isLt⟩
      left_inv := by intro ij; rfl
      right_inv := by intro ji; rfl }
  rw [Fintype.card_congr e,Fintype.card_sigma]
  simp only [Fintype.card_fin]
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => i)]
  exact Finset.sum_range_id_mul_two d

theorem pairIndex_card_real (d : ℕ) (hd : 1≤d) :
    (Fintype.card (PairIndex d):ℝ)=(d:ℝ)*((d:ℝ)-1)/2 := by
  have h := pairIndex_card d
  have hr : (Fintype.card (PairIndex d):ℝ)*2=(d:ℝ)*((d:ℝ)-1) := by
    exact_mod_cast h
  linarith

end Cloning.ValueComparison
