import Cloning.Occupation
import Mathlib.Data.Fin.Tuple.NatAntidiagonal
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Normalization of Werner's occupation law on the full Fock index set

We count fixed-total occupation vectors by stars and bars and pass from the
finite shell identity to a normalized probability law on `Fin s → ℕ`.
-/

namespace Cloning.WernerNormalization

noncomputable section
open scoped BigOperators
open Finset

/-- Werner's eigenvalue, padded by zero beyond its finite occupation support. -/
def occupationLaw (n m s : ℕ) (k : Fin s → ℕ) : ℝ :=
  if (∑ i, k i) ≤ m - n then
    Occupation.wernerWeight n m (s + 1) (∑ i, k i) else 0

theorem occupationLaw_nonneg (n m s : ℕ) (k : Fin s → ℕ) :
    0 ≤ occupationLaw n m s k := by
  unfold occupationLaw Occupation.wernerWeight
  split_ifs <;> positivity

/-- Stars and bars for the actual occupation vectors, rather than grouped weights. -/
theorem antidiagonalTuple_card (s t : ℕ) :
    (Finset.Nat.antidiagonalTuple (s + 1) t).card = (t + s).choose s := by
  have hlen : ∀ s t, (List.Nat.antidiagonalTuple (s + 1) t).length =
      (t + s).choose s := by
    intro s
    induction s with
    | zero => intro t; simp
    | succ s ih =>
      intro t
      rw [List.Nat.antidiagonalTuple]
      simp only [List.length_flatMap, List.length_map]
      simp only [List.Nat.antidiagonal, List.map_map, Function.comp_def, ih]
      rw [← List.sum_toFinset _ List.nodup_range]
      simp only [List.toFinset_range]
      rw [← Finset.sum_flip]
      calc
        _ = ∑ r ∈ range (t + 1), (r + s).choose s := by
          apply sum_congr rfl
          intro r hr
          rw [Nat.sub_sub_self (Nat.lt_succ_iff.mp (mem_range.mp hr))]
        _ = _ := Nat.sum_range_add_choose t s
  exact hlen s t

/-- The finite set containing exactly all padded occupation indices. -/
def occupationSupport (s b : ℕ) : Finset (Fin s → ℕ) :=
  (range (b + 1)).biUnion (Finset.Nat.antidiagonalTuple s)

theorem mem_occupationSupport {s b : ℕ} {k : Fin s → ℕ} :
    k ∈ occupationSupport s b ↔ (∑ i, k i) ≤ b := by
  simp only [occupationSupport, mem_biUnion, mem_range,
    Finset.Nat.mem_antidiagonalTuple]
  constructor
  · rintro ⟨t, ht, hkt⟩
    omega
  · intro hk
    exact ⟨∑ i, k i, by omega, rfl⟩

theorem occupationLaw_sum (n m s : ℕ) (hnm : n ≤ m) (hs : 1 ≤ s) :
    (∑ k ∈ occupationSupport s (m - n), occupationLaw n m s k) = 1 := by
  have hd : Set.PairwiseDisjoint (↑(range (m - n + 1)))
      (Finset.Nat.antidiagonalTuple s) := by
    intro a ha b hb hab
    apply disjoint_left.mpr
    intro k hka hkb
    apply hab
    exact (Finset.Nat.mem_antidiagonalTuple.mp hka).symm.trans
      (Finset.Nat.mem_antidiagonalTuple.mp hkb)
  rw [occupationSupport, sum_biUnion hd]
  have hinner : ∀ t ∈ range (m - n + 1),
      (∑ k ∈ Finset.Nat.antidiagonalTuple s t, occupationLaw n m s k) =
        ((t + (s + 1) - 2).choose ((s + 1) - 2) : ℝ) *
          Occupation.wernerWeight n m (s + 1) t := by
    intro t ht
    have ht' : t ≤ m - n := Nat.lt_succ_iff.mp (mem_range.mp ht)
    have heq : (∑ k ∈ Finset.Nat.antidiagonalTuple s t, occupationLaw n m s k) =
        (Finset.Nat.antidiagonalTuple s t).card *
          Occupation.wernerWeight n m (s + 1) t := by
      calc
        _ = ∑ _k ∈ Finset.Nat.antidiagonalTuple s t,
            Occupation.wernerWeight n m (s + 1) t := by
          apply sum_congr rfl
          intro k hk
          simp only [occupationLaw, Finset.Nat.mem_antidiagonalTuple.mp hk,
            if_pos ht']
        _ = _ := by simp
    rw [heq]
    have hs' : s = (s - 1) + 1 := by omega
    rw [hs', antidiagonalTuple_card]
    congr 2
  rw [sum_congr rfl hinner]
  exact Occupation.werner_occupation_normalization n m (s + 1) hnm (by omega)

theorem occupationLaw_hasSum (n m s : ℕ) (hnm : n ≤ m) (hs : 1 ≤ s) :
    HasSum (occupationLaw n m s) 1 := by
  rw [← occupationLaw_sum n m s hnm hs]
  apply hasSum_sum_of_ne_finset_zero
  intro k hk
  unfold occupationLaw
  rw [if_neg]
  exact fun h => hk (mem_occupationSupport.mpr h)

end
end Cloning.WernerNormalization
