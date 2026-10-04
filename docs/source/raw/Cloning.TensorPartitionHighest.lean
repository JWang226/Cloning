import Cloning.TensorWedgeHighest
import Cloning.TensorLieProduct
import Mathlib.Order.Interval.Finset.Fin

/-! Normalized highest tensors for arbitrary finite Young diagrams, constructed
as literal products of antisymmetric columns. No irreducible-sector or Schur
identification is asserted here. -/
noncomputable section
open scoped BigOperators InnerProductSpace ComplexOrder
namespace Cloning.TensorLie
open Cloning.PCT
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

/-- Any finite list of column heights gives an actual normalized highest tensor. -/
theorem exists_highestTensor_of_columns {k d : ℕ} (h : Fin k → ℕ)
    (hd : ∀ j, h j ≤ d) :
    ∃ Ω : TensorRegister (∑ j, h j) (Fin d), ‖Ω‖ = 1 ∧
      (∀ a b : Fin d, a < b → collectiveGenerator (∑ j, h j) a b Ω = 0) ∧
      (∀ a : Fin d, collectiveGenerator (∑ j, h j) a a Ω =
        ((∑ j : Fin k, if a.val < h j then 1 else 0 : ℕ) : ℂ) • Ω) := by
  induction k with
  | zero =>
    simp only [Fin.sum_univ_zero]
    refine ⟨registerBasis (Fin 0 → Fin d) Fin.elim0,
      (registerBasis _).orthonormal.norm_eq_one _, ?_, ?_⟩
    · intro a b _
      simp [collectiveGenerator]
    · intro a
      simp [collectiveGenerator]
  | succ k ih =>
    obtain ⟨Ω, hΩ, hraise, hcartan⟩ := ih (fun j => h j.succ) (fun j => hd j.succ)
    rw [Fin.sum_univ_succ]
    refine ⟨tensorJoin (columnHighestTensor (hd 0)) Ω,
      tensorJoin_norm_one _ _ (columnHighestTensor_norm _) hΩ, ?_, ?_⟩
    · intro a b hab
      exact tensorJoin_raising_zero a b _ _ (columnHighestTensor_raising_zero _ a b hab)
        (hraise a b hab)
    · intro a
      have he := tensorJoin_cartan a (columnHighestTensor (hd 0)) Ω
        (if a.val < h 0 then (1 : ℂ) else 0)
        ((∑ j : Fin k, if a.val < h j.succ then 1 else 0 : ℕ) : ℂ)
        (columnHighestTensor_cartan _ a) (hcartan a)
      simpa only [Fin.sum_univ_succ, Nat.cast_add, Nat.cast_ite, Nat.cast_one,
        Nat.cast_zero] using he

/-- Height of the column with zero-based index `j`. -/
def partitionColumnHeight {d : ℕ} (μ : Fin d → ℕ) (j : ℕ) : ℕ :=
  (Finset.univ.filter (fun i => j < μ i)).card

theorem partitionColumnHeight_le {d : ℕ} (μ : Fin d → ℕ) (j : ℕ) :
    partitionColumnHeight μ j ≤ d := by
  exact (Finset.card_filter_le ..).trans_eq (Fintype.card_fin d)

/-- Decreasing rows make each column an initial segment of physical letters. -/
theorem lt_partitionColumnHeight_iff {d : ℕ} (μ : Fin d → ℕ)
    (hμ : Antitone μ) (i : Fin d) (j : ℕ) :
    i.val < partitionColumnHeight μ j ↔ j < μ i := by
  constructor
  · intro hi
    by_contra hj
    have hs : Finset.univ.filter (fun t => j < μ t) ⊆ Finset.Iio i := by
      intro t ht
      have htm : j < μ t := (Finset.mem_filter.mp ht).2
      apply Finset.mem_Iio.mpr
      by_contra hti
      exact (not_lt_of_ge ((hμ (le_of_not_gt hti)).trans (le_of_not_gt hj))) htm
    have hc := Finset.card_le_card hs
    rw [Fin.card_Iio] at hc
    exact Nat.not_lt_of_ge hc hi
  · intro hj
    have hs : Finset.Iic i ⊆ Finset.univ.filter (fun t => j < μ t) := by
      intro t ht
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj.trans_le (hμ (Finset.mem_Iic.mp ht))⟩
    have hc := Finset.card_le_card hs
    rw [Fin.card_Iic] at hc
    exact hc

/-- Count a bounded initial segment of the column indices. -/
theorem sum_column_indicators {N m : ℕ} (hm : m ≤ N) :
    (∑ j : Fin N, if j.val < m then 1 else 0 : ℕ) = m := by
  rw [← Finset.card_filter]
  by_cases hmN : m < N
  · let i : Fin N := ⟨m, hmN⟩
    have he : Finset.univ.filter (fun j : Fin N => j.val < m) = Finset.Iio i := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iio]
      rfl
    rw [he, Fin.card_Iio]
  · have he : m = N := le_antisymm hm (le_of_not_gt hmN)
    subst m
    simp

/-- The number of columns containing row `i` is exactly that row's length. -/
theorem sum_partitionColumnHeight_indicators {d N : ℕ} (μ : Fin d → ℕ)
    (hμ : Antitone μ) (hN : ∀ i, μ i ≤ N) (i : Fin d) :
    (∑ j : Fin N, if i.val < partitionColumnHeight μ j.val then 1 else 0 : ℕ) = μ i := by
  simp_rw [lt_partitionColumnHeight_iff μ hμ]
  exact sum_column_indicators (hN i)

/-- Counting the boxes by columns equals counting them by rows. -/
theorem sum_partitionColumnHeight {d N : ℕ} (μ : Fin d → ℕ)
    (hN : ∀ i, μ i ≤ N) :
    (∑ j : Fin N, partitionColumnHeight μ j.val) = ∑ i, μ i := by
  simp only [partitionColumnHeight, Finset.card_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  exact sum_column_indicators (hN i)

/-- Every finite partition has an actual unit highest tensor of its exact weight.
The ambient space is the literal `sum μ`-fold physical tensor register. -/
theorem exists_partitionHighestTensor {d : ℕ} (μ : Fin d → ℕ) (hμ : Antitone μ) :
    ∃ Ω : TensorRegister (∑ i, μ i) (Fin d), ‖Ω‖ = 1 ∧
      (∀ a b : Fin d, a < b → collectiveGenerator (∑ i, μ i) a b Ω = 0) ∧
      (∀ a : Fin d, collectiveGenerator (∑ i, μ i) a a Ω = (μ a : ℂ) • Ω) := by
  have hN : ∀ i, μ i ≤ ∑ t, μ t := fun i => Finset.single_le_sum
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  have he := exists_highestTensor_of_columns
    (fun j : Fin (∑ i, μ i) => partitionColumnHeight μ j.val)
    (fun j => partitionColumnHeight_le μ j.val)
  have hsum : (∑ j : Fin (∑ i, μ i), partitionColumnHeight μ j.val) = ∑ i, μ i :=
    sum_partitionColumnHeight μ hN
  simp_rw [sum_partitionColumnHeight_indicators μ hμ hN] at he
  exact hsum ▸ he

/-- A fixed actual highest tensor for each finite partition. -/
def partitionHighestTensor {d : ℕ} (μ : Fin d → ℕ) (hμ : Antitone μ) :
    TensorRegister (∑ i, μ i) (Fin d) :=
  Classical.choose (exists_partitionHighestTensor μ hμ)

theorem partitionHighestTensor_norm {d : ℕ} (μ : Fin d → ℕ) (hμ : Antitone μ) :
    ‖partitionHighestTensor μ hμ‖ = 1 :=
  (Classical.choose_spec (exists_partitionHighestTensor μ hμ)).1

theorem partitionHighestTensor_raising_zero {d : ℕ} (μ : Fin d → ℕ) (hμ : Antitone μ)
    (a b : Fin d) (hab : a < b) :
    collectiveGenerator (∑ i, μ i) a b (partitionHighestTensor μ hμ) = 0 :=
  (Classical.choose_spec (exists_partitionHighestTensor μ hμ)).2.1 a b hab

theorem partitionHighestTensor_cartan {d : ℕ} (μ : Fin d → ℕ) (hμ : Antitone μ)
    (a : Fin d) :
    collectiveGenerator (∑ i, μ i) a a (partitionHighestTensor μ hμ) =
      (μ a : ℂ) • partitionHighestTensor μ hμ :=
  (Classical.choose_spec (exists_partitionHighestTensor μ hμ)).2.2 a

end Cloning.TensorLie
