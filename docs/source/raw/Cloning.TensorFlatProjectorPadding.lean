import Cloning.TensorFlatProjectorState

/-! Exact preservation of standard-tableau multiplicity by zero padding. -/
noncomputable section
open scoped BigOperators
namespace Cloning.TensorLie
open Cloning.YoungGeneral
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
variable {n r k : ℕ}

theorem coordinateWordEmbedding_prefix (w : Fin n → Fin r) (N : ℕ) :
    (fun a : Fin (r+k) => (Finset.univ.filter (fun t : Fin n => t.val < N ∧
      coordinateWordEmbedding n r k w t = a)).card) =
    padPartition (fun a => (Finset.univ.filter (fun t : Fin n => t.val < N ∧ w t = a)).card) k := by
  classical
  funext a
  induction a using Fin.addCases with
  | left a => simp [coordinateWordEmbedding, padPartition]
  | right a =>
    have he (t : Fin n) : Fin.castAdd k (w t) ≠ Fin.natAdd r a := by
      intro hh
      have hv := congrArg Fin.val hh
      simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
      omega
    simp [coordinateWordEmbedding, padPartition, he]

theorem coordinateWordEmbedding_rowCount (w : Fin n → Fin r) :
    rowCount (coordinateWordEmbedding n r k w) = padPartition (rowCount w) k := by
  simpa only [Fin.is_lt, true_and, rowCount] using coordinateWordEmbedding_prefix (k := k) w n

theorem coordinateWordEmbedding_standard (w : Fin n → Fin r) :
    IsStandardWord (coordinateWordEmbedding n r k w) ↔ IsStandardWord w := by
  constructor
  · intro hw N a b hab
    have he := hw N (show Fin.castAdd k a ≤ Fin.castAdd k b from hab)
    simpa only [congrFun (coordinateWordEmbedding_prefix w N) _, padPartition_left] using he
  · intro hw N
    rw [coordinateWordEmbedding_prefix]
    exact padPartition_antitone _ (hw N) k

/-- Zero terminal row counts force every actual row-word letter into the
smaller alphabet. -/
theorem word_supported_of_padded_rowCount (w : Fin n → Fin (r+k)) (mu : Fin r → ℕ)
    (hw : rowCount w = padPartition mu k) : ∀ t, (w t).val < r := by
  classical
  intro t
  by_contra ht
  have hr : r ≤ (w t).val := Nat.le_of_not_gt ht
  let a : Fin k := ⟨(w t).val-r, by omega⟩
  have he : w t = Fin.natAdd r a := Fin.ext (by simp only [Fin.val_natAdd]; dsimp [a]; omega)
  have hz : rowCount w (w t) = 0 := by rw [hw, he, padPartition_right]
  have hp : 0 < rowCount w (w t) := by
    apply Finset.card_pos.mpr
    exact ⟨t, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩
  omega

/-- The literal standard-tableau count is unchanged by zero padding. -/
theorem standardCount_padPartition (mu : Fin r → ℕ) (k : ℕ) :
    standardCount n (padPartition mu k) = standardCount n mu := by
  classical
  unfold standardCount
  symm
  apply Finset.card_bij (fun w _ => coordinateWordEmbedding n r k w)
  · intro w hw
    obtain ⟨_,hs,hc⟩ := Finset.mem_filter.mp hw
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, (coordinateWordEmbedding_standard w).mpr hs,
      (coordinateWordEmbedding_rowCount w).trans (congrArg (fun f => padPartition f k) hc)⟩
  · intro w hw v hv he
    exact (coordinateWordEmbedding n r k).injective he
  · intro w hw
    obtain ⟨_,hs,hc⟩ := Finset.mem_filter.mp hw
    have hsupport := word_supported_of_padded_rowCount w mu hc
    let v : Fin n → Fin r := fun t => ⟨(w t).val,hsupport t⟩
    have he : coordinateWordEmbedding n r k v = w := funext (fun t => Fin.ext rfl)
    refine ⟨v, ?_, he⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, (coordinateWordEmbedding_standard v).mp (he.symm ▸ hs), ?_⟩
    have hh := (coordinateWordEmbedding_rowCount v).symm.trans (he ▸ hc)
    funext a
    simpa only [padPartition_left] using congrFun hh (Fin.castAdd k a)

end Cloning.TensorLie
