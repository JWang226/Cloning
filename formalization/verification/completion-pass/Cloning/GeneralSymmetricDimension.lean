import Cloning.GeneralSymmetricOccupation
import Cloning.WernerNormalization
import Mathlib.Data.Fintype.BigOperators

/-! # All occupation profiles and the general symmetric-tensor dimension

Every nonnegative multiplicity vector summing to the tensor length is realized
by an actual computational word. Thus the constructed occupation basis has the
usual stars-and-bars dimension.
-/
noncomputable section
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000
open scoped BigOperators

namespace Cloning.GeneralSymmetricOccupation

theorem profile_sum {L d : ℕ} (w : Word L d) : ∑ a, profile w a = L := by
  have h := Fintype.card_congr (Equiv.sigmaFiberEquiv w)
  simpa [Fintype.card_sigma, profile] using h

/-- Every composition of the tensor length is realized by a computational word. -/
theorem exists_word_of_sum {L d : ℕ} (q : Fin d → ℕ) (hq : ∑ a, q a = L) :
    ∃ w : Word L d, profile w = q := by
  classical
  let e : Fin L ≃ (Σ a : Fin d, Fin (q a)) :=
    Fintype.equivOfCardEq (by simpa using hq.symm)
  let w : Word L d := fun i => (e i).1
  refine ⟨w, funext fun a => ?_⟩
  let f : {i : Fin L // w i = a} ≃ {x : Σ b : Fin d, Fin (q b) // x.1 = a} :=
    e.subtypeEquiv (fun _ => Iff.rfl)
  have h := Fintype.card_congr (f.trans (Equiv.sigmaSubtype a))
  simpa [profile] using h

/-- Realized occupations are exactly the stars-and-bars compositions. -/
def compositionEquiv (L d : ℕ) :
    Occupation L d ≃ {q : Fin d → ℕ // ∑ a, q a = L} where
  toFun q := ⟨q.val, by rcases q.property with ⟨w, hw⟩; rw [← hw]; exact profile_sum w⟩
  invFun q := ⟨q.val, exists_word_of_sum q.val q.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem occupation_card (L s : ℕ) :
    Fintype.card (Occupation L (s + 1)) = (L + s).choose s := by
  let e : Occupation L (s + 1) ≃
      {q // q ∈ Finset.Nat.antidiagonalTuple (s + 1) L} :=
    (compositionEquiv L (s + 1)).trans (Equiv.subtypeEquivRight (fun q : Fin (s + 1) → ℕ =>
      Finset.Nat.mem_antidiagonalTuple.symm))
  rw [Fintype.card_congr e, Fintype.card_coe]
  exact Cloning.WernerNormalization.antidiagonalTuple_card s L

end Cloning.GeneralSymmetricOccupation
