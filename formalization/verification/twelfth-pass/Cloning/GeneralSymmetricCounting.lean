import Cloning.GeneralSymmetricOccupation

/-! # Exact occupation-fiber counting for the Werner output

For any occupation and any set of `n` tensor slots, the proportion of its
computational words having the reference letter on those slots is
`choose(reference multiplicity, n) / choose(total length, n)`. The proof
double-counts pairs of a word and a subset of its reference-letter slots.
-/
noncomputable section
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000
open scoped BigOperators

namespace Cloning.GeneralSymmetricOccupation

/-- Words of a prescribed occupation. -/
def fiber {L d : ℕ} (q : Occupation L d) : Finset (Word L d) :=
  Finset.univ.filter (fun w => label w = q)

@[simp] theorem mem_fiber {L d : ℕ} (q : Occupation L d) (w : Word L d) :
    w ∈ fiber q ↔ label w = q := by simp [fiber]

@[simp] theorem fiber_card {L d : ℕ} (q : Occupation L d) :
    (fiber q).card = multiplicity q := rfl

/-- Slots carrying one fixed one-particle basis vector. -/
def letterSlots {L d : ℕ} (w : Word L d) (a : Fin d) : Finset (Fin L) :=
  Finset.univ.filter (fun i => w i = a)

@[simp] theorem mem_letterSlots {L d : ℕ} (w : Word L d) (a : Fin d) (i : Fin L) :
    i ∈ letterSlots w a ↔ w i = a := by simp [letterSlots]

theorem letterSlots_card {L d : ℕ} (w : Word L d) (a : Fin d) :
    (letterSlots w a).card = profile w a := by
  simp [letterSlots, profile, Fintype.card_subtype]

/-- The part of an occupation fiber surviving a fixed-slot pure input projector. -/
def accepted {L d : ℕ} (q : Occupation L d) (a : Fin d) (S : Finset (Fin L)) :
    Finset (Word L d) := (fiber q).filter (fun w => S ⊆ letterSlots w a)

@[simp] theorem mem_accepted {L d : ℕ} (q : Occupation L d) (a : Fin d)
    (S : Finset (Fin L)) (w : Word L d) :
    w ∈ accepted q a S ↔ label w = q ∧ ∀ i ∈ S, w i = a := by
  simp [accepted, Finset.subset_iff]

/-- Permuting slots gives a genuine bijection between the accepted word sets. -/
theorem accepted_card_eq_of_card_eq {L d : ℕ} (q : Occupation L d) (a : Fin d)
    (S T : Finset (Fin L)) (hST : S.card = T.card) :
    (accepted q a S).card = (accepted q a T).card := by
  classical
  let e : ↥S ≃ ↥T := Finset.equivOfCardEq hST
  let σ : Equiv.Perm (Fin L) := e.extendSubtype
  have hσ : ∀ i : Fin L, i ∈ S ↔ σ i ∈ T := by
    intro i
    exact ⟨e.extendSubtype_mem i, fun h => by
      by_contra hi
      exact e.extendSubtype_not_mem i hi h⟩
  let E : Word L d ≃ Word L d :=
    { toFun := fun w => w ∘ σ.symm
      invFun := fun w => w ∘ σ
      left_inv := fun w => by funext i; simp
      right_inv := fun w => by funext i; simp }
  apply Finset.card_equiv E
  intro w
  simp only [mem_accepted]
  change (label w = q ∧ ∀ i ∈ S, w i = a) ↔
    (label (w ∘ σ.symm) = q ∧ ∀ i ∈ T, w (σ.symm i) = a)
  rw [label_permute]
  refine and_congr_right (fun _ => ⟨?_, ?_⟩)
  · intro h i hi
    apply h (σ.symm i)
    exact (hσ _).mpr (by simpa using hi)
  · intro h i hi
    simpa using h (σ i) ((hσ i).mp hi)

private theorem subset_sum {L d : ℕ} (w : Word L d) (a : Fin d) (n : ℕ) :
    (∑ S ∈ Finset.powersetCard n (Finset.univ : Finset (Fin L)),
      if S ⊆ letterSlots w a then (1 : ℕ) else 0) = (profile w a).choose n := by
  classical
  have hf : (Finset.powersetCard n (Finset.univ : Finset (Fin L))).filter
      (fun S => S ⊆ letterSlots w a) = Finset.powersetCard n (letterSlots w a) := by
    ext S
    simp only [Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_univ, true_and]
    tauto
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one, hf,
    Finset.card_powersetCard, letterSlots_card]
  norm_cast

/-- Exact finite double-counting identity underlying the occupation eigenvalue. -/
theorem accepted_card_mul_choose {L d : ℕ} (q : Occupation L d) (a : Fin d)
    (S : Finset (Fin L)) :
    (accepted q a S).card * L.choose S.card =
      multiplicity q * (q.val a).choose S.card := by
  classical
  let sets := Finset.powersetCard S.card (Finset.univ : Finset (Fin L))
  have hconstant : (∑ T ∈ sets, (accepted q a T).card) =
      (accepted q a S).card * L.choose S.card := by
    calc
      _ = ∑ _T ∈ sets, (accepted q a S).card := by
        apply Finset.sum_congr rfl
        intro T hT
        apply accepted_card_eq_of_card_eq
        exact (Finset.mem_powersetCard.mp hT).2
      _ = _ := by simp [sets, Finset.card_powersetCard, mul_comm]
  rw [← hconstant]
  have hf : ∀ T, (accepted q a T).card =
      ∑ w ∈ fiber q, if T ⊆ letterSlots w a then (1 : ℕ) else 0 := by
    intro T
    rw [accepted, Finset.card_eq_sum_ones, Finset.sum_filter]
  simp_rw [hf]
  rw [Finset.sum_comm]
  calc
    _ = ∑ w ∈ fiber q, (profile w a).choose S.card := by
      apply Finset.sum_congr rfl
      intro w hw
      exact subset_sum w a S.card
    _ = ∑ _w ∈ fiber q, (q.val a).choose S.card := by
      apply Finset.sum_congr rfl
      intro w hw
      have h := congrArg (fun r : Occupation L d => r.val a) (mem_fiber q w |>.mp hw)
      exact congrArg (fun k : ℕ => k.choose S.card) h
    _ = _ := by simp

/-- The physical occupation probability of passing a fixed-slot input projector. -/
theorem accepted_proportion {L d : ℕ} (q : Occupation L d) (a : Fin d)
    (S : Finset (Fin L)) :
    ((accepted q a S).card : ℝ) / multiplicity q =
      ((q.val a).choose S.card : ℝ) / L.choose S.card := by
  have hmul : ((accepted q a S).card : ℝ) * (L.choose S.card : ℝ) =
      (multiplicity q : ℝ) * ((q.val a).choose S.card : ℝ) := by
    exact_mod_cast accepted_card_mul_choose q a S
  have hm : (multiplicity q : ℝ) ≠ 0 := by exact_mod_cast (multiplicity_pos q).ne'
  have hc : (L.choose S.card : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (by simpa using Finset.card_le_univ S)).ne'
  apply (div_eq_div_iff hm hc).mpr
  simpa [mul_comm] using hmul

end Cloning.GeneralSymmetricOccupation
