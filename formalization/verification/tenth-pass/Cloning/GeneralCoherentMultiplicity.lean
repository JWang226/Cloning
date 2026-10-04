import Cloning.GeneralSymmetricDimension
import Mathlib.Data.Fintype.Perm

/-! Exact multinomial occupation multiplicities by splitting a permutation
into its induced computational word and the bijections of all letter fibers. -/
noncomputable section
open scoped BigOperators
namespace Cloning.GeneralSymmetricOccupation
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

private abbrev WordFiber {L d : ℕ} (w : Word L d) := {v : Word L d // profile v = profile w}
private abbrev FiberBijections {L d : ℕ} (w : Word L d) (v : WordFiber w) :=
  ∀ a : Fin d, {i : Fin L // w i = a} ≃ {i : Fin L // v.val i = a}

private def fiberPerm {L d : ℕ} (w : Word L d)
    (x : Σ v : WordFiber w, FiberBijections w v) : Equiv.Perm (Fin L) :=
  Equiv.ofFiberEquiv x.2

private theorem fiberPerm_injective {L d : ℕ} (w : Word L d) :
    Function.Injective (fiberPerm w) := by
  rintro ⟨⟨v, hv⟩, e⟩ ⟨⟨u, hu⟩, f⟩ h
  have heq : v = u := by
    funext i
    obtain ⟨j, rfl⟩ := (fiberPerm w ⟨⟨v, hv⟩, e⟩).surjective i
    change v (Equiv.ofFiberEquiv e j) = u (Equiv.ofFiberEquiv e j)
    have he := Equiv.ofFiberEquiv_map e j
    change v (Equiv.ofFiberEquiv e j) = w j at he
    rw [he]
    have hp := Equiv.ofFiberEquiv_map f j
    change u (fiberPerm w ⟨⟨u, hu⟩, f⟩ j) = w j at hp
    rw [← h] at hp
    exact hp.symm
  subst u
  congr 1
  funext a
  apply Equiv.ext
  intro i
  apply Subtype.ext
  rcases i with ⟨i, hi⟩
  subst a
  have hp := congrArg (fun σ : Equiv.Perm (Fin L) => σ i) h
  simpa [fiberPerm, Equiv.ofFiberEquiv] using hp

private theorem fiberPerm_surjective {L d : ℕ} (w : Word L d) :
    Function.Surjective (fiberPerm w) := by
  intro σ
  let v : WordFiber w := ⟨w ∘ σ.symm, profile_permute w σ.symm⟩
  let e : FiberBijections w v := fun a =>
    { toFun := fun i => ⟨σ i, by change w (σ.symm (σ i)) = a; simpa using i.property⟩
      invFun := fun i => ⟨σ.symm i, i.property⟩
      left_inv := by intro i; exact Subtype.ext (σ.symm_apply_apply i)
      right_inv := by intro i; exact Subtype.ext (σ.apply_symm_apply i) }
  refine ⟨⟨v, e⟩, ?_⟩
  ext i
  simp [fiberPerm, Equiv.ofFiberEquiv_apply, e]

/-- Permutations split into an occupation word and independent bijections of
its letter fibers. This gives the multinomial count without assuming it. -/
theorem multiplicity_mul_factorials {L d : ℕ} (q : Occupation L d) :
    multiplicity q * ∏ a, (q.val a).factorial = L.factorial := by
  classical
  obtain ⟨w, hw⟩ := label_surjective L d q
  subst q
  let E : (Σ v : WordFiber w, FiberBijections w v) ≃ Equiv.Perm (Fin L) :=
    Equiv.ofBijective (fiberPerm w) ⟨fiberPerm_injective w, fiberPerm_surjective w⟩
  have hc := Fintype.card_congr E
  rw [Fintype.card_sigma, Fintype.card_perm, Fintype.card_fin] at hc
  have hf (v : WordFiber w) : Fintype.card (FiberBijections w v) =
      ∏ a, (profile w a).factorial := by
    rw [Fintype.card_pi]
    apply Finset.prod_congr rfl
    intro a ha
    exact Fintype.card_equiv (Fintype.equivOfCardEq (congrFun v.property a).symm)
  simp_rw [hf] at hc
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul] at hc
  have hwcard : Fintype.card (WordFiber w) = multiplicity (label w) := by
    simp only [WordFiber, multiplicity, Fintype.card_subtype]
    congr 1
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
  rw [hwcard] at hc
  exact hc

end Cloning.GeneralSymmetricOccupation
