import Cloning.PCTPurificationFrame
import Cloning.PCTPurificationInvariance

/-! The actual tensor power of every orthonormal one-particle frame commutes
with the physical symmetric projection. Consequently the framed Werner output
has the original symmetric-sandwich expression with its rotated pure input. -/
noncomputable section
open scoped BigOperators InnerProductSpace ComplexOrder Topology
open Cloning.InfiniteTraceClass
namespace Cloning.PCT
open GeneralSymmetricOccupation GeneralCoherent
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

def wordPermutation (L d : ℕ) (σ : Equiv.Perm (Fin L)) : Word L d ≃ Word L d where
  toFun w := w ∘ σ
  invFun w := w ∘ σ.symm
  left_inv w := by funext i; simp
  right_inv w := by funext i; simp

theorem tensorFrame_preserves_symmetric {d : ℕ}
    {u : Fin d → Register (Fin d)} (hu : Orthonormal ℂ u) (L : ℕ)
    {x : TensorSpace L d} (hx : x ∈ symmetricSubspace L d) :
    tensorFrame hu L x ∈ symmetricSubspace L d := by
  intro v σ
  simp only [tensorFrame_apply]
  calc
    _ = ∑ w : Word L d, x (w ∘ σ) * ∏ i, u (w (σ i)) (v (σ i)) := by
      exact ((wordPermutation L d σ).sum_comp
        (fun w => x w * ∏ i, u (w i) ((v ∘ σ) i))).symm
    _ = ∑ w : Word L d, x w * ∏ i, u (w i) (v i) := by
      apply Finset.sum_congr rfl
      intro w hw
      rw [hx w σ, Equiv.prod_comp σ (fun i => u (w i) (v i))]

theorem symmetricSubspace_map_tensorFrame {d : ℕ}
    {u : Fin d → Register (Fin d)} (hu : Orthonormal ℂ u) (L : ℕ) :
    (symmetricSubspace L d).map (tensorFrame hu L).toLinearMap = symmetricSubspace L d := by
  letI : FiniteDimensional ℂ (TensorSpace L d) :=
    (registerBasis (Word L d)).toOrthonormalBasis.toBasis.finiteDimensional_of_finite
  have hp : ∀ x ∈ symmetricSubspace L d, (tensorFrame hu L).toLinearMap x ∈
      symmetricSubspace L d := fun x hx => tensorFrame_preserves_symmetric hu L hx
  let f := (tensorFrame hu L).toLinearMap.restrict hp
  have hf : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    exact (tensorFrame hu L).injective (congrArg Subtype.val h)
  have hs := LinearMap.surjective_of_injective hf
  apply le_antisymm
  · rintro y ⟨x, hx, rfl⟩
    exact hp x hx
  · intro y hy
    obtain ⟨x, hx⟩ := hs ⟨y, hy⟩
    exact ⟨x.val, x.property, congrArg Subtype.val hx⟩

/-- Physical symmetric projection commutes with a tensor-power unitary.
This follows from the actual permutation-invariant range, not from a
postulated representation covariance. -/
theorem tensorFrame_projector {d : ℕ}
    {u : Fin d → Register (Fin d)} (hu : Orthonormal ℂ u) (L : ℕ) (x : TensorSpace L d) :
    tensorFrame hu L (projector L d x) = projector L d (tensorFrame hu L x) := by
  have he := symmetricSubspace_map_tensorFrame hu L
  letI : ((symmetricSubspace L d).map (tensorFrame hu L).toLinearMap).HasOrthogonalProjection := by
    rw [he]
    infer_instance
  have h := (tensorFrame hu L).map_starProjection (symmetricSubspace L d) x
  simpa only [he, ← projector_eq_starProjection] using h

theorem tensorFrame_projector_commutes {d : ℕ}
    {u : Fin d → Register (Fin d)} (hu : Orthonormal ℂ u) (L : ℕ) :
    (tensorFrame hu L).toContinuousLinearMap * projector L d =
      projector L d * (tensorFrame hu L).toContinuousLinearMap := by
  apply ContinuousLinearMap.ext
  intro x
  exact tensorFrame_projector hu L x

theorem tensorFrame_adjoint_projector_commutes {d : ℕ}
    {u : Fin d → Register (Fin d)} (hu : Orthonormal ℂ u) (L : ℕ) :
    (tensorFrame hu L).toContinuousLinearMap.adjoint * projector L d =
      projector L d * (tensorFrame hu L).toContinuousLinearMap.adjoint := by
  have h := congrArg star (tensorFrame_projector_commutes hu L)
  simpa only [star_mul, (projector_selfAdjoint L d).star_eq,
    ContinuousLinearMap.star_eq_adjoint] using h.symm

theorem tensorFrame_single {C : Type*} [Fintype C] [DecidableEq C] {d : ℕ}
    {u : Fin d → Register C} (hu : Orthonormal ℂ u) (L : ℕ) (w : Word L d) :
    tensorFrame hu L (lp.single 2 w 1) = tensorVector (fun i => u (w i)) := by
  rw [tensorFrame, OrthogonalFamily.linearIsometry_apply_single]
  exact one_smul ℂ _

theorem tensorFrame_adjoint_single_apply {C : Type*} [Fintype C] [DecidableEq C] {d : ℕ}
    {u : Fin d → Register C} (hu : Orthonormal ℂ u) (L : ℕ)
    (c : Fin L → C) (w : Word L d) :
    (tensorFrame hu L).toContinuousLinearMap.adjoint (lp.single 2 c 1) w =
      star (∏ i, u (w i) (c i)) := by
  rw [← register_inner_single, ContinuousLinearMap.adjoint_inner_right]
  change ⟪tensorFrame hu L (lp.single 2 w 1), lp.single 2 c 1⟫_ℂ = _
  rw [tensorFrame_single, lp.inner_single_right]
  simp [RCLike.inner_apply]

theorem fullFrame_resolution {C : Type*} [Fintype C] [DecidableEq C] {d : ℕ}
    (u : OrthonormalBasis (Fin d) ℂ (Register C)) (a c : C) :
    (∑ j, u j a * star (u j c)) = if a = c then 1 else 0 := by
  have h := congrArg (fun v : Register C => v a) (u.sum_repr' (lp.single 2 c 1))
  simpa only [lp.coeFn_sum, Finset.sum_apply, lp.coeFn_smul, Pi.smul_apply,
    smul_eq_mul, lp.inner_single_right, RCLike.inner_apply, one_mul,
    lp.single_apply, Pi.single_apply, mul_comm, starRingEnd_apply] using h

/-- The rotated input is literally the reference pure state on the selected
slots and the full identity on all remaining slots, including coherences. -/
theorem tensorFrame_fixedSlot_coefficient {C : Type*} [Fintype C] [DecidableEq C]
    {L d : ℕ} (u : OrthonormalBasis (Fin d) ℂ (Register C))
    (j₀ : Fin d) (S : Finset (Fin L)) (a c : Fin L → C) :
    operatorConjugation (tensorFrame u.orthonormal L).toContinuousLinearMap
      (fixedSlotProjector j₀ S) (lp.single 2 c 1) a =
      ∏ i, if i ∈ S then u j₀ (a i) * star (u j₀ (c i))
        else if a i = c i then 1 else 0 := by
  classical
  change tensorFrame u.orthonormal L
    (fixedSlotProjector j₀ S ((tensorFrame u.orthonormal L).toContinuousLinearMap.adjoint
      (lp.single 2 c 1))) a = _
  rw [tensorFrame_apply]
  simp only [fixedSlotProjector_apply, tensorFrame_adjoint_single_apply]
  have he (w : Word L d) :
      (if S ⊆ letterSlots w j₀ then star (∏ i, u (w i) (c i)) else 0) *
        ∏ i, u (w i) (a i) =
      ∏ i, if i ∈ S then
        (if w i = j₀ then u (w i) (a i) * star (u (w i) (c i)) else 0)
        else u (w i) (a i) * star (u (w i) (c i)) := by
    have hpred : S ⊆ letterSlots w j₀ ↔ ∀ i, i ∈ S → w i = j₀ := by
      simp only [Finset.subset_iff, mem_letterSlots]
    have hi (i : Fin L) :
        (if i ∈ S then
          (if w i = j₀ then u (w i) (a i) * star (u (w i) (c i)) else 0)
          else u (w i) (a i) * star (u (w i) (c i))) =
        if (i ∈ S → w i = j₀) then u (w i) (a i) * star (u (w i) (c i)) else 0 := by
      by_cases hs : i ∈ S <;> simp [hs]
    simp only [hi, Fintype.prod_ite_zero, ← hpred]
    split_ifs <;> simp [Finset.prod_mul_distrib, mul_comm]
  calc
    _ = ∑ w : Word L d, ∏ i, if i ∈ S then
        (if w i = j₀ then u (w i) (a i) * star (u (w i) (c i)) else 0)
        else u (w i) (a i) * star (u (w i) (c i)) := by
      apply Finset.sum_congr rfl
      intro w hw
      simpa only [map_prod, starRingEnd_apply] using he w
    _ = ∏ i, ∑ j : Fin d, if i ∈ S then
        (if j = j₀ then u j (a i) * star (u j (c i)) else 0)
        else u j (a i) * star (u j (c i)) :=
      (Fintype.prod_sum (fun (i : Fin L) (j : Fin d) => if i ∈ S then
        (if j = j₀ then u j (a i) * star (u j (c i)) else 0)
        else u j (a i) * star (u j (c i)))).symm
    _ = _ := by
      apply Finset.prod_congr rfl
      intro i hi
      by_cases hs : i ∈ S
      · simp [hs]
      · simp only [hs, if_false, fullFrame_resolution]

/-- Conjugating the physical Werner sandwich by the actual tensor-power
unitary leaves the symmetric projectors fixed and rotates only its input. -/
theorem tensorFrame_werner_sandwich {L s : ℕ}
    {u : Fin (s + 1) → Register (Fin (s + 1))} (hu : Orthonormal ℂ u)
    (a : Fin (s + 1)) (S : Finset (Fin L)) :
    operatorConjugation (tensorFrame hu L).toContinuousLinearMap (wernerOutputOperator a S) =
      (((Nat.choose (S.card + s) s : ℝ) / Nat.choose (L + s) s : ℝ) : ℂ) •
        (projector L (s + 1) *
          operatorConjugation (tensorFrame hu L).toContinuousLinearMap (fixedSlotProjector a S) *
          projector L (s + 1)) := by
  rw [wernerOutputOperator, map_smul, occupation_card, occupation_card]
  congr 1
  change (tensorFrame hu L).toContinuousLinearMap *
      (projector L (s + 1) * fixedSlotProjector a S * projector L (s + 1)) *
      (tensorFrame hu L).toContinuousLinearMap.adjoint = _
  have h := tensorFrame_projector_commutes hu L
  have ha := tensorFrame_adjoint_projector_commutes hu L
  simp only [← mul_assoc]
  rw [h]
  simp only [mul_assoc]
  rw [← ha]
  rfl

end Cloning.PCT
