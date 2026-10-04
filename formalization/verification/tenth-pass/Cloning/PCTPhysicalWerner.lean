import Cloning.PCTWernerCovariance

/-! Physical Werner cloning in arbitrary finite one-particle registers. The
symmetric projector is defined by permutation invariance, independently of a
purification frame, and the rotated output is identified with its literal
pure-input symmetric sandwich. -/
noncomputable section
open scoped BigOperators InnerProductSpace ComplexOrder Topology
open Cloning.InfiniteTraceClass
namespace Cloning.PCT
open GeneralSymmetricOccupation GeneralCoherent
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

local instance registerFiniteDimensional (C : Type*) [Fintype C] [DecidableEq C] :
    FiniteDimensional ℂ (Register C) :=
  (registerBasis C).toOrthonormalBasis.toBasis.finiteDimensional_of_finite

variable {C : Type*} [Fintype C] [DecidableEq C]

def physicalSymmetric (L : ℕ) : Submodule ℂ (Register (Fin L → C)) where
  carrier := {v | ∀ (w : Fin L → C) (σ : Equiv.Perm (Fin L)), v (w ∘ σ) = v w}
  zero_mem' := by intro w σ; rfl
  add_mem' := by intro v u hv hu w σ; exact congrArg₂ (· + ·) (hv w σ) (hu w σ)
  smul_mem' := by intro a v hv w σ; exact congrArg (a • ·) (hv w σ)

/-- Canonical physical symmetric projector, defined without any chosen
purification vector or one-particle orthonormal frame. -/
def physicalProjector (L : ℕ) : Register (Fin L → C) →L[ℂ] Register (Fin L → C) :=
  (physicalSymmetric (C := C) L).starProjection

def permuteRegister {L : ℕ} (σ : Equiv.Perm (Fin L)) (x : Register (Fin L → C)) :
    Register (Fin L → C) :=
  ⟨fun w => x (w ∘ σ), memℓp_gen (by
    simp only [ENNReal.toReal_ofNat]; exact (hasSum_fintype _).summable)⟩

@[simp] theorem permuteRegister_apply {L : ℕ} (σ : Equiv.Perm (Fin L))
    (x : Register (Fin L → C)) (w : Fin L → C) : permuteRegister σ x w = x (w ∘ σ) := rfl

theorem tensorFrame_permute {d L : ℕ} {u : Fin d → Register C} (hu : Orthonormal ℂ u)
    (σ : Equiv.Perm (Fin L)) (x : TensorSpace L d) :
    tensorFrame hu L (permuteRegister σ x) = permuteRegister σ (tensorFrame hu L x) := by
  ext v
  simp only [tensorFrame_apply, permuteRegister_apply]
  calc
    _ = ∑ w : Word L d, x w * ∏ i, u (w (σ.symm i)) (v i) := by
      have he := (wordPermutation L d σ.symm).sum_comp
        (fun w => x (w ∘ σ) * ∏ i, u (w i) (v i))
      have hc (w : Word L d) : (w ∘ σ.symm) ∘ σ = w := by funext i; simp
      simpa only [wordPermutation, Equiv.coe_fn_mk, hc, Function.comp_apply] using he.symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro w hw
      congr 1
      have he := Equiv.prod_comp σ (fun i => u (w (σ.symm i)) (v i))
      simpa only [Equiv.symm_apply_apply, Function.comp_apply] using he.symm

theorem tensorFrame_surjective {d L : ℕ} (u : OrthonormalBasis (Fin d) ℂ (Register C)) :
    Function.Surjective (tensorFrame u.orthonormal L) := by
  have hc : Fintype.card C = d := by
    have h₁ := Module.finrank_eq_card_basis (registerBasis C).toOrthonormalBasis.toBasis
    have h₂ := Module.finrank_eq_card_basis u.toBasis
    simpa using h₁.symm.trans h₂
  apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := (tensorFrame u.orthonormal L).toLinearMap) ?_).mp
    (tensorFrame u.orthonormal L).injective
  rw [Module.finrank_eq_card_basis (registerBasis (Word L d)).toOrthonormalBasis.toBasis,
    Module.finrank_eq_card_basis (registerBasis (Fin L → C)).toOrthonormalBasis.toBasis]
  simp only [Word, Fintype.card_fun, Fintype.card_fin, hc]

theorem physicalSymmetric_map_tensorFrame {d : ℕ}
    (u : OrthonormalBasis (Fin d) ℂ (Register C)) (L : ℕ) :
    (symmetricSubspace L d).map (tensorFrame u.orthonormal L).toLinearMap =
      physicalSymmetric (C := C) L := by
  apply le_antisymm
  · rintro y ⟨x, hx, rfl⟩
    intro w σ
    have hp : permuteRegister σ x = x := by ext v; exact hx v σ
    have he := tensorFrame_permute u.orthonormal σ x
    rw [hp] at he
    exact (congrArg (fun v : Register (Fin L → C) => v w) he).symm
  · intro y hy
    obtain ⟨x, rfl⟩ := tensorFrame_surjective (L := L) u y
    refine ⟨x, ?_, rfl⟩
    intro w σ
    have hp : permuteRegister σ (tensorFrame u.orthonormal L x) =
        tensorFrame u.orthonormal L x := by ext v; exact hy v σ
    have he := tensorFrame_permute u.orthonormal σ x
    rw [hp] at he
    exact congrArg (fun v : TensorSpace L d => v w) ((tensorFrame u.orthonormal L).injective he)

theorem tensorFrame_physicalProjector {d : ℕ}
    (u : OrthonormalBasis (Fin d) ℂ (Register C)) (L : ℕ) (x : TensorSpace L d) :
    tensorFrame u.orthonormal L (projector L d x) =
      physicalProjector L (tensorFrame u.orthonormal L x) := by
  have he := physicalSymmetric_map_tensorFrame u L
  have h := (tensorFrame u.orthonormal L).map_starProjection (symmetricSubspace L d) x
  simpa only [he, ← projector_eq_starProjection] using h

theorem tensorFrame_adjoint_physicalProjector {d : ℕ}
    (u : OrthonormalBasis (Fin d) ℂ (Register C)) (L : ℕ) (x : Register (Fin L → C)) :
    (tensorFrame u.orthonormal L).toContinuousLinearMap.adjoint (physicalProjector L x) =
      projector L d ((tensorFrame u.orthonormal L).toContinuousLinearMap.adjoint x) := by
  apply ext_inner_left ℂ
  intro v
  rw [ContinuousLinearMap.adjoint_inner_right]
  have hp : (physicalProjector (C := C) L).adjoint = physicalProjector L := by
    exact (isStarProjection_starProjection (U := physicalSymmetric (C := C) L)).isSelfAdjoint.adjoint_eq
  rw [← ContinuousLinearMap.adjoint_inner_left, hp]
  change ⟪physicalProjector L (tensorFrame u.orthonormal L v), x⟫_ℂ = _
  rw [← tensorFrame_physicalProjector]
  change ⟪(tensorFrame u.orthonormal L).toContinuousLinearMap (projector L d v), x⟫_ℂ = _
  rw [← ContinuousLinearMap.adjoint_inner_right]
  have hq : (projector L d).adjoint = projector L d := (projector_selfAdjoint L d).adjoint_eq
  rw [← hq, ContinuousLinearMap.adjoint_inner_left, hq]

/-- A pure product on the selected slots tensored with full identities on all
remaining slots, specified in the actual computational register. -/
def pureSlotsMatrix {L : ℕ} (ψ : Register C) (S : Finset (Fin L)) :
    Matrix (Fin L → C) (Fin L → C) ℂ := fun a c =>
  ∏ i, if i ∈ S then ψ (a i) * star (ψ (c i)) else if a i = c i then 1 else 0

def pureSlotsOperator {L : ℕ} (ψ : Register C) (S : Finset (Fin L)) :
    Register (Fin L → C) →L[ℂ] Register (Fin L → C) :=
  InfiniteFiniteCorner.ofMatrix (registerBasis (Fin L → C)) (pureSlotsMatrix ψ S)

theorem pureSlotsOperator_coefficient {L : ℕ} (ψ : Register C) (S : Finset (Fin L))
    (a c : Fin L → C) : pureSlotsOperator ψ S (lp.single 2 c 1) a = pureSlotsMatrix ψ S a c := by
  rw [← register_inner_single]
  have h := InfiniteFiniteCorner.matrixOf_ofMatrix (registerBasis (Fin L → C)).orthonormal
    (pureSlotsMatrix ψ S)
  simpa only [InfiniteFiniteCorner.matrixOf, registerBasis_apply, pureSlotsOperator] using
    congrArg (fun M => M a c) h

theorem tensorFrame_fixedSlot_physical {L d : ℕ}
    (u : OrthonormalBasis (Fin d) ℂ (Register C)) (j₀ : Fin d) (S : Finset (Fin L)) :
    operatorConjugation (tensorFrame u.orthonormal L).toContinuousLinearMap (fixedSlotProjector j₀ S) =
      pureSlotsOperator (u j₀) S := by
  apply register_operator_ext
  intro a c
  rw [tensorFrame_fixedSlot_coefficient, pureSlotsOperator_coefficient]
  rfl

/-- The actual framed Werner output is the canonical physical Werner
symmetric sandwich on an arbitrary purification, with the full environment
identity. The projector and input operator on the right are frame-independent. -/
theorem wernerOutput_physical_purification {L s : ℕ}
    (u : OrthonormalBasis (Fin (s + 1)) ℂ (Register C)) (S : Finset (Fin L)) :
    ((QuantumChannel.ofIsometry (tensorFrame u.orthonormal L)).toLinearMap
      (wernerOutput (s := s) S)).1 =
      (((Nat.choose (S.card + s) s : ℝ) / Nat.choose (L + s) s : ℝ) : ℂ) •
        (physicalProjector L * pureSlotsOperator (u 0) S * physicalProjector L) := by
  change operatorConjugation (tensorFrame u.orthonormal L).toContinuousLinearMap
    (wernerOutput (s := s) S).1 = _
  rw [wernerOutput_op, wernerOutputOperator, occupation_card, occupation_card]
  change operatorConjugation (tensorFrame u.orthonormal L).toContinuousLinearMap (_ • _) = _
  rw [map_smul]
  congr 1
  apply ContinuousLinearMap.ext
  intro x
  change tensorFrame u.orthonormal L (projector L (s + 1)
    (fixedSlotProjector 0 S (projector L (s + 1)
      ((tensorFrame u.orthonormal L).toContinuousLinearMap.adjoint x)))) = _
  rw [tensorFrame_physicalProjector, ← tensorFrame_adjoint_physicalProjector]
  have he := congrArg (fun T : Register (Fin L → C) →L[ℂ] Register (Fin L → C) =>
    physicalProjector L (T (physicalProjector L x))) (tensorFrame_fixedSlot_physical u 0 S)
  exact he

end Cloning.PCT
