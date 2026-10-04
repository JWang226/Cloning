import Cloning.TensorCyclicFiltration
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! A weight-dependent formal expansion of the exact matrix-unit action on
lowering words. The expansion realizes in every physical highest tensor of
the given weight, without assuming a representation isomorphism. -/
noncomputable section
open scoped BigOperators InnerProductSpace
namespace Cloning.TensorLie
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {n d : ℕ}

abbrev FormalLowering (d : ℕ) := List (PositiveRoot d) →₀ ℂ

noncomputable def highestAction (mu : Fin d → ℂ) (a b : Fin d) : List (PositiveRoot d) → FormalLowering d
  | [] => if h : b < a then Finsupp.single [⟨(b, a), h⟩] 1
      else if a = b then Finsupp.single [] (mu a) else 0
  | c :: w => Finsupp.mapDomain (List.cons c) (highestAction mu a b w) +
      (if b = c.val.2 then highestAction mu a c.val.1 w else 0) -
      (if c.val.1 = a then highestAction mu c.val.2 b w else 0)

def formalRealization (Ω : TensorRegister n (Fin d)) :
    FormalLowering d →ₗ[ℂ] TensorRegister n (Fin d) :=
  Finsupp.linearCombination ℂ (loweringWord Ω)

@[simp] theorem formalRealization_single (Ω : TensorRegister n (Fin d))
    (w : List (PositiveRoot d)) (c : ℂ) :
    formalRealization Ω (Finsupp.single w c) = c • loweringWord Ω w :=
  Finsupp.linearCombination_single ℂ c w

theorem formalRealization_prepend (Ω : TensorRegister n (Fin d))
    (a : PositiveRoot d) (f : FormalLowering d) :
    formalRealization Ω (Finsupp.mapDomain (List.cons a) f) =
      collectiveGenerator n a.val.2 a.val.1 (formalRealization Ω f) := by
  change Finsupp.linearCombination ℂ (loweringWord Ω) (Finsupp.mapDomain (List.cons a) f) = _
  rw [Finsupp.linearCombination_mapDomain]
  simp [formalRealization, Finsupp.linearCombination_apply, Finsupp.sum, loweringWord]

/-- The same finite formal expansion realizes the action in every actual
highest tensor having the specified Cartan eigenvalues. -/
theorem formalRealization_highestAction
    (Ω : TensorRegister n (Fin d)) (mu : Fin d → ℂ)
    (hweight : ∀ a, collectiveGenerator n a a Ω = mu a • Ω)
    (hraise : ∀ a b, a < b → collectiveGenerator n a b Ω = 0)
    (a b : Fin d) (w : List (PositiveRoot d)) :
    formalRealization Ω (highestAction mu a b w) =
      collectiveGenerator n a b (loweringWord Ω w) := by
  induction w generalizing a b with
  | nil =>
      rcases lt_trichotomy a b with hab | hab | hab
      · have hba : ¬ b < a := not_lt_of_gt hab
        simp [highestAction, hba, ne_of_lt hab, loweringWord, hraise a b hab]
      · subst b
        simp [highestAction, loweringWord, hweight]
      · simp [highestAction, hab, loweringWord]
  | cons c w ih =>
      simp only [highestAction, map_sub, map_add, formalRealization_prepend, ih]
      have he := congrArg (fun T : TensorRegister n (Fin d) →L[ℂ] TensorRegister n (Fin d) =>
        T (loweringWord Ω w)) (collectiveGenerator_commutator (n := n) a b c.val.2 c.val.1)
      simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.mul_apply] at he
      have he' : collectiveGenerator n a b (loweringWord Ω (c :: w)) =
          collectiveGenerator n c.val.2 c.val.1
            (collectiveGenerator n a b (loweringWord Ω w)) +
          ((if b = c.val.2 then collectiveGenerator n a c.val.1 else 0)
            (loweringWord Ω w) -
          (if c.val.1 = a then collectiveGenerator n c.val.2 b else 0)
            (loweringWord Ω w)) := by
        change _ - _ = _ at he
        simpa only [loweringWord] using (sub_eq_iff_eq_add.mp he).trans (add_comm _ _)
      rw [he']
      split_ifs <;> simp only [map_zero, ih, ContinuousLinearMap.zero_apply] <;> abel

end Cloning.TensorLie
