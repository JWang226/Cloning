import Cloning.WeylIrreducibleMultimode

/-! Classification of bounded eigenoperators for the actual Weyl conjugation
action. This is a consequence of the proved scalar commutant, not an assumed
representation theorem. -/

noncomputable section
open scoped InnerProductSpace Topology BigOperators

namespace Cloning.MultimodeCoherent
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

variable {d : ℕ}

/-- Character appearing when two actual displacement operators are commuted. -/
def weylCharacter (a b : Fin d → ℂ) : ℂ :=
  displacementPhase a b / displacementPhase b a

lemma displacementPhase_ne_zero (a b : Fin d → ℂ) : displacementPhase a b ≠ 0 := by
  intro h
  have hn := displacementPhase_norm a b
  rw [h, norm_zero] at hn
  norm_num at hn

/-- The exact Weyl commutation character for bounded operators. -/
theorem displacement_commutation (a b : Fin d → ℂ) :
    (displacement a).comp (displacement b) =
      weylCharacter a b • (displacement b).comp (displacement a) := by
  rw [displacement_comp, displacement_comp, smul_smul, weylCharacter,
    div_mul_cancel₀ _ (displacementPhase_ne_zero b a), add_comm b a]

/-- An operator transforming with the same commutation character as `D(b)`
becomes an operator in the ordinary commutant after multiplying by `D(-b)`. -/
lemma eigenoperator_mul_inverse_commutes (T : Fock d →L[ℂ] Fock d) (b : Fin d → ℂ)
    (hT : ∀ a : Fin d → ℂ, (displacement a).comp T =
      weylCharacter a b • T.comp (displacement a)) :
    ∀ a : Fin d → ℂ, (T.comp (displacement (-b))).comp (displacement a) =
      (displacement a).comp (T.comp (displacement (-b))) := by
  intro a
  apply ContinuousLinearMap.ext
  intro v
  have hW := congrArg (fun L : Fock d →L[ℂ] Fock d ↦ L (displacement (-b) v))
    (displacement_commutation a b)
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
    displacement_cancel_neg] at hW
  have hW' := congrArg (displacement (-b)) hW
  simp only [map_smul, displacement_neg_cancel] at hW'
  have h := congrArg (fun L : Fock d →L[ℂ] Fock d ↦ L (displacement (-b) v)) (hT a)
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply] at h
  change T (displacement (-b) (displacement a v)) = displacement a (T (displacement (-b) v))
  rw [hW', map_smul, ← h]

/-- Every bounded eigenoperator of the Weyl conjugation action is a scalar
multiple of the displacement with the matching character. -/
theorem eigenoperator_eq_scalar_displacement (T : Fock d →L[ℂ] Fock d) (b : Fin d → ℂ)
    (hT : ∀ a : Fin d → ℂ, (displacement a).comp T =
      weylCharacter a b • T.comp (displacement a)) :
    T = ⟪coherentVector 0, T (displacement (-b) (coherentVector 0))⟫_ℂ • displacement b := by
  have hscalar := displacement_commutant_scalar (T.comp (displacement (-b)))
    (eigenoperator_mul_inverse_commutes T b hT)
  have h := congrArg (fun L : Fock d →L[ℂ] Fock d ↦ L.comp (displacement b)) hscalar
  apply ContinuousLinearMap.ext
  intro v
  have hv := congrArg (fun L : Fock d →L[ℂ] Fock d ↦ L v) h
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply, displacement_neg_cancel] using hv

/-- Existence form of the bounded Weyl eigenoperator classification. -/
theorem exists_scalar_eigenoperator (T : Fock d →L[ℂ] Fock d) (b : Fin d → ℂ)
    (hT : ∀ a : Fin d → ℂ, (displacement a).comp T =
      weylCharacter a b • T.comp (displacement a)) :
    ∃ c : ℂ, T = c • displacement b :=
  ⟨_, eigenoperator_eq_scalar_displacement T b hT⟩

end Cloning.MultimodeCoherent
