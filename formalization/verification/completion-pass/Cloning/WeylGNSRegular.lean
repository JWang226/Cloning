import Cloning.WeylMultimodeContinuity

/-! Strongly continuous Weyl representations, with the exact phase convention
of the physical multimode displacement operators. -/

noncomputable section
open scoped InnerProductSpace Topology

namespace Cloning.WeylGNS

open MultimodeCoherent

variable (d : ℕ) (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- A genuine unitary action satisfying the Weyl relations and strong
continuity. No irreducibility or choice of a vacuum is included. -/
structure RegularWeyl where
  toIsometry : (Fin d → ℂ) → H ≃ₗᵢ[ℂ] H
  zero_apply : ∀ v, toIsometry 0 v = v
  mul_apply : ∀ a b v, toIsometry a (toIsometry b v) =
    displacementPhase a b • toIsometry (a + b) v
  continuous_apply : ∀ v, Continuous (fun a => toIsometry a v)

variable {d H}

def RegularWeyl.operator (W : RegularWeyl d H) (a : Fin d → ℂ) : H →L[ℂ] H :=
  (W.toIsometry a).toContinuousLinearEquiv.toContinuousLinearMap

@[simp] theorem RegularWeyl.operator_apply (W : RegularWeyl d H)
    (a : Fin d → ℂ) (v : H) : W.operator a v = W.toIsometry a v := rfl

@[simp] theorem RegularWeyl.operator_norm (W : RegularWeyl d H)
    (a : Fin d → ℂ) (v : H) : ‖W.operator a v‖ = ‖v‖ :=
  (W.toIsometry a).norm_map v

theorem RegularWeyl.operator_mul (W : RegularWeyl d H) (a b : Fin d → ℂ) :
    (W.operator a).comp (W.operator b) = displacementPhase a b • W.operator (a + b) := by
  ext v
  exact W.mul_apply a b v

@[simp] theorem RegularWeyl.operator_zero (W : RegularWeyl d H) :
    W.operator 0 = ContinuousLinearMap.id ℂ H := by
  ext v
  exact W.zero_apply v

/-- The concrete multimode Fock displacement gives a regular representation. -/
def fockRegularWeyl (d : ℕ) : RegularWeyl d (Fock d) where
  toIsometry := weylUnitary
  zero_apply := by intro v; simp
  mul_apply := by
    intro a b v
    exact congrArg (fun T : Fock d →L[ℂ] Fock d => T v) (displacement_comp a b)
  continuous_apply := continuous_displacement

end Cloning.WeylGNS
