import Cloning.TensorFundamentalBranchingLift

/-! Orthogonal projection followed by the canonical exact cyclic intertwiner. -/
noncomputable section
open scoped BigOperators InnerProductSpace
namespace Cloning.TensorLie
open Cloning.PCT
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
variable {n m d : ℕ}
local instance (n d : ℕ) : FiniteDimensional ℂ (TensorRegister n (Fin d)) :=
  (registerBasis (Fin n → Fin d)).toOrthonormalBasis.toBasis.finiteDimensional_of_finite

variable (Ω : TensorRegister n (Fin d)) (Ψ : TensorRegister m (Fin d))
    (mu : Fin d → ℂ)
    (hΩweight : ∀ a, collectiveGenerator n a a Ω = mu a • Ω)
    (hΨweight : ∀ a, collectiveGenerator m a a Ψ = mu a • Ψ)
    (hΩraise : ∀ a b, a < b → collectiveGenerator n a b Ω = 0)
    (hΨraise : ∀ a b, a < b → collectiveGenerator m a b Ψ = 0)
    (hΩnorm : ‖Ω‖ = 1) (hΨnorm : ‖Ψ‖ = 1)

/-- An everywhere-defined intertwiner: project onto the actual source sector,
then apply the proved exact cyclic isometry into the target sector. -/
def projectedCyclicTransport : TensorRegister n (Fin d) →L[ℂ] TensorRegister m (Fin d) :=
  LinearMap.toContinuousLinearMap ((cyclicSector Ψ).subtype.comp
    ((highestCyclicIsometry Ω Ψ mu hΩweight hΨweight hΩraise hΨraise hΩnorm hΨnorm).toLinearMap.comp
      (cyclicSector Ω).orthogonalProjection.toLinearMap))

theorem projectedCyclicTransport_mem (x : TensorRegister n (Fin d)) :
    projectedCyclicTransport Ω Ψ mu hΩweight hΨweight hΩraise hΨraise hΩnorm hΨnorm x ∈
      cyclicSector Ψ :=
  (highestCyclicIsometry Ω Ψ mu hΩweight hΨweight hΩraise hΨraise hΩnorm hΨnorm
    ((cyclicSector Ω).orthogonalProjection x)).property

/-- Projection commutes with all physical generators because the sector is
invariant under their actual Hilbert adjoints. -/
theorem projectedCyclicTransport_intertwines (a b : Fin d) (x : TensorRegister n (Fin d)) :
    projectedCyclicTransport Ω Ψ mu hΩweight hΨweight hΩraise hΨraise hΩnorm hΨnorm
        (collectiveGenerator n a b x) =
      collectiveGenerator m a b
        (projectedCyclicTransport Ω Ψ mu hΩweight hΨweight hΩraise hΨraise hΩnorm hΨnorm x) := by
  have hp : (cyclicSector Ω).orthogonalProjection (collectiveGenerator n a b x) =
      cyclicGenerator Ω mu hΩweight hΩraise a b ((cyclicSector Ω).orthogonalProjection x) := by
    apply Subtype.ext
    exact invariant_starProjection_commutes (cyclicSector Ω)
      (fun a b x hx => cyclicSector_generator_invariant Ω mu hΩweight hΩraise a b hx) a b x
  change (highestCyclicIsometry Ω Ψ mu hΩweight hΨweight hΩraise hΨraise hΩnorm hΨnorm
    ((cyclicSector Ω).orthogonalProjection (collectiveGenerator n a b x)) : TensorRegister m (Fin d)) = _
  rw [hp, highestCyclicIsometry_intertwines]
  rfl

/-- The distinguished highest tensor survives projection and is transported exactly. -/
theorem projectedCyclicTransport_highest :
    projectedCyclicTransport Ω Ψ mu hΩweight hΨweight hΩraise hΨraise hΩnorm hΨnorm Ω = Ψ := by
  have hp : (cyclicSector Ω).orthogonalProjection Ω = ⟨Ω, highest_mem_cyclicSector Ω⟩ := by
    apply Subtype.ext
    exact Submodule.starProjection_eq_self_iff.mpr (highest_mem_cyclicSector Ω)
  change (highestCyclicIsometry Ω Ψ mu hΩweight hΨweight hΩraise hΨraise hΩnorm hΨnorm
    ((cyclicSector Ω).orthogonalProjection Ω) : TensorRegister m (Fin d)) = _
  rw [hp]
  exact highestCyclicIsometry_loweringWord Ω Ψ mu hΩweight hΨweight hΩraise hΨraise hΩnorm hΨnorm []

end Cloning.TensorLie
