import Cloning.WeylGaussianProjectionSandwich
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Positive

/-! The actual closed vacuum space of an arbitrary regular Weyl representation. -/
noncomputable section
open scoped BigOperators Topology InnerProductSpace ComplexOrder
namespace Cloning.WeylGNS
open Cloning.MultimodeCoherent
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
variable {d : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (W : RegularWeyl d H)

theorem RegularWeyl.gaussianProjection_isIdempotent : IsIdempotentElem W.gaussianProjection :=
  W.gaussianProjection_idempotent

theorem RegularWeyl.gaussianProjection_isStarProjection : IsStarProjection W.gaussianProjection :=
  ⟨W.gaussianProjection_isIdempotent, W.gaussianProjection_selfAdjoint⟩

theorem RegularWeyl.gaussianProjection_nonneg : 0≤W.gaussianProjection :=
  W.gaussianProjection.nonneg_iff_isPositive.mpr
    (ContinuousLinearMap.IsPositive.of_isStarProjection W.gaussianProjection_isStarProjection)

theorem RegularWeyl.gaussianProjection_norm_le : ‖W.gaussianProjection‖≤1 :=
  IsStarProjection.norm_le _ W.gaussianProjection_isStarProjection

def RegularWeyl.vacuumSpace : Submodule ℂ H := W.gaussianProjection.range

instance RegularWeyl.vacuumSpace_complete : CompleteSpace W.vacuumSpace :=
  (ContinuousLinearMap.IsIdempotentElem.isClosed_range W.gaussianProjection_isIdempotent).completeSpace_coe

@[simp] theorem RegularWeyl.gaussianProjection_vacuum (v : W.vacuumSpace) :
    W.gaussianProjection v=v :=
  (LinearMap.IsIdempotentElem.mem_range_iff
    (ContinuousLinearMap.IsIdempotentElem.toLinearMap W.gaussianProjection_isIdempotent)).mp v.2

theorem RegularWeyl.vacuum_coefficient (z : Fin d → ℂ) (v w : W.vacuumSpace) :
    ⟪(v : H),W.operator z w⟫_ℂ=
      (gaussianWeight (fun _ : Fin d ↦ (1/2:ℝ)) z : ℂ)*⟪(v : H),(w : H)⟫_ℂ := by
  calc
    _ = ⟪W.gaussianProjection v,W.operator z (W.gaussianProjection w)⟫_ℂ := by
      rw [W.gaussianProjection_vacuum, W.gaussianProjection_vacuum]
    _ = ⟪(v : H),W.gaussianProjection (W.operator z (W.gaussianProjection w))⟫_ℂ :=
      W.gaussianProjection_symmetric _ _
    _ = _ := by
      rw [W.gaussianProjection_sandwich_apply, inner_smul_right, W.gaussianProjection_vacuum]

theorem RegularWeyl.translated_vacuum_inner (a b : Fin d → ℂ) (v w : W.vacuumSpace) :
    ⟪W.operator a v,W.operator b w⟫_ℂ=
      displacementPhase (-a) b*(gaussianWeight (fun _ : Fin d ↦ (1/2:ℝ)) (b-a) : ℂ)*
        ⟪(v : H),(w : H)⟫_ℂ := by
  rw [W.inner_operator]
  have he : W.operator (-a) (W.operator b w)=displacementPhase (-a) b • W.operator (b-a) w := by
    simpa only [neg_add_eq_sub] using W.mul_apply (-a) b (w : H)
  rw [he, inner_smul_right, W.vacuum_coefficient]
  ring

end Cloning.WeylGNS
