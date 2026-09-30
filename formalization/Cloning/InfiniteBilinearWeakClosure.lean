import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.Complex.Basic

/-!
# Bounded linear maps from pointwise weak-dual closure

Pointwise weak-dual limits of bilinear maps retain the linear equations in
the first argument. Each equation is checked after scalar evaluation, where
it defines a closed set. A uniform norm bound then constructs an actual
continuous linear map into the strong dual.
-/

namespace Cloning.InfiniteBilinearWeakClosure

noncomputable section
open scoped Topology

variable {E F α : Type*}
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

theorem closure_add (U : α → E →L[ℂ] (F →L[ℂ] ℂ)) (f : E → WeakDual ℂ F)
    (hf : f ∈ closure (Set.range (fun a x ↦ StrongDual.toWeakDual (U a x)))) (x y : E) :
    f (x + y) = f x + f y := by
  apply WeakDual.toStrongDual.injective
  apply ContinuousLinearMap.ext
  intro z
  change f (x + y) z = f x z + f y z
  have hc : IsClosed {g : E → WeakDual ℂ F | g (x + y) z = g x z + g y z} :=
    isClosed_eq ((WeakDual.eval_continuous z).comp (continuous_apply (x + y)))
      (((WeakDual.eval_continuous z).comp (continuous_apply x)).add
        ((WeakDual.eval_continuous z).comp (continuous_apply y)))
  apply closure_minimal _ hc hf
  rintro _ ⟨a, rfl⟩
  change U a (x + y) z = U a x z + U a y z
  rw [map_add]
  rfl

theorem closure_smul (U : α → E →L[ℂ] (F →L[ℂ] ℂ)) (f : E → WeakDual ℂ F)
    (hf : f ∈ closure (Set.range (fun a x ↦ StrongDual.toWeakDual (U a x)))) (c : ℂ) (x : E) :
    f (c • x) = c • f x := by
  apply WeakDual.toStrongDual.injective
  apply ContinuousLinearMap.ext
  intro z
  change f (c • x) z = c • (f x z)
  have hc : IsClosed {g : E → WeakDual ℂ F | g (c • x) z = c • (g x z)} :=
    isClosed_eq ((WeakDual.eval_continuous z).comp (continuous_apply (c • x)))
      (((WeakDual.eval_continuous z).comp (continuous_apply x)).const_smul c)
  apply closure_minimal _ hc hf
  rintro _ ⟨a, rfl⟩
  change U a (c • x) z = c • (U a x z)
  rw [map_smul]
  rfl

/-- The algebraic linear map supplied by weak closure, with values interpreted
in the strong dual. Continuity in the first argument follows from a bound. -/
def closureLinearMap (U : α → E →L[ℂ] (F →L[ℂ] ℂ)) (f : E → WeakDual ℂ F)
    (hf : f ∈ closure (Set.range (fun a x ↦ StrongDual.toWeakDual (U a x)))) :
    E →ₗ[ℂ] (F →L[ℂ] ℂ) where
  toFun := fun x ↦ WeakDual.toStrongDual (f x)
  map_add' := fun x y ↦ by rw [closure_add U f hf x y, map_add]
  map_smul' := fun c x ↦ by rw [closure_smul U f hf c x, map_smul]; rfl

/-- Actual bounded bilinear map extracted from a weak-closure point and its
uniform first-argument norm bound. -/
def boundedClosureMap (U : α → E →L[ℂ] (F →L[ℂ] ℂ)) (f : E → WeakDual ℂ F)
    (hf : f ∈ closure (Set.range (fun a x ↦ StrongDual.toWeakDual (U a x))))
    (C : ℝ) (hbound : ∀ x, ‖WeakDual.toStrongDual (f x)‖ ≤ C * ‖x‖) :
    E →L[ℂ] (F →L[ℂ] ℂ) :=
  (closureLinearMap U f hf).mkContinuous C hbound

theorem boundedClosureMap_apply (U : α → E →L[ℂ] (F →L[ℂ] ℂ)) (f : E → WeakDual ℂ F)
    (hf : f ∈ closure (Set.range (fun a x ↦ StrongDual.toWeakDual (U a x))))
    (C : ℝ) (hbound : ∀ x, ‖WeakDual.toStrongDual (f x)‖ ≤ C * ‖x‖) (x : E) :
    boundedClosureMap U f hf C hbound x = WeakDual.toStrongDual (f x) := rfl

/-- Version matching simultaneous compactness extraction, which returns the
family as strong-dual values together with weak-closure membership. -/
def boundedStrongClosureMap (U : α → E →L[ℂ] (F →L[ℂ] ℂ)) (f : E → F →L[ℂ] ℂ)
    (hf : (fun x ↦ StrongDual.toWeakDual (f x)) ∈
      closure (Set.range (fun a x ↦ StrongDual.toWeakDual (U a x))))
    (C : ℝ) (hbound : ∀ x, ‖f x‖ ≤ C * ‖x‖) : E →L[ℂ] (F →L[ℂ] ℂ) :=
  boundedClosureMap U (fun x ↦ StrongDual.toWeakDual (f x)) hf C hbound

theorem boundedStrongClosureMap_apply (U : α → E →L[ℂ] (F →L[ℂ] ℂ))
    (f : E → F →L[ℂ] ℂ)
    (hf : (fun x ↦ StrongDual.toWeakDual (f x)) ∈
      closure (Set.range (fun a x ↦ StrongDual.toWeakDual (U a x))))
    (C : ℝ) (hbound : ∀ x, ‖f x‖ ≤ C * ‖x‖) (x : E) :
    boundedStrongClosureMap U f hf C hbound x = f x := rfl

end
end Cloning.InfiniteBilinearWeakClosure
