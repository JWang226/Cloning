import Cloning.TensorHighestGramIntertwiner
import Cloning.TensorCyclicSectorCovariance
import Cloning.TensorCyclicSectorWeightTrace

/-! Exact cyclic isometries intertwine the literal physical tensor powers. -/
noncomputable section
open scoped BigOperators InnerProductSpace Matrix
namespace Cloning.TensorLie
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {n d : ℕ}

local instance : FiniteDimensional ℂ (TensorRegister n (Fin d)) :=
  (Cloning.PCT.registerBasis (Fin n → Fin d)).toOrthonormalBasis.toBasis.finiteDimensional_of_finite

/-- Integration of an intertwiner between two actual cyclic sectors in the
same physical tensor register. -/
theorem cyclicIntertwiner_tensorOperator
    (Ω Ψ : TensorRegister n (Fin d)) (mu nu : Fin d → ℂ)
    (hΩweight : ∀ a, collectiveGenerator n a a Ω = mu a • Ω)
    (hΨweight : ∀ a, collectiveGenerator n a a Ψ = nu a • Ψ)
    (hΩraise : ∀ a b, a < b → collectiveGenerator n a b Ω = 0)
    (hΨraise : ∀ a b, a < b → collectiveGenerator n a b Ψ = 0)
    (T : cyclicSector Ω →L[ℂ] cyclicSector Ψ)
    (hT : ∀ a b x, T (cyclicGenerator Ω mu hΩweight hΩraise a b x) =
      cyclicGenerator Ψ nu hΨweight hΨraise a b (T x))
    (X : Matrix (Fin d) (Fin d) ℂ) (x : cyclicSector Ω) :
    T (cyclicTensorOperator Ω mu hΩweight hΩraise X x) =
      cyclicTensorOperator Ψ nu hΨweight hΨraise X (T x) := by
  let S := cyclicSector Ω
  let V := cyclicSector Ψ
  let A : TensorRegister n (Fin d) →L[ℂ] TensorRegister n (Fin d) :=
    V.subtypeL.comp (T.comp S.orthogonalProjection)
  have hproj (y : S) : S.orthogonalProjection y = y := by
    apply Subtype.ext
    exact Submodule.starProjection_eq_self_iff.mpr y.property
  have hA (y : S) : A y = (T y : TensorRegister n (Fin d)) := by
    change (T (S.orthogonalProjection y) : TensorRegister n (Fin d)) = _
    rw [hproj]
  have hprojE (a b : Fin d) (y : TensorRegister n (Fin d)) :
      S.orthogonalProjection (collectiveGenerator n a b y) =
        cyclicGenerator Ω mu hΩweight hΩraise a b (S.orthogonalProjection y) := by
    apply Subtype.ext
    exact invariant_starProjection_commutes S
      (fun a b z hz => cyclicSector_generator_invariant Ω mu hΩweight hΩraise a b hz) a b y
  have hcomm (a b : Fin d) : A * collectiveGenerator n a b = collectiveGenerator n a b * A := by
    apply ContinuousLinearMap.ext
    intro y
    change (T (S.orthogonalProjection (collectiveGenerator n a b y)) : TensorRegister n (Fin d)) = _
    rw [hprojE, hT]
    rfl
  have hh := congrArg (fun Q : TensorRegister n (Fin d) →L[ℂ] TensorRegister n (Fin d) => Q x)
    (tensorOperator_commutes_of_generators A hcomm X)
  apply Subtype.ext
  change (T (cyclicTensorOperator Ω mu hΩweight hΩraise X x) : TensorRegister n (Fin d)) =
    tensorOperator n X (T x)
  simpa only [ContinuousLinearMap.mul_apply, ← cyclicTensorOperator_coe_apply Ω mu hΩweight hΩraise X x,
    hA] using hh

/-- The canonical exact Gram isometry intertwines every literal tensor power. -/
theorem highestCyclicIsometry_tensorOperator_sameLength
    (Ω Ψ : TensorRegister n (Fin d)) (mu : Fin d → ℂ)
    (hΩweight : ∀ a, collectiveGenerator n a a Ω = mu a • Ω)
    (hΨweight : ∀ a, collectiveGenerator n a a Ψ = mu a • Ψ)
    (hΩraise : ∀ a b, a < b → collectiveGenerator n a b Ω = 0)
    (hΨraise : ∀ a b, a < b → collectiveGenerator n a b Ψ = 0)
    (hΩnorm : ‖Ω‖ = 1) (hΨnorm : ‖Ψ‖ = 1)
    (X : Matrix (Fin d) (Fin d) ℂ) (x : cyclicSector Ω) :
    highestCyclicIsometry Ω Ψ mu hΩweight hΨweight hΩraise hΨraise hΩnorm hΨnorm
        (cyclicTensorOperator Ω mu hΩweight hΩraise X x) =
      cyclicTensorOperator Ψ mu hΨweight hΨraise X
        (highestCyclicIsometry Ω Ψ mu hΩweight hΨweight hΩraise hΨraise hΩnorm hΨnorm x) :=
  cyclicIntertwiner_tensorOperator Ω Ψ mu mu hΩweight hΨweight hΩraise hΨraise
    (highestCyclicIsometry Ω Ψ mu hΩweight hΨweight hΩraise hΨraise hΩnorm hΨnorm).toLinearIsometry.toContinuousLinearMap
    (fun a b x => highestCyclicIsometry_intertwines Ω Ψ mu hΩweight hΨweight hΩraise hΨraise
      hΩnorm hΨnorm a b x) X x

/-- Full literal covariance of the canonical cyclic isometry. Equality of the
Cartan weights itself forces equality of the physical tensor lengths. -/
theorem highestCyclicIsometry_tensorOperator {m : ℕ}
    (Ω : TensorRegister n (Fin d)) (Ψ : TensorRegister m (Fin d)) (mu : Fin d → ℂ)
    (hΩweight : ∀ a, collectiveGenerator n a a Ω = mu a • Ω)
    (hΨweight : ∀ a, collectiveGenerator m a a Ψ = mu a • Ψ)
    (hΩraise : ∀ a b, a < b → collectiveGenerator n a b Ω = 0)
    (hΨraise : ∀ a b, a < b → collectiveGenerator m a b Ψ = 0)
    (hΩnorm : ‖Ω‖ = 1) (hΨnorm : ‖Ψ‖ = 1)
    (X : Matrix (Fin d) (Fin d) ℂ) (x : cyclicSector Ω) :
    highestCyclicIsometry Ω Ψ mu hΩweight hΨweight hΩraise hΨraise hΩnorm hΨnorm
        (cyclicTensorOperator Ω mu hΩweight hΩraise X x) =
      cyclicTensorOperator Ψ mu hΨweight hΨraise X
        (highestCyclicIsometry Ω Ψ mu hΩweight hΨweight hΩraise hΨraise hΩnorm hΨnorm x) := by
  have hnm := highest_tensorLength_eq Ω Ψ mu hΩweight hΨweight hΩnorm hΨnorm
  subst m
  exact highestCyclicIsometry_tensorOperator_sameLength Ω Ψ mu hΩweight hΨweight
    hΩraise hΨraise hΩnorm hΨnorm X x

/-- In particular, the exact Gram isometry is equivariant under the literal
physical unitary actions on both sectors. -/
theorem highestCyclicIsometry_unitary {m : ℕ}
    (Ω : TensorRegister n (Fin d)) (Ψ : TensorRegister m (Fin d)) (mu : Fin d → ℂ)
    (hΩweight : ∀ a, collectiveGenerator n a a Ω = mu a • Ω)
    (hΨweight : ∀ a, collectiveGenerator m a a Ψ = mu a • Ψ)
    (hΩraise : ∀ a b, a < b → collectiveGenerator n a b Ω = 0)
    (hΨraise : ∀ a b, a < b → collectiveGenerator m a b Ψ = 0)
    (hΩnorm : ‖Ω‖ = 1) (hΨnorm : ‖Ψ‖ = 1)
    (U : Matrix (Fin d) (Fin d) ℂ) (hU : Uᴴ * U = 1) (x : cyclicSector Ω) :
    highestCyclicIsometry Ω Ψ mu hΩweight hΨweight hΩraise hΨraise hΩnorm hΨnorm
        (cyclicUnitary Ω mu hΩweight hΩraise U hU x) =
      cyclicUnitary Ψ mu hΨweight hΨraise U hU
        (highestCyclicIsometry Ω Ψ mu hΩweight hΨweight hΩraise hΨraise hΩnorm hΨnorm x) :=
  highestCyclicIsometry_tensorOperator Ω Ψ mu hΩweight hΨweight hΩraise hΨraise
    hΩnorm hΨnorm U x

end Cloning.TensorLie
