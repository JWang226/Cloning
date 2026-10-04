import Cloning.TensorCyclicSectorDiagonal
import Cloning.TensorCyclicSectorTransvection

/-! Literal tensor-power covariance of the physical highest-weight cyclic sectors. -/
noncomputable section
open scoped BigOperators InnerProductSpace Matrix
namespace Cloning.TensorLie
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {n d : ℕ}

local instance : FiniteDimensional ℂ (TensorRegister n (Fin d)) :=
  (Cloning.PCT.registerBasis (Fin n → Fin d)).toOrthonormalBasis.toBasis.finiteDimensional_of_finite

/-- Commuting with the actual collective generators implies commuting with
all literal tensor powers, including singular matrices. -/
theorem tensorOperator_commutes_of_generators
    (T : TensorRegister n (Fin d) →L[ℂ] TensorRegister n (Fin d))
    (hT : ∀ a b, T * collectiveGenerator n a b = collectiveGenerator n a b * T)
    (X : Matrix (Fin d) (Fin d) ℂ) :
    T * tensorOperator n X = tensorOperator n X * T := by
  apply Matrix.diagonal_transvection_induction
    (fun X => T * tensorOperator n X = tensorOperator n X * T) X
  · intro D _
    exact tensorOperator_diagonal_commutes T (fun a => hT a a) D
  · intro t
    exact tensorOperator_transvection_commutes T t.i t.j t.hij (hT t.i t.j) t.c
  · intro A B hA hB
    rw [tensorOperator_mul, ← mul_assoc, hA, mul_assoc, hB, ← mul_assoc]

/-- Every subspace invariant under the actual collective matrix units is
invariant under every literal tensor power. -/
theorem generatorInvariant_tensorOperator_invariant
    (W : Submodule ℂ (TensorRegister n (Fin d)))
    (hW : ∀ a b x, x ∈ W → collectiveGenerator n a b x ∈ W)
    (X : Matrix (Fin d) (Fin d) ℂ) {x : TensorRegister n (Fin d)} (hx : x ∈ W) :
    tensorOperator n X x ∈ W := by
  have hcomm := tensorOperator_commutes_of_generators W.starProjection
    (fun a b => ContinuousLinearMap.ext (invariant_starProjection_commutes W hW a b)) X
  apply Submodule.starProjection_eq_self_iff.mp
  have hh := congrArg (fun T : TensorRegister n (Fin d) →L[ℂ] TensorRegister n (Fin d) => T x) hcomm
  simpa only [ContinuousLinearMap.mul_apply, Submodule.starProjection_eq_self_iff.mpr hx] using hh

variable (Ω : TensorRegister n (Fin d)) (mu : Fin d → ℂ)
    (hweight : ∀ a, collectiveGenerator n a a Ω = mu a • Ω)
    (hraise : ∀ a b, a < b → collectiveGenerator n a b Ω = 0)

include mu hweight hraise in
/-- Actual highest-weight cyclic sectors are invariant under `X` on every tensor
factor, without a group-invariance assumption. -/
theorem cyclicSector_tensorOperator_invariant
    (X : Matrix (Fin d) (Fin d) ℂ) {x : TensorRegister n (Fin d)} (hx : x ∈ cyclicSector Ω) :
    tensorOperator n X x ∈ cyclicSector Ω :=
  generatorInvariant_tensorOperator_invariant (cyclicSector Ω)
    (fun a b x hx => cyclicSector_generator_invariant Ω mu hweight hraise a b hx) X hx

/-- The literal restricted tensor-power action. -/
def cyclicTensorOperator (X : Matrix (Fin d) (Fin d) ℂ) :
    cyclicSector Ω →L[ℂ] cyclicSector Ω :=
  ((tensorOperator n X).comp (cyclicSector Ω).subtypeL).codRestrict
    (cyclicSector Ω) (fun x => cyclicSector_tensorOperator_invariant Ω mu hweight hraise X x.property)

@[simp] theorem cyclicTensorOperator_coe_apply (X : Matrix (Fin d) (Fin d) ℂ)
    (x : cyclicSector Ω) :
    (cyclicTensorOperator Ω mu hweight hraise X x : TensorRegister n (Fin d)) =
      tensorOperator n X x := rfl

@[simp] theorem cyclicTensorOperator_one :
    cyclicTensorOperator Ω mu hweight hraise (1 : Matrix (Fin d) (Fin d) ℂ) = 1 := by
  apply ContinuousLinearMap.ext
  intro x
  apply Subtype.ext
  simp only [cyclicTensorOperator_coe_apply, tensorOperator_one, ContinuousLinearMap.one_apply]

theorem cyclicTensorOperator_mul (X Y : Matrix (Fin d) (Fin d) ℂ) :
    cyclicTensorOperator Ω mu hweight hraise (X * Y) =
      cyclicTensorOperator Ω mu hweight hraise X * cyclicTensorOperator Ω mu hweight hraise Y := by
  apply ContinuousLinearMap.ext
  intro x
  apply Subtype.ext
  simp only [cyclicTensorOperator_coe_apply, tensorOperator_mul, ContinuousLinearMap.mul_apply]

/-- Physical unitaries restrict to honest linear isometric equivalences of the
entire cyclic sector. Both maps are literal tensor powers. -/
def cyclicUnitary (U : Matrix (Fin d) (Fin d) ℂ) (hU : Uᴴ * U = 1) :
    cyclicSector Ω ≃ₗᵢ[ℂ] cyclicSector Ω where
  toLinearEquiv := {
    toLinearMap := (cyclicTensorOperator Ω mu hweight hraise U).toLinearMap
    invFun := cyclicTensorOperator Ω mu hweight hraise Uᴴ
    left_inv := by
      intro x
      have hh := congrArg (fun T : cyclicSector Ω →L[ℂ] cyclicSector Ω => T x)
        (cyclicTensorOperator_mul Ω mu hweight hraise Uᴴ U)
      simpa only [hU, cyclicTensorOperator_one, ContinuousLinearMap.one_apply,
        ContinuousLinearMap.mul_apply] using hh.symm
    right_inv := by
      intro x
      have hU' : U * Uᴴ = 1 := mul_eq_one_comm.mp hU
      have hh := congrArg (fun T : cyclicSector Ω →L[ℂ] cyclicSector Ω => T x)
        (cyclicTensorOperator_mul Ω mu hweight hraise U Uᴴ)
      simpa only [hU', cyclicTensorOperator_one, ContinuousLinearMap.one_apply,
        ContinuousLinearMap.mul_apply] using hh.symm }
  norm_map' := by
    intro x
    change ‖tensorOperator n U (x : TensorRegister n (Fin d))‖ = ‖(x : TensorRegister n (Fin d))‖
    exact tensorOperator_norm U hU (x : TensorRegister n (Fin d))

@[simp] theorem cyclicUnitary_coe_apply (U : Matrix (Fin d) (Fin d) ℂ)
    (hU : Uᴴ * U = 1) (x : cyclicSector Ω) :
    (cyclicUnitary Ω mu hweight hraise U hU x : TensorRegister n (Fin d)) =
      tensorOperator n U x := rfl

end Cloning.TensorLie
