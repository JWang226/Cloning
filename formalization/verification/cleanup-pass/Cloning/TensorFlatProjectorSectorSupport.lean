import Cloning.TensorFlatProjectorRestriction

/-! Exact support operators and ranks on physical cyclic sectors. -/
noncomputable section
open scoped BigOperators InnerProductSpace
namespace Cloning.TensorLie
open Cloning.PCT
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
variable {n r k : ℕ}
local instance (n d : ℕ) : FiniteDimensional ℂ (TensorRegister n (Fin d)) :=
  (registerBasis (Fin n → Fin d)).toOrthonormalBasis.toBasis.finiteDimensional_of_finite

/-- The adjoint coordinate restriction preserves the smaller cyclic sector. -/
theorem coordinateTensorEmbedding_adjoint_mem (Ω : TensorRegister n (Fin r))
    (x : cyclicSector (coordinateTensorEmbedding n r k Ω)) :
    (coordinateTensorEmbedding n r k).toContinuousLinearMap.adjoint x ∈ cyclicSector Ω := by
  obtain ⟨y,hy,he⟩ := coordinateTensorProjection_mem_image Ω x.property
  change coordinateTensorEmbedding n r k y =
    coordinateTensorEmbedding n r k ((coordinateTensorEmbedding n r k).toContinuousLinearMap.adjoint x) at he
  rw [← (coordinateTensorEmbedding n r k).injective he]
  exact hy

theorem coordinateSectorEmbedding_adjoint_coe (Ω : TensorRegister n (Fin r))
    (x : cyclicSector (coordinateTensorEmbedding n r k Ω)) :
    ((coordinateSectorEmbedding (k := k) Ω).toContinuousLinearMap.adjoint x : TensorRegister n (Fin r)) =
      (coordinateTensorEmbedding n r k).toContinuousLinearMap.adjoint x := by
  let y : cyclicSector Ω := ⟨_,coordinateTensorEmbedding_adjoint_mem Ω x⟩
  have he : (coordinateSectorEmbedding (k := k) Ω).toContinuousLinearMap.adjoint x = y := by
    apply ext_inner_left ℂ
    intro z
    rw [ContinuousLinearMap.adjoint_inner_right]
    change ⟪coordinateTensorEmbedding n r k (z : TensorRegister n (Fin r)),
      (x : TensorRegister n (Fin (r+k)))⟫_ℂ =
        ⟪(z : TensorRegister n (Fin r)),
          (coordinateTensorEmbedding n r k).toContinuousLinearMap.adjoint x⟫_ℂ
    exact (ContinuousLinearMap.adjoint_inner_right
      (coordinateTensorEmbedding n r k).toContinuousLinearMap
      (z : TensorRegister n (Fin r)) (x : TensorRegister n (Fin (r+k)))).symm
  exact congrArg Subtype.val he

/-- The restricted physical rank-r matrix is exactly the range projection
of the actual rank-r cyclic-sector inclusion. -/
theorem coordinateSectorEmbedding_support
    (Ω : TensorRegister n (Fin r)) (mu : Fin r → ℕ)
    (hweight : ∀ a, collectiveGenerator n a a Ω = (mu a : ℂ) • Ω)
    (hraise : ∀ a b, a < b → collectiveGenerator n a b Ω = 0) :
    cyclicTensorOperator (coordinateTensorEmbedding n r k Ω)
      (fun a => (padPartition mu k a : ℂ))
      (coordinateTensorEmbedding_highest Ω mu hweight hraise).1
      (coordinateTensorEmbedding_highest Ω mu hweight hraise).2
      (coordinateSupportMatrix r k) =
    (coordinateSectorEmbedding (k := k) Ω).toContinuousLinearMap.comp
      (coordinateSectorEmbedding (k := k) Ω).toContinuousLinearMap.adjoint := by
  apply ContinuousLinearMap.ext
  intro x
  apply Subtype.ext
  change tensorOperator n (coordinateSupportMatrix r k) (x : TensorRegister n (Fin (r+k))) =
    coordinateTensorEmbedding n r k
      (((coordinateSectorEmbedding (k := k) Ω).toContinuousLinearMap.adjoint x : cyclicSector Ω) :
        TensorRegister n (Fin r))
  rw [coordinateSectorEmbedding_adjoint_coe, ← coordinateTensorProjection_eq_tensorOperator]
  rfl

/-- Its rank, equivalently its trace, is the actual support-sector dimension. -/
theorem trace_coordinateSector_support
    (Ω : TensorRegister n (Fin r)) (mu : Fin r → ℕ)
    (hweight : ∀ a, collectiveGenerator n a a Ω = (mu a : ℂ) • Ω)
    (hraise : ∀ a b, a < b → collectiveGenerator n a b Ω = 0) :
    LinearMap.trace ℂ (cyclicSector (coordinateTensorEmbedding n r k Ω))
      (cyclicTensorOperator (coordinateTensorEmbedding n r k Ω)
        (fun a => (padPartition mu k a : ℂ))
        (coordinateTensorEmbedding_highest Ω mu hweight hraise).1
        (coordinateTensorEmbedding_highest Ω mu hweight hraise).2
        (coordinateSupportMatrix r k)).toLinearMap =
      (Module.finrank ℂ (cyclicSector Ω) : ℂ) := by
  rw [coordinateSectorEmbedding_support Ω mu hweight hraise]
  let J := (coordinateSectorEmbedding (k := k) Ω).toContinuousLinearMap
  change LinearMap.trace ℂ _ (J.toLinearMap.comp J.adjoint.toLinearMap) = _
  rw [LinearMap.trace_comp_comm']
  have he : J.adjoint.comp J = 1 :=
    (ContinuousLinearMap.norm_map_iff_adjoint_comp_self J).mp (coordinateSectorEmbedding Ω).norm_map
  change LinearMap.trace ℂ _ (J.adjoint.comp J).toLinearMap = _
  rw [he]
  exact LinearMap.trace_id ℂ (cyclicSector Ω)

end Cloning.TensorLie
