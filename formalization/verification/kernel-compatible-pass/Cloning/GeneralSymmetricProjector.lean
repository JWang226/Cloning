import Cloning.GeneralSymmetricOccupation
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-! # The physical symmetric projector for arbitrary one-particle dimension

The rank-one sum of the constructed occupation columns is proved to be the
orthogonal projector onto the invariant subspace of all tensor-slot
permutations. Its computational-basis action is the average over exactly one
occupation fiber.
-/

noncomputable section
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000
open scoped BigOperators InnerProductSpace

namespace Cloning.GeneralSymmetricOccupation

/-- Explicit occupation-basis resolution of the symmetric tensor projector. -/
def projector (L d : ℕ) : TensorSpace L d →L[ℂ] TensorSpace L d :=
  ∑ q : Occupation L d, InnerProductSpace.rankOne ℂ (column q) (column q)

theorem projector_apply {L d : ℕ} (v : TensorSpace L d) :
    projector L d v = ∑ q : Occupation L d, ⟪column q, v⟫_ℂ • column q := by
  simp [projector, ContinuousLinearMap.sum_apply, InnerProductSpace.rankOne_apply]

theorem column_mem_symmetric {L d : ℕ} (q : Occupation L d) :
    column q ∈ symmetricSubspace L d := by
  intro w σ
  simp only [column_apply, label_permute]

theorem projector_mem_symmetric {L d : ℕ} (v : TensorSpace L d) :
    projector L d v ∈ symmetricSubspace L d := by
  rw [projector_apply]
  exact Submodule.sum_mem _ (fun q hq => Submodule.smul_mem _ _ (column_mem_symmetric q))

theorem inner_column {L d : ℕ} (q : Occupation L d) (v : TensorSpace L d) :
    ⟪column q, v⟫_ℂ =
      (Real.sqrt (multiplicity q : ℝ) : ℂ)⁻¹ *
        ∑ w ∈ Finset.univ.filter (fun w : Word L d => label w = q), v w := by
  classical
  rw [lp.inner_eq_tsum, tsum_fintype]
  simp only [column_apply, RCLike.inner_apply]
  rw [Finset.mul_sum]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro w hw
  split_ifs with h
  · simp [mul_comm]
  · simp

/-- Every computational coefficient is the average over its occupation fiber. -/
theorem projector_coefficient {L d : ℕ} (v : TensorSpace L d) (w : Word L d) :
    projector L d v w = (multiplicity (label w) : ℂ)⁻¹ *
      ∑ z ∈ Finset.univ.filter (fun z : Word L d => label z = label w), v z := by
  classical
  rw [projector_apply]
  simp only [lp.coeFn_sum, Finset.sum_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single (label w)]
  · rw [column_apply, if_pos rfl, inner_column]
    have hs : (Real.sqrt (multiplicity (label w) : ℝ) : ℂ) ^ 2 =
        (multiplicity (label w) : ℂ) := by
      rw [← Complex.ofReal_pow, Real.sq_sqrt (by positivity)]
      norm_cast
    rw [mul_assoc, mul_comm (_ : ℂ) ((Real.sqrt _ : ℂ)⁻¹), ← mul_assoc,
      ← pow_two, inv_pow, hs]
  · intro q hq hn
    simp [column_apply, Ne.symm hn]
  · simp

theorem projector_eq_self {L d : ℕ} {v : TensorSpace L d}
    (hv : v ∈ symmetricSubspace L d) : projector L d v = v := by
  classical
  ext w
  rw [projector_coefficient]
  have hs : (∑ z ∈ Finset.univ.filter (fun z : Word L d => label z = label w), v z) =
      (multiplicity (label w) : ℂ) * v w := by
    calc
      _ = ∑ _z ∈ Finset.univ.filter (fun z : Word L d => label z = label w), v w := by
        apply Finset.sum_congr rfl
        intro z hz
        exact (symmetric_iff_constant_on_fibers v).mp hv _ _ (Finset.mem_filter.mp hz).2
      _ = _ := by simp [multiplicity]
  rw [hs, ← mul_assoc, inv_mul_cancel₀, one_mul]
  exact_mod_cast (multiplicity_pos (label w)).ne'

theorem projector_idempotent (L d : ℕ) : IsIdempotentElem (projector L d) := by
  apply ContinuousLinearMap.ext
  intro v
  exact projector_eq_self (projector_mem_symmetric v)

theorem projector_selfAdjoint (L d : ℕ) : IsSelfAdjoint (projector L d) := by
  change star (projector L d) = projector L d
  simp [projector, ContinuousLinearMap.star_eq_adjoint]

theorem projector_isStarProjection (L d : ℕ) : IsStarProjection (projector L d) :=
  ⟨projector_idempotent L d, projector_selfAdjoint L d⟩

theorem projector_range (L d : ℕ) : (projector L d).range = symmetricSubspace L d := by
  ext v
  constructor
  · rintro ⟨u, rfl⟩
    exact projector_mem_symmetric u
  · intro hv
    exact ⟨v, projector_eq_self hv⟩

instance symmetricSubspace_hasOrthogonalProjection (L d : ℕ) :
    (symmetricSubspace L d).HasOrthogonalProjection := by
  rw [← projector_range]
  exact ContinuousLinearMap.IsIdempotentElem.hasOrthogonalProjection_range
    (projector_idempotent L d)

/-- The explicit fiber average is exactly Mathlib's orthogonal projection onto
permutation-invariant computational tensors. -/
theorem projector_eq_starProjection (L d : ℕ) :
    projector L d = (symmetricSubspace L d).starProjection := by
  apply ContinuousLinearMap.IsStarProjection.ext (projector_isStarProjection L d)
    isStarProjection_starProjection
  rw [projector_range, Submodule.range_starProjection]

end Cloning.GeneralSymmetricOccupation
