import Cloning.TensorFlatProjectorNaturality

/-! Literal physical support projection for the first `r` one-particle coordinates. -/
noncomputable section
open scoped BigOperators InnerProductSpace
namespace Cloning.TensorLie
open Cloning.PCT
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {n r k : ℕ}

def coordinateSupportMatrix (r k : ℕ) : Matrix (Fin (r+k)) (Fin (r+k)) ℂ :=
  Matrix.diagonal (fun a => if a.val < r then 1 else 0)

def coordinateTensorProjection (n r k : ℕ) :
    TensorRegister n (Fin (r+k)) →L[ℂ] TensorRegister n (Fin (r+k)) :=
  (coordinateTensorEmbedding n r k).toContinuousLinearMap.comp
    (coordinateTensorEmbedding n r k).toContinuousLinearMap.adjoint

theorem coordinateWordEmbedding_range (w : Fin n → Fin (r+k)) :
    w ∈ Set.range (coordinateWordEmbedding n r k) ↔ ∀ t, (w t).val < r := by
  constructor
  · rintro ⟨v,rfl⟩ t
    exact (v t).isLt
  · intro hw
    exact ⟨fun t => ⟨(w t).val,hw t⟩, funext (fun t => Fin.ext rfl)⟩

/-- The projection keeps precisely the words whose letters lie in the support. -/
theorem coordinateTensorProjection_apply (y : TensorRegister n (Fin (r+k)))
    (w : Fin n → Fin (r+k)) :
    coordinateTensorProjection n r k y w = if ∀ t, (w t).val < r then y w else 0 := by
  by_cases hw : ∀ t, (w t).val < r
  · rw [if_pos hw]
    obtain ⟨v,rfl⟩ := coordinateWordEmbedding_range w |>.mpr hw
    simp only [coordinateTensorProjection, ContinuousLinearMap.comp_apply,
      coordinateTensorEmbedding, LinearIsometry.coe_toContinuousLinearMap, registerEmbedding_apply_image, registerEmbedding_adjoint_apply]
  · rw [if_neg hw]
    exact registerEmbedding_apply_not_mem _ _ w
      (fun he => hw (coordinateWordEmbedding_range w |>.mp he))

/-- The coordinate projection is the literal tensor power of the rank-r matrix. -/
theorem coordinateTensorProjection_eq_tensorOperator :
    coordinateTensorProjection n r k = tensorOperator n (coordinateSupportMatrix r k) := by
  ext y w
  rw [coordinateTensorProjection_apply]
  change _ = tensorOperator n (Matrix.diagonal _) y w
  rw [tensorOperator_diagonal_apply]
  by_cases hw : ∀ t, (w t).val < r
  · simp [hw]
  · rw [if_neg hw]
    push_neg at hw
    obtain ⟨t,ht⟩ := hw
    have hp : (∏ s : Fin n, if (w s).val < r then (1:ℂ) else 0) = 0 := by
      exact Finset.prod_eq_zero (Finset.mem_univ t) (if_neg (not_lt.mpr ht))
    rw [hp, zero_mul]

@[simp] theorem coordinateTensorProjection_embedding (x : TensorRegister n (Fin r)) :
    coordinateTensorProjection n r k (coordinateTensorEmbedding n r k x) =
      coordinateTensorEmbedding n r k x := by
  ext w
  rw [coordinateTensorProjection_apply]
  split_ifs with hw
  · rfl
  · exact (registerEmbedding_apply_not_mem _ x w
      (fun he => hw (coordinateWordEmbedding_range w |>.mp he))).symm

/-- The adjoint inclusion reads off supported tensor coefficients. -/
theorem coordinateTensorEmbedding_adjoint_collective
    (y : TensorRegister n (Fin (r+k))) (a b : Fin r) :
    (coordinateTensorEmbedding n r k).toContinuousLinearMap.adjoint
      (collectiveGenerator n (Fin.castAdd k a) (Fin.castAdd k b) y) =
      collectiveGenerator n a b ((coordinateTensorEmbedding n r k).toContinuousLinearMap.adjoint y) := by
  let I := (coordinateTensorEmbedding n r k).toContinuousLinearMap
  have he : I.comp (collectiveGenerator n b a) =
      (collectiveGenerator n (Fin.castAdd k b) (Fin.castAdd k a)).comp I := by
    apply ContinuousLinearMap.ext
    intro x
    exact coordinateTensorEmbedding_collective x b a
  have hh := congrArg ContinuousLinearMap.adjoint he
  simp only [ContinuousLinearMap.adjoint_comp, collectiveGenerator_adjoint] at hh
  exact (congrArg (fun T => T y) hh).symm

theorem coordinateTensorProjection_collective
    (y : TensorRegister n (Fin (r+k))) (a b : Fin r) :
    coordinateTensorProjection n r k
      (collectiveGenerator n (Fin.castAdd k a) (Fin.castAdd k b) y) =
      collectiveGenerator n (Fin.castAdd k a) (Fin.castAdd k b)
        (coordinateTensorProjection n r k y) := by
  change coordinateTensorEmbedding n r k
    ((coordinateTensorEmbedding n r k).toContinuousLinearMap.adjoint
      (collectiveGenerator n (Fin.castAdd k a) (Fin.castAdd k b) y)) = _
  rw [coordinateTensorEmbedding_adjoint_collective, coordinateTensorEmbedding_collective]
  rfl

/-- A lowering step into an unsupported letter has zero supported compression. -/
theorem coordinateTensorProjection_collective_outside
    (y : TensorRegister n (Fin (r+k))) (a : Fin k) (b : Fin (r+k)) :
    coordinateTensorProjection n r k (collectiveGenerator n (Fin.natAdd r a) b y) = 0 := by
  ext w
  rw [coordinateTensorProjection_apply]
  by_cases hw : ∀ t, (w t).val < r
  · rw [if_pos hw, collectiveGenerator_apply]
    apply Finset.sum_eq_zero
    intro t _
    have hne : w t ≠ Fin.natAdd r a := by
      intro he
      have hh := congrArg Fin.val he
      have ht := hw t
      change (w t).val = r+a.val at hh
      omega
    simp [hne]
  · simp [hw]

end Cloning.TensorLie
