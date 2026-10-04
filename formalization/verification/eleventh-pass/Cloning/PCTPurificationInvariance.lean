import Cloning.PCTTensorFrame

/-! Independence of the reduced Werner output under an actual unitary change
of the purifying register. The proof uses exact computational coefficients of
the tensor-power channel, so the spectator cancellation holds before limits. -/
noncomputable section
open scoped BigOperators InnerProductSpace ComplexOrder Topology
open Filter MeasureTheory Cloning.InfiniteTraceClass
namespace Cloning.PCT
open GeneralSymmetricOccupation GeneralCoherent
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

def environmentRow (v : Register (A × B)) (a : A) : Register B :=
  ⟨fun b => v (a, b), memℓp_gen (by
    simp only [ENNReal.toReal_ofNat]; exact (hasSum_fintype _).summable)⟩

@[simp] theorem environmentRow_apply (v : Register (A × B)) (a : A) (b : B) :
    environmentRow v a b = v (a, b) := rfl

/-- Literal action of an environment isometry on each system-index row. -/
def environmentRotate (W : Register B →ₗᵢ[ℂ] Register B) (v : Register (A × B)) :
    Register (A × B) :=
  ⟨fun ab => W (environmentRow v ab.1) ab.2, memℓp_gen (by
    simp only [ENNReal.toReal_ofNat]; exact (hasSum_fintype _).summable)⟩

@[simp] theorem environmentRotate_apply (W : Register B →ₗᵢ[ℂ] Register B)
    (v : Register (A × B)) (a : A) (b : B) :
    environmentRotate W v (a, b) = W (environmentRow v a) b := rfl

@[simp] theorem environmentRow_rotate (W : Register B →ₗᵢ[ℂ] Register B)
    (v : Register (A × B)) (a : A) :
    environmentRow (environmentRotate W v) a = W (environmentRow v a) := by
  ext b
  rfl

theorem register_inner_rows (v w : Register (A × B)) :
    ⟪v, w⟫_ℂ = ∑ a, ⟪environmentRow v a, environmentRow w a⟫_ℂ := by
  simp only [lp.inner_eq_tsum, tsum_fintype, Fintype.sum_prod_type,
    environmentRow_apply]

theorem environmentRotate_inner (W : Register B →ₗᵢ[ℂ] Register B)
    (v w : Register (A × B)) :
    ⟪environmentRotate W v, environmentRotate W w⟫_ℂ = ⟪v, w⟫_ℂ := by
  rw [register_inner_rows, register_inner_rows v w]
  simp only [environmentRow_rotate, W.inner_map_map]

theorem environmentRotate_orthonormal {d : ℕ} {u : Fin d → Register (A × B)}
    (hu : Orthonormal ℂ u) (W : Register B →ₗᵢ[ℂ] Register B) :
    Orthonormal ℂ (fun j => environmentRotate W (u j)) := by
  rw [orthonormal_iff_ite]
  intro j k
  rw [environmentRotate_inner, orthonormal_iff_ite.mp hu]

/-- All reduced cross coefficients are invariant, including off-diagonal
coherences between different frame vectors. -/
theorem environmentRotate_cross (W : Register B →ₗᵢ[ℂ] Register B)
    (v w : Register (A × B)) (a c : A) :
    (∑ b, environmentRotate W v (a, b) * star (environmentRotate W w (c, b))) =
      ∑ b, v (a, b) * star (w (c, b)) := by
  have h := W.inner_map_map (environmentRow w c) (environmentRow v a)
  simpa only [lp.inner_eq_tsum, tsum_fintype, RCLike.inner_apply,
    environmentRow_apply, environmentRotate_apply] using h

theorem register_operator_ext {C : Type*} [Fintype C] [DecidableEq C]
    {X Y : Register C →L[ℂ] Register C}
    (h : ∀ a c, X (lp.single 2 c 1) a = Y (lp.single 2 c 1) a) : X = Y := by
  ext v a
  have hv : v = ∑ c, v c • (lp.single 2 c 1 : Register C) := by
    ext c
    simp [lp.single_apply, Pi.single_apply]
  rw [hv]
  simp only [map_sum, map_smul, lp.coeFn_sum, Finset.sum_apply, lp.coeFn_smul,
    Pi.smul_apply, smul_eq_mul, h]

theorem reducedTensorChannel_projector_coefficient {s : ℕ}
    {u : Fin (s + 1) → Register (A × B)} (hu : Orthonormal ℂ u) (L : ℕ)
    (x : TensorSpace L (s + 1)) (a c : Fin L → A) :
    ((reducedTensorChannel hu L).toLinearMap (vectorProjector x)).1 (lp.single 2 c 1) a =
      ∑ w : Word L (s + 1), ∑ v : Word L (s + 1), x w * star (x v) *
        ∏ i, ∑ b : B, u (w i) (a i, b) * star (u (v i) (c i, b)) := by
  change (partialTraceChannel.toLinearMap ((QuantumChannel.ofIsometry (regroup L)).toLinearMap
    ((QuantumChannel.ofIsometry (tensorFrame hu L)).toLinearMap (vectorProjector x)))).1 _ _ = _
  rw [QuantumChannel.ofIsometry_vectorProjector, QuantumChannel.ofIsometry_vectorProjector]
  change (partialTraceLinear (vectorProjector (regroup L (tensorFrame hu L x)))).1 _ _ = _
  rw [partialTraceLinear_coefficient]
  simp only [vectorProjector, TraceClass.ofOperator_coe, InnerProductSpace.rankOne_apply,
    lp.inner_single_right, RCLike.inner_apply, one_mul, lp.coeFn_smul, Pi.smul_apply,
    smul_eq_mul, regroup_apply, tensorFrame_apply, map_sum, map_mul, map_prod]
  calc
    _ = ∑ b : Fin L → B, ∑ w : Word L (s + 1), ∑ v : Word L (s + 1),
        x w * star (x v) * ∏ i, u (w i) (a i, b i) * star (u (v i) (c i, b i)) := by
      apply Finset.sum_congr rfl
      intro b hb
      rw [Finset.sum_mul]
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro w hw
      apply Finset.sum_congr rfl
      intro v hv
      rw [Finset.prod_mul_distrib]
      simp only [starRingEnd_apply]
      ring
    _ = ∑ w : Word L (s + 1), ∑ v : Word L (s + 1), x w * star (x v) *
        ∑ b : Fin L → B, ∏ i, u (w i) (a i, b i) * star (u (v i) (c i, b i)) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro w hw
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro w hw
      apply Finset.sum_congr rfl
      intro v hv
      exact congrArg (fun t : ℂ => x w * star (x v) * t)
        (Fintype.prod_sum (fun i b => u (w i) (a i, b) * star (u (v i) (c i, b)))).symm

theorem reducedTensorChannel_environment_projector {s : ℕ}
    {u : Fin (s + 1) → Register (A × B)} (hu : Orthonormal ℂ u)
    (W : Register B →ₗᵢ[ℂ] Register B) (L : ℕ) (x : TensorSpace L (s + 1)) :
    (reducedTensorChannel (environmentRotate_orthonormal hu W) L).toLinearMap (vectorProjector x) =
      (reducedTensorChannel hu L).toLinearMap (vectorProjector x) := by
  apply Subtype.ext
  apply register_operator_ext
  intro a c
  simp only [reducedTensorChannel_projector_coefficient, environmentRotate_cross]

/-- Haar randomization on the purifying register cancels exactly for the
actual reduced Werner output, before any asymptotic approximation. -/
theorem werner_reduced_environment_invariant {L s : ℕ}
    {u : Fin (s + 1) → Register (A × B)} (hu : Orthonormal ℂ u)
    (W : Register B →ₗᵢ[ℂ] Register B) (S : Finset (Fin L)) :
    (reducedTensorChannel (environmentRotate_orthonormal hu W) L).toLinearMap
      (wernerOutput (s := s) S) =
      (reducedTensorChannel hu L).toLinearMap (wernerOutput (s := s) S) := by
  simp only [wernerOutput, map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro q hq
  rw [reducedTensorChannel_environment_projector hu W L (column q)]

/-- Any probability randomization of purifying unitaries, in particular Haar
randomization, drops from the exact reduced physical output. Measurability of
the randomization is unnecessary because its reduced integrand is constant. -/
theorem integral_werner_reduced_environment {L s : ℕ}
    {u : Fin (s + 1) → Register (A × B)} (hu : Orthonormal ℂ u)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (W : Ω → Register B →ₗᵢ[ℂ] Register B) (S : Finset (Fin L)) :
    (∫ t, (reducedTensorChannel (environmentRotate_orthonormal hu (W t)) L).toLinearMap
      (wernerOutput (s := s) S) ∂μ) =
      (reducedTensorChannel hu L).toLinearMap (wernerOutput (s := s) S) := by
  have he (t : Ω) := werner_reduced_environment_invariant hu (W t) S
  simp_rw [he]
  simp

end Cloning.PCT
