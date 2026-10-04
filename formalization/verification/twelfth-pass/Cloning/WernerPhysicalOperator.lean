import Cloning.GeneralSymmetricProjector
import Cloning.GeneralSymmetricCounting
import Cloning.GeneralSymmetricDimension
import Cloning.WernerDimensionIdentity

/-! # Exact physical Werner output in arbitrary dimension

The fixed-slot projector is the computational tensor operator
`|a⟩⟨a|^⊗n ⊗ I` (with an arbitrary specified set of `n` slots). We compute
its compression by the actual symmetric projector and derive Werner's
occupation eigenvalues from the proved fiber-counting identity.
-/
noncomputable section
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000
open scoped BigOperators InnerProductSpace

namespace Cloning.GeneralSymmetricOccupation

/-- The tensor projector fixing the letter `a` on the specified input slots. -/
def fixedSlotProjector {L d : ℕ} (a : Fin d) (S : Finset (Fin L)) :
    TensorSpace L d →L[ℂ] TensorSpace L d :=
  ∑ w ∈ Finset.univ.filter (fun w : Word L d => S ⊆ letterSlots w a),
    InnerProductSpace.rankOne ℂ (lp.single 2 w 1) (lp.single 2 w 1)

/-- This is exactly the diagonal action of the physical product-input projector. -/
theorem fixedSlotProjector_apply {L d : ℕ} (a : Fin d) (S : Finset (Fin L))
    (v : TensorSpace L d) (w : Word L d) :
    fixedSlotProjector a S v w = if S ⊆ letterSlots w a then v w else 0 := by
  classical
  simp only [fixedSlotProjector, ContinuousLinearMap.sum_apply, InnerProductSpace.rankOne_apply,
    lp.inner_single_left, RCLike.inner_apply, map_one, mul_one,
    lp.coeFn_sum, Finset.sum_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul,
    lp.single_apply, Pi.single_apply]
  by_cases hw : S ⊆ letterSlots w a
  · rw [if_pos hw, Finset.sum_eq_single w]
    · simp
    · intro z hz hn
      simp [Ne.symm hn]
    · simp [hw]
  · rw [if_neg hw]
    apply Finset.sum_eq_zero
    intro z hz
    have hn : w ≠ z := by
      intro h
      subst z
      exact hw (Finset.mem_filter.mp hz).2
    simp [hn]

private theorem sum_fixedSlot_column {L d : ℕ} (a : Fin d) (S : Finset (Fin L))
    (q r : Occupation L d) :
    (∑ w ∈ fiber r, fixedSlotProjector a S (column q) w) =
      if r = q then ((accepted q a S).card : ℂ) *
        (Real.sqrt (multiplicity q : ℝ) : ℂ)⁻¹ else 0 := by
  classical
  by_cases hr : r = q
  · subst r
    rw [if_pos rfl]
    calc
      _ = ∑ w ∈ fiber q, if S ⊆ letterSlots w a then
          (Real.sqrt (multiplicity q : ℝ) : ℂ)⁻¹ else 0 := by
        apply Finset.sum_congr rfl
        intro w hw
        rw [fixedSlotProjector_apply, column_apply, if_pos ((mem_fiber q w).mp hw)]
      _ = _ := by rw [← Finset.sum_filter]; simp [accepted]
  · rw [if_neg hr]
    apply Finset.sum_eq_zero
    intro w hw
    have hn : label w ≠ q := by
      rw [(mem_fiber r w).mp hw]
      exact hr
    rw [fixedSlotProjector_apply, column_apply, if_neg hn]
    split_ifs <;> rfl

/-- Compressing a physical pure product input is diagonal in the full
occupation basis; the eigenvalue is the exact accepted-fiber proportion. -/
theorem compression_column {L d : ℕ} (a : Fin d) (S : Finset (Fin L))
    (q : Occupation L d) :
    projector L d (fixedSlotProjector a S (column q)) =
      ((((accepted q a S).card : ℝ) / multiplicity q : ℝ) : ℂ) • column q := by
  classical
  ext w
  rw [projector_coefficient]
  change (multiplicity (label w) : ℂ)⁻¹ *
      (∑ z ∈ fiber (label w), fixedSlotProjector a S (column q) z) = _
  rw [sum_fixedSlot_column]
  simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, column_apply]
  by_cases hw : label w = q
  · rw [if_pos hw, if_pos hw, hw]
    push_cast
    ring
  · rw [if_neg hw, if_neg hw]
    simp

/-- The fixed-slot compression eigenvalue is the binomial ratio derived from
computational tensor counting. -/
theorem compression_column_binomial {L d : ℕ} (a : Fin d) (S : Finset (Fin L))
    (q : Occupation L d) :
    projector L d (fixedSlotProjector a S (column q)) =
      ((((q.val a).choose S.card : ℝ) / L.choose S.card : ℝ) : ℂ) • column q := by
  rw [compression_column, accepted_proportion]

/-- Actual symmetric compression equals the proved diagonal resolution. -/
theorem compressed_operator_eq_sum {L d : ℕ} (a : Fin d) (S : Finset (Fin L)) :
    projector L d * fixedSlotProjector a S * projector L d =
      ∑ q : Occupation L d,
        ((((q.val a).choose S.card : ℝ) / L.choose S.card : ℝ) : ℂ) •
          InnerProductSpace.rankOne ℂ (column q) (column q) := by
  apply ContinuousLinearMap.ext
  intro v
  change projector L d (fixedSlotProjector a S (projector L d v)) = _
  rw [show projector L d v = ∑ q : Occupation L d, ⟪column q, v⟫_ℂ • column q
    from projector_apply v]
  simp only [map_sum, map_smul, compression_column_binomial,
    ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, InnerProductSpace.rankOne_apply]
  apply Finset.sum_congr rfl
  intro q hq
  rw [smul_smul, smul_smul, mul_comm]

/-- Werner's formula on the physical tensor space, at a pure product input.
The prefactor is the ratio of actual constructed symmetric-space dimensions. -/
def wernerOutputOperator {L s : ℕ} (a : Fin (s + 1)) (S : Finset (Fin L)) :
    TensorSpace L (s + 1) →L[ℂ] TensorSpace L (s + 1) :=
  (((Fintype.card (Occupation S.card (s + 1)) : ℝ) /
    Fintype.card (Occupation L (s + 1)) : ℝ) : ℂ) •
      (projector L (s + 1) * fixedSlotProjector a S * projector L (s + 1))

/-- Exact arbitrary-dimensional physical Werner eigenvalues, including zero
eigenvalues beyond the input-compatible occupation support. -/
theorem wernerOutputOperator_column {L s : ℕ} (a : Fin (s + 1))
    (S : Finset (Fin L)) (q : Occupation L (s + 1)) :
    wernerOutputOperator a S (column q) =
      ((((q.val a).choose S.card : ℝ) / (L + s).choose (S.card + s) : ℝ) : ℂ) • column q := by
  have hSL : S.card ≤ L := by simpa using Finset.card_le_univ S
  simp only [wernerOutputOperator, ContinuousLinearMap.smul_apply, ContinuousLinearMap.mul_apply,
    projector_eq_self (column_mem_symmetric q), compression_column_binomial, smul_smul,
    occupation_card]
  rw [← Complex.ofReal_mul, Cloning.Occupation.werner_dimension_identity _ _ _ _ hSL]

/-- Operator-level equality of the original symmetric-projection formula
and its occupation spectral decomposition. -/
theorem wernerOutputOperator_eq_sum {L s : ℕ} (a : Fin (s + 1))
    (S : Finset (Fin L)) :
    wernerOutputOperator a S =
      ∑ q : Occupation L (s + 1),
        ((((q.val a).choose S.card : ℝ) / (L + s).choose (S.card + s) : ℝ) : ℂ) •
          InnerProductSpace.rankOne ℂ (column q) (column q) := by
  have hSL : S.card ≤ L := by simpa using Finset.card_le_univ S
  rw [wernerOutputOperator, compressed_operator_eq_sum, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro q hq
  rw [smul_smul, occupation_card, occupation_card, ← Complex.ofReal_mul,
    Cloning.Occupation.werner_dimension_identity _ _ _ _ hSL]

end Cloning.GeneralSymmetricOccupation
