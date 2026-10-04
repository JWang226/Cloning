import Cloning.WernerPhysicalChannel
import Cloning.WernerPhysicalPullback
import Mathlib.Data.Matrix.Basis
import Cloning.InfiniteFiniteCorner

/-! # Agreement of the full Werner channel with the physical pure-output model

Computational operator matrices connect the full CPTP channel to the exact
trace-class output already used in the general-dimensional thermal limit.
-/
noncomputable section
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators InnerProductSpace Matrix Kronecker ComplexOrder

namespace Cloning.GeneralSymmetricOccupation

/-- A constant computational word is the unique member of its occupation fiber. -/
theorem label_eq_constant_iff {L d : ℕ} (w : Word L d) (a : Fin d) :
    label w = label (fun _ : Fin L => a) ↔ w = fun _ => a := by
  constructor
  · intro h
    obtain ⟨σ, hσ⟩ := (label_eq_iff_perm w (fun _ => a)).mp h
    exact funext fun i => (hσ i).symm
  · intro h
    rw [h]

theorem multiplicity_constant (L d : ℕ) (a : Fin d) :
    multiplicity (label (fun _ : Fin L => a)) = 1 := by
  classical
  unfold multiplicity
  have hf : Finset.univ.filter (fun w : Word L d => label w = label (fun _ => a)) =
      {fun _ : Fin L => a} := by
    ext w
    simp [label_eq_constant_iff]
  rw [hf]
  simp

theorem column_constant_apply (L d : ℕ) (a : Fin d) (w : Word L d) :
    column (label (fun _ : Fin L => a)) w = if w = (fun _ => a) then 1 else 0 := by
  simp [column_apply, multiplicity_constant, label_eq_constant_iff]

/-- The pure tensor input in the symmetric occupation register. -/
def pureInputMatrix (n d : ℕ) (a : Fin d) :
    Matrix (Occupation n d) (Occupation n d) ℂ :=
  Matrix.single (label (fun _ : Fin n => a)) (label (fun _ : Fin n => a)) 1

theorem pureInputMatrix_embedded (n d : ℕ) (a : Fin d) :
    columnMatrix n d * pureInputMatrix n d a * (columnMatrix n d).conjTranspose =
      Matrix.single (fun _ : Fin n => a) (fun _ : Fin n => a) 1 := by
  classical
  ext w z
  simp only [pureInputMatrix, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.single, Matrix.of_apply]
  simp only [ite_and, mul_ite, mul_one, mul_zero, columnMatrix]
  by_cases hw : w = (fun _ => a) <;> by_cases hz : z = (fun _ => a) <;>
    simp [column_constant_apply, hw, hz, eq_comm]

/-- Computational matrix coefficients, using the actual word-concatenation equivalence. -/
def pairOperatorMatrix {n r d : ℕ} (A : TensorSpace (n + r) d →L[ℂ] TensorSpace (n + r) d) :
    Matrix (Word n d × Word r d) (Word n d × Word r d) ℂ :=
  fun u v => A (lp.single 2 (wordPairEquiv n r d v) 1) (wordPairEquiv n r d u)

private theorem operator_apply_expansion {L d : ℕ}
    (A : TensorSpace L d →L[ℂ] TensorSpace L d) (v : TensorSpace L d) (w : Word L d) :
    A v w = ∑ z : Word L d, A (lp.single 2 z 1) w * v z := by
  classical
  have hv : v = ∑ z : Word L d, v z • (lp.single 2 z 1 : TensorSpace L d) := by
    ext z
    simp [lp.single_apply, Pi.single_apply]
  conv_lhs => rw [hv]
  simp [map_sum, map_smul, lp.coeFn_smul, mul_comm]

theorem pairOperatorMatrix_mul {n r d : ℕ}
    (A B : TensorSpace (n + r) d →L[ℂ] TensorSpace (n + r) d) :
    pairOperatorMatrix (n := n) (r := r) (A * B) = pairOperatorMatrix A * pairOperatorMatrix B := by
  classical
  ext u v
  simp only [pairOperatorMatrix, ContinuousLinearMap.mul_apply, Matrix.mul_apply]
  rw [operator_apply_expansion]
  exact ((wordPairEquiv n r d).sum_comp (fun z =>
    A (lp.single 2 z 1) (wordPairEquiv n r d u) *
      B (lp.single 2 (wordPairEquiv n r d v) 1) z)).symm

theorem pairOperatorMatrix_smul {n r d : ℕ} (c : ℂ)
    (A : TensorSpace (n + r) d →L[ℂ] TensorSpace (n + r) d) :
    pairOperatorMatrix (n := n) (r := r) (c • A) = c • pairOperatorMatrix A := by
  ext u v
  rfl

theorem pairOperatorMatrix_projector (n r d : ℕ) :
    pairOperatorMatrix (n := n) (r := r) (projector (n + r) d) =
      splitSymmetricProjector n r d := by
  classical
  ext u v
  simp only [pairOperatorMatrix, projector_apply, lp.coeFn_sum, Finset.sum_apply,
    lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, lp.inner_single_right,
    RCLike.inner_apply, starRingEnd_apply, one_mul,
    splitSymmetricProjector, Matrix.mul_apply, Matrix.conjTranspose_apply, splitColumnMatrix]
  apply Finset.sum_congr rfl
  intro q hq
  exact mul_comm _ _

private theorem inputSlots_append_iff {n r d : ℕ} (w : Word n d) (z : Word r d) (a : Fin d) :
    inputSlots n (n + r) (Nat.le_add_right n r) ⊆ letterSlots (Fin.append w z) a ↔
      w = fun _ => a := by
  constructor
  · intro h
    funext i
    have hi : Fin.castAdd r i ∈ inputSlots n (n + r) (Nat.le_add_right n r) := by
      rw [mem_inputSlots]
      exact i.isLt
    have hv := mem_letterSlots _ _ _ |>.mp (h hi)
    simpa using hv
  · intro h i hi
    rw [mem_inputSlots] at hi
    let j : Fin n := ⟨i.val, hi⟩
    have he : i = Fin.castAdd r j := Fin.ext rfl
    rw [he, mem_letterSlots]
    simp [h]

theorem pairOperatorMatrix_fixedSlot (n r d : ℕ) (a : Fin d) :
    pairOperatorMatrix (n := n) (r := r)
      (fixedSlotProjector a (inputSlots n (n + r) (Nat.le_add_right n r))) =
        (Matrix.single (fun _ : Fin n => a) (fun _ : Fin n => a) (1 : ℂ)) ⊗ₖ
          (1 : Matrix (Word r d) (Word r d) ℂ) := by
  classical
  ext ⟨w, z⟩ ⟨w', z'⟩
  simp only [pairOperatorMatrix, fixedSlotProjector_apply, lp.single_apply, Pi.single_apply,
    Matrix.kronecker_apply, Matrix.single_apply, Matrix.one_apply]
  have hc : inputSlots n (n + r) (Nat.le_add_right n r) ⊆
      letterSlots (wordPairEquiv n r d (w, z)) a ↔ w = (fun _ => a) :=
    inputSlots_append_iff w z a
  simp only [hc, (wordPairEquiv n r d).injective.eq_iff]
  by_cases hw : w = (fun _ => a) <;> by_cases hw' : w' = (fun _ => a) <;>
    by_cases hz : z = z' <;> simp_all [Prod.mk.injEq, eq_comm]

/-- The full CPTP Werner channel on the reference pure input agrees exactly
with the previous physical symmetric-sandwich operator. -/
theorem wernerChannel_pure_agrees (n r s : ℕ) (a : Fin (s + 1)) :
    splitColumnMatrix n r (s + 1) * (wernerChannel n r s).toFun
      (pureInputMatrix n (s + 1) a) * (splitColumnMatrix n r (s + 1)).conjTranspose =
        pairOperatorMatrix (n := n) (r := r)
          (wernerOutputOperator a (inputSlots n (n + r) (Nat.le_add_right n r))) := by
  rw [wernerChannel_physical_sandwich, pureInputMatrix_embedded, wernerOutputOperator,
    pairOperatorMatrix_smul, pairOperatorMatrix_mul, pairOperatorMatrix_mul,
    pairOperatorMatrix_projector, pairOperatorMatrix_fixedSlot,
    occupation_card, occupation_card, inputSlots_card]
  ext u v
  simp [Matrix.smul_apply, Complex.real_smul, Complex.ofReal_div]

/-- Agreement with the actual trace-class output used in the thermal theorem. -/
theorem wernerChannel_pure_traceClass_agrees (n r s : ℕ) :
    splitColumnMatrix n r (s + 1) * (wernerChannel n r s).toFun
      (pureInputMatrix n (s + 1) 0) * (splitColumnMatrix n r (s + 1)).conjTranspose =
        pairOperatorMatrix (n := n) (r := r)
          (wernerOutput (s := s) (inputSlots n (n + r) (Nat.le_add_right n r))).1 := by
  rw [wernerOutput_op]
  exact wernerChannel_pure_agrees n r s 0

end Cloning.GeneralSymmetricOccupation

namespace Cloning.GeneralSymmetricOccupation
open Cloning.InfiniteTraceClass

/-- All computational matrix coefficients determine the bounded operator. -/
theorem pairOperatorMatrix_injective (n r d : ℕ) :
    Function.Injective (@pairOperatorMatrix n r d) := by
  intro A B h
  apply ContinuousLinearMap.ext
  intro v
  ext w
  rw [operator_apply_expansion, operator_apply_expansion]
  apply Finset.sum_congr rfl
  intro z hz
  obtain ⟨u, rfl⟩ := (wordPairEquiv n r d).surjective w
  obtain ⟨t, rfl⟩ := (wordPairEquiv n r d).surjective z
  have he := congrArg (fun M : Matrix (Word n d × Word r d) (Word n d × Word r d) ℂ => M u t) h
  exact congrArg (fun c : ℂ => c * v (wordPairEquiv n r d t)) he

/-- A matrix lifted through the actual occupation basis has exactly the
computational tensor matrix used in the full-channel sandwich theorem. -/
theorem pairOperatorMatrix_ofMatrix {n r d : ℕ}
    (X : Matrix (Occupation (n + r) d) (Occupation (n + r) d) ℂ) :
    pairOperatorMatrix (n := n) (r := r)
      (Cloning.InfiniteFiniteCorner.ofMatrix (@column (n + r) d) X) =
        splitColumnMatrix n r d * X * (splitColumnMatrix n r d).conjTranspose := by
  classical
  ext u v
  simp only [pairOperatorMatrix, Cloning.InfiniteFiniteCorner.ofMatrix_apply,
    lp.coeFn_sum, Finset.sum_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul,
    lp.inner_single_right, RCLike.inner_apply, starRingEnd_apply, one_mul,
    Matrix.mul_apply, Matrix.conjTranspose_apply, splitColumnMatrix, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- Equality of actual trace-class operators: the full CPTP channel applied
to the reference pure state is the physical output used in the thermal limit. -/
theorem wernerChannel_pure_output (n r s : ℕ) :
    Cloning.InfiniteFiniteCorner.matrixLift (@column (n + r) (s + 1))
      ((wernerChannel n r s).toFun (pureInputMatrix n (s + 1) 0)) =
        wernerOutput (s := s) (inputSlots n (n + r) (Nat.le_add_right n r)) := by
  apply Subtype.ext
  apply pairOperatorMatrix_injective n r (s + 1)
  change pairOperatorMatrix (Cloning.InfiniteFiniteCorner.ofMatrix _ _) = _
  rw [pairOperatorMatrix_ofMatrix]
  exact wernerChannel_pure_traceClass_agrees n r s

end Cloning.GeneralSymmetricOccupation

namespace Cloning.GeneralSymmetricOccupation
open Cloning.InfiniteTraceClass
open scoped Topology
open Filter

/-- End-to-end thermal limit of the fully constructed CPTP Werner channel,
with actual trace-class output and an actual CPTP occupation pullback. -/
theorem wernerChannel_thermal_limit {s : ℕ} (hs : 1 ≤ s)
    (r : ℕ → ℕ) {γ : ℝ} (hγ : 1 < γ)
    (h : Tendsto (fun n ↦ ((n + r n : ℕ) : ℝ) / n) atTop (𝓝 γ)) :
    Tendsto (fun n ↦ (occupationRecovery (n + r n) s).toLinearMap
      (Cloning.InfiniteFiniteCorner.matrixLift (@column (n + r n) (s + 1))
        ((wernerChannel n (r n) s).toFun (pureInputMatrix n (s + 1) 0)))) atTop
      (𝓝 (Cloning.InfiniteOccupationStates.thermalOperator (@numberVector s) γ)) := by
  simp only [wernerChannel_pure_output]
  exact physical_werner_thermal_limit hs (fun n => n + r n)
    (fun n => Nat.le_add_right n (r n)) hγ h

end Cloning.GeneralSymmetricOccupation
