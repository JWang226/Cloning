import Cloning.GeneralSymmetricBalance

/-! # Werner's full CPTP channel on arbitrary symmetric inputs

The map is constructed from the actual symmetric-tensor splitting matrix.
Its partial-trace balance is proved combinatorially, so trace preservation
and complete positivity have no representation-theoretic assumptions.
The final identity is exactly the dimension-ratio symmetric sandwich in
the literal computational tensor basis, for every input matrix.
-/
noncomputable section
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators InnerProductSpace Matrix Kronecker ComplexOrder

namespace Cloning.GeneralSymmetricOccupation

/-- The full `n → n+r` Werner channel on arbitrary matrices of the input
symmetric sector, with complete positivity and trace preservation proved. -/
def wernerChannel (n r s : ℕ) :
    Cloning.Channels.MatrixChannel (Occupation n (s + 1)) (Occupation (n + r) (s + 1)) :=
  Cloning.CartanChannel.cartanChannel (splittingMatrix n r (s + 1))
    ((n + s).choose s : ℝ) ((n + r + s).choose s : ℝ)
    (by exact_mod_cast Nat.choose_pos (Nat.le_add_left s n))
    (by exact_mod_cast Nat.choose_pos (Nat.le_add_left s (n + r)))
    (splittingMatrix_balance n r s)

/-- Exact Kraus/sandwich formula in the two occupation registers. -/
theorem wernerChannel_apply (n r s : ℕ)
    (X : Matrix (Occupation n (s + 1)) (Occupation n (s + 1)) ℂ) :
    (wernerChannel n r s).toFun X =
      (((n + s).choose s : ℝ) / ((n + r + s).choose s : ℝ)) •
        ((splittingMatrix n r (s + 1)).conjTranspose *
          (X ⊗ₖ (1 : Matrix (Occupation r (s + 1)) (Occupation r (s + 1)) ℂ)) *
            splittingMatrix n r (s + 1)) :=
  Cloning.CartanChannel.cartanChannel_apply _ _ _ _ _ _ X

/-- The actual computational projector onto the output symmetric tensor space. -/
def splitSymmetricProjector (n r d : ℕ) :
    Matrix (Word n d × Word r d) (Word n d × Word r d) ℂ :=
  splitColumnMatrix n r d * (splitColumnMatrix n r d).conjTranspose

theorem splitSymmetricProjector_idempotent (n r d : ℕ) :
    splitSymmetricProjector n r d * splitSymmetricProjector n r d =
      splitSymmetricProjector n r d := by
  unfold splitSymmetricProjector
  calc
    _ = splitColumnMatrix n r d *
      ((splitColumnMatrix n r d).conjTranspose * splitColumnMatrix n r d) *
        (splitColumnMatrix n r d).conjTranspose := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [splitColumnMatrix_isometry]; simp

theorem splitSymmetricProjector_selfAdjoint (n r d : ℕ) :
    (splitSymmetricProjector n r d).conjTranspose = splitSymmetricProjector n r d := by
  simp [splitSymmetricProjector]

/-- Core physical tensor identity for every input matrix: the environment
identity is the whole computational tensor identity. -/
theorem physical_tensor_core {n r d : ℕ}
    (X : Matrix (Occupation n d) (Occupation n d) ℂ) :
    (splitColumnMatrix n r d).conjTranspose *
      ((columnMatrix n d * X * (columnMatrix n d).conjTranspose) ⊗ₖ
        (1 : Matrix (Word r d) (Word r d) ℂ)) * splitColumnMatrix n r d =
      (splittingMatrix n r d).conjTranspose *
        (X ⊗ₖ (1 : Matrix (Occupation r d) (Occupation r d) ℂ)) * splittingMatrix n r d := by
  calc
    _ = (splittingMatrix n r d).conjTranspose *
        ((columnMatrix n d ⊗ₖ columnMatrix r d).conjTranspose *
          ((columnMatrix n d * X * (columnMatrix n d).conjTranspose) ⊗ₖ
            (1 : Matrix (Word r d) (Word r d) ℂ)) *
              (columnMatrix n d ⊗ₖ columnMatrix r d)) * splittingMatrix n r d := by
      rw [← splittingMatrix_physical]
      simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = _ := by
      rw [Cloning.Compression.tensor_compression _ _ X
        (columnMatrix_isometry n d) (columnMatrix_isometry r d)]

/-- The constructed CPTP map equals Werner's symmetric-projection formula
in the actual computational tensor basis, on every symmetric input matrix. -/
theorem wernerChannel_physical_sandwich (n r s : ℕ)
    (X : Matrix (Occupation n (s + 1)) (Occupation n (s + 1)) ℂ) :
    splitColumnMatrix n r (s + 1) * (wernerChannel n r s).toFun X *
      (splitColumnMatrix n r (s + 1)).conjTranspose =
        (((n + s).choose s : ℝ) / ((n + r + s).choose s : ℝ)) •
          (splitSymmetricProjector n r (s + 1) *
            ((columnMatrix n (s + 1) * X * (columnMatrix n (s + 1)).conjTranspose) ⊗ₖ
              (1 : Matrix (Word r (s + 1)) (Word r (s + 1)) ℂ)) *
                splitSymmetricProjector n r (s + 1)) := by
  rw [wernerChannel_apply, ← physical_tensor_core]
  simp only [splitSymmetricProjector, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]

/-- The physical Werner map preserves trace for every input operator. -/
theorem wernerChannel_trace (n r s : ℕ)
    (X : Matrix (Occupation n (s + 1)) (Occupation n (s + 1)) ℂ) :
    Matrix.trace ((wernerChannel n r s).toFun X) = Matrix.trace X :=
  (wernerChannel n r s).trace_preserving X

/-- Positivity holds after arbitrary finite ancilla extension. -/
theorem wernerChannel_completelyPositive (n r s k : ℕ)
    (X : Matrix (Fin k × Occupation n (s + 1)) (Fin k × Occupation n (s + 1)) ℂ)
    (hX : X.PosSemidef) :
    (Cloning.Channels.amplify (wernerChannel n r s).toFun X).PosSemidef :=
  (wernerChannel n r s).completely_positive k X hX

end Cloning.GeneralSymmetricOccupation
