import Cloning.Channels
import Cloning.MatrixFidelityBlocks

/-!
# Discarding a finite classical label is a quantum channel

The map takes the sum of the diagonal blocks of any input matrix. Complete
positivity and trace preservation are proved directly, at every amplification.
-/

noncomputable section
open scoped BigOperators Matrix ComplexOrder
open Matrix
namespace Cloning.Channels

variable {ι n : Type*} [Fintype ι] [Fintype n]

/-- Sum the diagonal blocks, including on inputs with off-diagonal blocks. -/
def discardLabelMap (X : Matrix (Σ _ : ι, n) (Σ _ : ι, n) ℂ) : Matrix n n ℂ :=
  ∑ i, X.submatrix (fun a => ⟨i, a⟩) (fun a => ⟨i, a⟩)

omit [Fintype n] in
theorem discardLabelMap_add (X Y : Matrix (Σ _ : ι, n) (Σ _ : ι, n) ℂ) :
    discardLabelMap (X + Y) = discardLabelMap X + discardLabelMap Y := by
  simp [discardLabelMap, Matrix.submatrix_add, Finset.sum_add_distrib]

omit [Fintype n] in
theorem discardLabelMap_smul (c : ℂ) (X : Matrix (Σ _ : ι, n) (Σ _ : ι, n) ℂ) :
    discardLabelMap (c • X) = c • discardLabelMap X := by
  simp [discardLabelMap, Matrix.submatrix_smul, Finset.smul_sum]

theorem discardLabelMap_trace (X : Matrix (Σ _ : ι, n) (Σ _ : ι, n) ℂ) :
    trace (discardLabelMap X) = trace X := by
  unfold discardLabelMap
  rw [Matrix.trace_sum]
  simp [Matrix.trace, Matrix.diag, Fintype.sum_sigma]

omit [Fintype n] in
theorem discardLabelMap_completely_positive (k : ℕ)
    (X : Matrix (Fin k × (Σ _ : ι, n)) (Fin k × (Σ _ : ι, n)) ℂ)
    (hX : X.PosSemidef) : (amplify discardLabelMap X).PosSemidef := by
  have heq : amplify discardLabelMap X =
      ∑ i : ι, X.submatrix (fun p : Fin k × n => (p.1, ⟨i, p.2⟩))
        (fun p : Fin k × n => (p.1, ⟨i, p.2⟩)) := by
    ext a b
    simp [amplify, discardLabelMap, Matrix.submatrix_apply, Matrix.sum_apply]
  rw [heq]
  exact Matrix.posSemidef_sum _ (fun i _ => hX.submatrix _)

/-- A concrete CPTP map forgetting a finite classical label. -/
def discardLabelChannel : MatrixChannel (Σ _ : ι, n) n where
  toFun := discardLabelMap
  map_add := discardLabelMap_add
  map_smul := discardLabelMap_smul
  trace_preserving := discardLabelMap_trace
  completely_positive := discardLabelMap_completely_positive

omit [Fintype n] in
theorem discardLabelMap_blockDiagonal' [DecidableEq ι]
    (A : ι → Matrix n n ℂ) :
    discardLabelMap (Matrix.blockDiagonal' A) = ∑ i, A i := by
  unfold discardLabelMap
  apply Finset.sum_congr rfl
  intro i _
  ext a b
  simp [Matrix.submatrix_apply]

end Cloning.Channels
