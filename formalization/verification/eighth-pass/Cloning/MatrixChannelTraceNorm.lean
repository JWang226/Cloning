import Cloning.MatrixLiftedChannel
import Cloning.MatrixTraceNormOrder

/-!
# Trace-norm contraction of concrete matrix channels

The channel structure supplies complete positivity and trace preservation.
Positivity follows by one-dimensional amplification. The Hermitian Jordan
decomposition, followed by the positive-decomposition trace-norm bound,
then proves contraction. No contractivity assumption is made.
-/

noncomputable section
open scoped Matrix MatrixOrder ComplexOrder
open Cloning.MatrixFidelity

namespace Cloning.Channels.MatrixChannel

set_option backward.isDefEq.respectTransparency false

variable {α β : Type*} [Fintype α] [Fintype β]

/-- A concrete matrix channel preserves zero. -/
theorem map_zero (Φ : MatrixChannel α β) : Φ.toFun 0 = 0 := by
  simpa only [zero_smul] using Φ.map_smul (0 : ℂ) (0 : Matrix α α ℂ)

/-- A concrete matrix channel preserves additive inverses. -/
theorem map_neg (Φ : MatrixChannel α β) (X : Matrix α α ℂ) :
    Φ.toFun (-X) = -Φ.toFun X := by
  simpa only [neg_one_smul] using Φ.map_smul (-1 : ℂ) X

/-- A concrete matrix channel preserves differences. -/
theorem map_sub (Φ : MatrixChannel α β) (X Y : Matrix α α ℂ) :
    Φ.toFun (X - Y) = Φ.toFun X - Φ.toFun Y := by
  rw [sub_eq_add_neg, Φ.map_add, map_neg, ← sub_eq_add_neg]

/-- Complete positivity includes ordinary positivity. -/
theorem positive (Φ : MatrixChannel α β) {X : Matrix α α ℂ}
    (hX : X.PosSemidef) : (Φ.toFun X).PosSemidef :=
  Cloning.MatrixLiftedChannel.map_positive Φ hX

variable [DecidableEq α] [DecidableEq β]

/-- The trace of the positive and negative Jordan parts is the Hermitian
matrix's trace norm. -/
theorem jordan_trace_mass {D : Matrix α α ℂ} (hD : D.IsHermitian) :
    (Matrix.trace (D⁺)).re + (Matrix.trace (D⁻)).re = matrixTraceNorm D := by
  rw [← Complex.add_re, ← Matrix.trace_add, CFC.posPart_add_negPart D hD]
  rfl

/-- A trace-preserving positive matrix channel contracts the trace norm
of every Hermitian matrix, including matrices with positive and negative
eigenvalues and matrices with a nontrivial kernel. -/
theorem traceNorm_contract_hermitian (Φ : MatrixChannel α β)
    {D : Matrix α α ℂ} (hD : D.IsHermitian) :
    matrixTraceNorm (Φ.toFun D) ≤ matrixTraceNorm D := by
  have hpos : (D⁺).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp (CFC.posPart_nonneg D)
  have hneg : (D⁻).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp (CFC.negPart_nonneg D)
  have h := traceNorm_sub_le_trace_add (Φ.positive hpos) (Φ.positive hneg)
  rw [← Φ.map_sub, CFC.posPart_sub_negPart D hD,
    Φ.trace_preserving, Φ.trace_preserving, jordan_trace_mass hD] at h
  exact h

/-- Trace distance between positive input matrices cannot increase under
a concrete matrix channel. No input normalization is required. -/
theorem traceNorm_contract_sub (Φ : MatrixChannel α β)
    {X Y : Matrix α α ℂ} (hX : X.PosSemidef) (hY : Y.PosSemidef) :
    matrixTraceNorm (Φ.toFun X - Φ.toFun Y) ≤ matrixTraceNorm (X - Y) := by
  rw [← Φ.map_sub]
  exact Φ.traceNorm_contract_hermitian (hX.isHermitian.sub hY.isHermitian)

/-- A numerical input trace-distance estimate passes through the channel. -/
theorem traceNorm_contract_sub_le (Φ : MatrixChannel α β)
    {X Y : Matrix α α ℂ} (hX : X.PosSemidef) (hY : Y.PosSemidef)
    {ε : ℝ} (hε : matrixTraceNorm (X - Y) ≤ ε) :
    matrixTraceNorm (Φ.toFun X - Φ.toFun Y) ≤ ε :=
  (Φ.traceNorm_contract_sub hX hY).trans hε

end Cloning.Channels.MatrixChannel
