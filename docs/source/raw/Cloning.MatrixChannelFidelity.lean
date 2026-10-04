import Cloning.Channels
import Cloning.MatrixFidelitySymmetry
import Cloning.MatrixFidelityWitness
import Cloning.MatrixFidelityBlockBound
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! # Data processing for concrete finite-dimensional matrix channels

Complete positivity transports positive two-by-two operator blocks. This
provides the channel step in the semidefinite characterization of fidelity.
-/

noncomputable section
open scoped BigOperators Matrix MatrixOrder ComplexOrder Topology
open Matrix Filter

namespace Cloning.MatrixFidelity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

variable {α β : Type*} [Fintype α] [Fintype β]

/-- A completely positive matrix channel transports all four entries of
a positive two-by-two operator block. -/
theorem channel_fromBlocks_posSemidef (Φ : Cloning.Channels.MatrixChannel α β)
    {A X Y B : Matrix α α ℂ} (h : (Matrix.fromBlocks A X Y B).PosSemidef) :
    (Matrix.fromBlocks (Φ.toFun A) (Φ.toFun X) (Φ.toFun Y) (Φ.toFun B)).PosSemidef := by
  let encode : Fin 2 × α → α ⊕ α :=
    fun p => if p.1 = 0 then Sum.inl p.2 else Sum.inr p.2
  let decode : β ⊕ β → Fin 2 × β := Sum.elim (fun i => (0, i)) (fun i => (1, i))
  have hin := h.submatrix encode
  have hout := (Φ.completely_positive 2 _ hin).submatrix decode
  convert hout using 1
  ext i j
  cases i with
  | inl i =>
    cases j with
    | inl j => simp [Cloning.Channels.amplify, Matrix.submatrix, encode, decode]
    | inr j => simp [Cloning.Channels.amplify, Matrix.submatrix, encode, decode]
  | inr i =>
    cases j with
    | inl j => simp [Cloning.Channels.amplify, Matrix.submatrix, encode, decode]
    | inr j => simp [Cloning.Channels.amplify, Matrix.submatrix, encode, decode]

/-- Positivity of a channel follows from its one-dimensional amplification. -/
theorem channel_map_posSemidef (Φ : Cloning.Channels.MatrixChannel α β)
    {A : Matrix α α ℂ} (hA : A.PosSemidef) : (Φ.toFun A).PosSemidef := by
  have hin := hA.submatrix (Prod.snd : Fin 1 × α → α)
  have hout := (Φ.completely_positive 1 _ hin).submatrix (fun i : β => (0, i))
  simpa only [Cloning.Channels.amplify, Matrix.submatrix_apply] using hout

/-- A feasible fidelity block remains feasible after applying a channel.
Hermitian symmetry of the output block identifies its lower-left corner. -/
theorem channel_fidelity_block_posSemidef (Φ : Cloning.Channels.MatrixChannel α β)
    {A B X : Matrix α α ℂ}
    (h : (Matrix.fromBlocks A X Xᴴ B).PosSemidef) :
    (Matrix.fromBlocks (Φ.toFun A) (Φ.toFun X) (Φ.toFun X)ᴴ (Φ.toFun B)).PosSemidef := by
  have hp := channel_fromBlocks_posSemidef Φ h
  have hstar : (Φ.toFun X)ᴴ = Φ.toFun Xᴴ :=
    (Matrix.isHermitian_fromBlocks_iff.mp hp.isHermitian).2.1
  rwa [hstar]

/-- The channel's stated algebraic laws define an ordinary complex linear map. -/
def channelLinearMap (Φ : Cloning.Channels.MatrixChannel α β) :
    Matrix α α ℂ →ₗ[ℂ] Matrix β β ℂ where
  toFun := Φ.toFun
  map_add' := Φ.map_add
  map_smul' := Φ.map_smul

/-- Finite-dimensional matrix channels are continuous, as a consequence
of their linearity rather than an additional channel hypothesis. -/
theorem channel_continuous (Φ : Cloning.Channels.MatrixChannel α β) :
    Continuous Φ.toFun := (channelLinearMap Φ).continuous_of_finiteDimensional

/-- Compatibility with real scalar multiplication. -/
theorem channel_map_real_smul (Φ : Cloning.Channels.MatrixChannel α β)
    (ε : ℝ) (A : Matrix α α ℂ) : Φ.toFun (ε • A) = ε • Φ.toFun A :=
  (channelLinearMap Φ |>.restrictScalars ℝ).map_smul ε A

variable [DecidableEq α] [DecidableEq β]

omit [DecidableEq β] in
/-- The channel image of a positive-definite regularization is explicit;
the channel need not preserve the identity. -/
theorem channel_map_regularize (Φ : Cloning.Channels.MatrixChannel α β)
    (A : Matrix α α ℂ) (ε : ℝ) :
    Φ.toFun (Cloning.MatrixRegularization.regularize A ε) =
      Φ.toFun A + ε • Φ.toFun 1 := by
  rw [Cloning.MatrixRegularization.regularize, Φ.map_add, channel_map_real_smul]

/-- Fidelity data processing for positive-definite inputs. Complete
positivity transports an attaining block witness, and trace preservation
preserves its objective value. -/
theorem fidelity_data_processing_posDef (Φ : Cloning.Channels.MatrixChannel α β)
    {A B : Matrix α α ℂ} (hA : A.PosDef) (hB : B.PosDef) :
    fidelity A B ≤ fidelity (Φ.toFun A) (Φ.toFun B) := by
  obtain ⟨X, hblock, htrace⟩ := exists_fidelity_block_witness hA hB
  have h := trace_re_le_fidelity_of_block_posSemidef
    (channel_fidelity_block_posSemidef Φ hblock)
  rw [Φ.trace_preserving, htrace] at h
  exact h

/-- Data processing for actual root fidelity under an arbitrary finite
dimensional completely positive trace-preserving matrix channel. Positive
inputs may be singular and need not have unit trace. -/
theorem fidelity_data_processing (Φ : Cloning.Channels.MatrixChannel α β)
    {A B : Matrix α α ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    fidelity A B ≤ fidelity (Φ.toFun A) (Φ.toFun B) := by
  let ε : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
  have hε (k : ℕ) : 0 < ε k := by
    dsimp [ε]
    positivity
  let Aseq := fun k => Cloning.MatrixRegularization.regularize A (ε k)
  let Bseq := fun k => Cloning.MatrixRegularization.regularize B (ε k)
  have hAseq (k : ℕ) : (Aseq k).PosDef :=
    Cloning.MatrixRegularization.regularize_posDef hA (hε k)
  have hBseq (k : ℕ) : (Bseq k).PosDef :=
    Cloning.MatrixRegularization.regularize_posDef hB (hε k)
  have hAlim : Tendsto Aseq atTop (𝓝 A) :=
    (Cloning.MatrixRegularization.tendsto_regularize_zero A).comp
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hBlim : Tendsto Bseq atTop (𝓝 B) :=
    (Cloning.MatrixRegularization.tendsto_regularize_zero B).comp
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hin := tendsto_fidelity hA hB (fun k => (hAseq k).posSemidef)
    (fun k => (hBseq k).posSemidef) hAlim hBlim
  have hΦA := (channel_continuous Φ).continuousAt.tendsto.comp hAlim
  have hΦB := (channel_continuous Φ).continuousAt.tendsto.comp hBlim
  have hout := tendsto_fidelity (channel_map_posSemidef Φ hA)
    (channel_map_posSemidef Φ hB)
    (fun k => channel_map_posSemidef Φ (hAseq k).posSemidef)
    (fun k => channel_map_posSemidef Φ (hBseq k).posSemidef) hΦA hΦB
  apply le_of_tendsto_of_tendsto hin hout
  exact Filter.Eventually.of_forall (fun k =>
    fidelity_data_processing_posDef Φ (hAseq k) (hBseq k))

end Cloning.MatrixFidelity
