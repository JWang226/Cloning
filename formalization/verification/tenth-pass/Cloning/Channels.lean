import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Order

/-!
# Concrete finite-dimensional Kraus channels

Unlike the abstract fidelity interfaces elsewhere, these statements concern
actual complex matrices. Complete positivity is proved at every finite matrix
amplification. The remaining Cartan-specific input is the representation
theoretic construction of the Kraus operators and their normalization.
-/

open scoped BigOperators Matrix Kronecker ComplexOrder
open Matrix

noncomputable section

namespace Cloning.Channels

set_option autoImplicit false

variable {ι α β : Type*} [Fintype ι] [Fintype α] [Fintype β]

/-- Schrödinger-picture Kraus formula. -/
def krausMap (K : ι → Matrix β α ℂ) (X : Matrix α α ℂ) : Matrix β β ℂ :=
  ∑ i, K i * X * (K i)ᴴ

theorem krausMap_positive (K : ι → Matrix β α ℂ)
    {X : Matrix α α ℂ} (hX : X.PosSemidef) : (krausMap K X).PosSemidef := by
  apply Matrix.posSemidef_sum
  intro i _
  exact hX.mul_mul_conjTranspose_same (K i)

omit [Fintype β] in
theorem krausMap_add (K : ι → Matrix β α ℂ) (X Y : Matrix α α ℂ) :
    krausMap K (X + Y) = krausMap K X + krausMap K Y := by
  simp [krausMap, Matrix.mul_add, Matrix.add_mul, Finset.sum_add_distrib]

omit [Fintype β] in
theorem krausMap_smul (K : ι → Matrix β α ℂ) (c : ℂ) (X : Matrix α α ℂ) :
    krausMap K (c • X) = c • krausMap K X := by
  simp [krausMap, Matrix.mul_smul, Matrix.smul_mul, Finset.smul_sum]

/-- The dual identity ∑ K* K = I implies exact trace preservation. -/
theorem krausMap_trace [DecidableEq α] (K : ι → Matrix β α ℂ)
    (hK : ∑ i, (K i)ᴴ * K i = 1) (X : Matrix α α ℂ) :
    Matrix.trace (krausMap K X) = Matrix.trace X := by
  calc
    Matrix.trace (krausMap K X) = ∑ i, Matrix.trace ((K i)ᴴ * K i * X) := by
      simp only [krausMap, Matrix.trace_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc]
    _ = Matrix.trace ((∑ i, (K i)ᴴ * K i) * X) := by
      rw [Matrix.sum_mul, Matrix.trace_sum]
    _ = Matrix.trace X := by rw [hK, Matrix.one_mul]

/-- Applying a map to each ancilla matrix block: the actual matrix amplification. -/
def amplify {κ : Type*} (Φ : Matrix α α ℂ → Matrix β β ℂ)
    (X : Matrix (κ × α) (κ × α) ℂ) : Matrix (κ × β) (κ × β) ℂ :=
  fun a b => Φ (fun i j => X (a.1, i) (b.1, j)) a.2 b.2

omit [Fintype β] in
theorem amplify_krausMap {κ : Type*} [Fintype κ] [DecidableEq κ]
    (K : ι → Matrix β α ℂ) (X : Matrix (κ × α) (κ × α) ℂ) :
    amplify (krausMap K) X =
      krausMap (fun i => (1 : Matrix κ κ ℂ) ⊗ₖ K i) X := by
  ext ⟨a, i⟩ ⟨b, j⟩
  simp [amplify, krausMap, Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fintype.sum_prod_type, Matrix.one_apply, apply_ite]

/-- Every finite amplification preserves positive semidefinite matrices. -/
theorem krausMap_completely_positive {κ : Type*} [Fintype κ] [DecidableEq κ]
    (K : ι → Matrix β α ℂ) {X : Matrix (κ × α) (κ × α) ℂ}
    (hX : X.PosSemidef) : (amplify (krausMap K) X).PosSemidef := by
  rw [amplify_krausMap]
  exact krausMap_positive _ hX

/-- One transparent finite-dimensional channel structure. -/
structure MatrixChannel (α β : Type*) [Fintype α] [Fintype β] where
  toFun : Matrix α α ℂ → Matrix β β ℂ
  map_add : ∀ X Y, toFun (X + Y) = toFun X + toFun Y
  map_smul : ∀ (c : ℂ) X, toFun (c • X) = c • toFun X
  trace_preserving : ∀ X, Matrix.trace (toFun X) = Matrix.trace X
  completely_positive : ∀ (k : ℕ) (X : Matrix (Fin k × α) (Fin k × α) ℂ),
    X.PosSemidef → (amplify toFun X).PosSemidef

/-- A channel constructed from normalized Kraus matrices, with all laws proved. -/
def ofKraus [DecidableEq α] (K : ι → Matrix β α ℂ)
    (hK : ∑ i, (K i)ᴴ * K i = 1) : MatrixChannel α β where
  toFun := krausMap K
  map_add := krausMap_add K
  map_smul := krausMap_smul K
  trace_preserving := krausMap_trace K hK
  completely_positive := fun _ _ hX => krausMap_completely_positive K hX

end Cloning.Channels
