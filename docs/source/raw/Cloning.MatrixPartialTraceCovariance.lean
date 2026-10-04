import Cloning.Compression

/-!
# Covariance of the concrete finite-dimensional partial trace

The spectator unitary cancels under the partial trace. Consequently an
intertwining isometry has a covariant range projection, whose partial trace
commutes with the input representation. These are matrix identities and do not
assume the dimension balance that Schur's lemma will subsequently provide.
-/

noncomputable section

open scoped Matrix Kronecker

namespace Cloning.Compression

set_option linter.unusedSectionVars false

variable {A B C : Type*}
variable [Fintype A] [Fintype B] [Fintype C]
variable [DecidableEq A] [DecidableEq B] [DecidableEq C]

/-- Partial trace is equivariant under tensor conjugation; only the spectator
factor needs to be unitary. -/
theorem partialTrace_tensor_conjugation (U : Matrix A A ℂ) (W : Matrix B B ℂ)
    (X : Matrix (A × B) (A × B) ℂ) (hW : W.conjTranspose * W = 1) :
    partialTrace ((U ⊗ₖ W) * X * (U ⊗ₖ W).conjTranspose) =
      U * partialTrace X * U.conjTranspose := by
  apply Matrix.ext_iff_trace_mul_left.mpr
  intro T
  have htest : (U ⊗ₖ W).conjTranspose * (T ⊗ₖ (1 : Matrix B B ℂ)) *
      (U ⊗ₖ W) = (U.conjTranspose * T * U) ⊗ₖ (1 : Matrix B B ℂ) := by
    rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
      ← Matrix.mul_kronecker_mul]
    simp only [Matrix.mul_one, hW]
  calc
    _ = Matrix.trace ((T ⊗ₖ (1 : Matrix B B ℂ)) *
        ((U ⊗ₖ W) * X * (U ⊗ₖ W).conjTranspose)) :=
      (trace_tensor_pairing T _).symm
    _ = Matrix.trace (((U ⊗ₖ W).conjTranspose *
        (T ⊗ₖ (1 : Matrix B B ℂ)) * (U ⊗ₖ W)) * X) := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.trace_mul_cycle]
      simp only [Matrix.mul_assoc]
    _ = Matrix.trace (((U.conjTranspose * T * U) ⊗ₖ (1 : Matrix B B ℂ)) * X) := by
      rw [htest]
    _ = Matrix.trace ((U.conjTranspose * T * U) * partialTrace X) :=
      trace_tensor_pairing _ X
    _ = Matrix.trace (T * (U * partialTrace X * U.conjTranspose)) := by
      simp only [Matrix.mul_assoc]
      rw [Matrix.trace_mul_comm U.conjTranspose]
      simp only [Matrix.mul_assoc]

/-- Tensor covariance of the range operator follows from a unitary intertwiner.
No isometry assumption on `V` is required for this identity. -/
theorem intertwiner_range_conjugation (U : Matrix A A ℂ) (W : Matrix B B ℂ)
    (Z : Matrix C C ℂ) (V : Matrix (A × B) C ℂ)
    (hZ : Z * Z.conjTranspose = 1)
    (hintertwine : (U ⊗ₖ W) * V = V * Z) :
    (U ⊗ₖ W) * (V * V.conjTranspose) * (U ⊗ₖ W).conjTranspose =
      V * V.conjTranspose := by
  calc
    _ = ((U ⊗ₖ W) * V) * ((U ⊗ₖ W) * V).conjTranspose := by
      simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = (V * Z) * (V * Z).conjTranspose := by rw [hintertwine]
    _ = V * (Z * Z.conjTranspose) * V.conjTranspose := by
      simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = _ := by rw [hZ, Matrix.mul_one]

/-- The partially traced range operator is invariant under the first unitary. -/
theorem partialTrace_intertwiner_invariant (U : Matrix A A ℂ) (W : Matrix B B ℂ)
    (Z : Matrix C C ℂ) (V : Matrix (A × B) C ℂ)
    (hW : W.conjTranspose * W = 1) (hZ : Z * Z.conjTranspose = 1)
    (hintertwine : (U ⊗ₖ W) * V = V * Z) :
    U * partialTrace (V * V.conjTranspose) * U.conjTranspose =
      partialTrace (V * V.conjTranspose) := by
  rw [← partialTrace_tensor_conjugation U W _ hW,
    intertwiner_range_conjugation U W Z V hZ hintertwine]

/-- With a unitary first factor, invariance gives the commutation premise of
Schur's lemma. -/
theorem partialTrace_intertwiner_commutes (U : Matrix A A ℂ) (W : Matrix B B ℂ)
    (Z : Matrix C C ℂ) (V : Matrix (A × B) C ℂ)
    (hU : U.conjTranspose * U = 1) (hW : W.conjTranspose * W = 1)
    (hZ : Z * Z.conjTranspose = 1)
    (hintertwine : (U ⊗ₖ W) * V = V * Z) :
    partialTrace (V * V.conjTranspose) * U = U * partialTrace (V * V.conjTranspose) := by
  have h := congrArg (fun X => X * U)
    (partialTrace_intertwiner_invariant U W Z V hW hZ hintertwine)
  simpa only [Matrix.mul_assoc, hU, Matrix.mul_one] using h.symm

end Cloning.Compression
