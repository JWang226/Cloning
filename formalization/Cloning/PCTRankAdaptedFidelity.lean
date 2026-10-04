import Cloning.PCTRankAdaptedReduced
import Cloning.InfiniteFidelityHilbertSum
import Cloning.MatrixFidelityEmbedding
import Cloning.MatrixFidelityScaling

/-! Target-support compression and its exact root-fidelity factor. -/
noncomputable section
open scoped BigOperators InnerProductSpace Matrix MatrixOrder ComplexOrder
namespace Cloning.PCTRankAdapted
open Cloning.PCT Cloning.PCTPurificationChannel Cloning.FiniteKrausLift
open Cloning.InfiniteTraceClass Cloning.InfiniteFiniteCorner Cloning.Hybrid
open Cloning.InfiniteFidelityHilbertSum
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000
set_option linter.unusedSectionVars false
variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

/-- Fidelity to an embedded target depends exactly on compression to its
support; no assumption that the first state is supported there is imposed. -/
theorem matrix_fidelity_compression (J : Matrix B A ℂ) (hJ : Jᴴ * J = 1)
    (X : Matrix B B ℂ) (Y : Matrix A A ℂ) (hX : X.PosSemidef) (hY : Y.PosSemidef) :
    Cloning.MatrixFidelity.fidelity X (J * Y * Jᴴ) =
      Cloning.MatrixFidelity.fidelity (Jᴴ * X * J) Y := by
  unfold Cloning.MatrixFidelity.fidelity
  rw [Cloning.MatrixFidelity.sqrt_isometric_embedding J hJ hY]
  have he : (J * CFC.sqrt Y * Jᴴ) * X * (J * CFC.sqrt Y * Jᴴ) =
      J * (CFC.sqrt Y * (Jᴴ * X * J) * CFC.sqrt Y) * Jᴴ := by
    simp only [Matrix.mul_assoc]
  rw [he, Cloning.MatrixFidelity.sqrt_isometric_embedding J hJ
    (Cloning.MatrixFidelity.sandwich_posSemidef (hX.conjTranspose_mul_mul_same J) Y)]
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hJ, Matrix.one_mul]

theorem matrixOf_conjugation (J : Matrix B A ℂ) (X : TraceClass (Register A)) :
    matrixOf (registerBasis B) (conjugationLinearMap (matrixRegister J) X).1 =
      J * matrixOf (registerBasis A) X.1 * Jᴴ := by
  have h := congrArg (fun T : TraceClass (Register B) => matrixOf (registerBasis B) T.1)
    (conjugation_matrixRegister J (matrixOf (registerBasis A) X.1))
  rw [Cloning.PCTGlobal.registerLiftCLM_matrixOf X] at h
  exact h.trans (matrixOf_ofMatrix (registerBasis B).orthonormal _)

theorem matrixOf_real_smul (c : ℝ) (X : TraceClass (Register A)) :
    matrixOf (registerBasis A) ((c : ℂ) • X).1 = c • matrixOf (registerBasis A) X.1 := by
  ext a b
  change ⟪registerBasis A a, (c : ℂ) • (X.1 (registerBasis A b))⟫_ℂ =
    c • ⟪registerBasis A a, X.1 (registerBasis A b)⟫_ℂ
  simp only [inner_smul_right, Complex.real_smul]

/-- General finite physical support-factor identity used after the exact
Werner and partial-trace compression theorems. -/
theorem rootFidelity_of_compression (J : Matrix B A ℂ) (hJ : Jᴴ * J = 1)
    (X : PositiveTraceClass (Register B)) (Z Y : PositiveTraceClass (Register A))
    (c : ℝ) (hc : 0 ≤ c)
    (hcomp : conjugationLinearMap (matrixRegister J).adjoint X.1 = (c : ℂ) • Z.1) :
    X.rootFidelity (Y.map (QuantumChannel.ofIsometry (matrixIsometry J hJ)).toPositiveTracePreservingMap) =
      Real.sqrt c * Z.rootFidelity Y := by
  rw [← rootFidelity_matrixOf_basis (registerBasis B).toOrthonormalBasis,
    ← rootFidelity_matrixOf_basis (registerBasis A).toOrthonormalBasis Z Y]
  simp only [HilbertBasis.coe_toOrthonormalBasis]
  have hy : matrixOf (registerBasis B)
      (Y.map (QuantumChannel.ofIsometry (matrixIsometry J hJ)).toPositiveTracePreservingMap).1.1 =
      J * matrixOf (registerBasis A) Y.1.1 * Jᴴ := matrixOf_conjugation J Y.1
  rw [hy, matrix_fidelity_compression J hJ _ _
    (matrixOf_posSemidef _ X.2) (matrixOf_posSemidef _ Y.2)]
  have hM := congrArg (fun T : TraceClass (Register A) => matrixOf (registerBasis A) T.1) hcomp
  dsimp only at hM
  rw [← matrixRegister_conjTranspose, matrixOf_conjugation, Matrix.conjTranspose_conjTranspose,
    matrixOf_real_smul] at hM
  rw [hM, Cloning.MatrixFidelity.fidelity_smul_left c _ _ hc (matrixOf_posSemidef _ Z.2)]

end Cloning.PCTRankAdapted
