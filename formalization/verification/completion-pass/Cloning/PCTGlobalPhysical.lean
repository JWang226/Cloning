import Cloning.PCTGlobalWerner

/-! The state-independent full-environment physical PCT cloning channel. -/
noncomputable section
open scoped BigOperators Matrix InnerProductSpace ComplexOrder Topology
open Cloning.InfiniteTraceClass Cloning.PCT Cloning.PCTPurificationChannel
open Cloning.GeneralSymmetricOccupation Cloning.InfiniteFiniteCorner
open MeasureTheory Filter
namespace Cloning.PCTGlobal
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
variable {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]

/-- A frame determined solely by the physical alphabet and its dimension. -/
def fixedFrame {s : ℕ} (hcard : Fintype.card (A × A) = s + 1) :
    OrthonormalBasis (Fin (s + 1)) ℂ (Register (A × A)) :=
  coordinateFrame (Fintype.equivFinOfCardEq hcard).symm

/-- Full PCT cloning on all trace-class inputs. The frame and every channel
stage are fixed before the unknown state is supplied. -/
def channel {s : ℕ} (hcard : Fintype.card (A × A) = s + 1) (n r : ℕ) :
    QuantumChannel (Register (Fin n → A)) (Register (Fin (n + r) → A)) :=
  channelInFrame (fixedFrame hcard) n r

/-- The matrix recovered from a Haar output is an actual occupation matrix. -/
def recoveredMatrix {s : ℕ}
    (u : OrthonormalBasis (Fin (s + 1)) ℂ (Register (A × A))) (n : ℕ)
    (X : Matrix (Fin n → A) (Fin n → A) ℂ) :
    Matrix (Occupation n (s + 1)) (Occupation n (s + 1)) ℂ :=
  matrixOf (registerBasis _) ((sectorRecovery u n).toLinearMap
    (registerLiftCLM ((haarPurificationChannel n).toFun X))).1

theorem recoveredMatrix_lift {s : ℕ}
    (u : OrthonormalBasis (Fin (s + 1)) ℂ (Register (A × A))) (n : ℕ)
    (X : Matrix (Fin n → A) (Fin n → A) ℂ) :
    registerLiftCLM (recoveredMatrix u n X) =
      (sectorRecovery u n).toLinearMap (registerLiftCLM ((haarPurificationChannel n).toFun X)) :=
  registerLiftCLM_matrixOf _

theorem recoveredMatrix_embedding {s : ℕ}
    (u : OrthonormalBasis (Fin (s + 1)) ℂ (Register (A × A))) (n : ℕ)
    (X : Matrix (Fin n → A) (Fin n → A) ℂ) :
    matrixOf (registerBasis _)
      (operatorConjugation (groupedEmbedding u n).toContinuousLinearMap
        (registerLiftCLM (recoveredMatrix u n X)).1) =
      (haarPurificationChannel n).toFun X := by
  have he := sectorRecovery_purification_embedding u n X
  rw [← recoveredMatrix_lift u n X] at he
  have hm := congrArg (fun T : TraceClass (Register ((Fin n → A) × (Fin n → A))) =>
    matrixOf (registerBasis _) T.1) he
  exact hm.trans (matrixOf_ofMatrix (registerBasis _).orthonormal _)


/-- Exact channel-stage formula on arbitrary finite matrix inputs. -/
theorem channelInFrame_matrix_apply {s : ℕ}
    (u : OrthonormalBasis (Fin (s + 1)) ℂ (Register (A × A))) (n r : ℕ)
    (X : Matrix (Fin n → A) (Fin n → A) ℂ) :
    (channelInFrame u n r).toLinearMap (registerLiftCLM X) =
      partialTraceChannel.toLinearMap
        ((QuantumChannel.ofIsometry (regroup (n + r))).toLinearMap
          (conjugationLinearMap (physicalEmbedding u (n + r)).toContinuousLinearMap
            ((sectorChannel n r s).toLinearMap (registerLiftCLM (recoveredMatrix u n X))))) := by
  change partialTraceChannel.toLinearMap
    ((QuantumChannel.ofIsometry (regroup (n + r))).toLinearMap
      (conjugationLinearMap (physicalEmbedding u (n + r)).toContinuousLinearMap
        ((sectorChannel n r s).toLinearMap ((sectorRecovery u n).toLinearMap
          ((purificationChannel n).toLinearMap (registerLiftCLM X)))))) = _
  rw [purificationChannel_apply, recoveredMatrix_lift]

/-- Exact agreement of the global CPTP construction with the physical
Werner sandwich and partial trace for every complex input matrix. -/
theorem channelInFrame_physical {s : ℕ} (e : Fin (s + 1) ≃ A × A) (n r : ℕ)
    (X : Matrix (Fin n → A) (Fin n → A) ℂ) :
    (channelInFrame (coordinateFrame e) n r).toLinearMap (registerLiftCLM X) =
      physicalCloneTraceCLM n r s ((haarPurificationChannel n).toFun X) := by
  rw [channelInFrame_matrix_apply, sectorChannel_physical_sandwich,
    recoveredMatrix_embedding]
  rfl

/-- The fixed physical protocol equals the literal formula on arbitrary
inputs, not merely the tensor-power statistical model. -/
theorem channel_matrix_apply {s : ℕ} (hcard : Fintype.card (A × A) = s + 1) (n r : ℕ)
    (X : Matrix (Fin n → A) (Fin n → A) ℂ) :
    (channel hcard n r).toLinearMap (registerLiftCLM X) =
      physicalCloneTraceCLM n r s ((haarPurificationChannel n).toFun X) :=
  channelInFrame_physical (Fintype.equivFinOfCardEq hcard).symm n r X

/-- Coordinate-free coverage of all trace-class inputs on the finite system. -/
theorem channel_apply {s : ℕ} (hcard : Fintype.card (A × A) = s + 1) (n r : ℕ)
    (T : TraceClass (Register (Fin n → A))) :
    (channel hcard n r).toLinearMap T =
      physicalCloneTraceCLM n r s
        ((haarPurificationChannel n).toFun (matrixOf (registerBasis _) T.1)) := by
  have h := channel_matrix_apply hcard n r (matrixOf (registerBasis _) T.1)
  rwa [registerLiftCLM_matrixOf] at h

/-- Exact density-input action of the fully constructed, state-independent
CPTP purification-clone-trace channel. -/
theorem channel_tensorPower {s : ℕ} (hcard : Fintype.card (A × A) = s + 1)
    (n r : ℕ) (ρ : Cloning.MatrixFidelity.State A) :
    (channel hcard n r).toLinearMap (registerLiftCLM (tensorPower n ρ.matrix)) =
      reducedWernerOutput hcard (canonicalPurification ρ.matrix)
        (canonicalPurification_norm ρ) (inputSlots n (n + r) (Nat.le_add_right n r)) := by
  rw [channel_matrix_apply, physical_pct_eq_reducedWerner]

/-- The physical full-environment PCT channel, fixed independently of the
unknown density state, has the actual Gaussian product-mixture limit. -/
theorem channel_gaussian_product_mixture {s : ℕ} (hs : 1 ≤ s)
    (hcard : Fintype.card (A × A) = s + 1) (ρ : Cloning.MatrixFidelity.State A)
    (r : ℕ → ℕ) {γ : ℝ} (hγ : 1 < γ)
    (h : Tendsto (fun n ↦ ((n + r n : ℕ) : ℝ) / n) atTop (𝓝 γ)) :
    ∃ u : OrthonormalBasis (Fin (s + 1)) ℂ (Register (A × A)),
      u 0 = canonicalPurification ρ.matrix ∧
      Tendsto (fun n => ‖(channel hcard n (r n)).toLinearMap
        (registerLiftCLM (tensorPower n ρ.matrix)) -
        ∫ z, matrixTensorPower
          (reducedDensityMatrix (frameParticle u z (n + r n))) (n + r n)
          ∂MultimodeCoherentGaussianMixture.gaussianProductMeasure
            (fun _ : Fin s => γ - 1)‖) atTop (𝓝 0) := by
  simpa only [channel_matrix_apply] using
    physical_pct_gaussian_product_mixture hs hcard ρ r hγ h

end Cloning.PCTGlobal
