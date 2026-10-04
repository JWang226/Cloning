import Cloning.TensorSchurHaarOrthogonality

/-! Actual Schur Haar second moments after arbitrary orthonormal-column
compressions. The ambient sector dimension remains the normalization. -/
noncomputable section
open scoped BigOperators Matrix Topology Matrix.Norms.L2Operator
open MeasureTheory
namespace Cloning.TensorLie
open Cloning.PhysicalFlatConverse Cloning.PCTPurificationChannel
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

def matrixBimultCLM {I J K L : Type*} [Fintype I] [Fintype J] [Fintype K] [Fintype L]
    (A : Matrix I J ℂ) (B : Matrix K L ℂ) : Matrix J K ℂ →L[ℂ] Matrix I L ℂ :=
  LinearMap.toContinuousLinearMap {
    toFun M := A*M*B
    map_add' _ _ := by simp only [Matrix.mul_add,Matrix.add_mul]
    map_smul' _ _ := by simp only [Matrix.mul_smul,Matrix.smul_mul,RingHom.id_apply] }

variable {d : ℕ} [Nonempty (Fin d)]
variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

def compressedPartitionAction (mu : Fin d → ℕ) (hmu : Antitone mu)
    (Q : Matrix (PartitionIndex mu hmu) I ℂ)
    (U : unitary (Matrix (Fin d) (Fin d) ℂ)) : Matrix I I ℂ :=
  Qᴴ * partitionActionMatrix mu hmu U * Q

theorem compressedPartition_sandwich (mu nu : Fin d → ℕ) (hmu : Antitone mu) (hnu : Antitone nu)
    (Q : Matrix (PartitionIndex mu hmu) I ℂ) (S : Matrix (PartitionIndex nu hnu) J ℂ)
    (M : Matrix I J ℂ) (U : unitary (Matrix (Fin d) (Fin d) ℂ)) :
    compressedPartitionAction mu hmu Q U * M * (compressedPartitionAction nu hnu S U)ᴴ =
      Qᴴ * (partitionActionMatrix mu hmu U * (Q*M*Sᴴ) * (partitionActionMatrix nu hnu U)ᴴ) * S := by
  simp only [compressedPartitionAction,Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose,
    Matrix.mul_assoc]

theorem integrable_compressedPartition_sandwich (mu nu : Fin d → ℕ)
    (hmu : Antitone mu) (hnu : Antitone nu)
    (Q : Matrix (PartitionIndex mu hmu) I ℂ) (S : Matrix (PartitionIndex nu hnu) J ℂ)
    (M : Matrix I J ℂ) :
    Integrable (fun U => compressedPartitionAction mu hmu Q U * M *
      (compressedPartitionAction nu hnu S U)ᴴ) unitaryHaar := by
  simpa only [compressedPartition_sandwich,matrixBimultCLM,LinearMap.coe_toContinuousLinearMap,
    LinearMap.coe_mk,AddHom.coe_mk] using
    (matrixBimultCLM Qᴴ S).integrable_comp (integrable_mixedSandwich mu nu hmu hnu (Q*M*Sᴴ))

theorem integral_compressedPartition_sandwich (mu nu : Fin d → ℕ)
    (hmu : Antitone mu) (hnu : Antitone nu)
    (Q : Matrix (PartitionIndex mu hmu) I ℂ) (S : Matrix (PartitionIndex nu hnu) J ℂ)
    (M : Matrix I J ℂ) :
    (∫ U, compressedPartitionAction mu hmu Q U * M *
      (compressedPartitionAction nu hnu S U)ᴴ ∂unitaryHaar) =
        Qᴴ * mixedTwirl mu nu hmu hnu (Q*M*Sᴴ) * S := by
  have hh := (matrixBimultCLM Qᴴ S).integral_comp_comm
    (integrable_mixedSandwich mu nu hmu hnu (Q*M*Sᴴ))
  change (∫ U : unitary (Matrix (Fin d) (Fin d) ℂ),
    Qᴴ * (partitionActionMatrix mu hmu U * (Q*M*Sᴴ) * (partitionActionMatrix nu hnu U)ᴴ) * S ∂unitaryHaar) =
      Qᴴ * mixedTwirl mu nu hmu hnu (Q*M*Sᴴ) * S at hh
  simpa only [compressedPartition_sandwich] using hh

theorem integral_compressedPartition_sandwich_ne (mu nu : Fin d → ℕ)
    (hmu : Antitone mu) (hnu : Antitone nu) (hne : mu ≠ nu)
    (Q : Matrix (PartitionIndex mu hmu) I ℂ) (S : Matrix (PartitionIndex nu hnu) J ℂ)
    (M : Matrix I J ℂ) :
    (∫ U, compressedPartitionAction mu hmu Q U * M *
      (compressedPartitionAction nu hnu S U)ᴴ ∂unitaryHaar) = 0 := by
  rw [integral_compressedPartition_sandwich,mixedTwirl_eq_zero mu nu hmu hnu hne,
    Matrix.mul_zero,Matrix.zero_mul]

/-- The normalization is the ambient physical sector dimension, even after
compressing to a smaller orthonormal frame. -/
theorem integral_compressedPartition_sandwich_same (mu : Fin d → ℕ) (hmu : Antitone mu)
    (Q : Matrix (PartitionIndex mu hmu) I ℂ) (hQ : Qᴴ*Q=1) (M : Matrix I I ℂ) :
    (∫ U, compressedPartitionAction mu hmu Q U * M *
      (compressedPartitionAction mu hmu Q U)ᴴ ∂unitaryHaar) =
        (M.trace/(partitionDimension mu hmu : ℂ)) • (1 : Matrix I I ℂ) := by
  rw [integral_compressedPartition_sandwich]
  change Qᴴ * partitionTwirl mu hmu (Q*M*Qᴴ) * Q = _
  rw [partitionTwirl_eq]
  have ht : (Q*M*Qᴴ).trace=M.trace := by
    rw [Matrix.trace_mul_comm,← Matrix.mul_assoc,hQ,Matrix.one_mul]
  rw [ht,Matrix.mul_smul,Matrix.smul_mul,Matrix.mul_one,hQ]

theorem integral_compressedPartition_coefficients_ne (mu nu : Fin d → ℕ)
    (hmu : Antitone mu) (hnu : Antitone nu) (hne : mu ≠ nu)
    (Q : Matrix (PartitionIndex mu hmu) I ℂ) (S : Matrix (PartitionIndex nu hnu) J ℂ)
    (i j : I) (k l : J) :
    (∫ U, compressedPartitionAction mu hmu Q U i j *
      star (compressedPartitionAction nu hnu S U k l) ∂unitaryHaar) = 0 := by
  have hh := (matrixEntryCLM i k).integral_comp_comm
    (integrable_compressedPartition_sandwich mu nu hmu hnu Q S (Matrix.single j l (1:ℂ)))
  change (∫ U, (compressedPartitionAction mu hmu Q U * Matrix.single j l (1:ℂ) *
      (compressedPartitionAction nu hnu S U)ᴴ) i k ∂unitaryHaar) =
    (∫ U, compressedPartitionAction mu hmu Q U * Matrix.single j l (1:ℂ) *
      (compressedPartitionAction nu hnu S U)ᴴ ∂unitaryHaar) i k at hh
  simpa only [matrixEntry_sandwich_single,integral_compressedPartition_sandwich_ne mu nu hmu hnu hne,
    Matrix.zero_apply] using hh

theorem integral_compressedPartition_coefficients_same (mu : Fin d → ℕ) (hmu : Antitone mu)
    (Q : Matrix (PartitionIndex mu hmu) I ℂ) (hQ : Qᴴ*Q=1) (i j k l : I) :
    (∫ U, compressedPartitionAction mu hmu Q U i j *
      star (compressedPartitionAction mu hmu Q U k l) ∂unitaryHaar) =
        if i=k ∧ j=l then (partitionDimension mu hmu : ℂ)⁻¹ else 0 := by
  have hh := (matrixEntryCLM i k).integral_comp_comm
    (integrable_compressedPartition_sandwich mu mu hmu hmu Q Q (Matrix.single j l (1:ℂ)))
  change (∫ U, (compressedPartitionAction mu hmu Q U * Matrix.single j l (1:ℂ) *
      (compressedPartitionAction mu hmu Q U)ᴴ) i k ∂unitaryHaar) =
    (∫ U, compressedPartitionAction mu hmu Q U * Matrix.single j l (1:ℂ) *
      (compressedPartitionAction mu hmu Q U)ᴴ ∂unitaryHaar) i k at hh
  rw [integral_compressedPartition_sandwich_same mu hmu Q hQ] at hh
  simp only [matrixEntry_sandwich_single] at hh
  rw [hh]
  by_cases hik : i=k <;> by_cases hjl : j=l
  · subst k; subst l
    simp [Matrix.trace_single_eq_same]
  · simp [hik,hjl,Matrix.trace_single_eq_of_ne j l (1:ℂ) hjl]
  · simp [hik,hjl]
  · simp [hik,hjl]

end Cloning.TensorLie
