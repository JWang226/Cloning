import Cloning.PCTRankAdaptedTensor

/-! Exact compression of the physical Werner sandwich through a rectangular
one-particle isometry. The spectator identities are full identities and the
symmetric projector intertwining is derived from tensor permutations. -/
noncomputable section
open scoped BigOperators InnerProductSpace Matrix ComplexOrder
namespace Cloning.PCTRankAdapted
open Cloning.PCT Cloning.PCTPurificationChannel Cloning.FiniteKrausLift
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000
set_option linter.unusedSectionVars false
variable {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
  [DecidableEq A] [DecidableEq B] [DecidableEq C]

def slotTensor {L : ℕ} (M : Fin L → Matrix A B ℂ) :
    Matrix (Fin L → A) (Fin L → B) ℂ := fun a b => ∏ i, M i (a i) (b i)

theorem slotTensor_mul {L : ℕ} (M : Fin L → Matrix A B ℂ)
    (N : Fin L → Matrix B C ℂ) :
    slotTensor (fun i => M i * N i) = slotTensor M * slotTensor N := by
  ext a c
  simp only [slotTensor, Matrix.mul_apply, ← Finset.prod_mul_distrib]
  exact Fintype.prod_sum (fun i b => M i (a i) b * N i b (c i))

theorem slotTensor_star {L : ℕ} (M : Fin L → Matrix A B ℂ) :
    slotTensor (fun i => (M i)ᴴ) = (slotTensor M)ᴴ := by
  ext a b
  simp [slotTensor, Matrix.conjTranspose_apply]

theorem pureSlotsMatrix_eq_slotTensor {L : ℕ} (ψ : Register A) (S : Finset (Fin L)) :
    pureSlotsMatrix ψ S = slotTensor (fun i =>
      if i ∈ S then Matrix.vecMulVec (fun a => ψ a) (star (fun a => ψ a)) else 1) := by
  ext a b
  simp only [pureSlotsMatrix, slotTensor]
  apply Finset.prod_congr rfl
  intro i _
  split_ifs <;> simp_all [Matrix.vecMulVec_apply, Matrix.one_apply]

theorem pureMatrix_map (J : Matrix B A ℂ) (ψ : Register A) :
    Matrix.vecMulVec (fun b => matrixRegister J ψ b) (star (fun b => matrixRegister J ψ b)) =
      J * Matrix.vecMulVec (fun a => ψ a) (star (fun a => ψ a)) * Jᴴ := by
  rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.vecMul_conjTranspose, star_star]
  rfl

/-- Isometric compression of every slot factor, including the unnormalised
identity on spectator slots. -/
theorem pureSlotsMatrix_compression {L : ℕ} (J : Matrix B A ℂ) (hJ : Jᴴ * J = 1)
    (ψ : Register A) (S : Finset (Fin L)) :
    (tensorPower L J)ᴴ * pureSlotsMatrix (matrixRegister J ψ) S * tensorPower L J =
      pureSlotsMatrix ψ S := by
  rw [pureSlotsMatrix_eq_slotTensor, pureSlotsMatrix_eq_slotTensor]
  change (slotTensor (fun _ : Fin L => J))ᴴ * _ * slotTensor (fun _ : Fin L => J) = _
  rw [← slotTensor_star, ← slotTensor_mul, ← slotTensor_mul]
  congr 1
  funext i
  split_ifs with hi
  · rw [pureMatrix_map, Cloning.Compression.isometry_compress J _ hJ]
  · simp [hJ]

theorem pureSlotsOperator_eq_matrixRegister {L : ℕ} (ψ : Register A)
    (S : Finset (Fin L)) : pureSlotsOperator ψ S = matrixRegister (pureSlotsMatrix ψ S) :=
  registerLiftCLM_operator _

theorem pureSlotsOperator_compression {L : ℕ} (J : Matrix B A ℂ) (hJ : Jᴴ * J = 1)
    (ψ : Register A) (S : Finset (Fin L)) :
    (tensorMap L J).adjoint.comp ((pureSlotsOperator (matrixRegister J ψ) S).comp
      (tensorMap L J)) = pureSlotsOperator ψ S := by
  rw [pureSlotsOperator_eq_matrixRegister, pureSlotsOperator_eq_matrixRegister]
  change (matrixRegister (tensorPower L J)).adjoint.comp
    ((matrixRegister _).comp (matrixRegister (tensorPower L J))) = _
  rw [← matrixRegister_conjTranspose, ← matrixRegister_mul, ← matrixRegister_mul,
    ← Matrix.mul_assoc, pureSlotsMatrix_compression J hJ]

/-- Exact unscaled physical symmetric-sandwich compression. -/
theorem wernerSandwich_compression {L : ℕ} (J : Matrix B A ℂ) (hJ : Jᴴ * J = 1)
    (ψ : Register A) (S : Finset (Fin L)) :
    (tensorMap L J).adjoint.comp
      ((physicalProjector L * pureSlotsOperator (matrixRegister J ψ) S *
        physicalProjector L).comp (tensorMap L J)) =
      physicalProjector L * pureSlotsOperator ψ S * physicalProjector L := by
  apply ContinuousLinearMap.ext
  intro x
  change (tensorMap L J).adjoint (physicalProjector L
    (pureSlotsOperator (matrixRegister J ψ) S (physicalProjector L (tensorMap L J x)))) = _
  rw [tensorMap_physicalProjector, tensorMap_adjoint,
    ← tensorMap_physicalProjector]
  rw [← tensorMap_adjoint L J]
  change physicalProjector L (((tensorMap L J).adjoint.comp
    ((pureSlotsOperator (matrixRegister J ψ) S).comp (tensorMap L J)))
      (physicalProjector L x)) = _
  rw [pureSlotsOperator_compression J hJ]
  rfl

end Cloning.PCTRankAdapted
