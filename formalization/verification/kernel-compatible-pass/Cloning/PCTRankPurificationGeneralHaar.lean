import Cloning.PCTRankPurificationGeneralPurification
import Cloning.PCTRankPurificationGeneralEmbedding

/-! The actual rectangular purifier is the Haar mixture associated with
any chosen purification of the input. The Haar mixture is independent of
that choice even for singular reduced states. -/
noncomputable section
open scoped BigOperators Matrix Kronecker ComplexOrder InnerProductSpace
open MeasureTheory
namespace Cloning.PCTRankPurification
open Cloning.PCT Cloning.PCTPhysicalState Cloning.PCTRankAdapted Cloning.InfiniteTraceClass
open Cloning.PCTPurificationChannel Cloning.FiniteKrausLift Cloning.PCTReducedGaussian
open Cloning.PCTRankGlobal
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
variable {A E : Type*} [Fintype A] [Fintype E] [DecidableEq A] [DecidableEq E] [Nonempty E]

theorem environmentRotate_purificationEnvironment_mul
    (U V : unitary (Matrix E E ℂ)) (ψ : Register (A×E)) :
    environmentRotate (purificationEnvironment U) (environmentRotate (purificationEnvironment V) ψ)=
      environmentRotate (purificationEnvironment (V*U)) ψ := by
  ext ⟨a,b⟩
  simp only [environmentRotate_apply,purificationEnvironment,unitaryRegister_apply,
    Matrix.UnitaryGroup.transpose,Matrix.transpose_apply,environmentRow_apply,
    Submonoid.coe_mul,Matrix.mul_apply,Finset.mul_sum,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro d _
  ring

def purificationHaar (n : ℕ) (ψ : Register (A×E)) :
    TraceClass (Register ((Fin n→A)×(Fin n→E))) :=
  ∫U : unitary (Matrix E E ℂ),tensorProjector n
    (environmentRotate (purificationEnvironment U) ψ) ∂unitaryHaar

theorem purificationHaar_rotate (n : ℕ) (V : unitary (Matrix E E ℂ))
    (ψ : Register (A×E)) :
    purificationHaar n (environmentRotate (purificationEnvironment V) ψ)=purificationHaar n ψ := by
  unfold purificationHaar
  simp_rw [environmentRotate_purificationEnvironment_mul]
  exact integral_mul_left_eq_self (μ:=unitaryHaar)
    (fun U : unitary (Matrix E E ℂ)=>tensorProjector n
      (environmentRotate (purificationEnvironment U) ψ)) V

/-- The Haar average depends only on the literal reduced density matrix. -/
theorem purificationHaar_eq_of_reduced_eq (n : ℕ) (ψ φ : Register (A×E))
    (h : reducedDensityMatrix ψ=reducedDensityMatrix φ) :
    purificationHaar n ψ=purificationHaar n φ := by
  obtain ⟨V,hV⟩ := exists_environment_unitary_of_reduced_eq ψ φ h
  rw [← hV,purificationHaar_rotate]

variable {r : ℕ} [NeZero r]
local instance generalHaarAmbientNeZero (k : ℕ) : NeZero (r+k) := ⟨by have := NeZero.ne r; omega⟩

/-- Exact random-purification action for any purification in the prescribed
r-dimensional environment. The one channel always uses the coordinate J0. -/
theorem purificationChannel_of_purification (k n : ℕ)
    (b0 : (Fin n→Fin (r+k))×(Fin n→Fin r))
    (ρ : Cloning.MatrixFidelity.State (Fin (r+k)))
    (ψ : Register (Fin (r+k)×Fin r)) (hψ : reducedDensityMatrix ψ=ρ.matrix) :
    (PCTRankGlobal.purificationChannel n (Cloning.TensorLie.coordinateInclusionMatrix r k) b0).toLinearMap
      (tensorState ρ n).1=purificationHaar n ψ := by
  have hrank : ρ.matrix.rank≤r := by
    rw [← hψ]
    change ((show Matrix (Fin (r+k)) (Fin r) ℂ from fun a b=>ψ (a,b)) * (Matrix.conjTranspose (fun a b=>ψ (a,b)))).rank≤r
    exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_le_width _)
  obtain ⟨J,hJ,σ,hρ⟩ := exists_embedded_density r k ρ hrank
  subst ρ
  let φ := matrixRegister (J⊗ₖ(1 : Matrix (Fin r) (Fin r) ℂ)) (canonicalPurification σ.matrix)
  have hφ : reducedDensityMatrix φ=reducedDensityMatrix ψ := by
    rw [reducedDensityMatrix_system,canonicalPurification_reduced _ σ.positive,hψ]
    rfl
  rw [← purificationHaar_eq_of_reduced_eq n φ ψ hφ]
  change (PCTRankGlobal.purificationChannel n (Cloning.TensorLie.coordinateInclusionMatrix r k) b0).toLinearMap
    (registerLiftCLM (tensorPower n (J*σ.matrix*Jᴴ)))=_
  rw [PCTRankGlobal.purificationChannel_matrix,rankPurificationChannel_embedded_positive n k b0 J hJ σ.matrix σ.positive,
    ← PCTRankGlobal.embeddedHaarCLM_apply,PCTRankGlobal.embeddedHaar_physical]
  rfl

/-- The randomizing Haar integral disappears after the fixed Werner and
partial-trace stages, for every chosen purification of every rank-bound state. -/
theorem channel_of_purification {s : ℕ} (k n t : ℕ)
    (hcard : Fintype.card (Fin (r+k)×Fin r)=s+1)
    (b0 : (Fin n→Fin (r+k))×(Fin n→Fin r))
    (ρ : Cloning.MatrixFidelity.State (Fin (r+k)))
    (ψ : Register (Fin (r+k)×Fin r)) (hψnorm : ‖ψ‖=1)
    (hψ : reducedDensityMatrix ψ=ρ.matrix) :
    (PCTRankGlobal.channel hcard n t (Cloning.TensorLie.coordinateInclusionMatrix r k) b0).toLinearMap
      (tensorState ρ n).1=
      reducedWernerOutput hcard ψ hψnorm
        (Cloning.GeneralSymmetricOccupation.inputSlots n (n+t) (Nat.le_add_right n t)) := by
  have hrank : ρ.matrix.rank≤r := by
    rw [← hψ]
    change ((show Matrix (Fin (r+k)) (Fin r) ℂ from fun a b=>ψ (a,b)) * (Matrix.conjTranspose (fun a b=>ψ (a,b)))).rank≤r
    exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_le_width _)
  obtain ⟨J,hJ,σ,hρ⟩ := exists_embedded_density r k ρ hrank
  subst ρ
  rw [channel_embeddedState]
  let φ := matrixRegister (J⊗ₖ(1 : Matrix (Fin r) (Fin r) ℂ)) (canonicalPurification σ.matrix)
  have hφ : reducedDensityMatrix φ=reducedDensityMatrix ψ := by
    rw [reducedDensityMatrix_system,canonicalPurification_reduced _ σ.positive,hψ]
    rfl
  obtain ⟨W,hW⟩ := exists_environment_isometry_of_reduced_eq φ ψ hφ
  subst ψ
  exact (reducedWernerOutput_environment_invariant hcard φ
    ((matrixRegister_norm _ (systemEmbedding_isometry J hJ) _).trans (canonicalPurification_norm σ)) W _).symm

end Cloning.PCTRankPurification
