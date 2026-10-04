import Cloning.PCTRankGlobalChannel
import Cloning.PCTRankAdaptedProduct

/-! Rectangular system embeddings commute with literal purification tensor powers
and with every environment rotation. -/
noncomputable section
open scoped BigOperators Matrix Kronecker InnerProductSpace ComplexOrder Topology Matrix.Norms.L2Operator
open Cloning.InfiniteTraceClass Cloning.PCT Cloning.PCTPurificationChannel
open Cloning.GeneralSymmetricOccupation Cloning.InfiniteFiniteCorner
open Cloning.FiniteKrausLift Cloning.PCTRankAdapted MeasureTheory
namespace Cloning.PCTRankGlobal
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
variable {A B E : Type*} [Fintype A] [DecidableEq A]
  [Fintype B] [DecidableEq B] [Fintype E] [DecidableEq E]

/-- The actual one-system matrix action leaves the environment coordinate fixed. -/
theorem matrixRegister_system_apply (J : Matrix A B ℂ) (ψ : Register (B × E)) (a : A) (e : E) :
    matrixRegister (J ⊗ₖ (1 : Matrix E E ℂ)) ψ (a,e) = ∑ b, J a b * ψ (b,e) := by
  simp [matrixRegister_apply, Fintype.sum_prod_type, Matrix.kroneckerMap_apply, Matrix.one_apply]

theorem environmentRow_system (J : Matrix A B ℂ) (ψ : Register (B × E)) (a : A) :
    environmentRow (matrixRegister (J ⊗ₖ (1 : Matrix E E ℂ)) ψ) a =
      ∑ b, J a b • environmentRow ψ b := by
  ext e
  simp only [environmentRow_apply, matrixRegister_system_apply,
    lp.coeFn_sum, Finset.sum_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]

theorem environmentRotate_system (J : Matrix A B ℂ) (ψ : Register (B × E))
    (W : Register E →ₗᵢ[ℂ] Register E) :
    matrixRegister (J ⊗ₖ (1 : Matrix E E ℂ)) (environmentRotate W ψ) =
      environmentRotate W (matrixRegister (J ⊗ₖ (1 : Matrix E E ℂ)) ψ) := by
  ext ⟨a,e⟩
  simp only [matrixRegister_system_apply, environmentRotate_apply, environmentRow_system,
    map_sum, map_smul, lp.coeFn_sum, Finset.sum_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]

theorem tensorMap_tensorVector (n : ℕ) (J : Matrix A B ℂ) (ψ : Register B) :
    tensorMap n J (tensorVector (fun _ : Fin n => ψ)) =
      tensorVector (fun _ : Fin n => matrixRegister J ψ) := by
  ext w
  simp only [tensorMap_apply, tensorVector_apply, matrixRegister_apply]
  have h := Fintype.prod_sum (fun i : Fin n => fun b => J (w i) b * ψ b)
  rw [h]
  apply Finset.sum_congr rfl
  intro v _
  rw [Finset.prod_mul_distrib]
  ring

theorem grouped_system_tensorVector (n : ℕ) (J : Matrix A B ℂ) (ψ : Register (B × E)) :
    matrixRegister (tensorPower n J ⊗ₖ (1 : Matrix (Fin n → E) (Fin n → E) ℂ))
      (regroup n (tensorVector (fun _ : Fin n => ψ))) =
      regroup n (tensorVector (fun _ : Fin n => matrixRegister (J ⊗ₖ (1 : Matrix E E ℂ)) ψ)) := by
  have he := congrArg (fun T : Register (Fin n → B × E) →L[ℂ]
    Register ((Fin n → A) × (Fin n → E)) => T (tensorVector (fun _ : Fin n => ψ)))
    (regroup_tensorMap n J)
  simpa only [ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
    tensorMap_tensorVector] using he.symm

variable [Nonempty A] [Nonempty B]

/-- One fixed rectangular conjugation of the square purifier's finite output. -/
def embeddedHaarCLM (n : ℕ) (J : Matrix A B ℂ) :
    Matrix ((Fin n → B) × (Fin n → B)) ((Fin n → B) × (Fin n → B)) ℂ →L[ℂ]
      TraceClass (Register ((Fin n → A) × (Fin n → B))) :=
  registerLiftCLM.comp (LinearMap.toContinuousLinearMap
    { toFun X := (tensorPower n J ⊗ₖ (1 : Matrix (Fin n → B) (Fin n → B) ℂ)) * X *
        (tensorPower n J ⊗ₖ (1 : Matrix (Fin n → B) (Fin n → B) ℂ)).conjTranspose
      map_add' X Y := by simp [Matrix.mul_add, Matrix.add_mul]
      map_smul' c X := by simp [Matrix.mul_smul, Matrix.smul_mul] })

theorem embeddedHaarCLM_apply (n : ℕ) (J : Matrix A B ℂ)
    (X : Matrix ((Fin n → B) × (Fin n → B)) ((Fin n → B) × (Fin n → B)) ℂ) :
    embeddedHaarCLM n J X = registerLiftCLM
      ((tensorPower n J ⊗ₖ (1 : Matrix (Fin n → B) (Fin n → B) ℂ)) * X *
        (tensorPower n J ⊗ₖ (1 : Matrix (Fin n → B) (Fin n → B) ℂ)).conjTranspose) := rfl

/-- Each integrand is the actual embedded random-purification tensor projector. -/
theorem embeddedHaarCLM_integrand (n : ℕ) (J : Matrix A B ℂ)
    (ρ : Cloning.MatrixFidelity.State B) (U : unitary (Matrix B B ℂ)) :
    embeddedHaarCLM n J (entangledMoment n (purificationCoefficients ρ.matrix U)) =
      tensorProjector n (environmentRotate (purificationEnvironment U)
        (matrixRegister (J ⊗ₖ (1 : Matrix B B ℂ)) (canonicalPurification ρ.matrix))) := by
  rw [embeddedHaarCLM_apply, ← conjugation_matrixRegister, registerLiftCLM_entangledMoment,
    conjugationLinearMap_vectorProjector, grouped_system_tensorVector,
    physicalPurification_eq_environmentRotate, environmentRotate_system]
  rfl

theorem embeddedHaar_integrable (n : ℕ) (J : Matrix A B ℂ)
    (ρ : Cloning.MatrixFidelity.State B) :
    Integrable (fun U : unitary (Matrix B B ℂ) => tensorProjector n
      (environmentRotate (purificationEnvironment U)
        (matrixRegister (J ⊗ₖ (1 : Matrix B B ℂ)) (canonicalPurification ρ.matrix)))) unitaryHaar := by
  have hi := (embeddedHaarCLM n J).integrable_comp (integrable_purification_tensor n ρ.matrix)
  simpa only [embeddedHaarCLM_integrand] using hi

/-- Exact physical Haar-mixture identity after an arbitrary rectangular system embedding. -/
theorem embeddedHaar_physical (n : ℕ) (J : Matrix A B ℂ)
    (ρ : Cloning.MatrixFidelity.State B) :
    embeddedHaarCLM n J ((haarPurificationChannel n).toFun (tensorPower n ρ.matrix)) =
      ∫ U : unitary (Matrix B B ℂ), tensorProjector n
        (environmentRotate (purificationEnvironment U)
          (matrixRegister (J ⊗ₖ (1 : Matrix B B ℂ)) (canonicalPurification ρ.matrix)))
        ∂unitaryHaar := by
  rw [haarPurificationChannel_tensorPower n _ ρ.positive,
    ← (embeddedHaarCLM n J).integral_comp_comm (integrable_purification_tensor n ρ.matrix)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun U => embeddedHaarCLM_integrand n J ρ U)

/-- The actual fixed downstream channel removes Haar randomization after embedding. -/
theorem downstream_embeddedHaar {s : ℕ} (hcard : Fintype.card (A × B) = s+1)
    (n r : ℕ) (J : Matrix A B ℂ) (hJ : J.conjTranspose * J = 1)
    (ρ : Cloning.MatrixFidelity.State B) :
    (downstream hcard n r).toLinearMap
      (embeddedHaarCLM n J ((haarPurificationChannel n).toFun (tensorPower n ρ.matrix))) =
      (embeddedPurificationOutput hcard J hJ ρ n r).1 := by
  rw [embeddedHaar_physical]
  exact downstream_randomized hcard n r _
    ((matrixRegister_norm _ (systemEmbedding_isometry J hJ) _).trans (canonicalPurification_norm ρ))
    unitaryHaar purificationEnvironment (embeddedHaar_integrable n J ρ)

end Cloning.PCTRankGlobal
