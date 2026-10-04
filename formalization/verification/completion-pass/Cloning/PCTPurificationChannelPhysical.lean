import Cloning.PCTPurificationChannelAction
import Cloning.PCTReducedGaussian
import Mathlib.Analysis.Normed.Lp.LpEquiv

/-!
# Register realization of the random-purification channel

This identifies the finite-matrix Haar output with the trace-class mixture of
literal purification tensor powers. The environment action is explicitly the
transpose unitary, so the matrix and register conventions agree pointwise.
-/

noncomputable section
open scoped BigOperators Matrix MatrixOrder ComplexOrder InnerProductSpace Matrix.Norms.L2Operator Topology
open Matrix MeasureTheory Filter Cloning.InfiniteTraceClass

namespace Cloning.PCTPurificationChannel

open Cloning.PCT Cloning.PCTReducedGaussian

set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

variable {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]

local instance physicalRegisterFiniteDimensional (I : Type*) [Fintype I] [DecidableEq I] :
    FiniteDimensional ℂ (Register I) :=
  (registerBasis I).toOrthonormalBasis.toBasis.finiteDimensional_of_finite

def unitaryColumn (U : unitary (Matrix A A ℂ)) (b : A) : Register A :=
  ⟨fun a => (U : Matrix A A ℂ) a b, memℓp_gen (by
    simp only [ENNReal.toReal_ofNat]; exact (hasSum_fintype _).summable)⟩

theorem unitaryColumn_orthonormal (U : unitary (Matrix A A ℂ)) :
    Orthonormal ℂ (unitaryColumn U) := by
  rw [orthonormal_iff_ite]
  intro a b
  have hU : (U : Matrix A A ℂ)ᴴ * U = 1 := Unitary.star_mul_self_of_mem U.property
  have h := congrArg (fun M => M a b) hU
  simpa only [lp.inner_eq_tsum, tsum_fintype, RCLike.inner_apply, unitaryColumn,
    Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply, starRingEnd_apply, mul_comm] using h

/-- Actual matrix action on the finite physical Hilbert register. -/
def unitaryRegister (U : unitary (Matrix A A ℂ)) : Register A →ₗᵢ[ℂ] Register A :=
  (unitaryColumn_orthonormal U).orthogonalFamily.linearIsometry

theorem unitaryRegister_apply (U : unitary (Matrix A A ℂ)) (x : Register A) (a : A) :
    unitaryRegister U x a = ∑ b, (U : Matrix A A ℂ) a b * x b := by
  rw [unitaryRegister, OrthogonalFamily.linearIsometry_apply, tsum_fintype]
  simp [unitaryColumn, mul_comm]

/-- The transpose is the environment action associated with right matrix
multiplication of a bipartite coefficient matrix. -/
def purificationEnvironment (U : unitary (Matrix A A ℂ)) : Register A →ₗᵢ[ℂ] Register A :=
  unitaryRegister (Matrix.UnitaryGroup.transpose U)

def canonicalPurification (ρ : Matrix A A ℂ) : Register (A × A) :=
  coefficientVector (CFC.sqrt ρ)

def physicalPurification (ρ : Matrix A A ℂ) (U : unitary (Matrix A A ℂ)) : Register (A × A) :=
  coefficientVector (purificationCoefficients ρ U)

theorem physicalPurification_eq_environmentRotate (ρ : Matrix A A ℂ)
    (U : unitary (Matrix A A ℂ)) :
    physicalPurification ρ U = environmentRotate (purificationEnvironment U)
      (canonicalPurification ρ) := by
  ext ⟨a, b⟩
  simp only [physicalPurification, coefficientVector_apply, purificationCoefficients,
    Matrix.mul_apply, environmentRotate_apply, purificationEnvironment,
    unitaryRegister_apply,
    environmentRow_apply, canonicalPurification, Matrix.UnitaryGroup.transpose, Matrix.transpose_apply]
  apply Finset.sum_congr rfl
  intro c _
  exact mul_comm _ _

theorem canonicalPurification_reduced (ρ : Matrix A A ℂ) (hρ : ρ.PosSemidef) :
    reducedDensityMatrix (canonicalPurification ρ) = ρ := by
  rw [canonicalPurification, reducedDensityMatrix_coefficientVector,
    Cloning.MatrixFidelity.sqrt_conjTranspose, Cloning.MatrixFidelity.sqrt_mul_self hρ]

theorem trace_reducedDensityMatrix (ψ : Register (A × A)) :
    (Matrix.trace (reducedDensityMatrix ψ)).re = ‖ψ‖ ^ 2 := by
  have h := lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ENNReal).toReal) ψ
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, tsum_fintype] at h
  rw [h]
  simp only [Matrix.trace, Matrix.diag, reducedDensityMatrix, Complex.re_sum,
    Fintype.sum_prod_type, Complex.star_def, Complex.mul_conj, Complex.ofReal_re,
    Complex.normSq_eq_norm_sq]

theorem canonicalPurification_norm (ρ : Cloning.MatrixFidelity.State A) :
    ‖canonicalPurification ρ.matrix‖ = 1 := by
  have h := trace_reducedDensityMatrix (canonicalPurification ρ.matrix)
  rw [canonicalPurification_reduced _ ρ.positive, ρ.trace_one] at h
  norm_num at h
  nlinarith [norm_nonneg (canonicalPurification ρ.matrix)]

theorem physicalPurification_norm (ρ : Cloning.MatrixFidelity.State A)
    (U : unitary (Matrix A A ℂ)) : ‖physicalPurification ρ.matrix U‖ = 1 := by
  rw [physicalPurification_eq_environmentRotate, environmentRotate_norm,
    canonicalPurification_norm]

/-- Computational matrices embedded into the actual trace-class Banach space. -/
def registerLiftCLM {I : Type*} [Fintype I] [DecidableEq I] :
    Matrix I I ℂ →L[ℂ] TraceClass (Register I) :=
  LinearMap.toContinuousLinearMap
    { toFun := InfiniteFiniteCorner.matrixLift (registerBasis I)
      map_add' := by intros; simp [InfiniteFiniteCorner.matrixLift, add_smul, Finset.sum_add_distrib]
      map_smul' := by intros; simp [InfiniteFiniteCorner.matrixLift, Finset.smul_sum, smul_smul] }

theorem registerLiftCLM_coefficient {I : Type*} [Fintype I] [DecidableEq I]
    (M : Matrix I I ℂ) (a c : I) :
    (registerLiftCLM M).1 (lp.single 2 c 1) a = M a c := by
  have he := InfiniteFiniteCorner.matrixOf_ofMatrix (registerBasis I).orthonormal M
  have h := congrArg (fun N => N a c) he
  simpa only [InfiniteFiniteCorner.matrixOf, registerBasis_apply, register_inner_single,
    registerLiftCLM, LinearMap.coe_toContinuousLinearMap', InfiniteFiniteCorner.ofMatrix] using h

theorem registerLiftCLM_rankOne {I : Type*} [Fintype I] [DecidableEq I]
    (x : Register I) :
    registerLiftCLM (fun a c => x a * star (x c)) = vectorProjector x := by
  apply Subtype.ext
  apply register_operator_ext
  intro a c
  rw [registerLiftCLM_coefficient]
  simp only [vectorProjector, TraceClass.ofOperator_coe, InnerProductSpace.rankOne_apply,
    lp.inner_single_right, RCLike.inner_apply, one_mul, lp.coeFn_smul,
    Pi.smul_apply, smul_eq_mul]
  exact mul_comm _ _

theorem registerLiftCLM_entangledMoment (n : ℕ) (ρ : Matrix A A ℂ)
    (U : unitary (Matrix A A ℂ)) :
    registerLiftCLM (entangledMoment n (purificationCoefficients ρ U)) =
      vectorProjector (regroup n (tensorVector (fun _ : Fin n => physicalPurification ρ U))) := by
  rw [← registerLiftCLM_rankOne]
  congr 1
  ext ⟨a, b⟩ ⟨c, d⟩
  simp only [entangledMoment, entangledTensor, tensorPower, regroup_apply, tensorVector,
    physicalPurification, coefficientVector_apply]

/-- The matrix channel's output is exactly the physical trace-class Haar
mixture used by PCT, with the transpose convention made explicit. -/
theorem haarPurificationChannel_physical (n : ℕ) (ρ : Matrix A A ℂ)
    (hρ : ρ.PosSemidef) :
    registerLiftCLM ((haarPurificationChannel (A := A) n).toFun (tensorPower n ρ)) =
      ∫ U : unitary (Matrix A A ℂ), vectorProjector
        (regroup n (tensorVector (fun _ : Fin n =>
          environmentRotate (purificationEnvironment U) (canonicalPurification ρ))))
        ∂unitaryHaar := by
  rw [haarPurificationChannel_tensorPower n ρ hρ,
    ← ContinuousLinearMap.integral_comp_comm _ (integrable_purification_tensor n ρ)]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro U
  change registerLiftCLM (entangledMoment n (purificationCoefficients ρ U)) = _
  rw [registerLiftCLM_entangledMoment, physicalPurification_eq_environmentRotate]

theorem haarPurification_physical_integrable (n : ℕ) (ρ : Matrix A A ℂ) :
    Integrable (fun U : unitary (Matrix A A ℂ) => vectorProjector
      (regroup n (tensorVector (fun _ : Fin n => physicalPurification ρ U)))) unitaryHaar := by
  have h := registerLiftCLM.integrable_comp (integrable_purification_tensor n ρ)
  simpa only [registerLiftCLM_entangledMoment] using h

/-- Identity-ancilla insertion from the grouped purification input into the
first `n` physical slots. -/
def slotInsertion (n r : ℕ)
    (X : Matrix ((Fin n → A) × (Fin n → A)) ((Fin n → A) × (Fin n → A)) ℂ) :
    Matrix (Fin (n + r) → A × A) (Fin (n + r) → A × A) ℂ :=
  fun a c => X
    ((fun i => (a (Fin.castAdd r i)).1), (fun i => (a (Fin.castAdd r i)).2))
    ((fun i => (c (Fin.castAdd r i)).1), (fun i => (c (Fin.castAdd r i)).2)) *
    ∏ j : Fin r, if a (Fin.natAdd n j) = c (Fin.natAdd n j) then 1 else 0

def slotInsertionCLM (n r : ℕ) :
    Matrix ((Fin n → A) × (Fin n → A)) ((Fin n → A) × (Fin n → A)) ℂ →L[ℂ]
      Matrix (Fin (n + r) → A × A) (Fin (n + r) → A × A) ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := slotInsertion n r
      map_add' := by intros; ext a c; simp [slotInsertion, add_mul]
      map_smul' := by intros; ext a c; simp [slotInsertion, mul_assoc] }

theorem slotInsertion_entangledMoment (n r : ℕ) (M : Matrix A A ℂ) :
    slotInsertion n r (entangledMoment n M) =
      pureSlotsMatrix (coefficientVector M)
        (GeneralSymmetricOccupation.inputSlots n (n + r) (Nat.le_add_right n r)) := by
  ext a c
  rw [pureSlotsMatrix, Fin.prod_univ_add]
  simp only [GeneralSymmetricOccupation.mem_inputSlots, Fin.val_castAdd, Fin.isLt,
    if_true, coefficientVector, Fin.val_natAdd, not_lt_of_ge (Nat.le_add_right n _),
    if_false, slotInsertion, entangledMoment, entangledTensor, tensorPower,
    star_prod, Finset.prod_mul_distrib]

/-- Werner's literal symmetric sandwich followed by the physical partial
trace, as a continuous linear map of the finite input matrix. -/
def physicalCloneTraceCLM (n r s : ℕ) :
    Matrix ((Fin n → A) × (Fin n → A)) ((Fin n → A) × (Fin n → A)) ℂ →L[ℂ]
      TraceClass (Register (Fin (n + r) → A)) :=
  LinearMap.toContinuousLinearMap
    (partialTraceChannel.toLinearMap.comp
      ((QuantumChannel.ofIsometry (regroup (n + r))).toLinearMap.comp
        (((((n + s).choose s : ℝ) / ((n + r + s).choose s : ℝ) : ℝ) : ℂ) •
          (conjugationLinearMap (physicalProjector (C := A × A) (n + r))).comp
            (registerLiftCLM.toLinearMap.comp (slotInsertionCLM n r).toLinearMap))))

theorem physicalCloneTraceCLM_purification (n r s : ℕ)
    (hcard : Fintype.card (A × A) = s + 1) (ρ : Cloning.MatrixFidelity.State A)
    (U : unitary (Matrix A A ℂ)) :
    physicalCloneTraceCLM n r s (entangledMoment n (purificationCoefficients ρ.matrix U)) =
      reducedWernerOutput hcard (physicalPurification ρ.matrix U) (physicalPurification_norm ρ U)
        (GeneralSymmetricOccupation.inputSlots n (n + r) (Nat.le_add_right n r)) := by
  have hP : (physicalProjector (C := A × A) (n + r)).adjoint =
      physicalProjector (C := A × A) (n + r) :=
    (isStarProjection_starProjection (U := physicalSymmetric (C := A × A) (n + r))).isSelfAdjoint.adjoint_eq
  simp only [physicalCloneTraceCLM, LinearMap.coe_toContinuousLinearMap',
    LinearMap.comp_apply, LinearMap.smul_apply, ContinuousLinearMap.coe_coe,
    slotInsertionCLM, LinearMap.coe_mk, AddHom.coe_mk]
  rw [slotInsertion_entangledMoment]
  unfold reducedWernerOutput
  congr 2
  apply Subtype.ext
  simp only [pureWernerOutput,
    TraceClass.ofOperator_coe, pureWernerOperator, GeneralSymmetricOccupation.inputSlots_card]
  change _ • operatorConjugation (physicalProjector (C := A × A) (n + r))
      (pureSlotsOperator (physicalPurification ρ.matrix U) _) = _
  congr 1
  apply ContinuousLinearMap.ext
  intro x
  simp only [operatorConjugation_apply, hP, ContinuousLinearMap.mul_apply]

/-- Actual finite random purification followed by the literal Werner/trace
map equals the frame-independent pure-purification output. -/
theorem physical_pct_eq_reducedWerner (n r s : ℕ)
    (hcard : Fintype.card (A × A) = s + 1) (ρ : Cloning.MatrixFidelity.State A) :
    physicalCloneTraceCLM n r s
      ((haarPurificationChannel (A := A) n).toFun (tensorPower n ρ.matrix)) =
      reducedWernerOutput hcard (canonicalPurification ρ.matrix) (canonicalPurification_norm ρ)
        (GeneralSymmetricOccupation.inputSlots n (n + r) (Nat.le_add_right n r)) := by
  rw [haarPurificationChannel_tensorPower n _ ρ.positive,
    ← ContinuousLinearMap.integral_comp_comm _ (integrable_purification_tensor n ρ.matrix)]
  have he (U : unitary (Matrix A A ℂ)) :
      physicalCloneTraceCLM n r s (entangledMoment n (purificationCoefficients ρ.matrix U)) =
        reducedWernerOutput hcard (canonicalPurification ρ.matrix) (canonicalPurification_norm ρ)
          (GeneralSymmetricOccupation.inputSlots n (n + r) (Nat.le_add_right n r)) := by
    rw [physicalCloneTraceCLM_purification n r s hcard ρ U]
    simpa only [← physicalPurification_eq_environmentRotate] using
      reducedWernerOutput_environment_invariant hcard _ (canonicalPurification_norm ρ)
        (purificationEnvironment U)
        (GeneralSymmetricOccupation.inputSlots n (n + r) (Nat.le_add_right n r))
  simp_rw [he]
  simp


set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency true

/-- The actual finite Haar purification channel, followed by the literal
Werner sandwich and physical partial trace, has the Gaussian product-mixture
limit. The purification frame is constructed, and Haar randomization is
removed by environment invariance. The downstream sandwich here is a
continuous linear map; its global CPTP extension is a separate statement. -/
theorem physical_pct_gaussian_product_mixture {s : ℕ} (hs : 1 ≤ s)
    (hcard : Fintype.card (A × A) = s + 1) (ρ : Cloning.MatrixFidelity.State A)
    (r : ℕ → ℕ) {γ : ℝ} (hγ : 1 < γ)
    (h : Filter.Tendsto (fun n ↦ ((n + r n : ℕ) : ℝ) / n) Filter.atTop (𝓝 γ)) :
    ∃ u : OrthonormalBasis (Fin (s + 1)) ℂ (Register (A × A)),
      u 0 = canonicalPurification ρ.matrix ∧
      Filter.Tendsto (fun n => ‖physicalCloneTraceCLM n (r n) s
        ((haarPurificationChannel (A := A) n).toFun (tensorPower n ρ.matrix)) -
        ∫ z, matrixTensorPower
          (reducedDensityMatrix (frameParticle u z (n + r n))) (n + r n)
          ∂MultimodeCoherentGaussianMixture.gaussianProductMeasure
            (fun _ : Fin s => γ - 1)‖) Filter.atTop (𝓝 0) := by
  obtain ⟨u, hu, ht⟩ := exists_pct_product_mixture (A := A) (B := A) (s := s) hs hcard
    (canonicalPurification ρ.matrix) (canonicalPurification_norm ρ)
    (unitaryHaar (A := A)) (purificationEnvironment (A := A)) (fun n => n + r n)
    (fun n => Nat.le_add_right n (r n)) hγ h
  refine ⟨u, hu, ?_⟩
  have he (n : ℕ) := physical_pct_eq_reducedWerner n (r n) s hcard ρ
  simpa only [he, randomizedPurificationOutput_eq] using ht

end Cloning.PCTPurificationChannel
