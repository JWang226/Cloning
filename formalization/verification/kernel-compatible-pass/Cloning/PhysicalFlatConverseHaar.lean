import Cloning.PhysicalFlatConverseCommutant
import Cloning.TensorFlatProjectorMatrix
import Cloning.PCTPurificationChannelHaar

/-! Literal Haar averaging on a physical highest-weight sector is the
trace-normalized identity. Scalarity follows from the differentiated actual
unitary action, including every repeated copy of a Schur label separately. -/
noncomputable section
open scoped BigOperators InnerProductSpace Matrix Topology Matrix.Norms.L2Operator
open MeasureTheory
namespace Cloning.PhysicalFlatConverse
open Cloning.TensorLie Cloning.PCT Cloning.PCTPurificationChannel
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
variable {d : ℕ}

local instance (n d : ℕ) : FiniteDimensional ℂ (TensorRegister n (Fin d)) :=
  (registerBasis (Fin n → Fin d)).toOrthonormalBasis.toBasis.finiteDimensional_of_finite

theorem continuous_tensorOperator (n d : ℕ) :
    Continuous (tensorOperator n : Matrix (Fin d) (Fin d) ℂ → _) := by
  change Continuous (fun X => registerMatrixCLM (tensorPower n X))
  apply (registerMatrixCLM (I := Fin n → Fin d)).continuous.comp
  unfold tensorPower
  fun_prop

theorem continuous_partitionActionMatrix (mu : Fin d → ℕ) (hmu : Antitone mu) :
    Continuous (partitionActionMatrix mu hmu) := by
  have hc : Continuous (partitionTensorAction mu hmu) := by
    change Continuous (fun X => cyclicTensorOperator _ _ _ _ X)
    simp_rw [← sectorCompression_tensorOperator _ _ _ _]
    exact (sectorCompression (cyclicSector (partitionHighestTensor mu hmu))).continuous.comp
      (continuous_tensorOperator (∑ a, mu a) d)
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  simp only [partitionActionMatrix_apply]
  exact continuous_const.inner (hc.clm_apply continuous_const)

@[simp] theorem partitionActionMatrix_one (mu : Fin d → ℕ) (hmu : Antitone mu) :
    partitionActionMatrix mu hmu (1 : Matrix (Fin d) (Fin d) ℂ) = 1 := by
  unfold partitionActionMatrix partitionTensorAction
  rw [cyclicTensorOperator_one]
  exact LinearMap.toMatrix_id _

theorem partitionActionMatrix_unitary (mu : Fin d → ℕ) (hmu : Antitone mu)
    (U : unitary (Matrix (Fin d) (Fin d) ℂ)) :
    (partitionActionMatrix mu hmu U)ᴴ * partitionActionMatrix mu hmu U = 1 := by
  rw [← partitionActionMatrix_star, ← partitionActionMatrix_mul]
  rw [show (U : Matrix (Fin d) (Fin d) ℂ)ᴴ * U = 1 from Unitary.star_mul_self_of_mem U.property,
    partitionActionMatrix_one]

/-- Schur scalarity for the actual matrix action, with no commutant premise
beyond commutation with the literal physical unitary matrices. -/
theorem partitionActionMatrix_unitary_commutant_scalar
    (mu : Fin d → ℕ) (hmu : Antitone mu)
    (M : Matrix (PartitionIndex mu hmu) (PartitionIndex mu hmu) ℂ)
    (hcomm : ∀ U : unitary (Matrix (Fin d) (Fin d) ℂ),
      M * partitionActionMatrix mu hmu U = partitionActionMatrix mu hmu U * M) :
    ∃ c : ℂ, M = c • (1 : Matrix (PartitionIndex mu hmu) (PartitionIndex mu hmu) ℂ) := by
  let B := (partitionBasis mu hmu).toBasis
  let T := (Matrix.toLin B B M).toContinuousLinearMap
  have hT : ∀ U : unitary (Matrix (Fin d) (Fin d) ℂ),
      T * partitionTensorAction mu hmu U = partitionTensorAction mu hmu U * T := by
    intro U
    apply ContinuousLinearMap.coe_injective
    apply (LinearMap.toMatrix B B).injective
    simp only [ContinuousLinearMap.coe_mul, LinearMap.toMatrix_mul, T,
      LinearMap.coe_toContinuousLinearMap, LinearMap.toMatrix_toLin]
    exact hcomm U
  obtain ⟨c,hc⟩ := cyclicTensorOperator_unitary_commutant_scalar
    (partitionHighestTensor mu hmu) (fun a => (mu a : ℂ))
    (partitionHighestTensor_cartan mu hmu) (partitionHighestTensor_raising_zero mu hmu)
    (partitionHighestTensor_norm mu hmu) T hT
  refine ⟨c, ?_⟩
  have hh := congrArg (fun F => LinearMap.toMatrix B B (F : _ →L[ℂ] _).toLinearMap) hc
  simpa only [T, LinearMap.coe_toContinuousLinearMap, LinearMap.toMatrix_toLin,
    ContinuousLinearMap.coe_smul, map_smul, ContinuousLinearMap.coe_id, LinearMap.toMatrix_id] using hh

variable [Nonempty (Fin d)]

def partitionTwirl (mu : Fin d → ℕ) (hmu : Antitone mu)
    (M : Matrix (PartitionIndex mu hmu) (PartitionIndex mu hmu) ℂ) :=
  ∫ U : unitary (Matrix (Fin d) (Fin d) ℂ),
    partitionActionMatrix mu hmu U * M * (partitionActionMatrix mu hmu U)ᴴ ∂unitaryHaar

theorem continuous_partitionSandwich (mu : Fin d → ℕ) (hmu : Antitone mu)
    (M : Matrix (PartitionIndex mu hmu) (PartitionIndex mu hmu) ℂ) :
    Continuous (fun U : unitary (Matrix (Fin d) (Fin d) ℂ) =>
      partitionActionMatrix mu hmu U * M * (partitionActionMatrix mu hmu U)ᴴ) := by
  have h : Continuous (fun U : unitary (Matrix (Fin d) (Fin d) ℂ) =>
      partitionActionMatrix mu hmu U) :=
    (continuous_partitionActionMatrix mu hmu).comp continuous_subtype_val
  exact (h.mul continuous_const).mul h.star

theorem integrable_partitionSandwich (mu : Fin d → ℕ) (hmu : Antitone mu)
    (M : Matrix (PartitionIndex mu hmu) (PartitionIndex mu hmu) ℂ) :
    Integrable (fun U : unitary (Matrix (Fin d) (Fin d) ℂ) =>
      partitionActionMatrix mu hmu U * M * (partitionActionMatrix mu hmu U)ᴴ) unitaryHaar :=
  (continuous_partitionSandwich mu hmu M).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

theorem partitionTwirl_invariant (mu : Fin d → ℕ) (hmu : Antitone mu)
    (M : Matrix (PartitionIndex mu hmu) (PartitionIndex mu hmu) ℂ)
    (V : unitary (Matrix (Fin d) (Fin d) ℂ)) :
    partitionActionMatrix mu hmu V * partitionTwirl mu hmu M *
      (partitionActionMatrix mu hmu V)ᴴ = partitionTwirl mu hmu M := by
  have hh := (matrixSandwichCLM (partitionActionMatrix mu hmu V)).integral_comp_comm
    (integrable_partitionSandwich mu hmu M)
  change (∫ U : unitary (Matrix (Fin d) (Fin d) ℂ),
    partitionActionMatrix mu hmu V * (partitionActionMatrix mu hmu U * M *
      (partitionActionMatrix mu hmu U)ᴴ) * (partitionActionMatrix mu hmu V)ᴴ ∂unitaryHaar) =
      partitionActionMatrix mu hmu V * partitionTwirl mu hmu M *
        (partitionActionMatrix mu hmu V)ᴴ at hh
  rw [← hh]
  have he (U : unitary (Matrix (Fin d) (Fin d) ℂ)) :
      partitionActionMatrix mu hmu V * (partitionActionMatrix mu hmu U * M *
        (partitionActionMatrix mu hmu U)ᴴ) * (partitionActionMatrix mu hmu V)ᴴ =
      partitionActionMatrix mu hmu (V*U) * M * (partitionActionMatrix mu hmu (V*U))ᴴ := by
    simp only [Submonoid.coe_mul, partitionActionMatrix_mul, Matrix.conjTranspose_mul]
    noncomm_ring
  simp_rw [he]
  exact integral_mul_left_eq_self (μ := unitaryHaar)
    (fun U : unitary (Matrix (Fin d) (Fin d) ℂ) =>
      partitionActionMatrix mu hmu U * M * (partitionActionMatrix mu hmu U)ᴴ) V

theorem partitionTwirl_scalar (mu : Fin d → ℕ) (hmu : Antitone mu)
    (M : Matrix (PartitionIndex mu hmu) (PartitionIndex mu hmu) ℂ) :
    ∃ c : ℂ, partitionTwirl mu hmu M = c • (1 : Matrix (PartitionIndex mu hmu) _ ℂ) := by
  apply partitionActionMatrix_unitary_commutant_scalar
  intro U
  have hh := congrArg (fun X => X * partitionActionMatrix mu hmu U)
    (partitionTwirl_invariant mu hmu M U)
  simpa only [Matrix.mul_assoc, partitionActionMatrix_unitary, Matrix.mul_one] using hh.symm

theorem trace_partitionTwirl (mu : Fin d → ℕ) (hmu : Antitone mu)
    (M : Matrix (PartitionIndex mu hmu) (PartitionIndex mu hmu) ℂ) :
    (partitionTwirl mu hmu M).trace = M.trace := by
  let tr := (Matrix.traceLinearMap (PartitionIndex mu hmu) ℂ ℂ).toContinuousLinearMap
  have hh := tr.integral_comp_comm (integrable_partitionSandwich mu hmu M)
  change (∫ U : unitary (Matrix (Fin d) (Fin d) ℂ),
    (partitionActionMatrix mu hmu U * M * (partitionActionMatrix mu hmu U)ᴴ).trace ∂unitaryHaar) =
    (partitionTwirl mu hmu M).trace at hh
  rw [← hh]
  have he (U : unitary (Matrix (Fin d) (Fin d) ℂ)) :
      (partitionActionMatrix mu hmu U * M * (partitionActionMatrix mu hmu U)ᴴ).trace = M.trace := by
    rw [Matrix.trace_mul_cycle, partitionActionMatrix_unitary, Matrix.one_mul]
  simp_rw [he]
  simp

/-- Exact physical sector Haar average, not merely an assumed invariant form. -/
theorem partitionTwirl_eq (mu : Fin d → ℕ) (hmu : Antitone mu)
    (M : Matrix (PartitionIndex mu hmu) (PartitionIndex mu hmu) ℂ) :
    partitionTwirl mu hmu M = (M.trace / (partitionDimension mu hmu : ℂ)) •
      (1 : Matrix (PartitionIndex mu hmu) _ ℂ) := by
  obtain ⟨c,hc⟩ := partitionTwirl_scalar mu hmu M
  have ht := trace_partitionTwirl mu hmu M
  rw [hc,Matrix.trace_smul,Matrix.trace_one,Fintype.card_fin,smul_eq_mul] at ht
  have hd : (partitionDimension mu hmu : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (ne_of_gt (partitionDimension_pos mu hmu))
  rw [hc, ← ht, mul_div_cancel_right₀ _ hd]

end Cloning.PhysicalFlatConverse
