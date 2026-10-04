import Cloning.PCTPurificationChannel
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Topology.Algebra.Star.Unitary
import Mathlib.Tactic.FunProp

/-!
# A canonical Haar square-root purification channel

The compact unitary group, normalized Haar probability, entangled tensor
moment and resulting finite-sample CPTP map are all constructed here. No
integrability or normalization premises remain in `haarPurificationChannel`.
The separate identification with the Haar mixture of purifications requires
the commutation of the moment with tensor-power inputs.
-/

noncomputable section
open scoped BigOperators Matrix Kronecker MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Matrix MeasureTheory

namespace Cloning.PCTPurificationChannel

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

variable {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]

local instance matrixCStarHaar (I : Type*) [Fintype I] [DecidableEq I] :
    CStarAlgebra (Matrix I I ℂ) where

theorem isCompact_unitary_matrices :
    IsCompact (unitary (Matrix A A ℂ) : Set (Matrix A A ℂ)) := by
  apply Metric.isCompact_iff_isClosed_bounded.mpr
  refine ⟨isClosed_unitary, isBounded_iff_forall_norm_le.mpr ⟨1, ?_⟩⟩
  intro U hU
  exact (CStarRing.norm_coe_unitary (⟨U, hU⟩ : unitary (Matrix A A ℂ))).le

instance unitaryMatricesCompact : CompactSpace (unitary (Matrix A A ℂ)) :=
  isCompact_iff_compactSpace.mp isCompact_unitary_matrices

instance unitaryMatricesMeasurableSpace : MeasurableSpace (unitary (Matrix A A ℂ)) :=
  borel _

instance unitaryMatricesBorelSpace : BorelSpace (unitary (Matrix A A ℂ)) := ⟨rfl⟩

/-- Normalized Haar measure on the actual finite-dimensional unitary group. -/
def unitaryHaar : Measure (unitary (Matrix A A ℂ)) :=
  Measure.haarMeasure ⊤
deriving Measure.IsHaarMeasure

instance unitaryHaar_probability : IsProbabilityMeasure (unitaryHaar (A := A)) :=
  ⟨Measure.haarMeasure_self⟩

theorem continuous_entangledMoment (n : ℕ) :
    Continuous (fun U : unitary (Matrix A A ℂ) => entangledMoment n (U : Matrix A A ℂ)) := by
  apply continuous_pi
  intro ab
  apply continuous_pi
  intro cd
  simp only [entangledMoment, entangledTensor, tensorPower]
  have he (a b : A) : Continuous (fun U : unitary (Matrix A A ℂ) => U.val a b) :=
    (continuous_apply b).comp ((continuous_apply a).comp continuous_subtype_val)
  exact (continuous_finset_prod _ (fun i _ => he _ _)).mul
    (continuous_finset_prod _ (fun i _ => he _ _)).star

theorem integrable_haar_entangledMoment (n : ℕ) :
    Integrable (fun U : unitary (Matrix A A ℂ) => entangledMoment n (U : Matrix A A ℂ))
      unitaryHaar :=
  (continuous_entangledMoment n).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- Canonical maximally entangled Haar moment, on the two word registers. -/
def haarMoment (n : ℕ) :=
  integralMoment n (unitaryHaar (A := A)) (fun U => (U : Matrix A A ℂ))

theorem haarMoment_posSemidef (n : ℕ) : (haarMoment (A := A) n).PosSemidef :=
  integralMoment_posSemidef _ _ _

theorem partialTrace_haarMoment (n : ℕ) :
    Cloning.Compression.partialTrace (haarMoment (A := A) n) = 1 :=
  partialTrace_integralMoment n _ _ (fun U => Unitary.star_mul_self_of_mem U.property)
    (integrable_haar_entangledMoment n)

/-- The canonical Haar square-root map is CPTP for every finite sample size. -/
def haarPurificationChannel (n : ℕ) :
    Cloning.Channels.MatrixChannel (Fin n → A) ((Fin n → A) × (Fin n → A)) :=
  purificationChannel (haarMoment n) (haarMoment_posSemidef n) (partialTrace_haarMoment n)

theorem haarPurificationChannel_apply (n : ℕ) (X : Matrix (Fin n → A) (Fin n → A) ℂ) :
    (haarPurificationChannel (A := A) n).toFun X = purificationMap (haarMoment n) X :=
  purificationChannel_apply _ _ _ _

/-- Action of a one-particle matrix on the first of the two tensor registers. -/
def leftTensor (n : ℕ) (X : Matrix A A ℂ) :=
  tensorPower n X ⊗ₖ (1 : Matrix (Fin n → A) (Fin n → A) ℂ)

theorem leftTensor_mul (n : ℕ) (X Y : Matrix A A ℂ) :
    leftTensor n (X * Y) = leftTensor n X * leftTensor n Y := by
  simp only [leftTensor, tensorPower_mul, ← Matrix.mul_kronecker_mul, Matrix.one_mul]

theorem leftTensor_star (n : ℕ) (X : Matrix A A ℂ) :
    leftTensor n Xᴴ = (leftTensor n X)ᴴ := by
  simp [leftTensor, tensorPower_star, Matrix.conjTranspose_kronecker]

@[simp] theorem leftTensor_one (n : ℕ) : leftTensor n (1 : Matrix A A ℂ) = 1 := by
  simp [leftTensor, Matrix.one_kronecker_one]

theorem entangledTensor_mul (n : ℕ) (V U : Matrix A A ℂ) :
    entangledTensor n (V * U) = leftTensor n V *ᵥ entangledTensor n U := by
  funext ⟨a, b⟩
  rw [entangledTensor, tensorPower_mul]
  simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct, leftTensor,
    Matrix.kronecker_apply, Matrix.one_apply, entangledTensor, Fintype.sum_prod_type,
    mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]

theorem entangledMoment_mul (n : ℕ) (V U : Matrix A A ℂ) :
    entangledMoment n (V * U) =
      leftTensor n V * entangledMoment n U * (leftTensor n V)ᴴ := by
  change Matrix.vecMulVec (entangledTensor n (V * U)) (star (entangledTensor n (V * U))) =
    leftTensor n V * Matrix.vecMulVec (entangledTensor n U) (star (entangledTensor n U)) *
      (leftTensor n V)ᴴ
  rw [entangledTensor_mul, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul,
    Matrix.vecMul_conjTranspose, star_star]

/-- A fixed matrix sandwich, bundled for commuting with Bochner integration. -/
def matrixSandwichCLM {I : Type*} [Fintype I] [DecidableEq I] (V : Matrix I I ℂ) :
    Matrix I I ℂ →L[ℂ] Matrix I I ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun X => V * X * Vᴴ
      map_add' := by intros; simp [Matrix.mul_add, Matrix.add_mul]
      map_smul' := by intros; simp [Matrix.mul_smul, Matrix.smul_mul] }

/-- Left Haar invariance gives exact invariance of the entangled moment under
all tensor powers of one-particle unitaries on the input register. -/
theorem haarMoment_unitary_invariant (n : ℕ) (V : unitary (Matrix A A ℂ)) :
    leftTensor n (V : Matrix A A ℂ) * haarMoment n *
      (leftTensor n (V : Matrix A A ℂ))ᴴ = haarMoment n := by
  have h := (matrixSandwichCLM (leftTensor n (V : Matrix A A ℂ))).integral_comp_comm
    (integrable_haar_entangledMoment (A := A) n)
  change (∫ U : unitary (Matrix A A ℂ), leftTensor n (V : Matrix A A ℂ) *
      entangledMoment n (U : Matrix A A ℂ) * (leftTensor n (V : Matrix A A ℂ))ᴴ
        ∂unitaryHaar) =
      leftTensor n (V : Matrix A A ℂ) * haarMoment n *
        (leftTensor n (V : Matrix A A ℂ))ᴴ at h
  rw [← h]
  simp_rw [← entangledMoment_mul]
  exact integral_mul_left_eq_self
    (μ := unitaryHaar) (fun U : unitary (Matrix A A ℂ) => entangledMoment n (U : Matrix A A ℂ)) V

theorem haarMoment_commute_unitary (n : ℕ) (V : unitary (Matrix A A ℂ)) :
    Commute (haarMoment (A := A) n) (leftTensor n (V : Matrix A A ℂ)) := by
  have hn : (leftTensor n (V : Matrix A A ℂ))ᴴ * leftTensor n (V : Matrix A A ℂ) = 1 := by
    have hV : (V : Matrix A A ℂ)ᴴ * V = 1 := Unitary.star_mul_self_of_mem V.property
    rw [← leftTensor_star, ← leftTensor_mul, hV, leftTensor_one]
  have h := congrArg (fun X => X * leftTensor n (V : Matrix A A ℂ))
    (haarMoment_unitary_invariant n V)
  simp only [Matrix.mul_assoc, hn, Matrix.mul_one] at h
  exact h.symm

end Cloning.PCTPurificationChannel
