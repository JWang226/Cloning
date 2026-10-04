import Cloning.FiniteKrausLift
import Cloning.PurificationSupport
import Cloning.WernerPhysicalAgreement

/-! Actual trace-class channels and symmetric-sector recovery used in the
state-independent full-environment PCT protocol. -/
noncomputable section
open scoped BigOperators Matrix InnerProductSpace ComplexOrder
open Cloning.InfiniteTraceClass Cloning.PCT Cloning.PCTPurificationChannel
open Cloning.GeneralSymmetricOccupation

namespace Cloning.PCTGlobal
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

variable {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]

local instance registerFiniteDimensional (I : Type*) [Fintype I] [DecidableEq I] :
    FiniteDimensional ℂ (Register I) :=
  (registerBasis I).toOrthonormalBasis.toBasis.finiteDimensional_of_finite

/-- Haar random purification as a genuine trace-class channel on all inputs. -/
def purificationChannel (n : ℕ) : QuantumChannel (Register (Fin n → A))
    (Register ((Fin n → A) × (Fin n → A))) :=
  FiniteKrausLift.channel (purificationKraus (haarMoment (A := A) n))
    ((purificationKraus_normalization (haarMoment_posSemidef n)).trans
      (partialTrace_haarMoment n))

theorem purificationChannel_apply (n : ℕ) (X : Matrix (Fin n → A) (Fin n → A) ℂ) :
    (purificationChannel (A := A) n).toLinearMap (registerLiftCLM X) =
      registerLiftCLM ((haarPurificationChannel n).toFun X) := by
  rw [purificationChannel, FiniteKrausLift.channel_registerLiftCLM,
    ← purificationMap_eq_kraus, haarPurificationChannel_apply]

/-- The occupation Werner map lifted through its actual finite Kraus matrices. -/
def sectorChannel (n r s : ℕ) : QuantumChannel (OccupationSpace n (s + 1))
    (OccupationSpace (n + r) (s + 1)) :=
  FiniteKrausLift.channel
    (CartanChannel.cartanKraus (splittingMatrix n r (s + 1))
      ((n + s).choose s : ℝ) ((n + r + s).choose s : ℝ))
    (CartanChannel.cartanKraus_normalization _ _ _
      (by exact_mod_cast Nat.choose_pos (Nat.le_add_left s n))
      (by exact_mod_cast Nat.choose_pos (Nat.le_add_left s (n + r)))
      (splittingMatrix_balance n r s))

theorem sectorChannel_apply (n r s : ℕ)
    (X : Matrix (Occupation n (s + 1)) (Occupation n (s + 1)) ℂ) :
    (sectorChannel n r s).toLinearMap (registerLiftCLM X) =
      registerLiftCLM ((wernerChannel n r s).toFun X) := by
  rw [sectorChannel, FiniteKrausLift.channel_registerLiftCLM]
  rfl

/-- Occupation coordinates embedded into a chosen complete physical frame. -/
def physicalEmbedding {s : ℕ}
    (u : OrthonormalBasis (Fin (s + 1)) ℂ (Register (A × A))) (L : ℕ) :
    OccupationSpace L (s + 1) →ₗᵢ[ℂ] Register (Fin L → A × A) :=
  (tensorFrame u.orthonormal L).comp (isometry L (s + 1))

/-- The same occupation embedding with system and environment regrouped. -/
def groupedEmbedding {s : ℕ}
    (u : OrthonormalBasis (Fin (s + 1)) ℂ (Register (A × A))) (L : ℕ) :
    OccupationSpace L (s + 1) →ₗᵢ[ℂ] Register ((Fin L → A) × (Fin L → A)) :=
  (regroup L).comp (physicalEmbedding u L)

theorem physicalEmbedding_range {s : ℕ}
    (u : OrthonormalBasis (Fin (s + 1)) ℂ (Register (A × A))) (L : ℕ) :
    (physicalEmbedding u L).toLinearMap.range = physicalSymmetric L := by
  change ((tensorFrame u.orthonormal L).toLinearMap.comp
    (isometry L (s + 1)).toLinearMap).range = _
  rw [LinearMap.range_comp, isometry_range, physicalSymmetric_map_tensorFrame]

theorem regroup_surjective (L : ℕ) :
    Function.Surjective (regroup (A := A) (B := A) L) := by
  intro y
  let x : Register (Fin L → A × A) := ⟨fun w => y ((fun i => (w i).1), fun i => (w i).2),
    memℓp_gen (by simp only [ENNReal.toReal_ofNat]; exact (hasSum_fintype _).summable)⟩
  refine ⟨x, ?_⟩
  ext ⟨a,b⟩
  simp [regroup_apply, x]

theorem groupedEmbedding_range {s : ℕ}
    (u : OrthonormalBasis (Fin (s + 1)) ℂ (Register (A × A))) (L : ℕ) :
    (groupedEmbedding u L).toLinearMap.range = PurificationSupport.groupedSymmetric L := by
  ext y
  constructor
  · rintro ⟨x,rfl⟩
    apply (PurificationSupport.regroup_mem_groupedSymmetric_iff L _).mpr
    rw [← physicalEmbedding_range u L]
    exact ⟨x,rfl⟩
  · intro hy
    obtain ⟨z,rfl⟩ := regroup_surjective L y
    have hz := (PurificationSupport.regroup_mem_groupedSymmetric_iff L z).mp hy
    rw [← physicalEmbedding_range u L] at hz
    obtain ⟨x,rfl⟩ := hz
    exact ⟨x,rfl⟩

/-- The occupation embedding resolves the physical grouped symmetric projector. -/
theorem groupedEmbedding_projection {s : ℕ}
    (u : OrthonormalBasis (Fin (s + 1)) ℂ (Register (A × A))) (L : ℕ) :
    (groupedEmbedding u L).toContinuousLinearMap.comp
      (groupedEmbedding u L).toContinuousLinearMap.adjoint =
        (PurificationSupport.groupedSymmetric (A := A) L).starProjection := by
  apply ContinuousLinearMap.ext
  intro y
  symm
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · rw [← groupedEmbedding_range u L]
    exact ⟨_,rfl⟩
  · intro w hw
    rw [← groupedEmbedding_range u L] at hw
    obtain ⟨x,rfl⟩ := hw
    rw [inner_sub_left]
    change ⟪y, groupedEmbedding u L x⟫_ℂ -
      ⟪groupedEmbedding u L ((groupedEmbedding u L).toContinuousLinearMap.adjoint y),
        groupedEmbedding u L x⟫_ℂ = 0
    rw [LinearIsometry.inner_map_map, ContinuousLinearMap.adjoint_inner_left]
    exact sub_self _

/-- Actual channel compression with a fixed replacement state off the sector. -/
def sectorRecovery {s : ℕ}
    (u : OrthonormalBasis (Fin (s + 1)) ℂ (Register (A × A))) (n : ℕ) :
    QuantumChannel (Register ((Fin n → A) × (Fin n → A))) (OccupationSpace n (s + 1)) :=
  QuantumChannel.isometricRecovery (groupedEmbedding u n) (vacuumRegister n s)

end Cloning.PCTGlobal
