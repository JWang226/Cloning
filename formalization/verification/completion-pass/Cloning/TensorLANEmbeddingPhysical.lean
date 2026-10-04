import Cloning.TensorLANEmbeddingFrame
import Cloning.TensorCartanCutoffFrame
import Cloning.MultimodeCoherentGaussianMixture

/-! Concrete all-input physical sector/Fock channels built from the literal
common cutoff frame and the actual occupation number vectors. -/
noncomputable section
open scoped BigOperators InnerProductSpace
namespace Cloning.TensorLAN
open Cloning.PCT Cloning.TensorLie Cloning.InfiniteTraceClass
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {n d : ℕ}
local instance (n d : ℕ) : FiniteDimensional ℂ (TensorRegister n (Fin d)) :=
  (registerBasis (Fin n → Fin d)).toOrthonormalBasis.toBasis.finiteDimensional_of_finite

abbrev RootFock (d : ℕ) := MultimodeCoherent.Fock (Fintype.card (PositiveRoot d))

def fockOccupation (d : ℕ) (k : PositiveRoot d → ℕ) : Fin (Fintype.card (PositiveRoot d)) → ℕ :=
  fun i => k ((Fintype.equivFin (PositiveRoot d)).symm i)

theorem fockOccupation_injective (d : ℕ) : Function.Injective (fockOccupation d) := by
  intro k l h
  funext a
  have he := congrFun h ((Fintype.equivFin (PositiveRoot d)) a)
  simpa only [fockOccupation, Equiv.symm_apply_apply] using he

def cutoffNumberFrame (d R : ℕ) (i : CutoffIndex d R) : RootFock d :=
  MultimodeCoherentGaussianMixture.numberBasis _ (fockOccupation d (cutoffOccupation d R i).val)

theorem cutoffNumberFrame_orthonormal (d R : ℕ) : Orthonormal ℂ (cutoffNumberFrame d R) := by
  apply (MultimodeCoherentGaussianMixture.numberBasis _).orthonormal.comp
  intro i j h
  apply (cutoffOccupation d R).injective
  exact Subtype.ext (fockOccupation_injective d h)

/-- The physical cutoff regarded as a subspace of the whole cyclic sector. -/
def sectorCutoff (Ω : TensorRegister n (Fin d)) (R : ℕ) : Submodule ℂ (cyclicSector Ω) :=
  (cyclicCutoff Ω (R : ℤ)).comap (cyclicSector Ω).subtype

def sectorCutoffEquiv (Ω : TensorRegister n (Fin d)) (R : ℕ) :
    sectorCutoff Ω R ≃ₗᵢ[ℂ] cyclicCutoff Ω (R : ℤ) where
  toLinearEquiv := Submodule.comapSubtypeEquivOfLe (cyclicCutoff_le_cyclicSector Ω (R : ℤ))
  norm_map' _ := rfl

def sectorCutoffBasis (Ω : TensorRegister n (Fin d)) (mu : Fin d → ℕ) (R : ℕ)
    (hgap : ∀ a : PositiveRoot d, 0 < rootGap mu a)
    (hli : LinearIndependent ℂ (cutoffRawFrame Ω mu R)) :
    OrthonormalBasis (CutoffIndex d R) ℂ (sectorCutoff Ω R) :=
  (cutoffOrthonormalBasis Ω mu R hgap hli).map (sectorCutoffEquiv Ω R).symm

@[simp] theorem sectorCutoffBasis_coe (Ω : TensorRegister n (Fin d)) (mu : Fin d → ℕ) (R : ℕ)
    (hgap : ∀ a : PositiveRoot d, 0 < rootGap mu a)
    (hli : LinearIndependent ℂ (cutoffRawFrame Ω mu R)) (i : CutoffIndex d R) :
    (sectorCutoffBasis Ω mu R hgap hli i : cyclicSector Ω) = cutoffSectorFrame Ω mu R i := by
  apply Subtype.ext
  simp only [sectorCutoffBasis, OrthonormalBasis.map_apply]
  exact cutoffOrthonormalBasis_coe Ω mu R hgap hli i

/-- The literal multimode vacuum used for every discarded physical component. -/
def rootVacuum (d : ℕ) : RootFock d :=
  MultimodeCoherentGaussianMixture.numberBasis _ (fun _ => 0)

theorem rootVacuum_norm (d : ℕ) : ‖rootVacuum d‖ = 1 :=
  (MultimodeCoherentGaussianMixture.numberBasis _).orthonormal.norm_eq_one _

/-- Compress the complete physical sector onto its actual root-height cutoff,
transport the common ONB to number vectors, and replace lost trace by vacuum. -/
def sectorToFock (Ω : TensorRegister n (Fin d)) (mu : Fin d → ℕ) (R : ℕ)
    (hgap : ∀ a : PositiveRoot d, 0 < rootGap mu a)
    (hli : LinearIndependent ℂ (cutoffRawFrame Ω mu R)) : QuantumChannel (cyclicSector Ω) (RootFock d) :=
  frameForwardChannel (sectorCutoff Ω R) (sectorCutoffBasis Ω mu R hgap hli)
    (cutoffNumberFrame d R) (cutoffNumberFrame_orthonormal d R)
    (DensityState.pure (rootVacuum d) (rootVacuum_norm d))

/-- Reverse compression acts on the complete infinite Fock space; discarded
occupation mass is replaced by the physical highest state. -/
def fockToSector (Ω : TensorRegister n (Fin d)) (mu : Fin d → ℕ) (R : ℕ)
    (hΩ : ‖Ω‖ = 1)
    (hgap : ∀ a : PositiveRoot d, 0 < rootGap mu a)
    (hli : LinearIndependent ℂ (cutoffRawFrame Ω mu R)) : QuantumChannel (RootFock d) (cyclicSector Ω) :=
  frameReverseChannel (sectorCutoff Ω R) (sectorCutoffBasis Ω mu R hgap hli)
    (cutoffNumberFrame d R) (cutoffNumberFrame_orthonormal d R)
    (DensityState.pure ⟨Ω, highest_mem_cyclicSector Ω⟩ hΩ)

theorem sectorToFock_frame (Ω : TensorRegister n (Fin d)) (mu : Fin d → ℕ) (R : ℕ)
    (hgap : ∀ a : PositiveRoot d, 0 < rootGap mu a)
    (hli : LinearIndependent ℂ (cutoffRawFrame Ω mu R)) (i : CutoffIndex d R) :
    (sectorToFock Ω mu R hgap hli).toLinearMap (vectorProjector (cutoffSectorFrame Ω mu R i)) =
      vectorProjector (cutoffNumberFrame d R i) := by
  rw [← sectorCutoffBasis_coe Ω mu R hgap hli i]
  exact (frameForwardChannel_retained _ _ _ _ _ _).trans
    (congrArg vectorProjector (basisFrameIsometry_basis _ _ _ _ i))

theorem fockToSector_frame (Ω : TensorRegister n (Fin d)) (mu : Fin d → ℕ) (R : ℕ)
    (hΩ : ‖Ω‖ = 1)
    (hgap : ∀ a : PositiveRoot d, 0 < rootGap mu a)
    (hli : LinearIndependent ℂ (cutoffRawFrame Ω mu R)) (i : CutoffIndex d R) :
    (fockToSector Ω mu R hΩ hgap hli).toLinearMap (vectorProjector (cutoffNumberFrame d R i)) =
      vectorProjector (cutoffSectorFrame Ω mu R i) := by
  rw [← sectorCutoffBasis_coe Ω mu R hgap hli i,
    ← basisFrameIsometry_basis (sectorCutoff Ω R) (sectorCutoffBasis Ω mu R hgap hli)
      (cutoffNumberFrame d R) (cutoffNumberFrame_orthonormal d R) i]
  exact frameReverseChannel_retained _ _ _ _ _ _

end Cloning.TensorLAN
