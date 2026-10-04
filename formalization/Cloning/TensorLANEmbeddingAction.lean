import Cloning.TensorLANEmbeddingPhysical
import Cloning.InfiniteTraceClassNormalPart

/-! Exact action on every finite cutoff matrix, including coherences, and
trace-norm comparison bounds for positive input states. -/
noncomputable section
open scoped BigOperators InnerProductSpace ComplexOrder
namespace Cloning.InfiniteTraceClass
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

@[simp] theorem traceCLM_rankOneOperator (x y : H) :
    traceCLM (rankOneOperator x y) = ⟪y, x⟫_ℂ := trace_rankOne_general x y

theorem conjugationLinearMap_rankOneOperator (V : H →L[ℂ] K) (x y : H) :
    conjugationLinearMap V (rankOneOperator x y) = rankOneOperator (V x) (V y) := by
  apply Subtype.ext
  ext z
  change V (⟪y, V.adjoint z⟫_ℂ • x) = ⟪V y, z⟫_ℂ • V x
  rw [map_smul, ContinuousLinearMap.adjoint_inner_right]

/-- A concrete finite matrix realized in an arbitrary Hilbert-space frame. -/
def frameMatrix {ι : Type*} [Fintype ι] (f : ι → H) (A : Matrix ι ι ℂ) : TraceClass H :=
  ∑ i, ∑ j, A i j • rankOneOperator (f i) (f j)

end Cloning.InfiniteTraceClass

namespace Cloning.TensorLAN
open Cloning.InfiniteTraceClass
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {ι : Type*} [Fintype ι]
variable (S : Submodule ℂ H) [S.HasOrthogonalProjection]

/-- Exact preservation of arbitrary retained coherences. -/
theorem frameForwardChannel_rankOne (b : OrthonormalBasis ι ℂ S)
    (f : ι → K) (hf : Orthonormal ℂ f) (σ : DensityState K) (x y : S) :
    (frameForwardChannel S b f hf σ).toLinearMap (rankOneOperator (x : H) (y : H)) =
      rankOneOperator (basisFrameIsometry S b f hf x) (basisFrameIsometry S b f hf y) := by
  rw [frameForwardChannel, QuantumChannel.ofContraction_apply, conjugationLinearMap_rankOneOperator,
    traceCLM_rankOneOperator, traceCLM_rankOneOperator, frameTransport_on_subspace,
    frameTransport_on_subspace, LinearIsometry.inner_map_map]
  simp only [Submodule.coe_inner, sub_self, zero_smul, add_zero]

theorem frameReverseChannel_rankOne (b : OrthonormalBasis ι ℂ S)
    (f : ι → K) (hf : Orthonormal ℂ f) (ρ : DensityState H) (x y : S) :
    (frameReverseChannel S b f hf ρ).toLinearMap
      (rankOneOperator (basisFrameIsometry S b f hf x) (basisFrameIsometry S b f hf y)) =
      rankOneOperator (x : H) (y : H) := by
  rw [frameReverseChannel, QuantumChannel.ofContraction_apply, conjugationLinearMap_rankOneOperator,
    frameTransport_adjoint_isometry, frameTransport_adjoint_isometry,
    traceCLM_rankOneOperator, traceCLM_rankOneOperator, LinearIsometry.inner_map_map]
  simp only [Submodule.coe_inner, sub_self, zero_smul, add_zero]

/-- Every complex matrix in the retained cutoff is transported exactly. -/
theorem frameForwardChannel_matrix (b : OrthonormalBasis ι ℂ S)
    (f : ι → K) (hf : Orthonormal ℂ f) (σ : DensityState K) (A : Matrix ι ι ℂ) :
    (frameForwardChannel S b f hf σ).toLinearMap (frameMatrix (fun i => (b i : H)) A) =
      frameMatrix f A := by
  simp only [frameMatrix, map_sum, map_smul, frameForwardChannel_rankOne, basisFrameIsometry_basis]

theorem frameReverseChannel_matrix (b : OrthonormalBasis ι ℂ S)
    (f : ι → K) (hf : Orthonormal ℂ f) (ρ : DensityState H) (A : Matrix ι ι ℂ) :
    (frameReverseChannel S b f hf ρ).toLinearMap (frameMatrix f A) =
      frameMatrix (fun i => (b i : H)) A := by
  have he (i j : ι) : (frameReverseChannel S b f hf ρ).toLinearMap
      (rankOneOperator (f i) (f j)) = rankOneOperator (b i : H) (b j : H) := by
    simpa only [basisFrameIsometry_basis] using
      frameReverseChannel_rankOne S b f hf ρ (b i) (b j)
  simp only [frameMatrix, map_sum, map_smul, he]

/-- Input approximation controls output approximation without any extra
constant, because the maps are proved positive and trace preserving. -/
theorem frameForwardChannel_matrix_error (b : OrthonormalBasis ι ℂ S)
    (f : ι → K) (hf : Orthonormal ℂ f) (σ : DensityState K)
    (A : TraceClass H) (hA : 0 ≤ A.1) (M : Matrix ι ι ℂ)
    (hM : 0 ≤ (frameMatrix (fun i => (b i : H)) M).1) :
    ‖(frameForwardChannel S b f hf σ).toLinearMap A - frameMatrix f M‖ ≤
      ‖A - frameMatrix (fun i => (b i : H)) M‖ := by
  rw [← frameForwardChannel_matrix S b f hf σ M]
  exact (frameForwardChannel S b f hf σ).toPositiveTracePreservingMap.norm_map_sub_le _ _ hA hM

theorem frameReverseChannel_matrix_error (b : OrthonormalBasis ι ℂ S)
    (f : ι → K) (hf : Orthonormal ℂ f) (ρ : DensityState H)
    (A : TraceClass K) (hA : 0 ≤ A.1) (M : Matrix ι ι ℂ)
    (hM : 0 ≤ (frameMatrix f M).1) :
    ‖(frameReverseChannel S b f hf ρ).toLinearMap A - frameMatrix (fun i => (b i : H)) M‖ ≤
      ‖A - frameMatrix f M‖ := by
  rw [← frameReverseChannel_matrix S b f hf ρ M]
  exact (frameReverseChannel S b f hf ρ).toPositiveTracePreservingMap.norm_map_sub_le _ _ hA hM

section Physical
open Cloning.TensorLie Cloning.PCT
variable {n d : ℕ}
local instance (n d : ℕ) : FiniteDimensional ℂ (TensorRegister n (Fin d)) :=
  (registerBasis (Fin n → Fin d)).toOrthonormalBasis.toBasis.finiteDimensional_of_finite

theorem sectorToFock_matrix (Ω : TensorRegister n (Fin d)) (mu : Fin d → ℕ) (R : ℕ)
    (hgap : ∀ a : PositiveRoot d, 0 < rootGap mu a)
    (hli : LinearIndependent ℂ (cutoffRawFrame Ω mu R))
    (M : Matrix (CutoffIndex d R) (CutoffIndex d R) ℂ) :
    (sectorToFock Ω mu R hgap hli).toLinearMap (frameMatrix (cutoffSectorFrame Ω mu R) M) =
      frameMatrix (cutoffNumberFrame d R) M := by
  simpa only [sectorCutoffBasis_coe] using frameForwardChannel_matrix (sectorCutoff Ω R)
    (sectorCutoffBasis Ω mu R hgap hli) (cutoffNumberFrame d R) (cutoffNumberFrame_orthonormal d R)
    (DensityState.pure (rootVacuum d) (rootVacuum_norm d)) M

theorem fockToSector_matrix (Ω : TensorRegister n (Fin d)) (mu : Fin d → ℕ) (R : ℕ)
    (hΩ : ‖Ω‖ = 1)
    (hgap : ∀ a : PositiveRoot d, 0 < rootGap mu a)
    (hli : LinearIndependent ℂ (cutoffRawFrame Ω mu R))
    (M : Matrix (CutoffIndex d R) (CutoffIndex d R) ℂ) :
    (fockToSector Ω mu R hΩ hgap hli).toLinearMap (frameMatrix (cutoffNumberFrame d R) M) =
      frameMatrix (cutoffSectorFrame Ω mu R) M := by
  simpa only [sectorCutoffBasis_coe] using frameReverseChannel_matrix (sectorCutoff Ω R)
    (sectorCutoffBasis Ω mu R hgap hli) (cutoffNumberFrame d R) (cutoffNumberFrame_orthonormal d R)
    (DensityState.pure ⟨Ω, highest_mem_cyclicSector Ω⟩ hΩ) M

end Physical

end Cloning.TensorLAN
