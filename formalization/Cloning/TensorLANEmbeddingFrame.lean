import Cloning.TensorLANEmbeddingChannel
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-! Finite-frame partial isometries, extended by zero on the complete input
Hilbert space. Their adjoints give the reverse physical compression. -/
noncomputable section
open scoped BigOperators InnerProductSpace
namespace Cloning.TensorLAN
open Cloning.InfiniteTraceClass Module
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {ι : Type*} [Fintype ι]
variable (S : Submodule ℂ H) [S.HasOrthogonalProjection]

/-- Send a complete orthonormal basis onto the prescribed orthonormal target frame. -/
def basisFrameIsometry (b : OrthonormalBasis ι ℂ S) (f : ι → K) (hf : Orthonormal ℂ f) :
    S →ₗᵢ[ℂ] K :=
  (b.toBasis.constr ℂ f).isometryOfOrthonormal (v := b.toBasis) b.orthonormal (by
    simpa only [Function.comp_def, Basis.constr_basis] using hf)

@[simp] theorem basisFrameIsometry_basis (b : OrthonormalBasis ι ℂ S)
    (f : ι → K) (hf : Orthonormal ℂ f) (i : ι) : basisFrameIsometry S b f hf (b i) = f i := by
  exact Basis.constr_basis _ _ _ i

/-- The finite-frame map on every input vector: orthogonally compress, then transport. -/
def frameTransport (b : OrthonormalBasis ι ℂ S) (f : ι → K) (hf : Orthonormal ℂ f) : H →L[ℂ] K :=
  (basisFrameIsometry S b f hf).toContinuousLinearMap.comp S.orthogonalProjection

theorem frameTransport_contraction (b : OrthonormalBasis ι ℂ S)
    (f : ι → K) (hf : Orthonormal ℂ f) (x : H) : ‖frameTransport S b f hf x‖ ≤ ‖x‖ := by
  change ‖basisFrameIsometry S b f hf (S.orthogonalProjection x)‖ ≤ _
  rw [LinearIsometry.norm_map]
  exact S.norm_orthogonalProjection_apply_le x

theorem frameTransport_on_subspace (b : OrthonormalBasis ι ℂ S)
    (f : ι → K) (hf : Orthonormal ℂ f) (x : S) :
    frameTransport S b f hf x = basisFrameIsometry S b f hf x := by
  change basisFrameIsometry S b f hf (S.orthogonalProjection x) = _
  congr 1
  apply Subtype.ext
  exact Submodule.starProjection_eq_self_iff.mpr x.property

@[simp] theorem frameTransport_basis (b : OrthonormalBasis ι ℂ S)
    (f : ι → K) (hf : Orthonormal ℂ f) (i : ι) :
    frameTransport S b f hf (b i) = f i := by
  rw [frameTransport_on_subspace, basisFrameIsometry_basis]

theorem frameTransport_adjoint_contraction (b : OrthonormalBasis ι ℂ S)
    (f : ι → K) (hf : Orthonormal ℂ f) (x : K) :
    ‖(frameTransport S b f hf).adjoint x‖ ≤ ‖x‖ := by
  have hnorm : ‖frameTransport S b f hf‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ (by norm_num) (by
      intro y
      simpa only [one_mul] using frameTransport_contraction S b f hf y)
  calc
    _ ≤ ‖(frameTransport S b f hf).adjoint‖ * ‖x‖ := (frameTransport S b f hf).adjoint.le_opNorm x
    _ = ‖frameTransport S b f hf‖ * ‖x‖ := by rw [ContinuousLinearMap.adjoint.norm_map]
    _ ≤ 1 * ‖x‖ := mul_le_mul_of_nonneg_right hnorm (norm_nonneg x)
    _ = ‖x‖ := one_mul _

/-- The reverse partial isometry exactly recovers every retained vector. -/
theorem frameTransport_adjoint_isometry (b : OrthonormalBasis ι ℂ S)
    (f : ι → K) (hf : Orthonormal ℂ f) (x : S) :
    (frameTransport S b f hf).adjoint (basisFrameIsometry S b f hf x) = (x : H) := by
  apply ext_inner_left ℂ
  intro y
  rw [ContinuousLinearMap.adjoint_inner_right]
  change ⟪basisFrameIsometry S b f hf (S.orthogonalProjection y),
    basisFrameIsometry S b f hf x⟫_ℂ = _
  rw [LinearIsometry.inner_map_map]
  exact S.inner_orthogonalProjection_eq_of_mem_right x y

@[simp] theorem frameTransport_adjoint_basis (b : OrthonormalBasis ι ℂ S)
    (f : ι → K) (hf : Orthonormal ℂ f) (i : ι) :
    (frameTransport S b f hf).adjoint (f i) = (b i : H) := by
  rw [← basisFrameIsometry_basis S b f hf i, frameTransport_adjoint_isometry]

/-- Forward and backward channels use fixed explicit replacement states. -/
def frameForwardChannel (b : OrthonormalBasis ι ℂ S)
    (f : ι → K) (hf : Orthonormal ℂ f) (σ : DensityState K) : QuantumChannel H K :=
  QuantumChannel.ofContraction (frameTransport S b f hf) (frameTransport_contraction S b f hf) σ

def frameReverseChannel (b : OrthonormalBasis ι ℂ S)
    (f : ι → K) (hf : Orthonormal ℂ f) (ρ : DensityState H) : QuantumChannel K H :=
  QuantumChannel.ofContraction (frameTransport S b f hf).adjoint
    (frameTransport_adjoint_contraction S b f hf) ρ

theorem frameForwardChannel_retained (b : OrthonormalBasis ι ℂ S)
    (f : ι → K) (hf : Orthonormal ℂ f) (σ : DensityState K) (x : S) :
    (frameForwardChannel S b f hf σ).toLinearMap (vectorProjector (x : H)) =
      vectorProjector (basisFrameIsometry S b f hf x) := by
  rw [frameForwardChannel, QuantumChannel.ofContraction_vectorProjector_of_norm_eq]
  · rw [frameTransport_on_subspace]
  · rw [frameTransport_on_subspace, LinearIsometry.norm_map]
    rfl

theorem frameReverseChannel_retained (b : OrthonormalBasis ι ℂ S)
    (f : ι → K) (hf : Orthonormal ℂ f) (ρ : DensityState H) (x : S) :
    (frameReverseChannel S b f hf ρ).toLinearMap
      (vectorProjector (basisFrameIsometry S b f hf x)) = vectorProjector (x : H) := by
  rw [frameReverseChannel, QuantumChannel.ofContraction_vectorProjector_of_norm_eq]
  · rw [frameTransport_adjoint_isometry]
  · rw [frameTransport_adjoint_isometry, LinearIsometry.norm_map]
    rfl

end Cloning.TensorLAN
