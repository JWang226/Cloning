import Cloning.PhysicalFlatConverseHaar
import Cloning.MatrixFidelityMixtures
import Cloning.MatrixFidelityBounds
import Cloning.MatrixFidelityEmbedding
import Mathlib.Analysis.Convex.Integral

/-! Fidelity Jensen inequality for the actual compact Haar orbit, followed
by the exact physical sector dimension-ratio bound. -/
noncomputable section
open scoped BigOperators InnerProductSpace Matrix Topology Matrix.Norms.L2Operator MatrixOrder ComplexOrder
open MeasureTheory
namespace Cloning.PhysicalFlatConverse
open Cloning.TensorLie Cloning.MatrixFidelity Cloning.PCTPurificationChannel
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
variable {I : Type*} [Fintype I] [DecidableEq I]

local instance : CStarAlgebra (Matrix I I ℂ) where

/-- Jensen on a compact family of actual positive matrices. Integrability
and positivity of the averaged family are obtained from the stated objects. -/
theorem fidelity_compact_integral_le {A : Type*} [TopologicalSpace A] [CompactSpace A]
    [MeasurableSpace A] [BorelSpace A] (ν : Measure A) [IsProbabilityMeasure ν]
    (f : A → Matrix I I ℂ) (hf : Continuous f) (hp : ∀ a, (f a).PosSemidef)
    (T : Matrix I I ℂ) (hT : T.PosSemidef) :
    (∫ a, fidelity (f a) T ∂ν) ≤ fidelity (∫ a, f a ∂ν) T := by
  have hpair : Continuous (fun M : Matrix I I ℂ => (M,T)) :=
    continuous_id.prodMk continuous_const
  have hg : ContinuousOn (fun M : Matrix I I ℂ => fidelity M T) {M | M.PosSemidef} := by
    apply (continuousOn_fidelity (n := I)).comp hpair.continuousOn
    intro M hM
    exact ⟨hM,hT⟩
  have hs : IsClosed {M : Matrix I I ℂ | M.PosSemidef} := by
    simpa only [Matrix.nonneg_iff_posSemidef] using
      (isClosed_le continuous_const continuous_id : IsClosed {M : Matrix I I ℂ | 0 ≤ M})
  have hcont : Continuous (fun a => fidelity (f a) T) :=
    hg.comp_continuous hf hp
  exact (concaveOn_fidelity_left T).le_map_integral hg hs (ae_of_all ν hp)
    (hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    (hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))

variable {d : ℕ} [Nonempty (Fin d)]

theorem partitionTwirl_eq_real (mu : Fin d → ℕ) (hmu : Antitone mu)
    (M : Matrix (PartitionIndex mu hmu) (PartitionIndex mu hmu) ℂ) (hM : M.PosSemidef) :
    partitionTwirl mu hmu M = (M.trace.re / (partitionDimension mu hmu : ℝ)) •
      (1 : Matrix (PartitionIndex mu hmu) _ ℂ) := by
  have ht : M.trace = (M.trace.re : ℂ) := by
    apply Complex.ext <;> simp [trace_im_zero hM]
  have hc : M.trace / (partitionDimension mu hmu : ℂ) =
      ((M.trace.re / (partitionDimension mu hmu : ℝ) : ℝ) : ℂ) := by
    rw [Complex.ofReal_div, Complex.ofReal_natCast, ht]
    simp only [Complex.ofReal_re]
  rw [partitionTwirl_eq, hc]
  exact (RCLike.real_smul_eq_coe_smul (K := ℂ) _ _).symm

/-- Haar orbit average fidelity is bounded by the exact scalar-identity
value. The averaged matrix is the actual physical sector twirl. -/
theorem integral_partition_fidelity_le
    (mu : Fin d → ℕ) (hmu : Antitone mu)
    (M T : Matrix (PartitionIndex mu hmu) (PartitionIndex mu hmu) ℂ)
    (hM : M.PosSemidef) (hT : T.PosSemidef) :
    (∫ U : unitary (Matrix (Fin d) (Fin d) ℂ),
      fidelity (partitionActionMatrix mu hmu U * M * (partitionActionMatrix mu hmu U)ᴴ) T
        ∂unitaryHaar) ≤
      fidelity ((M.trace.re / (partitionDimension mu hmu : ℝ)) •
        (1 : Matrix (PartitionIndex mu hmu) _ ℂ)) T := by
  have hh := fidelity_compact_integral_le unitaryHaar
    (fun U : unitary (Matrix (Fin d) (Fin d) ℂ) =>
      partitionActionMatrix mu hmu U * M * (partitionActionMatrix mu hmu U)ᴴ)
    (continuous_partitionSandwich mu hmu M)
    (fun U => hM.mul_mul_conjTranspose_same _) T hT
  change _ ≤ fidelity (partitionTwirl mu hmu M) T at hh
  rwa [partitionTwirl_eq_real mu hmu M hM] at hh

/-- Exact finite-sector dimension loss for any positive channel output block,
with no covariance, normalization, or invariant-output assumption. -/
theorem integral_partition_flat_fidelity_le
    (mu : Fin d → ℕ) (hmu : Antitone mu)
    (M P : Matrix (PartitionIndex mu hmu) (PartitionIndex mu hmu) ℂ)
    (hM : M.PosSemidef) (hP : P.PosSemidef) (hPP : P*P=P)
    (q s : ℝ) (hq : 0 ≤ q) (hs : 0 < s) (htrace : P.trace.re = s) :
    (∫ U : unitary (Matrix (Fin d) (Fin d) ℂ),
      fidelity (partitionActionMatrix mu hmu U * M * (partitionActionMatrix mu hmu U)ᴴ) ((q/s) • P)
        ∂unitaryHaar) ≤
      Real.sqrt (M.trace.re * q / ((partitionDimension mu hmu : ℝ) / s)) := by
  apply (integral_partition_fidelity_le mu hmu M ((q/s) • P) hM
    (hP.smul (div_nonneg hq hs.le))).trans_eq
  exact fidelity_flat_projector_block _ q _ s (trace_re_nonneg hM) hq
    (Nat.cast_pos.mpr (partitionDimension_pos mu hmu)) hs hP hPP htrace

end Cloning.PhysicalFlatConverse
