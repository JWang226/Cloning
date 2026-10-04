import Cloning.PCTRankPurificationFrames

/-! Exact equality of the normalized compressed ambient Haar moment and
the smaller-rank Haar moment, retaining all physical multiplicities. -/
noncomputable section
open scoped BigOperators Classical Matrix Kronecker Matrix.Norms.L2Operator
open Matrix MeasureTheory
namespace Cloning.PCTRankPurification
open Cloning.TensorLie Cloning.PCTPurificationChannel
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
variable {n r : ℕ} [NeZero r]
local instance (k : ℕ) : NeZero (r+k) := ⟨by have := NeZero.ne r; omega⟩

variable (L : List (PhysicalHighestTensor n r))
  (hL : OrthogonalFamily ℂ (fun i : Fin L.length => (L.get i).sector)
    (fun i => (L.get i).sector.subtypeₗᵢ))
  (hspan : (⨆i : Fin L.length,(L.get i).sector)=⊤)

include hL hspan in
theorem normalizedCoordinateAction_moment (k : ℕ)
    (N : Matrix (Fin n → Fin (r+k)) (Fin n → Fin (r+k)) ℂ) (hN : Nᴴ=N)
    (hNE : ∀i : Fin L.length,N*(L.get i).liftEmbeddingMatrix k=
      (rankMomentScale (L.get i).weight (L.get i).weight_antitone k : ℂ) • (L.get i).liftEmbeddingMatrix k) :
    matrixMomentIntegral unitaryHaar
      (fun U : unitary (Matrix (Fin (r+k)) (Fin (r+k)) ℂ) => normalizedCoordinateAction k N U)=
      matrixMomentIntegral unitaryHaar
        (fun V : unitary (Matrix (Fin r) (Fin r) ℂ) => tensorPower n V.val) := by
  have hf : Integrable (fun U : unitary (Matrix (Fin (r+k)) (Fin (r+k)) ℂ) =>
      matrixMoment (normalizedCoordinateAction k N U)) unitaryHaar := by
    have hh := integrable_matrixMoment_mul unitaryHaar
      (fun U : unitary (Matrix (Fin (r+k)) (Fin (r+k)) ℂ) => tensorPower n (U.val*coordinateInclusionMatrix r k))
      (integrable_rectangularMoment n (coordinateInclusionMatrix r k))
      ((coordinateTensorMatrix n r k)ᴴ*N) (1 : Matrix (Fin n → Fin r) (Fin n → Fin r) ℂ)
    simpa only [tensorPower_mul,← coordinateTensorMatrix_eq_tensorPower,Matrix.mul_one,
      normalizedCoordinateAction,Matrix.mul_assoc] using hh
  have hg : Integrable (fun V : unitary (Matrix (Fin r) (Fin r) ℂ) =>
      matrixMoment (tensorPower n V.val)) unitaryHaar := by
    simpa only [Matrix.mul_one,rectangularMoment_eq_matrixMoment] using
      integrable_rectangularMoment n (1 : Matrix (Fin r) (Fin r) ℂ)
  apply matrixMomentIntegral_eq_of_frame_coefficients _ _ _ _ hf hg (physicalFrame L) (physicalFrame L)
    (physicalFrame_complete L hL hspan) (physicalFrame_complete L hL hspan)
  rintro ⟨i,a⟩ ⟨j,c⟩ ⟨s,b⟩ ⟨t,e⟩
  simp only [physicalFrame_block]
  by_cases his : i=s
  · subst s
    by_cases hjt : j=t
    · subst t
      simp only [normalizedCoordinateAction_block_diagonal _ _ _ hN _ (hNE _),
        tensorPower_block_diagonal,Matrix.smul_apply,smul_eq_mul,map_mul,
        Complex.star_def,Complex.conj_ofReal]
      have hcoeff := normalized_rank_compressed_coefficients
        (L.get i).weight (L.get j).weight (L.get i).weight_antitone (L.get j).weight_antitone k a b c e
      rw [← integral_const_mul] at hcoeff
      simpa only [Complex.star_def,mul_assoc,mul_left_comm,mul_comm] using hcoeff
    · have hbig := embeddingMatrix_orthogonal (fun i : Fin L.length => (L.get i).coordinateLift k)
        (coordinateLift_family_orthogonal (fun i : Fin L.length => L.get i) hL k) j t hjt
      have hsmall := embeddingMatrix_orthogonal (fun i : Fin L.length => L.get i) hL j t hjt
      simp only [normalizedCoordinateAction_block_orthogonal _ _ _ _ hN _ (hNE j) hbig,
        tensorPower_block_orthogonal _ _ hsmall,Matrix.zero_apply,star_zero,mul_zero,integral_zero]
  · have hbig := embeddingMatrix_orthogonal (fun i : Fin L.length => (L.get i).coordinateLift k)
      (coordinateLift_family_orthogonal (fun i : Fin L.length => L.get i) hL k) i s his
    have hsmall := embeddingMatrix_orthogonal (fun i : Fin L.length => L.get i) hL i s his
    simp only [normalizedCoordinateAction_block_orthogonal _ _ _ _ hN _ (hNE i) hbig,
      tensorPower_block_orthogonal _ _ hsmall,Matrix.zero_apply,zero_mul,integral_zero]

end Cloning.PCTRankPurification
