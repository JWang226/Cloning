import Cloning.PCTRankPurificationMatrices
import Cloning.TensorSchurHaarCompression

/-! The normalized compressed ambient Haar coefficients are exactly those
of the smaller physical representation. -/
noncomputable section
open scoped BigOperators Classical InnerProductSpace Matrix Matrix.Norms.L2Operator
open MeasureTheory
namespace Cloning.TensorLie
open Cloning.PCTPurificationChannel
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
variable {r : ℕ} [NeZero r]
local instance (k : ℕ) : NeZero (r+k) := ⟨by have := NeZero.ne r; omega⟩

def rankMomentScale (mu : Fin r → ℕ) (hmu : Antitone mu) (k : ℕ) : ℝ :=
  Real.sqrt ((partitionDimension (padPartition mu k) (padPartition_antitone mu hmu k) : ℝ)/
    (partitionDimension mu hmu : ℝ))

theorem rankMomentScale_pos (mu : Fin r → ℕ) (hmu : Antitone mu) (k : ℕ) :
    0<rankMomentScale mu hmu k :=
  Real.sqrt_pos.2 (div_pos (Nat.cast_pos.2 (partitionDimension_pos _ _))
    (Nat.cast_pos.2 (partitionDimension_pos _ _)))

theorem rankMomentScale_square (mu : Fin r → ℕ) (hmu : Antitone mu) (k : ℕ) :
    (rankMomentScale mu hmu k : ℂ)*(rankMomentScale mu hmu k : ℂ)*
      (partitionDimension (padPartition mu k) (padPartition_antitone mu hmu k) : ℂ)⁻¹ =
      (partitionDimension mu hmu : ℂ)⁻¹ := by
  have he : rankMomentScale mu hmu k*rankMomentScale mu hmu k/
      (partitionDimension (padPartition mu k) (padPartition_antitone mu hmu k) : ℝ) =
      (partitionDimension mu hmu : ℝ)⁻¹ := by
    rw [rankMomentScale,Real.mul_self_sqrt (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))]
    have ha : (partitionDimension (padPartition mu k) (padPartition_antitone mu hmu k) : ℝ)≠0 :=
      Nat.cast_ne_zero.2 (partitionDimension_pos _ _).ne'
    have hb : (partitionDimension mu hmu : ℝ)≠0 := Nat.cast_ne_zero.2 (partitionDimension_pos _ _).ne'
    field_simp
  simp only [div_eq_mul_inv] at he
  have hh := congrArg (fun x : ℝ => (x : ℂ)) he
  simpa only [Complex.ofReal_mul,Complex.ofReal_inv,Complex.ofReal_natCast] using hh

theorem padPartition_injective (k : ℕ) : Function.Injective (fun mu : Fin r → ℕ => padPartition mu k) := by
  intro mu nu h
  funext a
  simpa only [padPartition_left] using congrFun h (Fin.castAdd k a)

/-- Exact agreement of all second moments after the physical dimension normalization. -/
theorem normalized_rank_compressed_coefficients (mu nu : Fin r → ℕ)
    (hmu : Antitone mu) (hnu : Antitone nu) (k : ℕ)
    (a b : PartitionIndex mu hmu) (c e : PartitionIndex nu hnu) :
    (rankMomentScale mu hmu k : ℂ)*(rankMomentScale nu hnu k : ℂ)*
      (∫ U : unitary (Matrix (Fin (r+k)) (Fin (r+k)) ℂ),
        compressedPartitionAction (padPartition mu k) (padPartition_antitone mu hmu k)
          (rankSectorMatrix mu hmu k) U a b *
        star (compressedPartitionAction (padPartition nu k) (padPartition_antitone nu hnu k)
          (rankSectorMatrix nu hnu k) U c e) ∂unitaryHaar) =
      ∫ V : unitary (Matrix (Fin r) (Fin r) ℂ),
        partitionActionMatrix mu hmu V a b*star (partitionActionMatrix nu hnu V c e) ∂unitaryHaar := by
  by_cases h : mu=nu
  · subst nu
    rw [integral_compressedPartition_coefficients_same _ _ _ (rankSectorMatrix_isometry mu hmu k),
      integral_partition_coefficients_same]
    by_cases hab : a=c ∧ b=e
    · rw [if_pos hab,if_pos hab]
      exact rankMomentScale_square mu hmu k
    · rw [if_neg hab,if_neg hab,mul_zero]
  · rw [integral_compressedPartition_coefficients_ne _ _ _ _
      (fun he => h (padPartition_injective k he)),integral_partition_coefficients_ne _ _ _ _ h,mul_zero]

end Cloning.TensorLie
