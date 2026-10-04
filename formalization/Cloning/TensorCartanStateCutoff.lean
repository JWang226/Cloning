import Cloning.TensorCartanChannel
import Cloning.TensorCartanCutoffAmplitude
import Cloning.TensorGibbsCutoffState

/-! Exact product-cutoff support of the actual Cartan inclusion. -/
noncomputable section
open scoped BigOperators InnerProductSpace
namespace Cloning.TensorLie
open Cloning.PCT
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {d : ℕ}

theorem cartanAmbientInclusion_mem_productCutoff
    (mu nu : Fin d → ℕ) (hmu : Antitone mu) (hnu : Antitone nu) (R : ℕ)
    (x : cyclicSector (partitionHighestTensor (fun a => mu a + nu a)
      (sumPartition_antitone mu nu hmu hnu)))
    (hx : (x : TensorRegister _ (Fin d)) ∈
      cyclicCutoff (partitionHighestTensor _ (sumPartition_antitone mu nu hmu hnu)) (R : ℤ)) :
    cartanAmbientInclusion mu nu hmu hnu x ∈
      tensorProductSector (cyclicCutoff (partitionHighestTensor mu hmu) (R : ℤ))
        (cyclicCutoff (partitionHighestTensor nu hnu) (R : ℤ)) := by
  let P := tensorProductSector (cyclicCutoff (partitionHighestTensor mu hmu) (R : ℤ))
    (cyclicCutoff (partitionHighestTensor nu hnu) (R : ℤ))
  let Ω := partitionHighestTensor (fun a => mu a + nu a) (sumPartition_antitone mu nu hmu hnu)
  let S := (P.comap (cartanAmbientInclusion mu nu hmu hnu).toLinearMap).map (cyclicSector Ω).subtype
  have hS : cyclicCutoff Ω (R : ℤ) ≤ S := by
    apply Submodule.span_le.mpr
    rintro y ⟨w, hw, rfl⟩
    refine ⟨⟨loweringWord Ω w, loweringWord_mem_cyclicSector Ω w⟩, ?_, rfl⟩
    change cartanAmbientInclusion mu nu hmu hnu
      ⟨loweringWord Ω w, loweringWord_mem_cyclicSector Ω w⟩ ∈ P
    rw [show cartanAmbientInclusion mu nu hmu hnu
        ⟨loweringWord Ω w, loweringWord_mem_cyclicSector Ω w⟩ =
        loweringWord (cartanHighest mu nu hmu hnu) w from
      cartanInclusion_loweringWord mu nu hmu hnu w]
    rw [cartanHighest, loweringWord_tensorJoin_split]
    apply P.list_sum_mem
    intro z hz
    obtain ⟨⟨u, v⟩, huv, rfl⟩ := List.mem_map.mp hz
    have hh := (loweringSplits_grading w u v huv).1
    exact tensorJoin_mem_tensorProductSector _ _
      (loweringWord_mem_cyclicCutoff _ u (by omega))
      (loweringWord_mem_cyclicCutoff _ v (by omega))
  obtain ⟨y, hy, he⟩ := hS hx
  have hxy : y = x := Subtype.ext he
  rw [← hxy]
  exact hy

theorem cartanCutoffFrame_mem_productCutoff
    (mu nu : Fin d → ℕ) (hmu : Antitone mu) (hnu : Antitone nu)
    (R : ℕ) (i : CutoffIndex d R) :
    cartanAmbientInclusion mu nu hmu hnu
      (cutoffSectorFrame (partitionHighestTensor _ (sumPartition_antitone mu nu hmu hnu))
        (fun a => mu a + nu a) R i) ∈
      tensorProductSector (cyclicCutoff (partitionHighestTensor mu hmu) (R : ℤ))
        (cyclicCutoff (partitionHighestTensor nu hnu) (R : ℤ)) :=
  cartanAmbientInclusion_mem_productCutoff mu nu hmu hnu R _ (cutoffFrame_mem _ _ R i)

/-- The actual Cartan image of every cutoff frame vector has an exact finite
expansion in the two factor cutoff frames. No tail or asymptotic premise is used. -/
theorem cartanCutoffFrame_product_expansion
    (mu nu : Fin d → ℕ) (hmu : Antitone mu) (hnu : Antitone nu)
    (R : ℕ)
    (hmuGap : ∀ a : PositiveRoot d, 0 < rootGap mu a)
    (hnuGap : ∀ a : PositiveRoot d, 0 < rootGap nu a)
    (hmuLI : LinearIndependent ℂ (cutoffRawFrame (partitionHighestTensor mu hmu) mu R))
    (hnuLI : LinearIndependent ℂ (cutoffRawFrame (partitionHighestTensor nu hnu) nu R))
    (i : CutoffIndex d R) :
    cartanAmbientInclusion mu nu hmu hnu
      (cutoffSectorFrame (partitionHighestTensor _ (sumPartition_antitone mu nu hmu hnu))
        (fun a => mu a + nu a) R i) =
      ∑ j : CutoffIndex d R, ∑ k : CutoffIndex d R,
        cartanCutoffFrameMatrixElement mu nu hmu hnu R i j k •
          tensorJoin (cutoffFrame (partitionHighestTensor mu hmu) mu R j)
            (cutoffFrame (partitionHighestTensor nu hnu) nu R k) := by
  let P := cyclicCutoff (partitionHighestTensor mu hmu) (R : ℤ)
  let Q := cyclicCutoff (partitionHighestTensor nu hnu) (R : ℤ)
  let bP := cutoffOrthonormalBasis _ mu R hmuGap hmuLI
  let bQ := cutoffOrthonormalBasis _ nu R hnuGap hnuLI
  let y : tensorProductSector P Q :=
    ⟨cartanAmbientInclusion mu nu hmu hnu
      (cutoffSectorFrame (partitionHighestTensor _ (sumPartition_antitone mu nu hmu hnu))
        (fun a => mu a + nu a) R i), cartanCutoffFrame_mem_productCutoff mu nu hmu hnu R i⟩
  have h := congrArg (fun v : tensorProductSector P Q =>
    (v : TensorRegister ((∑ a, mu a) + ∑ a, nu a) (Fin d)))
    ((productSectorBasis P Q bP bQ).sum_repr y)
  simp only [Submodule.coe_sum, Submodule.coe_smul, OrthonormalBasis.repr_apply_apply,
    productSectorBasis_apply, productSectorFrame_coe] at h
  have hi (j k : CutoffIndex d R) :
      ⟪productSectorFrame P Q bP bQ (j,k), y⟫_ℂ =
        cartanCutoffFrameMatrixElement mu nu hmu hnu R i j k := by
    change ⟪tensorJoin (bP j : TensorRegister (∑ a, mu a) (Fin d))
      (bQ k : TensorRegister (∑ a, nu a) (Fin d)),
      (y : TensorRegister ((∑ a, mu a) + ∑ a, nu a) (Fin d))⟫_ℂ = _
    simp only [bP, bQ, cutoffOrthonormalBasis_coe]
    rfl
  rw [Fintype.sum_prod_type] at h
  simp only [hi] at h
  simpa only [P, Q, bP, bQ, y, cutoffOrthonormalBasis_coe] using h.symm

end Cloning.TensorLie
