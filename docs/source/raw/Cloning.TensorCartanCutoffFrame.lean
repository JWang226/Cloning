import Cloning.TensorPBWCutoffBasis
import Cloning.TensorWeightFrameLimit
import Cloning.TensorCartanMatrixLimit

/-! A common finite occupation frame for the actual physical cutoffs. Literal
Gram--Schmidt preserves the exact weights and approaches the normalized PBW
vectors; eventual completeness follows from the proved physical spanning. -/
noncomputable section
open scoped BigOperators InnerProductSpace Topology
open Filter InnerProductSpace
namespace Cloning.TensorLie
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {n d : ℕ}

abbrev CutoffIndex (d R : ℕ) := Fin (Fintype.card (HeightOccupation d R))

def cutoffOccupation (d R : ℕ) : CutoffIndex d R ≃ HeightOccupation d R :=
  (Fintype.equivFin (HeightOccupation d R)).symm

def cutoffWord (d R : ℕ) (i : CutoffIndex d R) : List (PositiveRoot d) :=
  canonicalWord (cutoffOccupation d R i).val

theorem cutoffWord_perm_iff (R : ℕ) (i j : CutoffIndex d R) :
    (cutoffWord d R i).Perm (cutoffWord d R j) ↔ i = j := by
  unfold cutoffWord
  rw [canonicalWord_perm_iff, Subtype.val_inj]
  exact (cutoffOccupation d R).injective.eq_iff

theorem cutoffWord_height_le (R : ℕ) (i : CutoffIndex d R) :
    loweringHeight (cutoffWord d R i) ≤ R := by
  rw [cutoffWord, canonicalWord_height]
  exact (cutoffOccupation d R i).property

def cutoffRawFrame (Ω : TensorRegister n (Fin d)) (mu : Fin d → ℕ) (R : ℕ)
    (i : CutoffIndex d R) : TensorRegister n (Fin d) :=
  normalizedLoweringWord Ω mu (cutoffWord d R i)

def cutoffFrame (Ω : TensorRegister n (Fin d)) (mu : Fin d → ℕ) (R : ℕ) :
    CutoffIndex d R → TensorRegister n (Fin d) :=
  gramSchmidtNormed ℂ (cutoffRawFrame Ω mu R)

theorem cutoffRawFrame_mem (Ω : TensorRegister n (Fin d)) (mu : Fin d → ℕ)
    (R : ℕ) (i : CutoffIndex d R) : cutoffRawFrame Ω mu R i ∈ cyclicCutoff Ω (R : ℤ) :=
  normalizedLoweringWord_mem_cyclicCutoff Ω mu _ (by exact_mod_cast cutoffWord_height_le R i)

theorem span_cutoffFrame_eq_raw (Ω : TensorRegister n (Fin d)) (mu : Fin d → ℕ) (R : ℕ) :
    Submodule.span ℂ (Set.range (cutoffFrame Ω mu R)) =
      Submodule.span ℂ (Set.range (cutoffRawFrame Ω mu R)) :=
  (span_gramSchmidtNormed_range (𝕜 := ℂ) _).trans (span_gramSchmidt ℂ _)

theorem cutoffFrame_mem (Ω : TensorRegister n (Fin d)) (mu : Fin d → ℕ)
    (R : ℕ) (i : CutoffIndex d R) : cutoffFrame Ω mu R i ∈ cyclicCutoff Ω (R : ℤ) := by
  have hspan : Submodule.span ℂ (Set.range (cutoffFrame Ω mu R)) ≤ cyclicCutoff Ω (R : ℤ) := by
    rw [span_cutoffFrame_eq_raw]
    apply Submodule.span_le.mpr
    rintro x ⟨j, rfl⟩
    exact cutoffRawFrame_mem Ω mu R j
  exact hspan (Submodule.subset_span (Set.mem_range_self i))

theorem span_cutoffFrame_eq_cutoff (Ω : TensorRegister n (Fin d))
    (mu : Fin d → ℕ) (R : ℕ)
    (hgap : ∀ a : PositiveRoot d, 0 < rootGap mu a) :
    Submodule.span ℂ (Set.range (cutoffFrame Ω mu R)) = cyclicCutoff Ω (R : ℤ) := by
  rw [span_cutoffFrame_eq_raw]
  have hr : Set.range (cutoffRawFrame Ω mu R) =
      Set.range (fun k : HeightOccupation d R => normalizedLoweringWord Ω mu (canonicalWord k.val)) := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨cutoffOccupation d R i, rfl⟩
    · rintro ⟨k, rfl⟩
      obtain ⟨i, rfl⟩ := (cutoffOccupation d R).surjective k
      exact ⟨i, rfl⟩
  rw [hr, span_normalizedLoweringWord_eq Ω mu hgap, cyclicCutoff_eq_span_canonical]

def cutoffFrameVector (Ω : TensorRegister n (Fin d)) (mu : Fin d → ℕ) (R : ℕ)
    (i : CutoffIndex d R) : cyclicCutoff Ω (R : ℤ) :=
  ⟨cutoffFrame Ω mu R i, cutoffFrame_mem Ω mu R i⟩

def cutoffSectorFrame (Ω : TensorRegister n (Fin d)) (mu : Fin d → ℕ) (R : ℕ)
    (i : CutoffIndex d R) : cyclicSector Ω :=
  ⟨cutoffFrame Ω mu R i, cyclicCutoff_le_cyclicSector Ω _ (cutoffFrame_mem Ω mu R i)⟩

theorem cutoffFrame_cartan (Ω : TensorRegister n (Fin d)) (mu : Fin d → ℕ) (R : ℕ)
    (hweight : ∀ a, collectiveGenerator n a a Ω = (mu a : ℂ) • Ω)
    (i : CutoffIndex d R) (a : Fin d) :
    collectiveGenerator n a a (cutoffFrame Ω mu R i) =
      ((mu a : ℂ) + (loweringWeight (cutoffWord d R i) a : ℂ)) • cutoffFrame Ω mu R i := by
  have h := gramSchmidtNormed_cartan (cutoffRawFrame Ω mu R)
    (fun i a => (mu a : ℝ) + loweringWeight (cutoffWord d R i) a) (fun i a => by
      simpa only [Complex.ofReal_add, Complex.ofReal_natCast, Complex.ofReal_intCast] using
        cartan_normalizedLoweringWord Ω mu hweight (cutoffWord d R i) a) i a
  simpa only [Complex.ofReal_add, Complex.ofReal_natCast, Complex.ofReal_intCast] using h

def cutoffOrthonormalBasis (Ω : TensorRegister n (Fin d)) (mu : Fin d → ℕ) (R : ℕ)
    (hgap : ∀ a : PositiveRoot d, 0 < rootGap mu a)
    (hli : LinearIndependent ℂ (cutoffRawFrame Ω mu R)) :
    OrthonormalBasis (CutoffIndex d R) ℂ (cyclicCutoff Ω (R : ℤ)) := by
  have hon : Orthonormal ℂ (cutoffFrameVector Ω mu R) := by
    rw [orthonormal_iff_ite]
    intro i j
    exact orthonormal_iff_ite.mp (gramSchmidtNormed_orthonormal (𝕜 := ℂ) hli) i j
  have hspan : Submodule.span ℂ (Set.range (cutoffFrameVector Ω mu R)) = ⊤ :=
    (Submodule.span_range_subtype_eq_top_iff (cyclicCutoff Ω (R : ℤ))
      (cutoffFrame_mem Ω mu R)).mpr (span_cutoffFrame_eq_cutoff Ω mu R hgap)
  exact OrthonormalBasis.mk hon hspan.ge

@[simp] theorem cutoffOrthonormalBasis_coe (Ω : TensorRegister n (Fin d))
    (mu : Fin d → ℕ) (R : ℕ) (hgap : ∀ a : PositiveRoot d, 0 < rootGap mu a)
    (hli : LinearIndependent ℂ (cutoffRawFrame Ω mu R)) (i : CutoffIndex d R) :
    (cutoffOrthonormalBasis Ω mu R hgap hli i : TensorRegister n (Fin d)) =
      cutoffFrame Ω mu R i := by
  simp [cutoffOrthonormalBasis, cutoffFrameVector]

/-- The common actual orthogonal frame converges to its occupation word. -/
theorem partition_cutoffFrame_close
    (mu : ℕ → Fin d → ℕ) (hmu : ∀ N, Antitone (mu N))
    (δ : ℕ → ℝ) (hδ : Tendsto δ atTop atTop)
    (hgap : ∀ᶠ N in atTop, ∀ a : PositiveRoot d, δ N ≤ rootGap (mu N) a)
    (R : ℕ) (i : CutoffIndex d R) :
    Tendsto (fun N => ‖cutoffFrame (partitionHighestTensor (mu N) (hmu N)) (mu N) R i -
      cutoffRawFrame (partitionHighestTensor (mu N) (hmu N)) (mu N) R i‖) atTop (𝓝 0) := by
  apply gramSchmidtNormed_sub_tendsto_zero
  intro i j
  simpa only [cutoffRawFrame, normalizedLoweringWord, cutoffWord_perm_iff] using
    partition_normalized_gram_tendsto (fun a : PositiveRoot d => a) Function.injective_id
      mu hmu δ hδ hgap (cutoffWord d R i) (cutoffWord d R j)

/-- Eventual complete ONBs are constructed from the actual root-gap conditions;
no independent frame or basis premise remains in this endpoint. -/
theorem partition_eventually_cutoffOrthonormalBasis
    (mu : ℕ → Fin d → ℕ) (hmu : ∀ N, Antitone (mu N))
    (δ : ℕ → ℝ) (hδ : Tendsto δ atTop atTop)
    (hgap : ∀ᶠ N in atTop, ∀ a : PositiveRoot d, δ N ≤ rootGap (mu N) a) (R : ℕ) :
    ∀ᶠ N in atTop, ∃ b : OrthonormalBasis (CutoffIndex d R) ℂ
      (cyclicCutoff (partitionHighestTensor (mu N) (hmu N)) (R : ℤ)),
      ∀ i, (b i : TensorRegister (∑ a, mu N a) (Fin d)) =
        cutoffFrame (partitionHighestTensor (mu N) (hmu N)) (mu N) R i := by
  have hli := partition_normalizedWord_eventually_linearIndependent
    (fun a : PositiveRoot d => a) Function.injective_id mu hmu δ hδ hgap
    (cutoffWord d R) (cutoffWord_perm_iff R)
  filter_upwards [hli, hgap, hδ.eventually (eventually_gt_atTop 0)] with N hN hg hp
  have hpos : ∀ a : PositiveRoot d, 0 < rootGap (mu N) a := fun a => hp.trans_le (hg a)
  exact ⟨cutoffOrthonormalBasis _ _ R hpos hN, cutoffOrthonormalBasis_coe _ _ R hpos hN⟩

end Cloning.TensorLie
