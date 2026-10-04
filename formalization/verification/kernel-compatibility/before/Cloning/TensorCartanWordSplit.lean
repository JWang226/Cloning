import Cloning.TensorCartanIntertwiner
import Cloning.TensorPBWNormalization
import Cloning.TensorPBWOrder

/-! Exact physical Cartan word splitting. Every left/right assignment is kept,
including its multiplicity; there is no asymptotic approximation in this module. -/
noncomputable section
open scoped BigOperators
namespace Cloning.TensorLie
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {n m d : ℕ}

/-- All ways to send the successive roots to the left or the right tensor
factor, retaining the original order separately within each factor. -/
def loweringSplits : List (PositiveRoot d) → List (List (PositiveRoot d) × List (PositiveRoot d))
  | [] => [([], [])]
  | a :: w => (loweringSplits w).map (fun uv => (a :: uv.1, uv.2)) ++
      (loweringSplits w).map (fun uv => (uv.1, a :: uv.2))

theorem loweringSplits_sublist (w : List (PositiveRoot d))
    (u v : List (PositiveRoot d)) (h : (u, v) ∈ loweringSplits w) :
    u.Sublist w ∧ v.Sublist w := by
  induction w generalizing u v with
  | nil =>
    simp only [loweringSplits, List.mem_singleton, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    exact ⟨List.Sublist.refl _, List.Sublist.refl _⟩
  | cons a w ih =>
    simp only [loweringSplits, List.mem_append, List.mem_map] at h
    rcases h with ⟨⟨s, t⟩, hst, he⟩ | ⟨⟨s, t⟩, hst, he⟩
    · cases he
      exact ⟨(ih s t hst).1.cons_cons a, (ih s t hst).2.cons a⟩
    · cases he
      exact ⟨(ih s t hst).1.cons a, (ih s t hst).2.cons_cons a⟩

theorem loweringSplits_grading (w : List (PositiveRoot d))
    (u v : List (PositiveRoot d)) (h : (u, v) ∈ loweringSplits w) :
    loweringHeight u + loweringHeight v = loweringHeight w ∧
    loweringWeight u + loweringWeight v = loweringWeight w ∧
    ∀ a : PositiveRoot d, u.count a + v.count a = w.count a := by
  induction w generalizing u v with
  | nil =>
    simp only [loweringSplits, List.mem_singleton, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    simp [loweringHeight]
  | cons a w ih =>
    simp only [loweringSplits, List.mem_append, List.mem_map] at h
    rcases h with ⟨⟨s, t⟩, hst, he⟩ | ⟨⟨s, t⟩, hst, he⟩
    · cases he
      obtain ⟨hH, hW, hC⟩ := ih s t hst
      refine ⟨?_, ?_, ?_⟩
      · simp only [loweringHeight]; omega
      · simp only [loweringWeight_cons, ← hW]; abel
      · intro b; simp only [List.count_cons]; rw [← hC b]; omega
    · cases he
      obtain ⟨hH, hW, hC⟩ := ih s t hst
      refine ⟨?_, ?_, ?_⟩
      · simp only [loweringHeight]; omega
      · simp only [loweringWeight_cons, ← hW]; abel
      · intro b; simp only [List.count_cons]; rw [← hC b]; omega

theorem loweringSplits_ordered (w : List (PositiveRoot d)) (hw : RootOrdered w)
    (u v : List (PositiveRoot d)) (h : (u, v) ∈ loweringSplits w) :
    RootOrdered u ∧ RootOrdered v :=
  ⟨List.Pairwise.sublist (loweringSplits_sublist w u v h).1 hw,
    List.Pairwise.sublist (loweringSplits_sublist w u v h).2 hw⟩

/-- The exact lowering coproduct follows directly from the literal tensor
Leibniz rule. It holds for arbitrary physical tensors. -/
theorem loweringWord_tensorJoin_split (Ω : TensorRegister n (Fin d))
    (Ψ : TensorRegister m (Fin d)) (w : List (PositiveRoot d)) :
    loweringWord (tensorJoin Ω Ψ) w =
      ((loweringSplits w).map (fun uv => tensorJoin (loweringWord Ω uv.1)
        (loweringWord Ψ uv.2))).sum := by
  induction w with
  | nil => simp [loweringWord, loweringSplits]
  | cons a w ih =>
    rw [loweringWord, ih, map_list_sum]
    simp only [loweringSplits, List.map_append, List.sum_append, List.map_map,
      Function.comp_def, loweringWord, collectiveGenerator_tensorJoin]
    exact List.sum_map_add

/-- Exact coefficient of one root assignment after the oscillator word
normalizations on source and both target factors. -/
def normalizedSplitCoefficient (mu nu : Fin d → ℕ)
    (w u v : List (PositiveRoot d)) : ℂ :=
  normalizedLoweringScale (fun a => mu a + nu a) w /
    (normalizedLoweringScale mu u * normalizedLoweringScale nu v)

theorem normalizedLoweringWord_tensorJoin_split
    (Ω : TensorRegister n (Fin d)) (Ψ : TensorRegister m (Fin d))
    (mu nu : Fin d → ℕ)
    (hmu : ∀ a : PositiveRoot d, 0 < (mu a.val.1 : ℝ) - mu a.val.2)
    (hnu : ∀ a : PositiveRoot d, 0 < (nu a.val.1 : ℝ) - nu a.val.2)
    (w : List (PositiveRoot d)) :
    normalizedLoweringWord (tensorJoin Ω Ψ) (fun a => mu a + nu a) w =
      ((loweringSplits w).map (fun uv => normalizedSplitCoefficient mu nu w uv.1 uv.2 •
        tensorJoin (normalizedLoweringWord Ω mu uv.1)
          (normalizedLoweringWord Ψ nu uv.2))).sum := by
  rw [normalizedLoweringWord_eq_scale, loweringWord_tensorJoin_split, List.smul_sum]
  simp only [List.map_map, Function.comp_def]
  apply congrArg List.sum
  apply List.map_congr_left
  intro uv _
  simp only [normalizedLoweringWord_eq_scale, tensorJoin_smul_left, tensorJoin_smul_right,
    smul_smul, normalizedSplitCoefficient]
  congr 1
  field_simp [normalizedLoweringScale_ne_zero mu hmu uv.1,
    normalizedLoweringScale_ne_zero nu hnu uv.2]

/-- The normalized source word as a vector in its actual full cyclic sector. -/
def normalizedSectorWord (Ω : TensorRegister n (Fin d)) (mu : Fin d → ℕ)
    (w : List (PositiveRoot d)) : cyclicSector Ω :=
  ⟨normalizedLoweringWord Ω mu w, by
    rw [normalizedLoweringWord_eq_scale]
    exact (cyclicSector Ω).smul_mem _ (loweringWord_mem_cyclicSector Ω w)⟩

theorem cartanAmbientInclusion_normalizedSectorWord
    (mu nu : Fin d → ℕ) (hmu : Antitone mu) (hnu : Antitone nu)
    (w : List (PositiveRoot d)) :
    cartanAmbientInclusion mu nu hmu hnu
      (normalizedSectorWord (partitionHighestTensor (fun a => mu a + nu a)
        (sumPartition_antitone mu nu hmu hnu)) (fun a => mu a + nu a) w) =
      normalizedLoweringWord (cartanHighest mu nu hmu hnu) (fun a => mu a + nu a) w := by
  have he : normalizedSectorWord (partitionHighestTensor (fun a => mu a + nu a)
        (sumPartition_antitone mu nu hmu hnu)) (fun a => mu a + nu a) w =
      normalizedLoweringScale (fun a => mu a + nu a) w •
      (⟨loweringWord (partitionHighestTensor (fun a => mu a + nu a)
        (sumPartition_antitone mu nu hmu hnu)) w, loweringWord_mem_cyclicSector _ _⟩ :
        cyclicSector _) := by
    apply Subtype.ext
    exact normalizedLoweringWord_eq_scale _ _ _
  rw [he, map_smul, normalizedLoweringWord_eq_scale]
  congr 1
  exact cartanInclusion_loweringWord mu nu hmu hnu w

/-- Literal Cartan inclusion on every normalized lowering word, expressed by
all left/right assignments with their exact finite-parameter coefficients. -/
theorem cartanAmbientInclusion_word_split
    (mu nu : Fin d → ℕ) (hmu : Antitone mu) (hnu : Antitone nu)
    (hmuGap : ∀ a : PositiveRoot d, 0 < (mu a.val.1 : ℝ) - mu a.val.2)
    (hnuGap : ∀ a : PositiveRoot d, 0 < (nu a.val.1 : ℝ) - nu a.val.2)
    (w : List (PositiveRoot d)) :
    cartanAmbientInclusion mu nu hmu hnu
      (normalizedSectorWord (partitionHighestTensor (fun a => mu a + nu a)
        (sumPartition_antitone mu nu hmu hnu)) (fun a => mu a + nu a) w) =
      ((loweringSplits w).map (fun uv => normalizedSplitCoefficient mu nu w uv.1 uv.2 •
        tensorJoin (normalizedLoweringWord (partitionHighestTensor mu hmu) mu uv.1)
          (normalizedLoweringWord (partitionHighestTensor nu hnu) nu uv.2))).sum := by
  rw [cartanAmbientInclusion_normalizedSectorWord]
  exact normalizedLoweringWord_tensorJoin_split _ _ mu nu hmuGap hnuGap w

end Cloning.TensorLie
