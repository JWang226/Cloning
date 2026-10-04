import Cloning.TensorCartanCutoffAmplitude
import Cloning.TensorGibbsThermalCutoff

/-! The finite cutoff Cartan coefficient sum is exactly the amplified thermal law. -/
noncomputable section
open scoped BigOperators
namespace Cloning.TensorLie
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {d R : ℕ}
attribute [local instance] Classical.propDecidable

private theorem occupationHeight_mono {k l : PositiveRoot d → ℕ} (h : ∀ a, k a ≤ l a) :
    occupationHeight k ≤ occupationHeight l :=
  Finset.sum_le_sum (fun a _ => Nat.mul_le_mul_left a.height (h a))

abbrev OccupationSplit (r : HeightOccupation d R) := ∀ a, Fin (r.val a + 1)

def occupationSplitLeft (r : HeightOccupation d R) (s : OccupationSplit r) : HeightOccupation d R :=
  ⟨fun a => s a, (occupationHeight_mono (fun a => Nat.le_of_lt_succ (s a).isLt)).trans r.property⟩

def occupationSplitRight (r : HeightOccupation d R) (s : OccupationSplit r) : HeightOccupation d R :=
  ⟨fun a => r.val a - s a, (occupationHeight_mono (fun a => Nat.sub_le _ _)).trans r.property⟩

def occupationSplitPair (r : HeightOccupation d R) (s : OccupationSplit r) :
    HeightOccupation d R × HeightOccupation d R :=
  (occupationSplitLeft r s, occupationSplitRight r s)

theorem occupationSplitPair_injective (r : HeightOccupation d R) :
    Function.Injective (occupationSplitPair r) := by
  intro s t h
  funext a
  apply Fin.ext
  exact congrArg (fun x => x.1.val a) h

theorem occupationSplitPair_counts (r : HeightOccupation d R) (s : OccupationSplit r)
    (a : PositiveRoot d) :
    (occupationSplitPair r s).1.val a + (occupationSplitPair r s).2.val a = r.val a := by
  exact Nat.add_sub_of_le (Nat.le_of_lt_succ (s a).isLt)

theorem exists_occupationSplitPair (r j k : HeightOccupation d R)
    (h : ∀ a, j.val a + k.val a = r.val a) :
    ∃ s, occupationSplitPair r s = (j,k) := by
  let s : OccupationSplit r := fun a => ⟨j.val a, by have := h a; omega⟩
  refine ⟨s, ?_⟩
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    funext a
    change r.val a - j.val a = k.val a
    have := h a
    omega

/-- The height cutoff contains every component of a compatible occupation split. -/
theorem sum_occupationSplits (r : HeightOccupation d R)
    (f : HeightOccupation d R → HeightOccupation d R → ℂ)
    (hz : ∀ j k, (¬ ∀ a, j.val a + k.val a = r.val a) → f j k = 0) :
    (∑ j, ∑ k, f j k) = ∑ s : OccupationSplit r,
      f (occupationSplitLeft r s) (occupationSplitRight r s) := by
  classical
  let F : HeightOccupation d R × HeightOccupation d R → ℂ := fun x => f x.1 x.2
  have hs : (∑ x ∈ Finset.univ.image (occupationSplitPair r), F x) = ∑ x, F x := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro x _ hx
    apply hz x.1 x.2
    intro he
    obtain ⟨s,hs⟩ := exists_occupationSplitPair r x.1 x.2 he
    exact hx (Finset.mem_image.mpr ⟨s,Finset.mem_univ _,hs⟩)
  rw [Finset.sum_image (fun a _ b _ h => occupationSplitPair_injective r h)] at hs
  simpa only [Fintype.sum_prod_type, F, occupationSplitPair] using hs.symm

def cutoffSplitAmplitude (t : PositiveRoot d → ℝ)
    (r j k : HeightOccupation d R) : ℂ :=
  if ∀ a, j.val a + k.val a = r.val a then
    ((∏ a, Cloning.Occupation.splitAmplitude (r.val a) (j.val a) (t a) : ℝ) : ℂ)
  else 0

theorem occupationSplitMatrixElement_eq_cutoffSplitAmplitude
    (t : PositiveRoot d → ℝ) (ht0 : ∀ a, 0 ≤ t a) (ht1 : ∀ a, t a ≤ 1)
    (r j k : HeightOccupation d R) :
    occupationSplitMatrixElement t (canonicalWord r.val) (canonicalWord j.val)
      (canonicalWord k.val) = cutoffSplitAmplitude t r j k := by
  classical
  by_cases h : ∀ a, j.val a + k.val a = r.val a
  · simp only [cutoffSplitAmplitude, if_pos h]
    simpa only [canonicalWord_count] using
      occupationSplitMatrixElement_eq_product_amplitude t ht0 ht1
        (canonicalWord r.val) (canonicalWord j.val) (canonicalWord k.val)
        (by simpa only [canonicalWord_count] using h)
  · rw [occupationSplitMatrixElement_eq_zero t _ _ _
      (by simpa only [canonicalWord_count] using h)]
    exact (if_neg h).symm

theorem cutoffSplitAmplitude_cross_zero
    (t : PositiveRoot d → ℝ) (r l j k : HeightOccupation d R) (h : r ≠ l) :
    starRingEnd ℂ (cutoffSplitAmplitude t r j k) * cutoffSplitAmplitude t l j k = 0 := by
  classical
  by_cases hr : ∀ a, j.val a + k.val a = r.val a
  · have hl : ¬ ∀ a, j.val a + k.val a = l.val a := by
      intro hl
      apply h
      apply Subtype.ext
      funext a
      exact (hr a).symm.trans (hl a)
    simp only [cutoffSplitAmplitude, if_neg hl, mul_zero]
  · simp only [cutoffSplitAmplitude, if_neg hr, map_zero, zero_mul]

def amplifiedOccupationWeight (t q : PositiveRoot d → ℝ) (r : PositiveRoot d → ℕ) : ℝ :=
  ∏ a, (t a * (1 - q a)) * (1 - t a + t a * q a) ^ r a

theorem cutoffSplitAmplitude_thermal_diagonal
    (t q : PositiveRoot d → ℝ) (ht0 : ∀ a, 0 ≤ t a) (ht1 : ∀ a, t a ≤ 1)
    (r : HeightOccupation d R) :
    ((∏ a, t a : ℝ) : ℂ) *
      (∑ j : HeightOccupation d R, ∑ k : HeightOccupation d R,
        starRingEnd ℂ (cutoffSplitAmplitude t r j k) *
          (((∏ a, (1 - q a)) * ∏ a, q a ^ j.val a : ℝ) : ℂ) *
          cutoffSplitAmplitude t r j k) = (amplifiedOccupationWeight t q r.val : ℂ) := by
  classical
  have hs := sum_occupationSplits r
    (fun j k => starRingEnd ℂ (cutoffSplitAmplitude t r j k) *
      (((∏ a, (1 - q a)) * ∏ a, q a ^ j.val a : ℝ) : ℂ) * cutoffSplitAmplitude t r j k)
    (by intro j k h; simp only [cutoffSplitAmplitude, if_neg h, map_zero, zero_mul])
  have ht (s : OccupationSplit r) :
      starRingEnd ℂ (cutoffSplitAmplitude t r (occupationSplitLeft r s) (occupationSplitRight r s)) *
        (((∏ a, (1 - q a)) * ∏ a, q a ^ (occupationSplitLeft r s).val a : ℝ) : ℂ) *
        cutoffSplitAmplitude t r (occupationSplitLeft r s) (occupationSplitRight r s) =
      (((∏ a, (1 - q a)) *
        (Cloning.Occupation.cartanAmplitude r.val t s ^ 2 * ∏ a, q a ^ (s a : ℕ)) : ℝ) : ℂ) := by
    have hc : ∀ a, (occupationSplitLeft r s).val a + (occupationSplitRight r s).val a = r.val a :=
      occupationSplitPair_counts r s
    simp only [cutoffSplitAmplitude, if_pos hc]
    simp only [occupationSplitLeft,
      Cloning.Occupation.cartanAmplitude, map_prod, Complex.conj_ofReal,
      Complex.ofReal_mul, Complex.ofReal_pow]
    ring
  rw [hs]
  simp_rw [ht]
  rw [← Complex.ofReal_sum, ← Finset.mul_sum,
    Cloning.Occupation.cartanAmplitude_thermal_moment r.val t q ht0 ht1,
    ← Complex.ofReal_mul]
  congr 1
  unfold amplifiedOccupationWeight
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  ring

theorem cutoffSplitAmplitude_thermal_matrix
    (t q : PositiveRoot d → ℝ) (ht0 : ∀ a, 0 ≤ t a) (ht1 : ∀ a, t a ≤ 1)
    (r l : HeightOccupation d R) :
    ((∏ a, t a : ℝ) : ℂ) *
      (∑ j : HeightOccupation d R, ∑ k : HeightOccupation d R,
        starRingEnd ℂ (cutoffSplitAmplitude t r j k) *
          (((∏ a, (1 - q a)) * ∏ a, q a ^ j.val a : ℝ) : ℂ) *
          cutoffSplitAmplitude t l j k) =
      if r = l then (amplifiedOccupationWeight t q r.val : ℂ) else 0 := by
  classical
  by_cases h : r = l
  · subst l
    rw [if_pos rfl]
    exact cutoffSplitAmplitude_thermal_diagonal t q ht0 ht1 r
  · rw [if_neg h]
    have ht (j k : HeightOccupation d R) :
        starRingEnd ℂ (cutoffSplitAmplitude t r j k) *
          (((∏ a, (1 - q a)) * ∏ a, q a ^ j.val a : ℝ) : ℂ) *
          cutoffSplitAmplitude t l j k = 0 := by
      rw [mul_right_comm, cutoffSplitAmplitude_cross_zero t r l j k h, zero_mul]
    simp only [ht, Finset.sum_const_zero, mul_zero]

end Cloning.TensorLie
