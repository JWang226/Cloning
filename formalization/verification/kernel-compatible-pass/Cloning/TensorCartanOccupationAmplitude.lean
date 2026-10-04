import Cloning.TensorCartanOccupationLimit

/-! Identification of the actual Cartan matrix-element limit with the existing
product-binomial occupation amplitudes. -/
noncomputable section
open scoped BigOperators InnerProductSpace Topology
open Filter
namespace Cloning.TensorLie
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {d : ℕ}

theorem wordAmplitude_nonneg (t : PositiveRoot d → ℝ) (w : List (PositiveRoot d)) :
    0 ≤ wordAmplitude t w := by
  unfold wordAmplitude
  apply List.prod_nonneg
  intro x hx
  obtain ⟨a, _, rfl⟩ := List.mem_map.mp hx
  exact Real.sqrt_nonneg _

theorem wordAmplitude_sq (t : PositiveRoot d → ℝ) (ht : ∀ a, 0 ≤ t a)
    (w : List (PositiveRoot d)) :
    wordAmplitude t w ^ 2 = ∏ a : PositiveRoot d, t a ^ w.count a := by
  induction w with
  | nil => simp [wordAmplitude]
  | cons a w ih =>
    change (Real.sqrt (t a) * wordAmplitude t w) ^ 2 = _
    rw [mul_pow, Real.sq_sqrt (ht a), ih]
    simp only [List.count_cons, beq_iff_eq, pow_add, Finset.prod_mul_distrib]
    simp [pow_ite, Finset.prod_ite_eq, mul_comm]

/-- After exact binomial grouping and factorial cancellation, the limit is the
same nonnegative product amplitude used by the oscillator channel. -/
theorem occupationSplitMatrixElement_eq_product_amplitude
    (t : PositiveRoot d → ℝ) (ht0 : ∀ a, 0 ≤ t a) (ht1 : ∀ a, t a ≤ 1)
    (w u v : List (PositiveRoot d))
    (hcount : ∀ a, u.count a + v.count a = w.count a) :
    occupationSplitMatrixElement t w u v =
      ((∏ a : PositiveRoot d, Cloning.Occupation.splitAmplitude (w.count a) (u.count a) (t a) : ℝ) : ℂ) := by
  rw [occupationSplitMatrixElement_eq_choices t w u v hcount]
  rw [← mul_assoc, ← mul_assoc, occupationChoices_mul_splitFactorialCoefficient w u v hcount]
  have hc : 0 ≤ (occupationChoices w (fun a => u.count a) : ℝ) := Nat.cast_nonneg _
  have hnonneg : 0 ≤ Real.sqrt (occupationChoices w (fun a => u.count a) : ℝ) *
      wordAmplitude t u * wordAmplitude (fun a => 1 - t a) v :=
    mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (wordAmplitude_nonneg t u))
      (wordAmplitude_nonneg _ v)
  have hpnonneg : 0 ≤ ∏ a : PositiveRoot d,
      Cloning.Occupation.splitAmplitude (w.count a) (u.count a) (t a) := by
    apply Finset.prod_nonneg
    intro a _
    exact Real.sqrt_nonneg _
  have he : (Real.sqrt (occupationChoices w (fun a => u.count a) : ℝ) *
      wordAmplitude t u * wordAmplitude (fun a => 1 - t a) v) ^ 2 =
      (∏ a : PositiveRoot d,
        Cloning.Occupation.splitAmplitude (w.count a) (u.count a) (t a)) ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hc, wordAmplitude_sq t ht0,
      wordAmplitude_sq (fun a => 1 - t a) (fun a => sub_nonneg.mpr (ht1 a)),
      ← Finset.prod_pow]
    simp only [occupationChoices, Nat.cast_prod]
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro a _
    rw [Cloning.Occupation.splitAmplitude_sq _ _ (ht0 a) (ht1 a)]
    simp only [Cloning.Occupation.splitWeight]
    have hv : w.count a - u.count a = v.count a := by have := hcount a; omega
    rw [hv]
  have he' : Real.sqrt (occupationChoices w (fun a => u.count a) : ℝ) *
      wordAmplitude t u * wordAmplitude (fun a => 1 - t a) v =
      ∏ a : PositiveRoot d, Cloning.Occupation.splitAmplitude (w.count a) (u.count a) (t a) := by
    nlinarith
  exact_mod_cast he'

/-- The manuscript's product occupation amplitude is the actual physical
Cartan matrix-element limit; it is no longer an assumed coefficient model. -/
theorem cartanWordMatrixElement_tendsto_product_amplitude
    (mu nu : ℕ → Fin d → ℕ) (hmu : ∀ N, Antitone (mu N)) (hnu : ∀ N, Antitone (nu N))
    (δmu δnu : ℕ → ℝ) (hδmu : Tendsto δmu atTop atTop) (hδnu : Tendsto δnu atTop atTop)
    (hmuGap : ∀ᶠ N in atTop, ∀ a : PositiveRoot d, δmu N ≤ rootGap (mu N) a)
    (hnuGap : ∀ᶠ N in atTop, ∀ a : PositiveRoot d, δnu N ≤ rootGap (nu N) a)
    (t : PositiveRoot d → ℝ) (ht0 : ∀ a, 0 ≤ t a) (ht1 : ∀ a, t a ≤ 1)
    (ht : ∀ a, Tendsto (fun N => rootFraction (mu N) (nu N) a) atTop (𝓝 (t a)))
    (w u v : List (PositiveRoot d))
    (hcount : ∀ a, u.count a + v.count a = w.count a) :
    Tendsto (fun N => cartanWordMatrixElement (mu N) (nu N) (hmu N) (hnu N) w u v)
      atTop (𝓝 ((∏ a : PositiveRoot d,
        Cloning.Occupation.splitAmplitude (w.count a) (u.count a) (t a) : ℝ) : ℂ)) := by
  rw [← occupationSplitMatrixElement_eq_product_amplitude t ht0 ht1 w u v hcount]
  exact cartanWordMatrixElement_tendsto mu nu hmu hnu δmu δnu hδmu hδnu hmuGap hnuGap t ht w u v

end Cloning.TensorLie
