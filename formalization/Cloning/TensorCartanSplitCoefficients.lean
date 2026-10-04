import Cloning.TensorCartanWordSplit

/-! Exact root-fraction form of Cartan splitting coefficients and their
fixed-word limits. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace Cloning.TensorLie
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {d : ℕ}

def rootGap (mu : Fin d → ℕ) (a : PositiveRoot d) : ℝ :=
  (mu a.val.1 : ℝ) - mu a.val.2

theorem rootGap_add (mu nu : Fin d → ℕ) (a : PositiveRoot d) :
    rootGap (fun i => mu i + nu i) a = rootGap mu a + rootGap nu a := by
  simp only [rootGap, Nat.cast_add]
  ring

def rootFraction (mu nu : Fin d → ℕ) (a : PositiveRoot d) : ℝ :=
  rootGap mu a / (rootGap mu a + rootGap nu a)

def wordAmplitude (q : PositiveRoot d → ℝ) (w : List (PositiveRoot d)) : ℝ :=
  (w.map (fun a => Real.sqrt (q a))).prod

def splitFactorialCoefficient (w u v : List (PositiveRoot d)) : ℂ :=
  (Real.sqrt (PBW.occupationFactorial u : ℝ) : ℂ) *
    (Real.sqrt (PBW.occupationFactorial v : ℝ) : ℂ) /
      (Real.sqrt (PBW.occupationFactorial w : ℝ) : ℂ)

theorem loweringScale_eq_prod (mu : Fin d → ℕ) (w : List (PositiveRoot d)) :
    loweringScale mu w = (w.map (fun a => (((Real.sqrt (rootGap mu a))⁻¹ : ℝ) : ℂ))).prod := by
  induction w with
  | nil => rfl
  | cons a w ih => simp only [loweringScale, List.map_cons, List.prod_cons, ih, rootGap]

theorem loweringScale_split (mu : Fin d → ℕ) (w u v : List (PositiveRoot d))
    (h : (u, v) ∈ loweringSplits w) :
    loweringScale mu w = loweringScale mu u * loweringScale mu v := by
  have hp : w.Perm (u ++ v) := by
    apply List.perm_iff_count.mpr
    intro a
    rw [List.count_append]
    exact ((loweringSplits_grading w u v h).2.2 a).symm
  simp only [loweringScale_eq_prod]
  rw [(hp.map _).prod_eq, List.map_append, List.prod_append]

/-- The quotient of raw normalization products depends only on root-gap
ratios. This identity precedes every asymptotic assertion. -/
theorem loweringScale_ratio (mu tau : Fin d → ℕ)
    (hmu : ∀ a : PositiveRoot d, 0 ≤ rootGap mu a)
    (w : List (PositiveRoot d)) :
    loweringScale tau w / loweringScale mu w =
      (wordAmplitude (fun a => rootGap mu a / rootGap tau a) w : ℂ) := by
  induction w with
  | nil => simp [loweringScale, wordAmplitude]
  | cons a w ih =>
    simp only [loweringScale, mul_div_mul_comm, ih, wordAmplitude, List.map_cons, List.prod_cons,
      Complex.ofReal_mul, Real.sqrt_div (hmu a), rootGap]
    congr 1
    push_cast
    rw [inv_div_inv]
    change (Real.sqrt (rootGap mu a) : ℂ) / (Real.sqrt (rootGap tau a) : ℂ) =
      (Real.sqrt (rootGap mu a / rootGap tau a) : ℂ)
    rw [Real.sqrt_div (hmu a), Complex.ofReal_div]

theorem normalizedSplitCoefficient_eq_amplitudes
    (mu nu : Fin d → ℕ)
    (hmu : ∀ a : PositiveRoot d, 0 < rootGap mu a)
    (hnu : ∀ a : PositiveRoot d, 0 < rootGap nu a)
    (w u v : List (PositiveRoot d)) (h : (u, v) ∈ loweringSplits w) :
    normalizedSplitCoefficient mu nu w u v =
      splitFactorialCoefficient w u v *
        (wordAmplitude (rootFraction mu nu) u : ℂ) *
        (wordAmplitude (rootFraction nu mu) v : ℂ) := by
  have hu := loweringScale_ratio mu (fun a => mu a + nu a) (fun a => (hmu a).le) u
  have hv := loweringScale_ratio nu (fun a => mu a + nu a) (fun a => (hnu a).le) v
  have hv' : (fun a => rootGap nu a / rootGap (fun i => mu i + nu i) a) =
      rootFraction nu mu := by funext a; simp only [rootGap_add, rootFraction]; rw [add_comm]
  have hu' : (fun a => rootGap mu a / rootGap (fun i => mu i + nu i) a) =
      rootFraction mu nu := by funext a; simp only [rootGap_add, rootFraction]
  rw [hu'] at hu
  rw [hv'] at hv
  rw [← hu, ← hv]
  simp only [normalizedSplitCoefficient, normalizedLoweringScale, splitFactorialCoefficient,
    loweringScale_split _ w u v h]
  have hf (t : List (PositiveRoot d)) : (Real.sqrt (PBW.occupationFactorial t : ℝ) : ℂ) ≠ 0 := by
    apply Complex.ofReal_ne_zero.mpr
    apply ne_of_gt
    apply Real.sqrt_pos.mpr
    exact_mod_cast PBW.occupationFactorial_pos t
  have hμ := loweringScale_ne_zero mu hmu u
  have hν := loweringScale_ne_zero nu hnu v
  field_simp [hf w, hf u, hf v, hμ, hν]

/-- Fixed words have continuous splitting amplitudes in their finitely many
root fractions, including limiting fractions zero or one. -/
theorem wordAmplitude_tendsto (q : ℕ → PositiveRoot d → ℝ) (t : PositiveRoot d → ℝ)
    (hq : ∀ a, Tendsto (fun N => q N a) atTop (𝓝 (t a)))
    (w : List (PositiveRoot d)) :
    Tendsto (fun N => wordAmplitude (q N) w) atTop (𝓝 (wordAmplitude t w)) := by
  apply tendsto_list_prod
  intro a _
  exact Real.continuous_sqrt.continuousAt.tendsto.comp (hq a)

/-- The finite-parameter physical Cartan coefficients converge to the product
oscillator splitting coefficients when all root fractions converge. -/
theorem normalizedSplitCoefficient_tendsto
    (mu nu : ℕ → Fin d → ℕ)
    (hmu : ∀ᶠ N in atTop, ∀ a : PositiveRoot d, 0 < rootGap (mu N) a)
    (hnu : ∀ᶠ N in atTop, ∀ a : PositiveRoot d, 0 < rootGap (nu N) a)
    (t s : PositiveRoot d → ℝ)
    (ht : ∀ a, Tendsto (fun N => rootFraction (mu N) (nu N) a) atTop (𝓝 (t a)))
    (hs : ∀ a, Tendsto (fun N => rootFraction (nu N) (mu N) a) atTop (𝓝 (s a)))
    (w u v : List (PositiveRoot d)) (h : (u, v) ∈ loweringSplits w) :
    Tendsto (fun N => normalizedSplitCoefficient (mu N) (nu N) w u v) atTop
      (𝓝 (splitFactorialCoefficient w u v * (wordAmplitude t u : ℂ) *
        (wordAmplitude s v : ℂ))) := by
  have htu : Tendsto (fun N => (wordAmplitude (rootFraction (mu N) (nu N)) u : ℂ)) atTop
      (𝓝 (wordAmplitude t u : ℂ)) :=
    Complex.continuous_ofReal.continuousAt.tendsto.comp (wordAmplitude_tendsto _ t ht u)
  have hsv : Tendsto (fun N => (wordAmplitude (rootFraction (nu N) (mu N)) v : ℂ)) atTop
      (𝓝 (wordAmplitude s v : ℂ)) :=
    Complex.continuous_ofReal.continuousAt.tendsto.comp (wordAmplitude_tendsto _ s hs v)
  apply (tendsto_const_nhds.mul htu |>.mul hsv).congr'
  filter_upwards [hmu, hnu] with N hμ hν
  exact (normalizedSplitCoefficient_eq_amplitudes (mu N) (nu N) hμ hν w u v h).symm


theorem rootFraction_reverse (mu nu : Fin d → ℕ) (a : PositiveRoot d)
    (h : rootGap mu a + rootGap nu a ≠ 0) :
    rootFraction nu mu a = 1 - rootFraction mu nu a := by
  unfold rootFraction
  rw [add_comm (rootGap nu a)]
  field_simp
  <;> ring

theorem rootFraction_mem_Icc (mu nu : Fin d → ℕ) (a : PositiveRoot d)
    (hmu : 0 < rootGap mu a) (hnu : 0 < rootGap nu a) :
    rootFraction mu nu a ∈ Set.Icc (0 : ℝ) 1 := by
  unfold rootFraction
  exact ⟨(div_pos hmu (add_pos hmu hnu)).le,
    (div_le_one (add_pos hmu hnu)).mpr (by linarith)⟩

/-- The two limiting amplitudes are complementary; only one root-fraction
limit is required from an application. -/
theorem normalizedSplitCoefficient_tendsto_complement
    (mu nu : ℕ → Fin d → ℕ)
    (hmu : ∀ᶠ N in atTop, ∀ a : PositiveRoot d, 0 < rootGap (mu N) a)
    (hnu : ∀ᶠ N in atTop, ∀ a : PositiveRoot d, 0 < rootGap (nu N) a)
    (t : PositiveRoot d → ℝ)
    (ht : ∀ a, Tendsto (fun N => rootFraction (mu N) (nu N) a) atTop (𝓝 (t a)))
    (w u v : List (PositiveRoot d)) (h : (u, v) ∈ loweringSplits w) :
    Tendsto (fun N => normalizedSplitCoefficient (mu N) (nu N) w u v) atTop
      (𝓝 (splitFactorialCoefficient w u v * (wordAmplitude t u : ℂ) *
        (wordAmplitude (fun a => 1 - t a) v : ℂ))) := by
  apply normalizedSplitCoefficient_tendsto mu nu hmu hnu t (fun a => 1 - t a) ht _ w u v h
  intro a
  apply (tendsto_const_nhds.sub (ht a)).congr'
  filter_upwards [hmu, hnu] with N hμ hν
  exact (rootFraction_reverse (mu N) (nu N) a (ne_of_gt (add_pos (hμ a) (hν a)))).symm

end Cloning.TensorLie
