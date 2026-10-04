import Cloning.PBWSymmetricFrameRateBlocks
import Cloning.TensorCartanOccupationAmplitude

/-! Uniform coefficient and tensor replacement bounds for quantitative Cartan
splitting in physical symmetric frames. -/
noncomputable section
open scoped ComplexOrder InnerProductSpace Topology BigOperators
namespace Cloning.TensorLie
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
variable {d : ℕ}

theorem wordAmplitude_le_one (t : PositiveRoot d → ℝ)
    (ht : ∀ a, t a ≤ 1) (w : List (PositiveRoot d)) :
    wordAmplitude t w ≤ 1 := by
  induction w with
  | nil => simp [wordAmplitude]
  | cons a w ih =>
    change Real.sqrt (t a) * wordAmplitude t w ≤ 1
    exact (mul_le_mul (by simpa using Real.sqrt_le_sqrt (ht a)) ih
      (wordAmplitude_nonneg t w) (by norm_num)).trans_eq (one_mul 1)

theorem normalizedSplitCoefficient_norm_le_factorial
    (mu nu : Fin d → ℕ)
    (hmu : ∀ a : PositiveRoot d, 0 < rootGap mu a)
    (hnu : ∀ a : PositiveRoot d, 0 < rootGap nu a)
    (w u v : List (PositiveRoot d)) (h : (u, v) ∈ loweringSplits w) :
    ‖normalizedSplitCoefficient mu nu w u v‖ ≤ ‖splitFactorialCoefficient w u v‖ := by
  rw [normalizedSplitCoefficient_eq_amplitudes mu nu hmu hnu w u v h]
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (wordAmplitude_nonneg _ _)]
  have hu := wordAmplitude_le_one (rootFraction mu nu)
    (fun a => (rootFraction_mem_Icc mu nu a (hmu a) (hnu a)).2) u
  have hv := wordAmplitude_le_one (rootFraction nu mu)
    (fun a => (rootFraction_mem_Icc nu mu a (hnu a) (hmu a)).2) v
  calc
    _ ≤ ‖splitFactorialCoefficient w u v‖ * 1 * 1 :=
      mul_le_mul (mul_le_mul_of_nonneg_left hu (norm_nonneg _)) hv
        (wordAmplitude_nonneg _ _) (mul_nonneg (norm_nonneg _) zero_le_one)
    _ = _ := by ring

theorem splitFactorialCoefficient_norm_le_one
    (w u v : List (PositiveRoot d))
    (hcount : ∀ a, u.count a + v.count a = w.count a) :
    ‖splitFactorialCoefficient w u v‖ ≤ 1 := by
  let C := occupationChoices w (fun a => u.count a)
  have hC : (1 : ℝ) ≤ C := by
    exact_mod_cast occupationChoices_pos w u v hcount
  have h := congrArg norm (occupationChoices_mul_splitFactorialCoefficient w u v hcount)
  have h' : (C : ℝ) * ‖splitFactorialCoefficient w u v‖ = Real.sqrt C := by
    simpa only [norm_mul, Complex.norm_natCast, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)] using h
  have hs : Real.sqrt (C : ℝ) ≤ C := by
    have hp := Real.sq_sqrt (le_trans zero_le_one hC)
    nlinarith [Real.sqrt_nonneg (C : ℝ)]
  nlinarith

theorem normalizedSplitCoefficient_norm_le_one
    (mu nu : Fin d → ℕ)
    (hmu : ∀ a : PositiveRoot d, 0 < rootGap mu a)
    (hnu : ∀ a : PositiveRoot d, 0 < rootGap nu a)
    (w u v : List (PositiveRoot d)) (h : (u, v) ∈ loweringSplits w) :
    ‖normalizedSplitCoefficient mu nu w u v‖ ≤ 1 :=
  (normalizedSplitCoefficient_norm_le_factorial mu nu hmu hnu w u v h).trans
    (splitFactorialCoefficient_norm_le_one w u v (loweringSplits_grading w u v h).2.2)

theorem tensorJoin_sub_le_of_close {n m : ℕ}
    (x u : TensorRegister n (Fin d)) (y v : TensorRegister m (Fin d))
    (e : ℝ) (he : 0 ≤ e) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (hx : ‖x-u‖ ≤ e) (hy : ‖y-v‖ ≤ e) :
    ‖tensorJoin x y - tensorJoin u v‖ ≤ e*(2+e) := by
  have heq : tensorJoin x y - tensorJoin u v =
      tensorJoin (x-u) y + tensorJoin u (y-v) := by
    ext z
    simp only [tensorJoin_apply, lp.coeFn_sub, Pi.sub_apply, lp.coeFn_add, Pi.add_apply]
    ring
  have hyn : ‖y‖ ≤ 1+e := by
    calc
      ‖y‖ = ‖(y-v)+v‖ := by rw [sub_add_cancel]
      _ ≤ ‖y-v‖+‖v‖ := norm_add_le _ _
      _ ≤ 1+e := by rw [hv]; linarith
  calc
    _ ≤ ‖tensorJoin (x-u) y‖ + ‖tensorJoin u (y-v)‖ := by
      rw [heq]; exact norm_add_le _ _
    _ = ‖x-u‖*‖y‖ + ‖u‖*‖y-v‖ := by rw [tensorJoin_norm, tensorJoin_norm]
    _ ≤ e*(1+e)+1*e := add_le_add
      (mul_le_mul hx hyn (norm_nonneg _) he) (by simpa only [hu, one_mul] using hy)
    _ = e*(2+e) := by ring

theorem loweringSplits_length (w : List (PositiveRoot d)) :
    (loweringSplits w).length = 2^w.length := by
  induction w with
  | nil => simp [loweringSplits]
  | cons a w ih => simp [loweringSplits, ih, pow_succ]; omega

theorem loweringSplits_length_le {R : ℕ} (w : List (PositiveRoot d))
    (hw : w.length ≤ R) : (loweringSplits w).length ≤ 2^R := by
  rw [loweringSplits_length]
  exact Nat.pow_le_pow_right (by decide) hw

/-- A list version keeps the multiplicities in the exact lowering coproduct. -/
theorem list_weighted_replacement_le {ι H : Type*} [NormedAddCommGroup H]
    [NormedSpace ℂ H] (l : List ι) (c : ι → ℂ) (x y : ι → H) (e : ℝ)
    (he : 0 ≤ e) (hc : ∀i∈l, ‖c i‖ ≤ 1) (hxy : ∀i∈l, ‖x i-y i‖ ≤ e) :
    ‖(l.map (fun i => c i • x i)).sum - (l.map (fun i => c i • y i)).sum‖ ≤
      (l.length : ℝ)*e := by
  induction l with
  | nil => simp
  | cons i l ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
    have hi : ‖c i • x i - c i • y i‖ ≤ e := by
      rw [← smul_sub, norm_smul]
      simpa only [one_mul] using mul_le_mul (hc i (by simp)) (hxy i (by simp))
        (norm_nonneg _) zero_le_one
    have ht := ih (fun j hj => hc j (by simp [hj])) (fun j hj => hxy j (by simp [hj]))
    calc
      _ = ‖(c i • x i-c i • y i) +
          ((l.map (fun i => c i • x i)).sum-(l.map (fun i => c i • y i)).sum)‖ := by
        congr 1; abel
      _ ≤ _ := (norm_add_le _ _).trans (add_le_add hi ht)
      _ = _ := by ring

/-- Replacing both tensor factors in the exact Cartan coproduct costs at most
`2^R * e * (2+e)` for a retained word of length at most `R`. -/
theorem cartan_split_tensor_replacement_le {n m R : ℕ}
    (mu nu : Fin d → ℕ)
    (hmu : ∀ a : PositiveRoot d, 0 < rootGap mu a)
    (hnu : ∀ a : PositiveRoot d, 0 < rootGap nu a)
    (w : List (PositiveRoot d)) (hw : w.length ≤ R)
    (x u : List (PositiveRoot d) → TensorRegister n (Fin d))
    (y v : List (PositiveRoot d) → TensorRegister m (Fin d))
    (e : ℝ) (he : 0 ≤ e)
    (hu : ∀ a b, (a,b)∈loweringSplits w → ‖u a‖=1)
    (hv : ∀ a b, (a,b)∈loweringSplits w → ‖v b‖=1)
    (hx : ∀ a b, (a,b)∈loweringSplits w → ‖x a-u a‖≤e)
    (hy : ∀ a b, (a,b)∈loweringSplits w → ‖y b-v b‖≤e) :
    ‖((loweringSplits w).map (fun ab => normalizedSplitCoefficient mu nu w ab.1 ab.2 •
        tensorJoin (x ab.1) (y ab.2))).sum -
      ((loweringSplits w).map (fun ab => normalizedSplitCoefficient mu nu w ab.1 ab.2 •
        tensorJoin (u ab.1) (v ab.2))).sum‖ ≤
      (2:ℝ)^R * (e*(2+e)) := by
  have hpos : 0≤e*(2+e) := mul_nonneg he (by linarith)
  refine (list_weighted_replacement_le (loweringSplits w)
    (fun ab => normalizedSplitCoefficient mu nu w ab.1 ab.2)
    (fun ab => tensorJoin (x ab.1) (y ab.2))
    (fun ab => tensorJoin (u ab.1) (v ab.2)) _ hpos
    (fun ab hab => normalizedSplitCoefficient_norm_le_one mu nu hmu hnu w ab.1 ab.2 hab)
    (fun ab hab => tensorJoin_sub_le_of_close _ _ _ _ e he
      (hu _ _ hab) (hv _ _ hab) (hx _ _ hab) (hy _ _ hab))).trans ?_
  apply mul_le_mul_of_nonneg_right _ hpos
  exact_mod_cast loweringSplits_length_le w hw

end Cloning.TensorLie
