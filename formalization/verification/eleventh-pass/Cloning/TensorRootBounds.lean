import Cloning.TensorCyclicOccupancy
import Cloning.PBWRootGram

/-! Local raw-root norm estimates derived from actual Cartan occupancy and
raising invariance. Zero highest-weight gaps are permitted in these bounds. -/
noncomputable section
open scoped InnerProductSpace
namespace Cloning.TensorLie
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

section RawRecurrence
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem creator_norm_sq_le_of_raw_commutator
    (F A : H →L[ℂ] H)
    (hadj : ∀ x y, ⟪F x, y⟫_ℂ = ⟪x, A y⟫_ℂ)
    (B : ℝ) (x : H) (hdef : ‖A (F x) - F (A x)‖ ≤ B * ‖x‖) :
    ‖F x‖ ^ 2 ≤ ‖A x‖ ^ 2 + B * ‖x‖ ^ 2 := by
  have hF : (⟪x, A (F x)⟫_ℂ).re = ‖F x‖ ^ 2 := by
    rw [← hadj]
    exact (norm_sq_eq_re_inner (𝕜 := ℂ) (F x)).symm
  have hA : (⟪x, F (A x)⟫_ℂ).re = ‖A x‖ ^ 2 := by
    calc
      _ = (⟪F (A x), x⟫_ℂ).re := inner_re_symm (𝕜 := ℂ) x (F (A x))
      _ = _ := by rw [hadj]; exact (norm_sq_eq_re_inner (𝕜 := ℂ) (A x)).symm
  have hh : (⟪x, A (F x) - F (A x)⟫_ℂ).re ≤ B * ‖x‖ ^ 2 := by
    calc
      _ ≤ ‖⟪x, A (F x) - F (A x)⟫_ℂ‖ := Complex.re_le_norm _
      _ ≤ ‖x‖ * ‖A (F x) - F (A x)‖ := norm_inner_le_norm _ _
      _ ≤ ‖x‖ * (B * ‖x‖) := mul_le_mul_of_nonneg_left hdef (norm_nonneg _)
      _ = _ := by ring
  simp only [inner_sub_right, Complex.sub_re, hF, hA] at hh
  linarith

theorem creator_norm_sq_le_raw_cutoff
    (F A : H →L[ℂ] H) (K : ℕ → Submodule ℂ H)
    (hadj : ∀ x y, ⟪F x, y⟫_ℂ = ⟪x, A y⟫_ℂ)
    (hzero : ∀ x ∈ K 0, A x = 0)
    (hlower : ∀ r x, x ∈ K (r + 1) → A x ∈ K r)
    (L : ℕ) (B : ℝ) (hB : 0 ≤ B)
    (hcomm : ∀ r, r ≤ L → ∀ x ∈ K r, ‖A (F x) - F (A x)‖ ≤ B * ‖x‖)
    (r : ℕ) (hr : r ≤ L) (x : H) (hx : x ∈ K r) :
    ‖F x‖ ^ 2 ≤ ((r : ℝ) + 1) * B * ‖x‖ ^ 2 := by
  induction r generalizing x with
  | zero =>
      have hh := creator_norm_sq_le_of_raw_commutator F A hadj B x (hcomm 0 hr x hx)
      simpa [hzero x hx] using hh
  | succ r ih =>
      have hr' : r ≤ L := by omega
      let C : ℝ := Real.sqrt (((r : ℝ) + 1) * B)
      have hC : 0 ≤ C := Real.sqrt_nonneg _
      have hCsq : C ^ 2 = ((r : ℝ) + 1) * B := Real.sq_sqrt (by positivity)
      have hlocal : ∀ y ∈ K r, ‖F y‖ ≤ C * ‖y‖ := by
        intro y hy
        have hybound := ih hr' y hy
        have hpos : 0 ≤ C * ‖y‖ := mul_nonneg hC (norm_nonneg _)
        have heq : (C * ‖y‖) ^ 2 = ((r : ℝ) + 1) * B * ‖y‖ ^ 2 := by
          rw [mul_pow, hCsq]
        nlinarith [norm_nonneg (F y)]
      have hAbound := PBW.annihilator_norm_le_from_local_creator F A (K r) C hC hadj hlocal
        x (hlower r x hx)
      have hAsq : ‖A x‖ ^ 2 ≤ ((r : ℝ) + 1) * B * ‖x‖ ^ 2 := by
        have hh := (sq_le_sq₀ (norm_nonneg (A x)) (mul_nonneg hC (norm_nonneg x))).mpr hAbound
        simpa [mul_pow, hCsq] using hh
      have hh := creator_norm_sq_le_of_raw_commutator F A hadj B x (hcomm (r + 1) hr x hx)
      simp only [Nat.cast_add, Nat.cast_one]
      nlinarith
end RawRecurrence

variable {n d : ℕ}

theorem collectiveGenerator_inner_adjoint (a b : Fin d) (x y : TensorRegister n (Fin d)) :
    ⟪collectiveGenerator n b a x, y⟫_ℂ = ⟪x, collectiveGenerator n a b y⟫_ℂ := by
  rw [← collectiveGenerator_adjoint b a, ContinuousLinearMap.adjoint_inner_right]

theorem root_diagonal_commutator (a b : Fin d) (x : TensorRegister n (Fin d)) :
    collectiveGenerator n a b (collectiveGenerator n b a x) -
      collectiveGenerator n b a (collectiveGenerator n a b x) =
    collectiveGenerator n a a x - collectiveGenerator n b b x := by
  have he := congrArg (fun T : TensorRegister n (Fin d) →L[ℂ] TensorRegister n (Fin d) => T x)
    (collectiveGenerator_commutator (n := n) a b b a)
  simpa only [if_true, ContinuousLinearMap.sub_apply, ContinuousLinearMap.mul_apply] using he

theorem root_commutator_norm_le
    (Ω : TensorRegister n (Fin d)) (mu : Fin d → ℕ)
    (hweight : ∀ a, collectiveGenerator n a a Ω = (mu a : ℂ) • Ω)
    (r : ℕ) {x : TensorRegister n (Fin d)} (hx : x ∈ cyclicCutoff Ω r) (a b : Fin d) :
    ‖collectiveGenerator n a b (collectiveGenerator n b a x) -
      collectiveGenerator n b a (collectiveGenerator n a b x)‖ ≤
      (|(mu a : ℝ) - mu b| + 2 * r) * ‖x‖ := by
  rw [root_diagonal_commutator]
  let y := collectiveGenerator n a a x - collectiveGenerator n b b x
  have he : y = (y - ((mu a : ℂ) - mu b) • x) + ((mu a : ℂ) - mu b) • x := by module
  calc
    ‖y‖ = ‖(y - ((mu a : ℂ) - mu b) • x) + ((mu a : ℂ) - mu b) • x‖ := congrArg norm he
    _ ≤ ‖y - ((mu a : ℂ) - mu b) • x‖ + ‖((mu a : ℂ) - mu b) • x‖ := norm_add_le _ _
    _ ≤ (2 * r : ℝ) * ‖x‖ + ‖((mu a : ℂ) - mu b) • x‖ :=
      add_le_add (cartan_difference_defect_norm_le Ω mu hweight r hx a b) le_rfl
    _ = _ := by
      rw [norm_smul]
      simp only [← Complex.ofReal_natCast, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      ring

/-- A raw lowering root has squared local norm at most
`(R+1)(|mu_a-mu_b|+2R)`. In particular zero weight gaps require no division. -/
theorem lowering_norm_sq_le_cyclicCutoff
    (Ω : TensorRegister n (Fin d)) (mu : Fin d → ℕ)
    (hweight : ∀ a, collectiveGenerator n a a Ω = (mu a : ℂ) • Ω)
    (hraise : ∀ a b, a < b → collectiveGenerator n a b Ω = 0)
    (a b : Fin d) (hab : a < b) (r : ℕ) {x : TensorRegister n (Fin d)}
    (hx : x ∈ cyclicCutoff Ω r) :
    ‖collectiveGenerator n b a x‖ ^ 2 ≤
      ((r : ℝ) + 1) * (|(mu a : ℝ) - mu b| + 2 * r) * ‖x‖ ^ 2 := by
  apply creator_norm_sq_le_raw_cutoff (collectiveGenerator n b a) (collectiveGenerator n a b)
    (fun t => cyclicCutoff Ω (t : ℤ)) (collectiveGenerator_inner_adjoint a b)
    (fun y hy => raising_zero_cyclicCutoff Ω (fun i => (mu i : ℂ)) hweight hraise a b hab hy)
    (fun t y hy => raising_lowers_cyclicCutoff Ω (fun i => (mu i : ℂ)) hweight hraise a b hab t hy)
    r (|(mu a : ℝ) - mu b| + 2 * r) (by positivity) _ r le_rfl x hx
  intro t ht y hy
  exact (root_commutator_norm_le Ω mu hweight t hy a b).trans (by gcongr)

theorem lowering_norm_le_cyclicCutoff
    (Ω : TensorRegister n (Fin d)) (mu : Fin d → ℕ)
    (hweight : ∀ a, collectiveGenerator n a a Ω = (mu a : ℂ) • Ω)
    (hraise : ∀ a b, a < b → collectiveGenerator n a b Ω = 0)
    (a b : Fin d) (hab : a < b) (r : ℕ) {x : TensorRegister n (Fin d)}
    (hx : x ∈ cyclicCutoff Ω r) :
    ‖collectiveGenerator n b a x‖ ≤
      Real.sqrt (((r : ℝ) + 1) * (|(mu a : ℝ) - mu b| + 2 * r)) * ‖x‖ := by
  have hb := lowering_norm_sq_le_cyclicCutoff Ω mu hweight hraise a b hab r hx
  have he := Real.sq_sqrt (by positivity : 0 ≤ ((r : ℝ) + 1) * (|(mu a : ℝ) - mu b| + 2 * r))
  have hn : 0 ≤ Real.sqrt (((r : ℝ) + 1) * (|(mu a : ℝ) - mu b| + 2 * r)) * ‖x‖ := by positivity
  nlinarith [mul_pow (Real.sqrt (((r : ℝ) + 1) * (|(mu a : ℝ) - mu b| + 2 * r))) ‖x‖ 2]

/-- The same local estimate holds for every off-diagonal raw root, in either orientation. -/
theorem root_norm_le_cyclicCutoff
    (Ω : TensorRegister n (Fin d)) (mu : Fin d → ℕ)
    (hweight : ∀ a, collectiveGenerator n a a Ω = (mu a : ℂ) • Ω)
    (hraise : ∀ a b, a < b → collectiveGenerator n a b Ω = 0)
    (a b : Fin d) (hab : a ≠ b) (r : ℕ) {x : TensorRegister n (Fin d)}
    (hx : x ∈ cyclicCutoff Ω r) :
    ‖collectiveGenerator n a b x‖ ≤
      Real.sqrt (((r : ℝ) + 1) * (|(mu a : ℝ) - mu b| + 2 * r)) * ‖x‖ := by
  rcases lt_or_gt_of_ne hab with hab | hba
  · apply PBW.annihilator_norm_le_from_local_creator
      (collectiveGenerator n b a) (collectiveGenerator n a b) (cyclicCutoff Ω r)
      _ (Real.sqrt_nonneg _) (collectiveGenerator_inner_adjoint a b)
      (fun y hy => lowering_norm_le_cyclicCutoff Ω mu hweight hraise a b hab r hy) x
    exact PBW.annihilator_mem_same_cutoff (collectiveGenerator n a b)
      (fun t => cyclicCutoff Ω (t : ℤ))
      (fun i j hij => cyclicCutoff_monotone Ω (Int.ofNat_le.mpr hij))
      (fun y hy => raising_zero_cyclicCutoff Ω (fun i => (mu i : ℂ)) hweight hraise a b hab hy)
      (fun t y hy => raising_lowers_cyclicCutoff Ω (fun i => (mu i : ℂ)) hweight hraise a b hab t hy)
      r x hx
  · simpa only [abs_sub_comm] using lowering_norm_le_cyclicCutoff Ω mu hweight hraise b a hba r hx

end Cloning.TensorLie
