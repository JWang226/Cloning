import Cloning.PBWCutoffGram

/-!
# Deriving local root bounds without assuming PBW independence

The fixed-height PBW argument must bound normalized root operators before it
can use Gram matrices. Here that bound follows from adjointness, strict lowering
of the annihilator through complete cutoff spaces, and the diagonal commutator
estimate. In particular it does not assume a PBW basis or a Gram bound.
-/

noncomputable section
open scoped InnerProductSpace
namespace Cloning.PBW
set_option backward.isDefEq.respectTransparency false

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Adjointness transfers a local creator bound to an annihilator whose image
lies in that local subspace. No bounded inverse or basis is required. -/
theorem annihilator_norm_le_from_local_creator
    (F A : H →L[ℂ] H) (S : Submodule ℂ H) (C : ℝ) (hC : 0 ≤ C)
    (hadj : ∀ x y, ⟪F x, y⟫_ℂ = ⟪x, A y⟫_ℂ)
    (hF : ∀ y ∈ S, ‖F y‖ ≤ C * ‖y‖) (x : H) (hx : A x ∈ S) :
    ‖A x‖ ≤ C * ‖x‖ := by
  have hsq : ‖A x‖ ^ 2 ≤ C * ‖A x‖ * ‖x‖ := by
    calc
      ‖A x‖ ^ 2 = (⟪F (A x), x⟫_ℂ).re := by
        rw [hadj]
        exact norm_sq_eq_re_inner (𝕜 := ℂ) (A x)
      _ ≤ ‖⟪F (A x), x⟫_ℂ‖ := Complex.re_le_norm _
      _ ≤ ‖F (A x)‖ * ‖x‖ := norm_inner_le_norm _ _
      _ ≤ (C * ‖A x‖) * ‖x‖ := mul_le_mul_of_nonneg_right (hF _ hx) (norm_nonneg _)
  have hnonneg : 0 ≤ C * ‖x‖ := mul_nonneg hC (norm_nonneg _)
  nlinarith [norm_nonneg (A x)]

/-- The diagonal canonical-commutator estimate gives the basic norm recurrence. -/
theorem creator_norm_sq_le_of_diagonal
    (F A : H →L[ℂ] H)
    (hadj : ∀ x y, ⟪F x, y⟫_ℂ = ⟪x, A y⟫_ℂ)
    (δ : ℝ) (x : H) (hdef : ‖A (F x) - F (A x) - x‖ ≤ δ * ‖x‖) :
    ‖F x‖ ^ 2 ≤ ‖A x‖ ^ 2 + (1 + δ) * ‖x‖ ^ 2 := by
  have hF : (⟪x, A (F x)⟫_ℂ).re = ‖F x‖ ^ 2 := by
    rw [← hadj]
    exact (norm_sq_eq_re_inner (𝕜 := ℂ) (F x)).symm
  have hA : (⟪x, F (A x)⟫_ℂ).re = ‖A x‖ ^ 2 := by
    calc
      _ = (⟪F (A x), x⟫_ℂ).re := inner_re_symm (𝕜 := ℂ) x (F (A x))
      _ = _ := by
        rw [hadj]
        exact (norm_sq_eq_re_inner (𝕜 := ℂ) (A x)).symm
  have hinner : (⟪x, A (F x) - F (A x) - x⟫_ℂ).re =
      ‖F x‖ ^ 2 - ‖A x‖ ^ 2 - ‖x‖ ^ 2 := by
    have hxnorm : (⟪x, x⟫_ℂ).re = ‖x‖ ^ 2 := (norm_sq_eq_re_inner (𝕜 := ℂ) x).symm
    simp only [inner_sub_right, Complex.sub_re, hF, hA, hxnorm]
  have hbound : (⟪x, A (F x) - F (A x) - x⟫_ℂ).re ≤ δ * ‖x‖ ^ 2 := by
    calc
      _ ≤ ‖⟪x, A (F x) - F (A x) - x⟫_ℂ‖ := Complex.re_le_norm _
      _ ≤ ‖x‖ * ‖A (F x) - F (A x) - x‖ := norm_inner_le_norm _ _
      _ ≤ ‖x‖ * (δ * ‖x‖) := mul_le_mul_of_nonneg_left hdef (norm_nonneg _)
      _ = _ := by ring
  rw [hinner] at hbound
  linarith

/-- The local normalized creator bound is derived by induction through complete
cutoff spaces: its squared norm on cutoff `r` is at most `(r+1)(1+δ)`.
The annihilator must vanish on cutoff zero and lower every higher cutoff.
This is the noncircular operator estimate used before PBW Gram convergence. -/
theorem creator_norm_sq_le_cutoff
    (F A : H →L[ℂ] H) (K : ℕ → Submodule ℂ H)
    (hadj : ∀ x y, ⟪F x, y⟫_ℂ = ⟪x, A y⟫_ℂ)
    (hzero : ∀ x ∈ K 0, A x = 0)
    (hlower : ∀ r x, x ∈ K (r + 1) → A x ∈ K r)
    (L : ℕ) (δ : ℝ) (hδ : 0 ≤ δ)
    (hdiag : ∀ r, r ≤ L → ∀ x ∈ K r,
      ‖A (F x) - F (A x) - x‖ ≤ δ * ‖x‖)
    (r : ℕ) (hr : r ≤ L) (x : H) (hx : x ∈ K r) :
    ‖F x‖ ^ 2 ≤ ((r : ℝ) + 1) * (1 + δ) * ‖x‖ ^ 2 := by
  induction r generalizing x with
  | zero =>
      have hh := creator_norm_sq_le_of_diagonal F A hadj δ x (hdiag 0 hr x hx)
      simpa [hzero x hx] using hh
  | succ r ih =>
      have hr' : r ≤ L := by omega
      let C : ℝ := Real.sqrt (((r : ℝ) + 1) * (1 + δ))
      have hC : 0 ≤ C := Real.sqrt_nonneg _
      have hCsq : C ^ 2 = ((r : ℝ) + 1) * (1 + δ) := Real.sq_sqrt (by positivity)
      have hlocal : ∀ y ∈ K r, ‖F y‖ ≤ C * ‖y‖ := by
        intro y hy
        have hybound := ih hr' y hy
        have hpos : 0 ≤ C * ‖y‖ := mul_nonneg hC (norm_nonneg _)
        have heq : (C * ‖y‖) ^ 2 = ((r : ℝ) + 1) * (1 + δ) * ‖y‖ ^ 2 := by
          rw [mul_pow, hCsq]
        nlinarith [norm_nonneg (F y)]
      have hAbound := annihilator_norm_le_from_local_creator F A (K r) C hC hadj hlocal
        x (hlower r x hx)
      have hAsq : ‖A x‖ ^ 2 ≤ ((r : ℝ) + 1) * (1 + δ) * ‖x‖ ^ 2 := by
        have hh := sq_le_sq₀ (norm_nonneg (A x)) (mul_nonneg hC (norm_nonneg x)) |>.mpr hAbound
        simpa [mul_pow, hCsq] using hh
      have hh := creator_norm_sq_le_of_diagonal F A hadj δ x (hdiag (r + 1) hr x hx)
      simp only [Nat.cast_add, Nat.cast_one]
      nlinarith

/-- A single local creator bound works on every cutoff below `L`. -/
theorem creator_norm_le_cutoff
    (F A : H →L[ℂ] H) (K : ℕ → Submodule ℂ H)
    (hadj : ∀ x y, ⟪F x, y⟫_ℂ = ⟪x, A y⟫_ℂ)
    (hzero : ∀ x ∈ K 0, A x = 0)
    (hlower : ∀ r x, x ∈ K (r + 1) → A x ∈ K r)
    (L : ℕ) (δ : ℝ) (hδ : 0 ≤ δ)
    (hdiag : ∀ r, r ≤ L → ∀ x ∈ K r,
      ‖A (F x) - F (A x) - x‖ ≤ δ * ‖x‖)
    (r : ℕ) (hr : r ≤ L) (x : H) (hx : x ∈ K r) :
    ‖F x‖ ≤ Real.sqrt (((L : ℝ) + 1) * (1 + δ)) * ‖x‖ := by
  have hh := creator_norm_sq_le_cutoff F A K hadj hzero hlower L δ hδ hdiag r hr x hx
  have hc : ((r : ℝ) + 1) * (1 + δ) * ‖x‖ ^ 2 ≤
      ((L : ℝ) + 1) * (1 + δ) * ‖x‖ ^ 2 := by gcongr
  have hs : (Real.sqrt (((L : ℝ) + 1) * (1 + δ))) ^ 2 =
      ((L : ℝ) + 1) * (1 + δ) := Real.sq_sqrt (by positivity)
  have hn : 0 ≤ Real.sqrt (((L : ℝ) + 1) * (1 + δ)) * ‖x‖ := by positivity
  nlinarith [mul_pow (Real.sqrt (((L : ℝ) + 1) * (1 + δ))) ‖x‖ 2]

end Cloning.PBW
