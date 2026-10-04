import Cloning.PBWCutoffGram
import Mathlib.Topology.Instances.Matrix

/-!
# Normalized PBW Gram limits

Factorial normalization turns the general-word Wick leading term into the
identity on distinct occupation lists. Local cutoff commutator errors tending
to zero therefore imply convergence of the actual normalized vector Gram
entries. The representation spaces may vary with the asymptotic parameter.
-/

noncomputable section
open scoped InnerProductSpace Topology
open Filter
namespace Cloning.PBW
set_option linter.unusedSectionVars false

variable {ι H : Type*} [DecidableEq ι]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The occupation factorial is always positive, including the vacuum word. -/
theorem occupationFactorial_pos (w : List ι) : 0 < occupationFactorial w := by
  induction w with
  | nil => simp [occupationFactorial]
  | cons i w ih => exact Nat.mul_pos (by omega) ih

/-- The normalization is determined only by root occupation numbers. -/
theorem occupationFactorial_eq_of_perm [Fintype ι] {u v : List ι} (h : u.Perm v) :
    occupationFactorial u = occupationFactorial v := by
  simp only [occupationFactorial_eq_prod]
  exact Finset.prod_congr rfl (fun i _ => congrArg Nat.factorial (h.count_eq i))

/-- Ordered PBW vector divided by the square root of its occupation factorial. -/
def normalizedWord (F : ι → H →L[ℂ] H) (w : List ι) (Ω : H) : H :=
  ((Real.sqrt (occupationFactorial w : ℝ))⁻¹ : ℂ) • word F w Ω

private theorem sqrt_factorial_ge_one (w : List ι) :
    1 ≤ Real.sqrt (occupationFactorial w : ℝ) := by
  apply Real.one_le_sqrt.mpr
  exact_mod_cast occupationFactorial_pos w

private theorem norm_normalization_le_one (w : List ι) :
    ‖((Real.sqrt (occupationFactorial w : ℝ))⁻¹ : ℂ)‖ ≤ 1 := by
  rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact (inv_le_one₀ (by have := sqrt_factorial_ge_one w; linarith)).mpr
    (sqrt_factorial_ge_one w)

/-- Factorial normalization can only improve the raw Wick Gram error. -/
theorem normalized_gram_error_le [Fintype ι]
    (F : ι → H →L[ℂ] H) (Ω : H) (u v : List ι) :
    ‖⟪normalizedWord F u Ω, normalizedWord F v Ω⟫_ℂ -
      (if u.Perm v then 1 else 0 : ℂ)‖ ≤
    ‖⟪word F u Ω, word F v Ω⟫_ℂ -
      (if u.Perm v then (occupationFactorial u : ℂ) else 0)‖ := by
  let a : ℂ := ((Real.sqrt (occupationFactorial u : ℝ))⁻¹ : ℂ)
  let b : ℂ := ((Real.sqrt (occupationFactorial v : ℝ))⁻¹ : ℂ)
  have ha : ‖a‖ ≤ 1 := norm_normalization_le_one u
  have hb : ‖b‖ ≤ 1 := norm_normalization_le_one v
  have hlead : (a * b) * (if u.Perm v then (occupationFactorial u : ℂ) else 0) =
      (if u.Perm v then 1 else 0 : ℂ) := by
    split_ifs with huv
    · have heq := occupationFactorial_eq_of_perm huv
      dsimp [a, b]
      rw [← heq]
      have hr : (Real.sqrt (occupationFactorial u : ℝ))⁻¹ *
          (Real.sqrt (occupationFactorial u : ℝ))⁻¹ * (occupationFactorial u : ℝ) = 1 := by
        have hs : Real.sqrt (occupationFactorial u : ℝ) ≠ 0 :=
          ne_of_gt (by have := sqrt_factorial_ge_one u; linarith)
        field_simp
        exact (Real.sq_sqrt (by positivity)).symm
      exact_mod_cast hr
    · simp
  have heq : ⟪normalizedWord F u Ω, normalizedWord F v Ω⟫_ℂ =
      (a * b) * ⟪word F u Ω, word F v Ω⟫_ℂ := by
    simp [normalizedWord, inner_smul_left, inner_smul_right, a, b, mul_assoc, mul_left_comm]
  rw [heq, ← hlead, ← mul_sub, norm_mul]
  calc
    _ ≤ 1 * ‖⟪word F u Ω, word F v Ω⟫_ℂ -
        (if u.Perm v then (occupationFactorial u : ℂ) else 0)‖ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      simpa only [norm_mul, one_mul] using mul_le_mul ha hb (norm_nonneg b) (by norm_num : (0:ℝ) ≤ 1)
    _ = _ := one_mul _

/-- Normalized fixed-height PBW Gram bound, with all inputs stated at the
operator and local commutator level. -/
theorem normalized_gram_error_le_of_cutoff [Fintype ι]
    (F A : ι → H →L[ℂ] H)
    (K : ℕ → Submodule ℂ H) (hK : Monotone K) (Ω : H) (hΩmem : Ω ∈ K 0)
    (hnorm : ⟪Ω, Ω⟫_ℂ = 1) (hΩ : ∀ i, A i Ω = 0)
    (hadj : ∀ i x y, ⟪F i x, y⟫_ℂ = ⟪x, A i y⟫_ℂ)
    (hF : ∀ i r x, x ∈ K r → F i x ∈ K (r + 1))
    (hA : ∀ i r x, x ∈ K r → A i x ∈ K (r + 1))
    (L : ℕ) (M ε : ℝ) (hM : 1 ≤ M) (hε : 0 ≤ ε)
    (hbound : ∀ i r, r ≤ L → ∀ x ∈ K r, ‖F i x‖ ≤ M * ‖x‖)
    (hcomm : ∀ i j r, r ≤ L → ∀ x ∈ K r,
      ‖commutatorDefect F A i j x‖ ≤ ε * ‖x‖)
    (u v : List ι) (hu : u.length ≤ L) (hv : v.length ≤ L) :
    ‖⟪normalizedWord F u Ω, normalizedWord F v Ω⟫_ℂ -
      (if u.Perm v then 1 else 0 : ℂ)‖ ≤
      (gramConstant L u.length : ℝ) * M ^ (2 * L) * ε :=
  (normalized_gram_error_le F Ω u v).trans
    (gram_error_le_of_cutoff F A K hK Ω hΩmem hnorm hΩ hadj hF hA
      L M ε hM hε hbound hcomm u v hu hv)

/-- Local normalized commutator convergence yields normalized Gram convergence,
even when every highest weight lives in a different Hilbert space. -/
theorem normalized_gram_tendsto_of_cutoff [Fintype ι]
    (E : ℕ → Type*) [∀ n, NormedAddCommGroup (E n)] [∀ n, InnerProductSpace ℂ (E n)]
    (F A : ∀ n, ι → E n →L[ℂ] E n)
    (K : ∀ n, ℕ → Submodule ℂ (E n)) (Ω : ∀ n, E n)
    (L : ℕ) (M : ℝ) (ε : ℕ → ℝ) (hM : 1 ≤ M) (hε : ∀ n, 0 ≤ ε n)
    (hεlim : Tendsto ε atTop (𝓝 0))
    (hK : ∀ n, Monotone (K n)) (hΩmem : ∀ n, Ω n ∈ K n 0)
    (hnorm : ∀ n, ⟪Ω n, Ω n⟫_ℂ = 1) (hΩ : ∀ n i, A n i (Ω n) = 0)
    (hadj : ∀ n i x y, ⟪F n i x, y⟫_ℂ = ⟪x, A n i y⟫_ℂ)
    (hF : ∀ n i r x, x ∈ K n r → F n i x ∈ K n (r + 1))
    (hA : ∀ n i r x, x ∈ K n r → A n i x ∈ K n (r + 1))
    (hbound : ∀ n i r, r ≤ L → ∀ x ∈ K n r, ‖F n i x‖ ≤ M * ‖x‖)
    (hcomm : ∀ n i j r, r ≤ L → ∀ x ∈ K n r,
      ‖commutatorDefect (F n) (A n) i j x‖ ≤ ε n * ‖x‖)
    (u v : List ι) (hu : u.length ≤ L) (hv : v.length ≤ L) :
    Tendsto (fun n => ⟪normalizedWord (F n) u (Ω n), normalizedWord (F n) v (Ω n)⟫_ℂ)
      atTop (𝓝 (if u.Perm v then 1 else 0)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun n => norm_nonneg _) (fun n =>
    normalized_gram_error_le_of_cutoff (F n) (A n) (K n) (hK n) (Ω n)
      (hΩmem n) (hnorm n) (hΩ n) (hadj n) (hF n) (hA n) L M (ε n)
      hM (hε n) (hbound n) (hcomm n) u v hu hv)
  simpa using hεlim.const_mul ((gramConstant L u.length : ℝ) * M ^ (2 * L))

end Cloning.PBW
