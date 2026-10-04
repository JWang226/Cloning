import Cloning.PBWNormalOrdering

/-!
# Fixed-cutoff PBW Gram estimates from local commutator bounds

For a filtered Hilbert space, creators and annihilators shift the cutoff by at
most one. A local creator bound `M` and local canonical-commutator defect `ε`
imply an explicit fixed-word Gram error bounded by `C(L,k) M^(2L) ε`.

In the highest-weight application one step of the filtration can be taken to
mean `d-1` units of simple-root height. Thus the theorem does not require every
positive root to have simple-root height one, or any global bounded-operator
estimate uniform in the highest weight. The construction of the representations
and proof of their local root estimates remain separate obligations.
-/

noncomputable section
open scoped InnerProductSpace
namespace Cloning.PBW
set_option linter.unusedSectionVars false

variable {ι H : Type*} [DecidableEq ι]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- A creation word of length `k` maps a vacuum in cutoff zero into cutoff `k`. -/
theorem word_mem_cutoff (F : ι → H →L[ℂ] H) (K : ℕ → Submodule ℂ H)
    (Ω : H) (hΩ : Ω ∈ K 0)
    (hF : ∀ i r x, x ∈ K r → F i x ∈ K (r + 1)) (w : List ι) :
    word F w Ω ∈ K w.length := by
  induction w with
  | nil => exact hΩ
  | cons i w ih => exact hF i w.length _ ih

/-- Local operator bounds control all bounded-length creation words. -/
theorem word_norm_le_cutoff (F : ι → H →L[ℂ] H) (K : ℕ → Submodule ℂ H)
    (Ω : H) (hΩ : Ω ∈ K 0) (hΩnorm : ‖Ω‖ ≤ 1)
    (hF : ∀ i r x, x ∈ K r → F i x ∈ K (r + 1))
    (L : ℕ) (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ i r, r ≤ L → ∀ x ∈ K r, ‖F i x‖ ≤ M * ‖x‖)
    (w : List ι) (hw : w.length ≤ L) : ‖word F w Ω‖ ≤ M ^ w.length := by
  induction w with
  | nil => simpa using hΩnorm
  | cons i w ih =>
      have hw' : w.length ≤ L := by simp only [List.length_cons] at hw; omega
      calc
        ‖word F (i :: w) Ω‖ ≤ M * ‖word F w Ω‖ :=
          hbound i w.length hw' _ (word_mem_cutoff F K Ω hΩ hF w)
        _ ≤ M * M ^ w.length := mul_le_mul_of_nonneg_left (ih hw') hM
        _ = M ^ (i :: w).length := by simp [pow_succ, mul_comm]

/-- A commutator defect has cutoff at most two greater than its input. -/
theorem commutatorDefect_mem_cutoff (F A : ι → H →L[ℂ] H)
    (K : ℕ → Submodule ℂ H) (hK : Monotone K)
    (hF : ∀ i r x, x ∈ K r → F i x ∈ K (r + 1))
    (hA : ∀ i r x, x ∈ K r → A i x ∈ K (r + 1))
    (i j : ι) (r : ℕ) (x : H) (hx : x ∈ K r) :
    commutatorDefect F A i j x ∈ K (r + 2) := by
  unfold commutatorDefect
  refine (K (r + 2)).sub_mem ((K (r + 2)).sub_mem
    (hA i (r + 1) _ (hF j r x hx)) (hF j (r + 1) _ (hA i r x hx))) ?_
  split_ifs
  · exact hK (by omega) hx
  · exact (K _).zero_mem

/-- Every error term from a word of length `k` lies in cutoff `k+1`. -/
theorem errorTerms_mem_cutoff (F A : ι → H →L[ℂ] H)
    (K : ℕ → Submodule ℂ H) (hK : Monotone K) (Ω : H) (hΩ : Ω ∈ K 0)
    (hF : ∀ i r x, x ∈ K r → F i x ∈ K (r + 1))
    (hA : ∀ i r x, x ∈ K r → A i x ∈ K (r + 1))
    (i : ι) (w : List ι) (x : H) (hx : x ∈ errorTerms F A Ω i w) :
    x ∈ K (w.length + 1) := by
  induction w generalizing x with
  | nil => simp [errorTerms] at hx
  | cons j w ih =>
      simp only [errorTerms, List.mem_cons, List.mem_map] at hx
      rcases hx with rfl | ⟨y, hy, rfl⟩
      · exact commutatorDefect_mem_cutoff F A K hK hF hA i j w.length _
          (word_mem_cutoff F K Ω hΩ hF w)
      · exact hF j (w.length + 1) y (ih y hy)

/-- The transported commutator errors are controlled by local cutoff estimates.
This discharges the error-term premise of `gram_error_le`. -/
theorem errorTerms_norm_le_cutoff (F A : ι → H →L[ℂ] H)
    (K : ℕ → Submodule ℂ H) (hK : Monotone K) (Ω : H)
    (hΩ : Ω ∈ K 0) (hΩnorm : ‖Ω‖ ≤ 1)
    (hF : ∀ i r x, x ∈ K r → F i x ∈ K (r + 1))
    (hA : ∀ i r x, x ∈ K r → A i x ∈ K (r + 1))
    (L : ℕ) (M ε : ℝ) (hM : 1 ≤ M) (hε : 0 ≤ ε)
    (hbound : ∀ i r, r ≤ L → ∀ x ∈ K r, ‖F i x‖ ≤ M * ‖x‖)
    (hcomm : ∀ i j r, r ≤ L → ∀ x ∈ K r,
      ‖commutatorDefect F A i j x‖ ≤ ε * ‖x‖)
    (i : ι) (w : List ι) (hw : w.length ≤ L)
    (x : H) (hx : x ∈ errorTerms F A Ω i w) :
    ‖x‖ ≤ ε * M ^ w.length := by
  induction w generalizing x with
  | nil => simp [errorTerms] at hx
  | cons j w ih =>
      have hw' : w.length ≤ L := by simp only [List.length_cons] at hw; omega
      simp only [errorTerms, List.mem_cons, List.mem_map] at hx
      rcases hx with rfl | ⟨y, hy, rfl⟩
      · calc
          _ ≤ ε * ‖word F w Ω‖ := hcomm i j w.length hw' _
            (word_mem_cutoff F K Ω hΩ hF w)
          _ ≤ ε * M ^ w.length := mul_le_mul_of_nonneg_left
            (word_norm_le_cutoff F K Ω hΩ hΩnorm hF L M (by linarith) hbound w hw') hε
          _ ≤ ε * M ^ (j :: w).length := by
            apply mul_le_mul_of_nonneg_left _ hε
            exact pow_le_pow_right₀ hM (by simp)
      · calc
          ‖F j y‖ ≤ M * ‖y‖ := hbound j (w.length + 1) hw _
            (errorTerms_mem_cutoff F A K hK Ω hΩ hF hA i w y hy)
          _ ≤ M * (ε * M ^ w.length) :=
            mul_le_mul_of_nonneg_left (ih hw' y hy) (by linarith)
          _ = ε * M ^ (j :: w).length := by simp [pow_succ]; ring

/-- General-rank fixed-cutoff PBW Gram estimate. The hypotheses concern only
local root actions and their commutators; the factorial Gram leading term is
proved by normal ordering. -/
theorem gram_error_le_of_cutoff (F A : ι → H →L[ℂ] H)
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
    ‖⟪word F u Ω, word F v Ω⟫_ℂ -
      (if u.Perm v then (occupationFactorial u : ℂ) else 0)‖ ≤
      (gramConstant L u.length : ℝ) * M ^ (2 * L) * ε := by
  have hΩnorm : ‖Ω‖ ≤ 1 := by
    have hh : ‖Ω‖ ^ 2 = 1 := by
      rw [@norm_sq_eq_re_inner ℂ, hnorm]
      rfl
    nlinarith [norm_nonneg Ω]
  have hw : ∀ w : List ι, w.length ≤ L → ‖word F w Ω‖ ≤ M ^ L := by
    intro w hw
    exact (word_norm_le_cutoff F K Ω hΩmem hΩnorm hF L M
      (by linarith) hbound w hw).trans (by gcongr; exact hM)
  have he : ∀ i w, w.length ≤ L →
      ∀ x ∈ errorTerms F A Ω i w, ‖x‖ ≤ ε * M ^ L := by
    intro i w hw x hx
    exact (errorTerms_norm_le_cutoff F A K hK Ω hΩmem hΩnorm hF hA
      L M ε hM hε hbound hcomm i w hw x hx).trans (by gcongr; exact hM)
  have hh := gram_error_le F A Ω L (M ^ L) (ε * M ^ L)
    (by positivity) (by positivity) hnorm hΩ hadj hw he u v hu hv
  rw [wick_eq_occupationFactorial] at hh
  simp only [Nat.cast_ite, Nat.cast_zero] at hh
  convert hh using 1; ring

end Cloning.PBW
