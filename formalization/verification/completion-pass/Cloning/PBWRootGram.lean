import Cloning.PBWRootBounds
import Cloning.PBWGramLimit

/-!
# Root-height filtration to normalized PBW Gram estimates

This connects the two different cutoffs needed by the manuscript proof.
Annihilators lower the *fine* simple-root-height cutoff by at least one, while
creators raise it by at most the maximal positive-root height `D`.
The normal-ordering proof uses the grouped cutoff `K (D*r)`. The creator bound
on that grouped cutoff is derived on the fine filtration first.

The result needs no separately postulated bounded-root-operator estimate:
small canonical-commutator defects, adjointness, and root-height shifts imply
the normalized factorial Gram estimate for every bounded-length word.
-/

noncomputable section
open scoped InnerProductSpace
namespace Cloning.PBW
set_option linter.unusedSectionVars false

variable {ι H : Type*} [DecidableEq ι] [Fintype ι]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Fine-cutoff strict lowering implies preservation of each fine cutoff. -/
theorem annihilator_mem_same_cutoff (A : H →L[ℂ] H)
    (K : ℕ → Submodule ℂ H) (hK : Monotone K)
    (hzero : ∀ x ∈ K 0, A x = 0)
    (hlower : ∀ r x, x ∈ K (r + 1) → A x ∈ K r)
    (r : ℕ) (x : H) (hx : x ∈ K r) : A x ∈ K r := by
  cases r with
  | zero => rw [hzero x hx]; exact (K 0).zero_mem
  | succ r => exact hK (Nat.le_succ r) (hlower r x hx)

/-- Root-height form of the fixed-word PBW Gram estimate. The normalized root
operator bound is a conclusion of `creator_norm_le_cutoff`, rather than an
additional premise. `D` can be `d-1` for the positive roots of `U(d)`. -/
theorem normalized_gram_error_le_of_root_filtration
    (F A : ι → H →L[ℂ] H) (K : ℕ → Submodule ℂ H) (hK : Monotone K)
    (Ω : H) (hΩmem : Ω ∈ K 0) (hnorm : ⟪Ω, Ω⟫_ℂ = 1)
    (hadj : ∀ i x y, ⟪F i x, y⟫_ℂ = ⟪x, A i y⟫_ℂ)
    (hzero : ∀ i x, x ∈ K 0 → A i x = 0)
    (hlower : ∀ i r x, x ∈ K (r + 1) → A i x ∈ K r)
    (D L : ℕ)
    (hraise : ∀ i r x, x ∈ K r → F i x ∈ K (r + D))
    (ε : ℝ) (hε : 0 ≤ ε) (hεone : ε ≤ 1)
    (hcomm : ∀ i j r, r ≤ L * D → ∀ x ∈ K r,
      ‖commutatorDefect F A i j x‖ ≤ ε * ‖x‖)
    (u v : List ι) (hu : u.length ≤ L) (hv : v.length ≤ L) :
    ‖⟪normalizedWord F u Ω, normalizedWord F v Ω⟫_ℂ -
      (if u.Perm v then 1 else 0 : ℂ)‖ ≤
      (gramConstant L u.length : ℝ) *
        (Real.sqrt (((L * D : ℕ) : ℝ) + 1) * Real.sqrt 2) ^ (2 * L) * ε := by
  let G : ℕ → Submodule ℂ H := fun r => K (r * D)
  let M : ℝ := Real.sqrt ((((L * D : ℕ) : ℝ) + 1) * 2)
  have hM : 1 ≤ M := by
    apply Real.one_le_sqrt.mpr
    have : 0 ≤ ((L * D : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith
  have hG : Monotone G := fun a b hab => hK (Nat.mul_le_mul_right D hab)
  have hF : ∀ i r x, x ∈ G r → F i x ∈ G (r + 1) := by
    intro i r x hx
    simpa [G, Nat.add_mul] using hraise i (r * D) x hx
  have hA : ∀ i r x, x ∈ G r → A i x ∈ G (r + 1) := by
    intro i r x hx
    apply hG (Nat.le_succ r)
    exact annihilator_mem_same_cutoff (A i) K hK (hzero i) (hlower i) (r * D) x hx
  have hdiag : ∀ i r, r ≤ L * D → ∀ x ∈ K r,
      ‖A i (F i x) - F i (A i x) - x‖ ≤ 1 * ‖x‖ := by
    intro i r hr x hx
    have hh := hcomm i i r hr x hx
    simp only [commutatorDefect, if_true] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right hεone (norm_nonneg _))
  have hbound : ∀ i r, r ≤ L → ∀ x ∈ G r, ‖F i x‖ ≤ M * ‖x‖ := by
    intro i r hr x hx
    have hh := creator_norm_le_cutoff (F i) (A i) K (hadj i) (hzero i) (hlower i)
      (L * D) 1 (by norm_num) (hdiag i) (r * D) (Nat.mul_le_mul_right D hr) x hx
    simpa [M, show (1 : ℝ) + 1 = 2 by norm_num] using hh
  have hcommG : ∀ i j r, r ≤ L → ∀ x ∈ G r,
      ‖commutatorDefect F A i j x‖ ≤ ε * ‖x‖ := by
    intro i j r hr x hx
    exact hcomm i j (r * D) (Nat.mul_le_mul_right D hr) x hx
  have hh := normalized_gram_error_le_of_cutoff F A G hG Ω
    (by simpa [G] using hΩmem) hnorm (fun i => hzero i Ω hΩmem) hadj hF hA
    L M ε hM hε hbound hcommG u v hu hv
  simpa [M, Real.sqrt_mul (by positivity : (0:ℝ) ≤ ((L * D : ℕ) : ℝ) + 1)] using hh

end Cloning.PBW
