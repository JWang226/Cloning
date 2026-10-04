import Cloning.WeylCharacterAlternantDenominator

/-! Dominance and the actual Euler spectrum force support on a single Weyl
orbit. Alternation then determines the polynomial from one coefficient. -/
noncomputable section
open scoped BigOperators Classical
open MvPolynomial
namespace Cloning.WeylCharacter
set_option backward.isDefEq.respectTransparency false

theorem support_on_orbit_of_eigen_dominance {d : ℕ}
    (P : MvPolynomial (Fin d) ℂ) (a : Fin d → ℕ) (ha : StrictAnti a)
    (heigen : eulerSquares P = (∑ i, (a i : ℂ)^2) • P)
    (hdom : ∀ m, coeff m P ≠ 0 → SubsetDominatedBy (fun i ↦ (m i : ℝ)) (fun i ↦ (a i : ℝ)))
    (m : Fin d →₀ ℕ) (hm : coeff m P ≠ 0) :
    ∃ σ : Equiv.Perm (Fin d), m = exponentOf (a ∘ σ) := by
  let σ : Equiv.Perm (Fin d) := Tuple.sort (α := OrderDual ℕ) (fun i : Fin d ↦ (m i : OrderDual ℕ))
  have hb : Antitone (fun i ↦ m (σ i)) := by
    intro i j hij
    exact (Tuple.monotone_sort (α := OrderDual ℕ) (fun i : Fin d ↦ (m i : OrderDual ℕ))) hij
  have hbr : Antitone (fun i ↦ (m (σ i) : ℝ)) := by
    intro i j hij
    change (m (σ j) : ℝ) ≤ (m (σ i) : ℝ)
    exact_mod_cast hb hij
  have har : StrictAnti (fun i ↦ (a i : ℝ)) := by
    intro i j hij
    change (a j : ℝ) < (a i : ℝ)
    exact_mod_cast ha hij
  have hsq := support_eulerSquares_eigenvalue P _ heigen m hm
  have hsqN : (∑ i, m i ^ 2) = ∑ i, a i ^ 2 := by exact_mod_cast hsq
  have hsqR : (∑ i, (m i : ℝ)^2) = ∑ i, (a i : ℝ)^2 := by exact_mod_cast hsqN
  have hperm : (∑ i, (m (σ i) : ℝ)^2) = ∑ i, (m i : ℝ)^2 :=
    Equiv.sum_comp σ (fun i ↦ (m i : ℝ)^2)
  have heq := fin_dominant_eq_of_sum_squares
    (fun i ↦ (a i : ℝ)) (fun i ↦ (m (σ i) : ℝ)) har hbr
    ((subsetDominatedBy_iff_permutations _ _).mp (hdom m hm) σ)
    (by rw [hperm, hsqR])
  refine ⟨σ.symm, ?_⟩
  ext i
  have hi := congrFun heq (σ.symm i)
  simpa only [Equiv.apply_symm_apply, exponentOf_apply, Function.comp_apply,
    Nat.cast_inj] using hi.symm

def Alternating {d : ℕ} (P : MvPolynomial (Fin d) ℂ) : Prop :=
  ∀ σ : Equiv.Perm (Fin d), rename σ P = ((Equiv.Perm.sign σ : ℤ) : ℂ) • P

theorem sign_complex_ne_zero {d : ℕ} (σ : Equiv.Perm (Fin d)) :
    ((Equiv.Perm.sign σ : ℤ) : ℂ) ≠ 0 := by
  exact_mod_cast (Equiv.Perm.sign σ).ne_zero

theorem alternating_coeff_permuted {d : ℕ} (P : MvPolynomial (Fin d) ℂ)
    (hP : Alternating P) (σ : Equiv.Perm (Fin d)) (m : Fin d →₀ ℕ) :
    coeff m P = ((Equiv.Perm.sign σ : ℤ) : ℂ) * coeff (m.mapDomain σ) P := by
  have h := congrArg (coeff (m.mapDomain σ)) (hP σ)
  rw [coeff_rename_mapDomain σ σ.injective, coeff_smul, smul_eq_mul] at h
  exact h

theorem exponentOf_comp_eq_mapDomain {d : ℕ} (a : Fin d → ℕ) (σ : Equiv.Perm (Fin d)) :
    exponentOf (a ∘ σ) = (exponentOf a).mapDomain σ.symm := by
  ext i
  simp [Finsupp.mapDomain_equiv_apply, exponentOf_apply]

theorem alternating_eq_of_orbit_and_top {d : ℕ} (P Q : MvPolynomial (Fin d) ℂ)
    (a : Fin d → ℕ) (hP : Alternating P) (hQ : Alternating Q)
    (hsP : ∀ m, coeff m P ≠ 0 → ∃ σ : Equiv.Perm (Fin d), m = exponentOf (a ∘ σ))
    (hsQ : ∀ m, coeff m Q ≠ 0 → ∃ σ : Equiv.Perm (Fin d), m = exponentOf (a ∘ σ))
    (htop : coeff (exponentOf a) P = coeff (exponentOf a) Q) : P = Q := by
  apply MvPolynomial.ext
  intro m
  by_cases hs : ∃ σ : Equiv.Perm (Fin d), m = exponentOf (a ∘ σ)
  · obtain ⟨σ, rfl⟩ := hs
    rw [exponentOf_comp_eq_mapDomain]
    apply mul_left_cancel₀ (sign_complex_ne_zero σ.symm)
    rw [← alternating_coeff_permuted P hP, ← alternating_coeff_permuted Q hQ, htop]
  · have hp : coeff m P = 0 := by by_contra hp; exact hs (hsP m hp)
    have hq : coeff m Q = 0 := by by_contra hq; exact hs (hsQ m hq)
    rw [hp, hq]

theorem alternant_alternating {d : ℕ} (a : Fin d → ℕ) : Alternating (alternant a) := by
  intro σ
  rw [alternant, AlgHom.map_det]
  have hmat : (fun i j : Fin d ↦ rename σ (X i ^ a j : MvPolynomial (Fin d) ℂ)) =
      (show Matrix (Fin d) (Fin d) (MvPolynomial (Fin d) ℂ) from fun i j ↦ X i ^ a j).submatrix σ
        id := by
    ext i j
    simp [Matrix.submatrix_apply]
  change Matrix.det (fun i j ↦ rename σ (X i ^ a j)) = _
  rw [hmat, Matrix.det_permute]
  simp [Algebra.smul_def]

theorem alternant_support_orbit {d : ℕ} (a : Fin d → ℕ) (m : Fin d →₀ ℕ)
    (hm : coeff m (alternant a) ≠ 0) :
    ∃ σ : Equiv.Perm (Fin d), m = exponentOf (a ∘ σ) := by
  by_contra! hh
  apply hm
  rw [alternant_expansion, coeff_sum]
  apply Finset.sum_eq_zero
  intro σ hσ
  simp [coeff_smul, coeff_monomial, Ne.symm (hh σ.symm)]

theorem alternant_top_coeff {d : ℕ} (a : Fin d → ℕ) (ha : Function.Injective a) :
    coeff (exponentOf a) (alternant a) = 1 := by
  rw [alternant_expansion, coeff_sum]
  have hneq (σ : Equiv.Perm (Fin d)) (hσ : σ ≠ 1) :
      exponentOf (a ∘ σ.symm) ≠ exponentOf a := by
    intro he
    apply hσ
    apply Equiv.ext
    intro i
    have hi := congrArg (fun m : Fin d →₀ ℕ ↦ m (σ i)) he
    simp only [exponentOf_apply, Function.comp_apply, Equiv.symm_apply_apply] at hi
    exact (ha hi).symm
  rw [Finset.sum_eq_single 1]
  · simp
  · intro σ hσ hσ1
    simp [coeff_smul, coeff_monomial, hneq σ hσ1]
  · simp

/-- A finite spectral uniqueness theorem, with all dominance, eigenvalue,
alternation and top coefficient hypotheses explicit. -/
theorem eq_alternant_of_spectral_data {d : ℕ} (P : MvPolynomial (Fin d) ℂ)
    (a : Fin d → ℕ) (ha : StrictAnti a) (hP : Alternating P)
    (heigen : eulerSquares P = (∑ i, (a i : ℂ)^2) • P)
    (hdom : ∀ m, coeff m P ≠ 0 → SubsetDominatedBy (fun i ↦ (m i : ℝ)) (fun i ↦ (a i : ℝ)))
    (htop : coeff (exponentOf a) P = 1) : P = alternant a := by
  apply alternating_eq_of_orbit_and_top P (alternant a) a hP (alternant_alternating a)
    (support_on_orbit_of_eigen_dominance P a ha heigen hdom) (alternant_support_orbit a)
  rw [htop, alternant_top_coeff a ha.injective]

end Cloning.WeylCharacter
