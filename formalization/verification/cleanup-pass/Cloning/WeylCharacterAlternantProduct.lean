import Cloning.WeylCharacterAlternantUniqueness

/-! Symmetry and physical highest-weight dominance are preserved, with the
staircase shift, on multiplication by the actual root denominator. -/
noncomputable section
open scoped BigOperators Classical Pointwise
open MvPolynomial Cloning.TensorLie
namespace Cloning.WeylCharacter
set_option backward.isDefEq.respectTransparency false

theorem alternating_smul {d : ℕ} (P : MvPolynomial (Fin d) ℂ)
    (hP : Alternating P) (c : ℂ) : Alternating (c • P) := by
  intro σ
  rw [map_smul, hP σ, smul_comm]

theorem denominator_alternating (d : ℕ) : Alternating (denominator d) := by
  rw [denominator_eq_scalar_vandermonde]
  exact alternating_smul (alternant (fun i : Fin d ↦ i.val))
    (alternant_alternating _) _

theorem denominator_mul_alternating {d : ℕ} (P : MvPolynomial (Fin d) ℂ)
    (hP : ∀ σ : Equiv.Perm (Fin d), rename σ P = P) :
    Alternating (denominator d * P) := by
  intro σ
  rw [map_mul, denominator_alternating d σ, hP σ, smul_mul_assoc]

theorem denominator_support_orbit {d : ℕ} (m : Fin d →₀ ℕ)
    (hm : coeff m (denominator d) ≠ 0) :
    ∃ σ : Equiv.Perm (Fin d), m = exponentOf (staircase ∘ σ) := by
  rw [denominator_eq_scalar_vandermonde, coeff_smul, smul_eq_mul] at hm
  have ha : coeff m (alternant (fun i : Fin d ↦ i.val)) ≠ 0 := (mul_ne_zero_iff.mp hm).2
  obtain ⟨σ, hσ⟩ := alternant_support_orbit (fun i : Fin d ↦ i.val) m ha
  refine ⟨σ.trans Fin.revPerm, ?_⟩
  rw [hσ]
  ext i
  simp only [exponentOf_apply, Function.comp_apply, Equiv.trans_apply,
    Fin.revPerm_apply, staircase, Fin.val_rev]
  have hi := (σ i).isLt
  omega

theorem symmetric_subset_dominance {d : ℕ} (P : MvPolynomial (Fin d) ℂ)
    (a : Fin d → ℝ) (hsym : ∀ σ : Equiv.Perm (Fin d), rename σ P = P)
    (hdom : ∀ m, coeff m P ≠ 0 → DominatedBy (fun i ↦ (m i : ℝ)) a)
    (m : Fin d →₀ ℕ) (hm : coeff m P ≠ 0) :
    SubsetDominatedBy (fun i ↦ (m i : ℝ)) a := by
  apply subsetDominatedBy_of_permutations
  intro σ
  have hcoeff : coeff (m.mapDomain σ.symm) P = coeff m P := by
    conv_lhs => rw [← hsym σ.symm, coeff_rename_mapDomain σ.symm σ.symm.injective]
  have h := hdom (m.mapDomain σ.symm) (by rw [hcoeff]; exact hm)
  simpa only [Finsupp.mapDomain_equiv_apply, Equiv.symm_symm, Function.comp_apply] using h

theorem denominator_mul_support_dominance {d : ℕ} (P : MvPolynomial (Fin d) ℂ)
    (a : Fin d → ℕ)
    (hdom : ∀ m, coeff m P ≠ 0 → SubsetDominatedBy (fun i ↦ (m i : ℝ)) (fun i ↦ (a i : ℝ)))
    (m : Fin d →₀ ℕ) (hm : coeff m (denominator d * P) ≠ 0) :
    SubsetDominatedBy (fun i ↦ (m i : ℝ)) (fun i ↦ ((a i + staircase i : ℕ) : ℝ)) := by
  have hs := MvPolynomial.support_mul (denominator d) P (MvPolynomial.mem_support_iff.mpr hm)
  obtain ⟨u, hu, v, hv, rfl⟩ := Finset.mem_add.mp hs
  obtain ⟨σ, rfl⟩ := denominator_support_orbit u (MvPolynomial.mem_support_iff.mp hu)
  have hsδ : Antitone (fun i : Fin d ↦ (staircase i : ℝ)) := by
    intro i j hij
    change (staircase j : ℝ) ≤ (staircase i : ℝ)
    exact_mod_cast (staircase_strictAnti d).antitone hij
  have h := subsetDominatedBy_add (hdom v (MvPolynomial.mem_support_iff.mp hv)) hsδ σ
  simpa only [Finsupp.add_apply, exponentOf_apply, Function.comp_apply, Nat.cast_add, add_comm] using h

end Cloning.WeylCharacter
