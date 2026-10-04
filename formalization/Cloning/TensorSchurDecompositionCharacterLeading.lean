import Cloning.TensorSchurDecompositionRadialEquation
import Cloning.TensorSchurDecompositionCharacterHighest
import Mathlib.RingTheory.MvPolynomial.MonomialOrder

/-! The leading coefficient of the actual Weyl-denominator character is one. -/
noncomputable section
open scoped BigOperators InnerProductSpace
namespace Cloning.TensorLie
open MvPolynomial
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
variable {n d : ℕ}

private theorem weightPrefix_succ (v : Fin d → ℤ) (i : Fin d) :
    weightPrefix v (i.val + 1) = weightPrefix v i.val + v i := by
  classical
  have he (j : Fin d) :
      (if j.val < i.val + 1 then v j else 0) =
        (if j.val < i.val then v j else 0) + (if j = i then v j else 0) := by
    by_cases hji : j = i
    · subst j; simp
    · have hv : j.val ≠ i.val := fun h => hji (Fin.ext h)
      by_cases hj : j.val < i.val <;> simp [hji, hj, show (j.val < i.val+1 ↔ j.val < i.val) by omega]
  simp only [weightPrefix, Finset.sum_filter, he, Finset.sum_add_distrib,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- Prefix dominance implies the lexicographic leading-monomial bound. -/
theorem lex_le_of_prefix_dominated (a b : Fin d →₀ ℕ)
    (h : ∀ R, weightPrefix (fun i => (a i : ℤ)) R ≤ weightPrefix (fun i => (b i : ℤ)) R) :
    MonomialOrder.lex.toSyn a ≤ MonomialOrder.lex.toSyn b := by
  rw [MonomialOrder.lex_le_iff]
  by_contra! hh
  obtain ⟨i, hi, hlt⟩ := Finsupp.Lex.lt_iff.mp hh
  have hp : weightPrefix (fun j => (a j : ℤ)) i.val =
      weightPrefix (fun j => (b j : ℤ)) i.val := by
    apply Finset.sum_congr rfl
    intro j hj
    have hj' : j < i := (Finset.mem_filter.mp hj).2
    exact congrArg (fun k : ℕ => (k : ℤ)) (hi j hj').symm
  have hb := h (i.val+1)
  rw [weightPrefix_succ, weightPrefix_succ, hp] at hb
  have hn : b i < a i := hlt
  omega

theorem physicalCharacterPolynomial_lex_degree_le
    (Ω : TensorRegister n (Fin d)) (mu : Fin d → ℕ)
    (hweight : ∀ a, collectiveGenerator n a a Ω = (mu a : ℂ) • Ω) :
    MonomialOrder.lex.toSyn (MonomialOrder.lex.degree (physicalCharacterPolynomial Ω)) ≤
      MonomialOrder.lex.toSyn (Finsupp.equivFunOnFinite.symm mu) := by
  apply MonomialOrder.degree_le_iff.mpr
  intro m hm
  apply lex_le_of_prefix_dominated
  intro R
  exact physicalCharacterPolynomial_support_dominated Ω mu hweight m (mem_support_iff.mp hm) R

private theorem lex_single_lt_of_lt (r : PositiveRoot d) :
    MonomialOrder.lex.toSyn (Finsupp.single r.val.2 1) <
      MonomialOrder.lex.toSyn (Finsupp.single r.val.1 1) := by
  rw [MonomialOrder.lex_lt_iff, Finsupp.Lex.lt_iff]
  refine ⟨r.val.1, ?_, ?_⟩
  · intro j hj
    simp [ne_of_lt hj, ne_of_lt (hj.trans r.property)]
  · simp [ne_of_lt r.property]

theorem weylDenominator_factor_lex_degree (r : PositiveRoot d) :
    MonomialOrder.lex.degree (X r.val.1 - X r.val.2 : MvPolynomial (Fin d) ℂ) =
      Finsupp.single r.val.1 1 := by
  rw [MonomialOrder.degree_sub_of_lt, MonomialOrder.degree_X]
  simpa only [MonomialOrder.degree_X] using lex_single_lt_of_lt r

theorem weylDenominator_factor_lex_coeff (r : PositiveRoot d) :
    MonomialOrder.lex.leadingCoeff (X r.val.1 - X r.val.2 : MvPolynomial (Fin d) ℂ) = 1 := by
  rw [MonomialOrder.leadingCoeff_sub_of_lt, MonomialOrder.leadingCoeff_X]
  simpa only [MonomialOrder.degree_X] using lex_single_lt_of_lt r

theorem sum_positiveRoot_single_left :
    (∑ r : PositiveRoot d, Finsupp.single r.val.1 (1 : ℕ)) =
      Finsupp.equivFunOnFinite.symm (@Cloning.WeylCharacter.staircase d) := by
  classical
  ext i
  simp only [Finsupp.finset_sum_apply, Finsupp.single_apply]
  rw [sum_positiveRoot (fun a (_ : Fin d) => if a = i then (1 : ℕ) else 0)]
  have he (a : Fin d) :
      (∑ b : Fin d, if a < b then (if a = i then 1 else 0) else 0) =
        if a = i then (∑ b : Fin d, if i < b then 1 else 0) else 0 := by
    by_cases h : a = i <;> simp [h]
  simp_rw [he]
  rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ i)]
  change (∑ b : Fin d, if i < b then 1 else 0) = Cloning.WeylCharacter.staircase i
  rw [← Finset.card_filter]
  have hs : Finset.univ.filter (fun b : Fin d => i < b) = Finset.Ioi i := by ext b; simp
  rw [hs, Fin.card_Ioi]
  rfl

theorem weylDenominator_lex_degree_le :
    MonomialOrder.lex.toSyn (MonomialOrder.lex.degree (weylDenominator d)) ≤
      MonomialOrder.lex.toSyn (Finsupp.equivFunOnFinite.symm (@Cloning.WeylCharacter.staircase d)) := by
  unfold weylDenominator
  have hh := MonomialOrder.lex.degree_prod_le
    (s := (Finset.univ : Finset (PositiveRoot d)))
    (P := fun r => (X r.val.1 - X r.val.2 : MvPolynomial (Fin d) ℂ))
  simpa only [weylDenominator_factor_lex_degree, sum_positiveRoot_single_left] using hh

theorem weylDenominator_staircase_coeff :
    coeff (Finsupp.equivFunOnFinite.symm (@Cloning.WeylCharacter.staircase d))
      (weylDenominator d) = 1 := by
  have hh := MonomialOrder.lex.coeff_prod_sum_degree
    (fun r : PositiveRoot d => (X r.val.1 - X r.val.2 : MvPolynomial (Fin d) ℂ)) Finset.univ
  simpa only [weylDenominator_factor_lex_degree, sum_positiveRoot_single_left,
    weylDenominator_factor_lex_coeff, Finset.prod_const_one, weylDenominator] using hh

/-- No lower physical weight or lower denominator monomial contributes to
this coefficient. Both actual leading coefficients are one. -/
theorem physicalCharacterPolynomial_denominator_highest_coeff
    (Ω : TensorRegister n (Fin d)) (mu : Fin d → ℕ) (hΩ : ‖Ω‖ = 1)
    (hweight : ∀ a, collectiveGenerator n a a Ω = (mu a : ℂ) • Ω)
    (hraise : ∀ a b, a < b → collectiveGenerator n a b Ω = 0) :
    coeff (Finsupp.equivFunOnFinite.symm (fun a => mu a + Cloning.WeylCharacter.staircase a))
      (weylDenominator d * physicalCharacterPolynomial Ω) = 1 := by
  have he : Finsupp.equivFunOnFinite.symm (fun a => mu a + Cloning.WeylCharacter.staircase a) =
      Finsupp.equivFunOnFinite.symm (@Cloning.WeylCharacter.staircase d) +
        Finsupp.equivFunOnFinite.symm mu := by ext a; simp [add_comm]
  rw [he, MonomialOrder.lex.coeff_mul_of_add_of_degree_le weylDenominator_lex_degree_le
    (physicalCharacterPolynomial_lex_degree_le Ω mu hweight),
    weylDenominator_staircase_coeff,
    physicalCharacterPolynomial_highest_coeff Ω mu hΩ hweight hraise, mul_one]

end Cloning.TensorLie
