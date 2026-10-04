import Cloning.TensorSchurDecompositionRadialTrace

/-! Finite Weyl-denominator calculus for the actual radial character equation. -/
noncomputable section
open scoped BigOperators InnerProductSpace
namespace Cloning.TensorLie
open Cloning.PCT MvPolynomial
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
variable {n d : ℕ}

def weylDenominator (d : ℕ) : MvPolynomial (Fin d) ℂ :=
  ∏ r : PositiveRoot d, (X r.val.1 - X r.val.2)

def weylDenominatorErase (r : PositiveRoot d) : MvPolynomial (Fin d) ℂ :=
  ∏ s ∈ Finset.univ.erase r, (X s.val.1 - X s.val.2)

theorem weylDenominator_factor (r : PositiveRoot d) :
    (X r.val.1 - X r.val.2) * weylDenominatorErase r = weylDenominator d := by
  exact Finset.mul_prod_erase Finset.univ
    (fun s : PositiveRoot d => (X s.val.1 - X s.val.2 : MvPolynomial (Fin d) ℂ))
    (Finset.mem_univ r)

/-- Product rule in a form retaining the exact missing-factor product. -/
theorem pderiv_finset_prod {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (f : ι → MvPolynomial (Fin d) ℂ) (a : Fin d) :
    pderiv a (∏ i ∈ s, f i) = ∑ i ∈ s, pderiv a (f i) * ∏ j ∈ s.erase i, f j := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, pderiv_mul, ih, Finset.sum_insert hi,
      Finset.erase_insert hi]
    congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    have hji : j ≠ i := ne_of_mem_of_not_mem hj hi
    rw [Finset.erase_insert_of_ne hji.symm, Finset.prod_insert (by simp [hi])]
    ring

theorem pderiv_weylDenominator (a : Fin d) :
    pderiv a (weylDenominator d) = ∑ r : PositiveRoot d,
      ((if r.val.1 = a then 1 else 0) - (if r.val.2 = a then 1 else 0)) *
        weylDenominatorErase r := by
  rw [weylDenominator, pderiv_finset_prod]
  simp only [map_sub, pderiv_X, Pi.single_apply, weylDenominatorErase]

/-- The derivative cross term grouped by positive roots. -/
theorem weylDenominator_euler_cross (f : MvPolynomial (Fin d) ℂ) :
    (∑ a : Fin d, (X a * pderiv a (weylDenominator d)) * (X a * pderiv a f)) =
      ∑ r : PositiveRoot d, weylDenominatorErase r *
        (X r.val.1 * (X r.val.1 * pderiv r.val.1 f) -
          X r.val.2 * (X r.val.2 * pderiv r.val.2 f)) := by
  simp_rw [pderiv_weylDenominator, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  simp only [sub_mul, mul_sub, ite_mul, mul_ite, one_mul, zero_mul, mul_zero,
    Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  ring

end Cloning.TensorLie
