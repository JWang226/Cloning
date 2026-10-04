import Cloning.WeylCharacterAlternantPolynomial
import Cloning.TensorCyclicFiltration
import Mathlib.Data.Fin.Rev

/-! The physical positive-root denominator and its exact Euler spectrum. -/
noncomputable section
open scoped BigOperators Classical
open MvPolynomial Cloning.TensorLie
namespace Cloning.WeylCharacter
set_option backward.isDefEq.respectTransparency false

theorem prod_positiveRoot {d : ℕ} {M : Type*} [CommMonoid M] (f : Fin d → Fin d → M) :
    (∏ r : PositiveRoot d, f r.val.1 r.val.2) =
      ∏ i : Fin d, ∏ j ∈ Finset.Ioi i, f i j := by
  rw [← Finset.prod_subtype (Finset.univ.filter (fun r : Fin d × Fin d ↦ r.1 < r.2))
    (by simp) (fun r ↦ f r.1 r.2)]
  rw [Finset.prod_filter, Fintype.prod_prod_type]
  apply Finset.prod_congr rfl
  intro i hi
  rw [← Finset.prod_filter]
  congr 1
  ext j
  simp

def denominator (d : ℕ) : MvPolynomial (Fin d) ℂ :=
  ∏ r : PositiveRoot d, (X r.val.1 - X r.val.2)

theorem denominator_eq_scalar_vandermonde (d : ℕ) :
    denominator d = ((-1 : ℂ)^Fintype.card (PositiveRoot d)) •
      (Matrix.vandermonde (fun i : Fin d ↦ (X i : MvPolynomial (Fin d) ℂ))).det := by
  rw [Matrix.det_vandermonde, ← prod_positiveRoot]
  unfold denominator
  calc
    _ = ∏ r : PositiveRoot d, (-1 : ℂ) • (X r.val.2 - X r.val.1) := by
      apply Finset.prod_congr rfl
      intro r hr
      simp
    _ = _ := by rw [Finset.prod_smul]; simp

def staircase {d : ℕ} (i : Fin d) : ℕ := d-1-i.val

theorem staircase_strictAnti (d : ℕ) : StrictAnti (@staircase d) := by
  intro i j hij
  have hi := i.isLt
  have hj := j.isLt
  simp only [staircase, Fin.lt_def] at *
  omega

theorem sum_staircase_sq (d : ℕ) :
    (∑ i : Fin d, (staircase i : ℂ)^2) = ∑ i : Fin d, (i.val : ℂ)^2 := by
  simpa only [staircase, Fin.revPerm_apply, Fin.val_rev, Nat.sub_sub, Nat.add_comm] using
    (Equiv.sum_comp (Fin.revPerm (n := d)) (fun i : Fin d ↦ (i.val : ℂ)^2))

theorem eulerSquares_denominator (d : ℕ) :
    eulerSquares (denominator d) = (∑ i : Fin d, (staircase i : ℂ)^2) • denominator d := by
  rw [denominator_eq_scalar_vandermonde, map_smul, eulerSquares_vandermonde,
    sum_staircase_sq, smul_comm]

theorem denominator_ne_zero (d : ℕ) : denominator d ≠ 0 := by
  unfold denominator
  apply Finset.prod_ne_zero_iff.mpr
  intro r hr
  apply sub_ne_zero.mpr
  exact (MvPolynomial.X_injective (R := ℂ)).ne (ne_of_lt r.property)

end Cloning.WeylCharacter
