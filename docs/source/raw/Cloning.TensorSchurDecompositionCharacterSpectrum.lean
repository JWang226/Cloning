import Cloning.TensorSchurDecompositionRadialEquation

/-! The physical Casimir eigenvalue is the squared shifted highest weight. -/
noncomputable section
open scoped BigOperators InnerProductSpace
namespace Cloning.TensorLie
open MvPolynomial
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
variable {n d : ℕ}

theorem sum_positiveRoot_left (f : Fin d → ℂ) :
    (∑ r : PositiveRoot d, f r.val.1) =
      ∑ a : Fin d, (Cloning.WeylCharacter.staircase a : ℂ) * f a := by
  classical
  rw [sum_positiveRoot (fun a (_ : Fin d) => f a)]
  apply Finset.sum_congr rfl
  intro a _
  rw [← Finset.sum_filter]
  have hs : Finset.univ.filter (fun b : Fin d => a < b) = Finset.Ioi a := by ext b; simp
  rw [hs, Finset.sum_const, nsmul_eq_mul, Fin.card_Ioi]
  rfl

theorem sum_positiveRoot_endpoints_complex (f : Fin d → ℂ) :
    (∑ r : PositiveRoot d, (f r.val.1 + f r.val.2)) =
      ((d : ℂ) - 1) * (∑ a, f a) := by
  have hs := sum_matrix_eq_diagonal_add_roots (fun a (_ : Fin d) => f a)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    ← Finset.mul_sum] at hs
  linear_combination hs.symm

theorem casimir_shifted_square (mu : Fin d → ℂ) :
    (∑ a : Fin d, (Cloning.WeylCharacter.staircase a : ℂ)^2) +
      casimirEigenvalue mu + ((d : ℂ) - 1) * (∑ a, mu a) =
      ∑ a : Fin d, (mu a + Cloning.WeylCharacter.staircase a)^2 := by
  have hp : (∑ r : PositiveRoot d, (mu r.val.1 - mu r.val.2)) +
      ((d : ℂ) - 1) * (∑ a, mu a) =
        2 * ∑ a : Fin d, (Cloning.WeylCharacter.staircase a : ℂ) * mu a := by
    rw [← sum_positiveRoot_endpoints_complex, ← sum_positiveRoot_left,
      ← Finset.sum_add_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    ring
  unfold casimirEigenvalue
  rw [← sum_positiveRoot (fun a b => mu a - mu b)]
  calc
    _ = (∑ a : Fin d, (Cloning.WeylCharacter.staircase a : ℂ)^2) +
        (∑ a, mu a * mu a) +
        2 * ∑ a : Fin d, (Cloning.WeylCharacter.staircase a : ℂ) * mu a := by
      linear_combination hp
    _ = _ := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro a _
      ring

/-- Exact physical Euler spectrum in the usual shifted-partition form. -/
theorem physicalCharacterPolynomial_eulerSquares_shifted
    (Ω : TensorRegister n (Fin d)) (mu : Fin d → ℕ)
    (hsum : ∑ a, mu a = n)
    (hweight : ∀ a, collectiveGenerator n a a Ω = (mu a : ℂ) • Ω)
    (hraise : ∀ a b, a < b → collectiveGenerator n a b Ω = 0) :
    Cloning.WeylCharacter.eulerSquares (weylDenominator d * physicalCharacterPolynomial Ω) =
      (∑ a : Fin d, ((mu a + Cloning.WeylCharacter.staircase a : ℕ) : ℂ)^2) •
        (weylDenominator d * physicalCharacterPolynomial Ω) := by
  have hn : (∑ a, (mu a : ℂ)) = n := by exact_mod_cast hsum
  rw [physicalCharacterPolynomial_eulerSquares Ω (fun a => (mu a : ℂ)) hweight hraise,
    ← hn, casimir_shifted_square]
  simp only [Nat.cast_add]

end Cloning.TensorLie
