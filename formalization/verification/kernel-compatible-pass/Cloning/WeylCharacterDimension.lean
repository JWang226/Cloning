import Cloning.WeylCharacterDimensionSpecialization

/-! The Weyl dimension product follows from the literal character alternant identity. -/
noncomputable section
open scoped BigOperators Classical
open Cloning.TensorLie
namespace Cloning.WeylCharacter
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

def dimensionProduct {d : ℕ} (μ : Fin d → ℕ) : ℝ :=
  ∏ r : PositiveRoot d,
    (((μ r.val.1 : ℝ) - μ r.val.2 + r.val.2.val - r.val.1.val) /
      ((r.val.2.val : ℝ) - r.val.1.val))

theorem shiftedHighestWeight_strictAnti {d : ℕ} (μ : Fin d → ℕ) (hμ : Antitone μ) :
    StrictAnti (fun i ↦ μ i + staircase i) := by
  intro i j hij
  have h1 := hμ hij.le
  have h2 := staircase_strictAnti d hij
  change μ j + staircase j < μ i + staircase i
  omega

theorem shiftedHighestWeight_gap {d : ℕ} (μ : Fin d → ℕ) (hμ : Antitone μ)
    (r : PositiveRoot d) :
    (((μ r.val.1 + staircase r.val.1 - (μ r.val.2 + staircase r.val.2) : ℕ) : ℂ) /
      ((r.val.2.val - r.val.1.val : ℕ) : ℂ)) =
    (((μ r.val.1 : ℝ) - μ r.val.2 + r.val.2.val - r.val.1.val) /
      ((r.val.2.val : ℝ) - r.val.1.val) : ℝ) := by
  have hgap := (shiftedHighestWeight_strictAnti μ hμ r.property).le
  have hij := Fin.lt_def.mp r.property
  have hi : r.val.1.val ≤ d - 1 := by have := r.val.1.isLt; omega
  have hj : r.val.2.val ≤ d - 1 := by have := r.val.2.isLt; omega
  rw [Nat.cast_sub hgap, Nat.cast_add, Nat.cast_add]
  simp only [staircase, Nat.cast_sub hi, Nat.cast_sub hj, Nat.cast_sub hij.le]
  push_cast
  congr 1
  ring

/-- Principal specialization at the identity gives the exact real Weyl product. -/
theorem eval_one_eq_dimensionProduct {d : ℕ}
    (χ : MvPolynomial (Fin d) ℂ) (μ : Fin d → ℕ) (hμ : Antitone μ)
    (hχ : χ * denominator d = alternant (fun i ↦ μ i + staircase i)) :
    MvPolynomial.eval (fun _ ↦ 1) χ = (dimensionProduct μ : ℂ) := by
  rw [eval_one_eq_root_gap_product χ _ (shiftedHighestWeight_strictAnti μ hμ) hχ]
  simp only [dimensionProduct, Complex.ofReal_prod]
  apply Finset.prod_congr rfl
  intro r _
  exact shiftedHighestWeight_gap μ hμ r

theorem dimensionProduct_eq_pairProduct {d : ℕ} (μ : Fin d → ℕ) :
    dimensionProduct μ = ∏ i : Fin d, ∏ j ∈ Finset.Ioi i,
      (((μ i : ℝ) - μ j + j.val - i.val) / ((j.val : ℝ) - i.val)) := by
  unfold dimensionProduct
  exact prod_positiveRoot (fun i j : Fin d ↦
    (((μ i : ℝ) - μ j + j.val - i.val) / ((j.val : ℝ) - i.val)))

theorem dimensionProduct_pos {d : ℕ} (μ : Fin d → ℕ) (hμ : Antitone μ) :
    0 < dimensionProduct μ := by
  apply Finset.prod_pos
  intro r _
  have hij : (r.val.1.val : ℝ) < r.val.2.val := by exact_mod_cast Fin.lt_def.mp r.property
  have hμij : (μ r.val.2 : ℝ) ≤ μ r.val.1 := by exact_mod_cast hμ r.property.le
  apply div_pos <;> linarith

end Cloning.WeylCharacter
