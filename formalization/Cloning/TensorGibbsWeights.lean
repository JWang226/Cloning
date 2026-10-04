import Cloning.TensorGibbsState
import Cloning.TensorPBWWeight

/-! Exact Boltzmann weights of physical lowering words. These identities
connect the literal sector density to occupation probabilities and the root
height, before any asymptotic basis or tail estimate is invoked. -/
noncomputable section
open scoped BigOperators InnerProductSpace ComplexOrder
namespace Cloning.TensorLie
open Cloning.PCT Cloning.InfiniteTraceClass
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {n d : ℕ}

def rootBoltzmann (p : Fin d → ℝ) (r : PositiveRoot d) : ℝ :=
  p r.val.2 / p r.val.1

def wordBoltzmann (p : Fin d → ℝ) (w : List (PositiveRoot d)) : ℝ :=
  (w.map (rootBoltzmann p)).prod

theorem prod_zpow_root_weight (p : Fin d → ℝ) (hp : ∀ a, p a ≠ 0)
    (r : PositiveRoot d) : (∏ a, p a ^ r.weight a) = rootBoltzmann p r := by
  simp only [PositiveRoot.weight, zpow_sub₀ (hp _), Finset.prod_div_distrib]
  simp [rootBoltzmann]

theorem prod_zpow_loweringWeight (p : Fin d → ℝ) (hp : ∀ a, p a ≠ 0)
    (w : List (PositiveRoot d)) :
    (∏ a, p a ^ loweringWeight w a) = wordBoltzmann p w := by
  induction w with
  | nil => simp [wordBoltzmann]
  | cons r w ih =>
    simp only [loweringWeight_cons, Pi.add_apply, zpow_add₀ (hp _),
      Finset.prod_mul_distrib, prod_zpow_root_weight p hp, ih]
    rfl

theorem shiftedWeight_boltzmann (p : Fin d → ℝ) (hp : ∀ a, p a ≠ 0)
    (mu : Fin d → ℕ) (w : List (PositiveRoot d)) :
    (∏ a, p a ^ ((mu a : ℤ) + loweringWeight w a)) =
      (∏ a, p a ^ mu a) * wordBoltzmann p w := by
  simp only [zpow_add₀ (hp _), zpow_natCast, Finset.prod_mul_distrib,
    prod_zpow_loweringWeight p hp]

theorem wordBoltzmann_pos (p : Fin d → ℝ) (hp : ∀ a, 0 < p a)
    (w : List (PositiveRoot d)) : 0 < wordBoltzmann p w := by
  induction w with
  | nil => simp [wordBoltzmann]
  | cons r w ih =>
    exact mul_pos (div_pos (hp _) (hp _)) ih

/-- Height decay is a derived product inequality once each finite physical
root ratio is bounded. No state-tail or operator approximation is an input. -/
theorem wordBoltzmann_le_pow_height (p : Fin d → ℝ) (hp : ∀ a, 0 ≤ p a)
    (θ : ℝ) (hθ : 0 ≤ θ)
    (hroot : ∀ r : PositiveRoot d, rootBoltzmann p r ≤ θ ^ r.height)
    (w : List (PositiveRoot d)) : wordBoltzmann p w ≤ θ ^ loweringHeight w := by
  induction w with
  | nil => simp [wordBoltzmann, loweringHeight]
  | cons r w ih =>
    change rootBoltzmann p r * wordBoltzmann p w ≤ θ ^ (r.height + loweringHeight w)
    rw [pow_add]
    exact mul_le_mul (hroot r) ih
      (by unfold wordBoltzmann; apply List.prod_nonneg; intro x hx
          obtain ⟨a, _, rfl⟩ := List.mem_map.mp hx
          exact div_nonneg (hp _) (hp _))
      (pow_nonneg hθ _)

theorem tensorOperator_diagonal_loweringWord
    (Ω : TensorRegister n (Fin d)) (mu : Fin d → ℕ)
    (hweight : ∀ a, collectiveGenerator n a a Ω = (mu a : ℂ) • Ω)
    (p : Fin d → ℝ) (hp : ∀ a, 0 < p a) (w : List (PositiveRoot d)) :
    tensorOperator n (Matrix.diagonal (fun a => (p a : ℂ))) (loweringWord Ω w) =
      (((∏ a, p a ^ mu a) * wordBoltzmann p w : ℝ) : ℂ) • loweringWord Ω w := by
  have h := tensorOperator_diagonal_weight (fun a => (p a : ℂ)) (loweringWord Ω w)
    (fun a => (mu a : ℤ) + loweringWeight w a) (fun a => by
      simpa only [Int.cast_add, Int.cast_natCast] using
        cartan_loweringWord Ω (fun a => (mu a : ℂ)) hweight w a)
  have hc : (∏ a, (p a : ℂ) ^ ((mu a : ℤ) + loweringWeight w a)) =
      (((∏ a, p a ^ mu a) * wordBoltzmann p w : ℝ) : ℂ) := by
    rw [← shiftedWeight_boltzmann p (fun a => (hp a).ne') mu w]
    simp only [Complex.ofReal_prod, Complex.ofReal_zpow]
  rw [hc] at h
  exact h

theorem sectorGibbsOperator_loweringWord
    (Ω : TensorRegister n (Fin d)) (mu : Fin d → ℕ)
    (hweight : ∀ a, collectiveGenerator n a a Ω = (mu a : ℂ) • Ω)
    (hraise : ∀ a b, a < b → collectiveGenerator n a b Ω = 0)
    (p : Fin d → ℝ) (hp : ∀ a, 0 < p a) (w : List (PositiveRoot d)) :
    sectorGibbsOperator Ω mu hweight hraise p
      ⟨loweringWord Ω w, loweringWord_mem_cyclicSector Ω w⟩ =
      (((∏ a, p a ^ mu a) * wordBoltzmann p w : ℝ) : ℂ) •
        (⟨loweringWord Ω w, loweringWord_mem_cyclicSector Ω w⟩ : cyclicSector Ω) := by
  apply Subtype.ext
  exact tensorOperator_diagonal_loweringWord Ω mu hweight p hp w

end Cloning.TensorLie
