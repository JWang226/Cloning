import Cloning.HybridThermalWitness

/-! The sharp classical Gaussian factor controls the weighted mass of an
arbitrary positive hybrid density averaged over the input Gaussian shifts.
Fubini and all needed integrability conditions are proved in the actual L1 model. -/

noncomputable section
open scoped ComplexOrder InnerProductSpace Topology BigOperators
open MeasureTheory Filter Cloning.InfiniteTraceClass
namespace Cloning.Hybrid
set_option backward.isDefEq.respectTransparency false

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {k : ℕ}

theorem gaussian_shift_weighted_mass_le
    (R : PositiveField (H := H) (volume : Measure (Fin k → ℝ)))
    (a : Fin k → ℝ) (ha : ∀ i, 0 < a i) {g : ℝ} (hg : 1 ≤ g) :
    (∫ h : Fin k → ℝ, GaussianAffinity.productDensity a h *
      ∫ v : Fin k → ℝ, GaussianAffinity.productWitness a (fun i => a i / g)
        (fun i => v i + Real.sqrt g * h i) * ‖(R.value v).1‖) ≤
      Thermal.classicalBase g ^ ((k : ℝ) / 2) * R.mass := by
  let G := GaussianAffinity.productDensity a
  let χ := GaussianAffinity.productWitness a (fun i => a i / g)
  let B : (Fin k → ℝ) → ℝ := fun v => ‖(R.value v).1‖
  let F : (Fin k → ℝ) × (Fin k → ℝ) → ℝ := fun z =>
    G z.1 * B z.2 * χ (fun i => z.2 i + Real.sqrt g * z.1 i)
  have hg0 : 0 < g := lt_of_lt_of_le zero_lt_one hg
  have hχp (v : Fin k → ℝ) : 0 < χ v :=
    GaussianAffinity.productWitness_pos a _ ha (fun i => div_pos (ha i) hg0) v
  have hχb (v : Fin k → ℝ) : ‖χ v‖ ≤
      ∏ i, Real.sqrt (Real.sqrt (a i) / Real.sqrt (a i / g)) := by
    rw [Real.norm_eq_abs, abs_of_pos (hχp v)]
    apply GaussianAffinity.productWitness_le a _ ha (fun i => div_pos (ha i) hg0)
    intro i
    exact (div_le_iff₀ hg0).mpr (by nlinarith [ha i])
  have hχc : Continuous χ := GaussianAffinity.continuous_productWitness a _ ha
    (fun i => div_pos (ha i) hg0)
  have hF : Integrable F (volume.prod volume) := by
    apply ((GaussianAffinity.integrable_productDensity a ha).mul_prod R.integrable.norm).mul_bdd
      ((hχc.comp (by fun_prop)).aestronglyMeasurable)
    exact Eventually.of_forall fun z => hχb _
  have he (v : Fin k → ℝ) :
      (∫ h : Fin k → ℝ, F (h, v)) = B v *
        (∫ h : Fin k → ℝ, G h * χ (fun i => v i + Real.sqrt g * h i)) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Eventually.of_forall fun h => by dsimp [F]; ring
  calc
    _ = ∫ h : Fin k → ℝ, ∫ v : Fin k → ℝ, F (h, v) := by
      apply integral_congr_ae
      exact Eventually.of_forall fun h => by
        dsimp only
        rw [← integral_const_mul]
        apply integral_congr_ae
        exact Eventually.of_forall fun v => by dsimp [F, G, B, χ]; ring
    _ = ∫ v : Fin k → ℝ, ∫ h : Fin k → ℝ, F (h, v) := integral_integral_swap hF
    _ ≤ ∫ v : Fin k → ℝ, B v * Thermal.classicalBase g ^ ((k : ℝ) / 2) := by
      apply integral_mono hF.integral_prod_right (R.integrable.norm.mul_const _)
      intro v
      dsimp only
      rw [he]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      simpa only [Fintype.card_fin] using
        GaussianAffinity.integral_product_translated_witness_le a ha hg v
    _ = _ := by rw [integral_mul_const]; exact mul_comm _ _

end Cloning.Hybrid
