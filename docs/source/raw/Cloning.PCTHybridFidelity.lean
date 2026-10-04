import Cloning.HybridGaussianAttainmentFidelity
import Cloning.MixedGaussianConverse
import Cloning.Main

/-! The root fidelity of the literal PCT Gaussian comparison field.
This computes an actual positive L1 state's fidelity. Identification with the
physical PCT output still requires the joint mixture and mixed LAN arguments. -/
noncomputable section
open scoped ComplexOrder InnerProductSpace Topology BigOperators
open MeasureTheory Cloning.InfiniteTraceClass Cloning.InfiniteFidelity
open Cloning.MultimodeCoherent Cloning.InfiniteDiagonalFidelity
namespace Cloning.Hybrid
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {k s : ℕ}

lemma pct_thermal_nonneg {g q : ℝ} (hg : 1 < g) (hq : 0 ≤ q) :
    0 ≤ Thermal.pct g q := by
  apply div_nonneg _ (Thermal.pct_denominator_pos hg hq).le
  exact add_nonneg (sub_nonneg.mpr hg.le) (mul_nonneg (zero_lt_one.trans hg).le hq)

/-- The literal PCT comparison field: covariance broadened by `2 g - 1`
and the PCT geometric thermal ratios. -/
def pctGaussianThermalField
    (a : Fin k → ℝ) (ha : ∀ i, 0 < a i) (g : ℝ) (hg : 1 < g)
    (q : Fin s → ℝ) (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i < 1) :
    PositiveField (H := Fock s) (volume : Measure (Fin k → ℝ)) :=
  gaussianThermalField (fun i => a i / (2 * g - 1))
    (fun i => div_pos (ha i) (by linarith))
    (fun i => Thermal.pct g (q i))
    (fun i => pct_thermal_nonneg hg (hq0 i))
    (fun i => Thermal.pct_lt_one hg (hq0 i) (hq1 i))

def pctGaussianThermalPositive
    (a : Fin k → ℝ) (ha : ∀ i, 0 < a i) (g : ℝ) (hg : 1 < g)
    (q : Fin s → ℝ) (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i < 1) : HybridPositive k s :=
  (pctGaussianThermalField a ha g hg q hq0 hq1).toPositiveL1

theorem norm_pctGaussianThermalPositive
    (a : Fin k → ℝ) (ha : ∀ i, 0 < a i) (g : ℝ) (hg : 1 < g)
    (q : Fin s → ℝ) (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i < 1) :
    ‖(pctGaussianThermalPositive a ha g hg q hq0 hq1).1‖ = 1 :=
  Cloning.MixedLANTransfer.norm_gaussianThermalPositive _ _ _ _ _

/-- Exact field root fidelity, including seed vacuum modes and empty products. -/
theorem pctGaussianThermalField_rootFidelity
    (a : Fin k → ℝ) (ha : ∀ i, 0 < a i) (g : ℝ) (hg : 1 < g)
    (q : Fin s → ℝ) (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i < 1) :
    (pctGaussianThermalField a ha g hg q hq0 hq1).rootFidelity
      (gaussianThermalField a ha q hq0 hq1) =
      Thermal.classicalBase (2 * g - 1) ^ ((k : ℝ) / 2) *
        ∏ i, Thermal.fidelity (q i) (Thermal.pct g (q i)) := by
  rw [PositiveField.rootFidelity_comm]
  unfold pctGaussianThermalField gaussianThermalField
  rw [PositiveField.rootFidelity_product, stateFidelity_productGeometric]
  have hc := GaussianAffinity.integral_product_dilation a ha (by linarith : 0 < 2 * g - 1)
  simpa only [Fintype.card_fin] using congrArg
    (fun x => x * ∏ i, Thermal.fidelity (q i) (Thermal.pct g (q i))) hc

/-- The same value for genuine positive L1 equivalence classes. -/
theorem pctGaussianThermalPositive_rootFidelity
    (a : Fin k → ℝ) (ha : ∀ i, 0 < a i) (g : ℝ) (hg : 1 < g)
    (q : Fin s → ℝ) (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i < 1) :
    (pctGaussianThermalPositive a ha g hg q hq0 hq1).rootFidelity
      (gaussianThermalPositive a ha q hq0 hq1) =
      Thermal.classicalBase (2 * g - 1) ^ ((k : ℝ) / 2) *
        ∏ i, Thermal.fidelity (q i) (Thermal.pct g (q i)) := by
  change (pctGaussianThermalField a ha g hg q hq0 hq1).toPositiveL1.rootFidelity
    (gaussianThermalField a ha q hq0 hq1).toPositiveL1 = _
  rw [PositiveField.toPositiveL1_rootFidelity]
  exact pctGaussianThermalField_rootFidelity a ha g hg q hq0 hq1

/-- For a physical simple spectrum, the actual product-field fidelity is
exactly the manuscript's PCT scalar. No physical LAN limit is asserted here. -/
theorem pctGaussianThermalPositive_rootFidelity_eq_pctValue
    (a : Fin k → ℝ) (ha : ∀ i, 0 < a i) (g : ℝ) (hg : 1 < g)
    (p : SimpleSpectrum (k + 1)) (e : Fin s ≃ PairIndex (k + 1)) :
    (pctGaussianThermalPositive a ha g hg (fun i => p.ratio (e i))
      (fun i => (p.ratio_pos (e i)).le) (fun i => p.ratio_lt_one (e i))).rootFidelity
      (gaussianThermalPositive a ha (fun i => p.ratio (e i))
        (fun i => (p.ratio_pos (e i)).le) (fun i => p.ratio_lt_one (e i))) = pctValue g p := by
  rw [pctGaussianThermalPositive_rootFidelity, pctValue, classicalValue]
  simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right]
  congr 1
  exact e.prod_comp (fun ij => Thermal.fidelity (p.ratio ij) (Thermal.pct g (p.ratio ij)))

end Cloning.Hybrid
