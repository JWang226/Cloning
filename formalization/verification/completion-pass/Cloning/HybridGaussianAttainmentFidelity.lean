import Cloning.HybridFoelnerPayoff
import Cloning.HybridL1Fidelity

/-!
# Exact fidelity of the attained hybrid Gaussian--thermal output

Scaling positive trace-class operators separates classical Hellinger affinity
from quantum root fidelity. Applied to the actual Gaussian product fields and
thermal density operators, this gives the full classical--quantum Gaussian
factor, both for fields and for their genuine positive L¹ classes.
-/

noncomputable section
open scoped ComplexOrder InnerProductSpace Topology BigOperators
open MeasureTheory Filter Cloning.InfiniteTraceClass Cloning.InfiniteFidelity
open Cloning.MultimodeCoherent Cloning.MultimodeCoherentGaussianMixture
open Cloning.InfiniteDiagonalFidelity
namespace Cloning.Hybrid
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

variable {Ω H : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma sqrt_real_smul_positive (c : ℝ) (hc : 0 ≤ c) (A : H →L[ℂ] H) (hA : 0 ≤ A) :
    CFC.sqrt ((c : ℂ) • A) = (Real.sqrt c : ℂ) • CFC.sqrt A := by
  simp only [Complex.coe_smul]
  apply CFC.sqrt_unique _ (smul_nonneg (Real.sqrt_nonneg _) (CFC.sqrt_nonneg _))
  rw [smul_mul_assoc, mul_smul_comm, smul_smul, ← pow_two, Real.sq_sqrt hc,
    CFC.sqrt_mul_sqrt_self A hA]

theorem PositiveTraceClass.rootFidelity_scale (a b : NNReal) (A B : PositiveTraceClass H) :
    (PositiveTraceClass.scale a A).rootFidelity (PositiveTraceClass.scale b B) =
      (Real.sqrt (a : ℝ) * Real.sqrt (b : ℝ)) * A.rootFidelity B := by
  have he : CFC.sqrt (((a : ℝ) : ℂ) • A.1.1) * CFC.sqrt (((b : ℝ) : ℂ) • B.1.1) =
      ((Real.sqrt (a : ℝ) * Real.sqrt (b : ℝ) : ℝ) : ℂ) •
        (CFC.sqrt A.1.1 * CFC.sqrt B.1.1) := by
    rw [sqrt_real_smul_positive (H := H) (a : ℝ) a.2 A.1.1 A.2,
      sqrt_real_smul_positive (H := H) (b : ℝ) b.2 B.1.1 B.2,
      smul_mul_assoc, mul_smul_comm, smul_smul, ← Complex.ofReal_mul]
  unfold PositiveTraceClass.rootFidelity fidelity
  change traceNorm (CFC.sqrt (((a : ℝ) : ℂ) • A.1.1) *
    CFC.sqrt (((b : ℝ) : ℂ) • B.1.1)) _ = _
  rw [traceNorm_transport he, traceNorm_smul]
  rw [Complex.norm_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))]

/-- Fidelity of genuine product fields factors into a classical affinity
and the fidelity of the normalized quantum states. -/
theorem PositiveField.rootFidelity_product
    (g h : Ω → ℝ) (hg : Integrable g μ) (hh : Integrable h μ)
    (hg0 : ∀ y, 0 ≤ g y) (hh0 : ∀ y, 0 ≤ h y) (A B : DensityState H) :
    (PositiveField.product g hg hg0 A).rootFidelity (PositiveField.product h hh hh0 B) =
      (∫ y, Real.sqrt (g y) * Real.sqrt (h y) ∂μ) * stateFidelity A B := by
  unfold PositiveField.rootFidelity
  simp only [PositiveField.product, PositiveTraceClass.rootFidelity_scale,
    Real.coe_toNNReal _ (hg0 _), Real.coe_toNNReal _ (hh0 _)]
  rw [integral_mul_const]
  rfl

variable {k s : ℕ}

/-- The actual centered output under classical dilation and quantum-limited
amplification. The parameters are precisions and geometric thermal ratios. -/
def amplifiedGaussianThermalField
    (a : Fin k → ℝ) (ha : ∀ i, 0 < a i) (g : ℝ) (hg : 1 < g)
    (q : Fin s → ℝ) (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i < 1) :
    PositiveField (H := Fock s) (volume : Measure (Fin k → ℝ)) :=
  gaussianThermalField (fun i => a i / g)
    (fun i => div_pos (ha i) (zero_lt_one.trans hg))
    (fun i => Thermal.amplified g (q i))
    (fun i => (hq0 i).trans (Thermal.lt_amplified hg (hq1 i)).le)
    (fun i => Thermal.amplified_lt_one (zero_lt_one.trans hg) (hq1 i))

/-- The full sharp factor is the fidelity of two literal hybrid density
fields, including thermal ratios equal to zero. -/
theorem gaussianThermalField_amplified_rootFidelity
    (a : Fin k → ℝ) (ha : ∀ i, 0 < a i) (g : ℝ) (hg : 1 < g)
    (q : Fin s → ℝ) (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i < 1) :
    (amplifiedGaussianThermalField a ha g hg q hq0 hq1).rootFidelity
      (gaussianThermalField a ha q hq0 hq1) =
      Thermal.classicalBase g ^ ((k : ℝ) / 2) * ∏ i, Thermal.modeFactor g (q i) := by
  rw [PositiveField.rootFidelity_comm]
  unfold amplifiedGaussianThermalField gaussianThermalField
  rw [PositiveField.rootFidelity_product, stateFidelity_productGeometric]
  have hc := GaussianAffinity.integral_product_dilation a ha (zero_lt_one.trans hg)
  simp only [Fintype.card_fin] at hc
  rw [hc]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  exact Thermal.fidelity_amplified_eq_modeFactor hg (hq0 i) (hq1 i)

/-- The same exact fidelity on positive equivalence classes of the genuine
operator-valued L¹ space. -/
theorem gaussianThermalField_amplified_toPositiveL1_rootFidelity
    (a : Fin k → ℝ) (ha : ∀ i, 0 < a i) (g : ℝ) (hg : 1 < g)
    (q : Fin s → ℝ) (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i < 1) :
    (amplifiedGaussianThermalField a ha g hg q hq0 hq1).toPositiveL1.rootFidelity
      (gaussianThermalField a ha q hq0 hq1).toPositiveL1 =
      Thermal.classicalBase g ^ ((k : ℝ) / 2) * ∏ i, Thermal.modeFactor g (q i) := by
  rw [PositiveField.toPositiveL1_rootFidelity]
  exact gaussianThermalField_amplified_rootFidelity a ha g hg q hq0 hq1

end Cloning.Hybrid
