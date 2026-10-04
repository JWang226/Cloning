import Cloning.HybridGaussianAttainmentChannel
import Cloning.HybridGaussianAttainmentFidelity
import Cloning.HybridGaussianConverse
import Cloning.ThermalParameterContinuity

/-! Exact covariance and Gaussian action of the actual hybrid amplifier. -/
noncomputable section
open scoped ComplexOrder InnerProductSpace Topology BigOperators
open MeasureTheory Filter Cloning.InfiniteTraceClass Cloning.MultimodeCoherent
open Cloning.MultimodeCoherentGaussianMixture Cloning.ThermalWitness
namespace Cloning.Hybrid
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
variable {k s : ℕ}

/-- The physical hybrid amplifier intertwines the full joint translation
representation at amplitude gain `sqrt g`, on every operator-valued L¹ input. -/
theorem gaussianAmplifierChannel_covariant (g : ℝ) (hg : 1 < g)
    (ξ : PhaseSpace k s) (A : HybridSpace k s) :
    (gaussianAmplifierChannel g hg).map (hybridTranslation ξ A) =
      hybridTranslation (Real.sqrt g • ξ) ((gaussianAmplifierChannel g hg).map A) := by
  have hr : 0 < Real.sqrt g := Real.sqrt_pos.mpr (zero_lt_one.trans hg)
  apply Lp.ext
  have ht := (Measure.quasiMeasurePreserving_smul (volume : Measure (Fin k → ℝ))
    (inv_ne_zero hr.ne')).ae (hybridTranslation_ae ξ A)
  have hd := (measurePreserving_sub_right volume (Real.sqrt g • ξ.1)).quasiMeasurePreserving.ae
    (gaussianAmplifierChannel_ae g hg A)
  filter_upwards [gaussianAmplifierChannel_ae g hg (hybridTranslation ξ A), ht,
    hybridTranslation_ae (Real.sqrt g • ξ) ((gaussianAmplifierChannel g hg).map A), hd]
    with y h₁ h₂ h₃ h₄
  rw [h₁, h₂, Cloning.MultimodeAmplifier.gainChannel_covariant, h₃]
  simp only [Prod.smul_fst, Prod.smul_snd] at *
  rw [h₄, map_smul]
  congr 3
  rw [smul_sub, smul_smul, inv_mul_cancel₀ hr.ne', one_smul]

lemma density_sqrt_dilation (a y g : ℝ) (ha : 0 < a) (hg : 0 < g) :
    (Real.sqrt g)⁻¹ * GaussianAffinity.density a ((Real.sqrt g)⁻¹ * y) =
      GaussianAffinity.density (a / g) y := by
  have hr : Real.sqrt g ≠ 0 := (Real.sqrt_pos.mpr hg).ne'
  have hp : Real.sqrt Real.pi ≠ 0 := (Real.sqrt_pos.mpr Real.pi_pos).ne'
  unfold GaussianAffinity.density
  rw [Real.sqrt_div ha.le]
  have he : -a * ((Real.sqrt g)⁻¹ * y) ^ 2 = -(a / g) * y ^ 2 := by
    rw [mul_pow, inv_pow, Real.sq_sqrt hg.le]
    ring
  rw [he]
  field_simp

lemma productDensity_sqrt_dilation (a : Fin k → ℝ) (ha : ∀ i, 0 < a i)
    (g : ℝ) (hg : 0 < g) (y : Fin k → ℝ) :
    (Real.sqrt g ^ k)⁻¹ * GaussianAffinity.productDensity a ((Real.sqrt g)⁻¹ • y) =
      GaussianAffinity.productDensity (fun i => a i / g) y := by
  calc
    _ = ∏ i, (Real.sqrt g)⁻¹ * GaussianAffinity.density (a i) ((Real.sqrt g)⁻¹ * y i) := by
      rw [Finset.prod_mul_distrib]
      simp [GaussianAffinity.productDensity, ← inv_pow]
    _ = _ := by
      unfold GaussianAffinity.productDensity
      apply Finset.prod_congr rfl
      intro i _
      exact density_sqrt_dilation (a i) (y i) g (ha i) hg

/-- The actual output of the physical channel is the dilated classical
Gaussian and the amplified quantum thermal state. -/
theorem gaussianAmplifierChannel_gaussianThermal_toL1
    (a : Fin k → ℝ) (ha : ∀ i, 0 < a i) (g : ℝ) (hg : 1 < g)
    (q : Fin s → ℝ) (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i < 1) :
    (gaussianAmplifierChannel g hg).map
      (gaussianThermalField a ha q hq0 hq1).toL1 =
      (amplifiedGaussianThermalField a ha g hg q hq0 hq1).toL1 := by
  have hr : 0 < Real.sqrt g := Real.sqrt_pos.mpr (zero_lt_one.trans hg)
  rw [gaussianThermalField_toL1, amplifiedGaussianThermalField, gaussianThermalField_toL1]
  apply Lp.ext
  have hp := (Measure.quasiMeasurePreserving_smul (volume : Measure (Fin k → ℝ))
    (inv_ne_zero hr.ne')).ae
    (prepareL1_ae (GaussianAffinity.productDensity a)
      (GaussianAffinity.integrable_productDensity a ha)
      (vectorMixture (numberBasis s) (productGeometric q)))
  filter_upwards [gaussianAmplifierChannel_ae g hg
    (prepareL1 (GaussianAffinity.productDensity a)
      (GaussianAffinity.integrable_productDensity a ha)
      (vectorMixture (numberBasis s) (productGeometric q))), hp,
    prepareL1_ae (GaussianAffinity.productDensity (fun i => a i / g))
      (GaussianAffinity.integrable_productDensity (fun i => a i / g)
        (fun i => div_pos (ha i) (zero_lt_one.trans hg)))
      (vectorMixture (numberBasis s) (productGeometric (fun i => Thermal.amplified g (q i))))]
    with y h₁ h₂ h₃
  rw [h₁, h₂, map_smul, Cloning.MultimodeAmplifier.gainChannel_productThermal_nonneg g hg hq0 hq1,
    h₃, smul_smul, ← Complex.ofReal_mul, productDensity_sqrt_dilation a ha g
      (zero_lt_one.trans hg)]

/-- Exact centered positive-state action, ready to insert into orbit fidelity. -/
theorem gaussianAmplifierChannel_gaussianThermalPositive
    (a : Fin k → ℝ) (ha : ∀ i, 0 < a i) (g : ℝ) (hg : 1 < g)
    (q : Fin s → ℝ) (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i < 1) :
    (gaussianThermalPositive a ha q hq0 hq1).map
      (gaussianAmplifierChannel g hg) =
      (amplifiedGaussianThermalField a ha g hg q hq0 hq1).toPositiveL1 := by
  apply Subtype.ext
  exact gaussianAmplifierChannel_gaussianThermal_toL1 a ha g hg q hq0 hq1

end Cloning.Hybrid
