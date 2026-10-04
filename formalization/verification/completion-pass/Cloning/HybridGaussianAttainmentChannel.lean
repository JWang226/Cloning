import Cloning.HybridCovariantization
import Cloning.AmplifierWeylThermal
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-! A genuine hybrid channel implementing deterministic classical dilation
and the physical quantum amplifier. Both operations act on all operator-valued
L1 inputs, including correlated classical--quantum inputs. -/
noncomputable section
open scoped ComplexOrder InnerProductSpace Topology BigOperators
open MeasureTheory Filter Cloning.InfiniteTraceClass Cloning.MultimodeCoherent
namespace Cloning.Hybrid
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
variable {k s : ℕ} {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

private lemma dilation_integrable (r : ℝ) (hr : 0 < r)
    (A : Lp (TraceClass H) 1 (volume : Measure (Fin k → ℝ))) :
    Integrable (fun y : Fin k → ℝ => (((r ^ k)⁻¹ : ℝ) : ℂ) • A (r⁻¹ • y)) :=
  ((L1.integrable_coeFn A).comp_smul (inv_ne_zero hr.ne')).smul ((((r ^ k)⁻¹ : ℝ) : ℂ))

private def dilationLinear (r : ℝ) (hr : 0 < r) :
    Lp (TraceClass H) 1 (volume : Measure (Fin k → ℝ)) →ₗ[ℂ]
      Lp (TraceClass H) 1 (volume : Measure (Fin k → ℝ)) where
  toFun A := (dilation_integrable r hr A).toL1 _
  map_add' A B := by
    apply Lp.ext
    have he := (Measure.quasiMeasurePreserving_smul (volume : Measure (Fin k → ℝ))
      (inv_ne_zero hr.ne')).ae (Lp.coeFn_add A B)
    filter_upwards [(dilation_integrable r hr (A+B)).coeFn_toL1,
      Lp.coeFn_add ((dilation_integrable r hr A).toL1 _) ((dilation_integrable r hr B).toL1 _),
      (dilation_integrable r hr A).coeFn_toL1, (dilation_integrable r hr B).coeFn_toL1, he]
      with y h₁ h₂ h₃ h₄ h₅
    rw [h₁, h₂, Pi.add_apply, h₃, h₄, h₅, Pi.add_apply, smul_add]
  map_smul' c A := by
    apply Lp.ext
    have he := (Measure.quasiMeasurePreserving_smul (volume : Measure (Fin k → ℝ))
      (inv_ne_zero hr.ne')).ae (Lp.coeFn_smul c A)
    filter_upwards [(dilation_integrable r hr (c • A)).coeFn_toL1,
      Lp.coeFn_smul c ((dilation_integrable r hr A).toL1 _),
      (dilation_integrable r hr A).coeFn_toL1, he] with y h₁ h₂ h₃ h₄
    change ((dilation_integrable r hr (c • A)).toL1 _) y = _
    simp only [RingHom.id_apply]
    rw [h₁, h₂, Pi.smul_apply, h₃, h₄, Pi.smul_apply]
    exact smul_comm _ _ _

private lemma dilationLinear_ae (r : ℝ) (hr : 0 < r)
    (A : Lp (TraceClass H) 1 (volume : Measure (Fin k → ℝ))) :
    dilationLinear r hr A =ᵐ[volume]
      fun y => (((r ^ k)⁻¹ : ℝ) : ℂ) • A (r⁻¹ • y) :=
  (dilation_integrable r hr A).coeFn_toL1

private lemma norm_dilationLinear (r : ℝ) (hr : 0 < r)
    (A : Lp (TraceClass H) 1 (volume : Measure (Fin k → ℝ))) :
    ‖dilationLinear r hr A‖ = ‖A‖ := by
  rw [L1.norm_eq_integral_norm, L1.norm_eq_integral_norm]
  calc
    _ = ∫ y : Fin k → ℝ, (r ^ k)⁻¹ * ‖A (r⁻¹ • y)‖ := by
      apply integral_congr_ae
      filter_upwards [dilationLinear_ae r hr A] with y hy
      rw [hy, norm_smul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (inv_nonneg.mpr (pow_nonneg hr.le _))]
    _ = _ := by
      rw [integral_const_mul, Measure.integral_comp_inv_smul_of_nonneg volume
        (fun y => ‖A y‖) hr.le]
      simp only [Module.finrank_pi, Fintype.card_fin, smul_eq_mul]
      rw [← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hr.ne'), one_mul]

/-- Dilation sends a density to `r⁻ᵏ A(y/r)` and preserves the actual L1 norm. -/
def classicalDilation (r : ℝ) (hr : 0 < r) :
    Lp (TraceClass H) 1 (volume : Measure (Fin k → ℝ)) →ₗᵢ[ℂ]
      Lp (TraceClass H) 1 (volume : Measure (Fin k → ℝ)) where
  toLinearMap := dilationLinear r hr
  norm_map' := norm_dilationLinear r hr

lemma classicalDilation_ae (r : ℝ) (hr : 0 < r)
    (A : Lp (TraceClass H) 1 (volume : Measure (Fin k → ℝ))) :
    classicalDilation r hr A =ᵐ[volume]
      fun y => (((r ^ k)⁻¹ : ℝ) : ℂ) • A (r⁻¹ • y) := dilationLinear_ae r hr A

lemma classicalDilation_completelyPositive (r : ℝ) (hr : 0 < r) :
    L1CompletelyPositive (classicalDilation (H := H) (k := k) r hr).toLinearMap := by
  intro n A hA
  have hp := (Measure.quasiMeasurePreserving_smul (volume : Measure (Fin k → ℝ))
    (inv_ne_zero hr.ne')).ae hA
  have he : ∀ᵐ y ∂volume, ∀ i j : Fin n,
      classicalDilation r hr (A i j) y = (((r ^ k)⁻¹ : ℝ) : ℂ) • A i j (r⁻¹ • y) :=
    ae_all_iff.mpr fun i => ae_all_iff.mpr fun j => classicalDilation_ae r hr (A i j)
  filter_upwards [hp, he] with y hp he
  change BlockPositive (fun i j => classicalDilation r hr (A i j) y)
  simp only [he]
  intro v
  change 0 ≤ ∑ i, ∑ j, ⟪v i, (((r ^ k)⁻¹ : ℝ) : ℂ) • ((A i j (r⁻¹ • y)).1 (v j))⟫_ℂ
  simp only [inner_smul_right, ← Finset.mul_sum]
  exact mul_nonneg (Complex.zero_le_real.mpr (inv_nonneg.mpr (pow_nonneg hr.le _))) (hp v)

lemma classicalDilation_tracePreserving (r : ℝ) (hr : 0 < r) :
    L1TracePreserving (classicalDilation (H := H) (k := k) r hr).toLinearMap := by
  intro A
  calc
    _ = ∫ y : Fin k → ℝ, (((r ^ k)⁻¹ : ℝ) : ℂ) * traceCLM (A (r⁻¹ • y)) := by
      apply integral_congr_ae
      filter_upwards [classicalDilation_ae r hr A] with y hy
      change traceCLM (classicalDilation r hr A y) = _
      simp only [hy, map_smul, smul_eq_mul]
    _ = _ := by
      rw [integral_const_mul, Measure.integral_comp_inv_smul_of_nonneg volume
        (fun y => traceCLM (A y)) hr.le]
      simp only [Module.finrank_pi, Fintype.card_fin, Complex.real_smul]
      rw [← mul_assoc, ← Complex.ofReal_mul, inv_mul_cancel₀ (pow_ne_zero _ hr.ne')]
      simp

/-- Deterministic dilation is an actual hybrid CPTP channel. -/
def classicalDilationChannel (r : ℝ) (hr : 0 < r) :
    Channel H H (volume : Measure (Fin k → ℝ)) where
  map := (classicalDilation r hr).toContinuousLinearMap
  completelyPositive := classicalDilation_completelyPositive r hr
  tracePreserving := classicalDilation_tracePreserving r hr

/-- A genuine quantum channel applied independently to every classical fibre. -/
def fibreChannel {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Φ : QuantumChannel H K) : Channel H K μ where
  map := Φ.toPositiveTracePreservingMap.toContinuousLinearMap.compLpL 1 μ
  completelyPositive := by
    intro n A hA
    have he : ∀ᵐ y ∂μ, ∀ i j : Fin n,
        Φ.toPositiveTracePreservingMap.toContinuousLinearMap.compLpL 1 μ (A i j) y =
          Φ.toLinearMap (A i j y) :=
      ae_all_iff.mpr fun i => ae_all_iff.mpr fun j =>
        Φ.toPositiveTracePreservingMap.toContinuousLinearMap.coeFn_compLpL (A i j)
    filter_upwards [he, hA] with y hy hp
    change BlockPositive (fun i j => Φ.toPositiveTracePreservingMap.toContinuousLinearMap.compLpL 1 μ (A i j) y)
    simpa only [hy] using Φ.completelyPositive n (fun i j => A i j y) hp
  tracePreserving := by
    intro A
    apply integral_congr_ae
    filter_upwards [Φ.toPositiveTracePreservingMap.toContinuousLinearMap.coeFn_compLpL A]
      with y hy
    change traceCLM (Φ.toPositiveTracePreservingMap.toContinuousLinearMap.compLpL 1 μ A y) = _
    rw [hy]
    exact Φ.trace_preserving _

lemma fibreChannel_ae {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Φ : QuantumChannel H K) (A : Lp (TraceClass H) 1 μ) :
    (fibreChannel μ Φ).map A =ᵐ[μ] fun y => Φ.toLinearMap (A y) :=
  Φ.toPositiveTracePreservingMap.toContinuousLinearMap.coeFn_compLpL A

/-- The physical product amplifier on all hybrid L1 inputs. -/
def gaussianAmplifierChannel (g : ℝ) (hg : 1 < g) : HybridChannel k s :=
  (fibreChannel volume (Cloning.MultimodeAmplifier.gainChannel g hg)).comp
    (classicalDilationChannel (Real.sqrt g) (Real.sqrt_pos.mpr (by linarith)))

lemma gaussianAmplifierChannel_ae (g : ℝ) (hg : 1 < g) (A : HybridSpace k s) :
    (gaussianAmplifierChannel g hg).map A =ᵐ[volume]
      fun y => (((Real.sqrt g ^ k)⁻¹ : ℝ) : ℂ) •
        (Cloning.MultimodeAmplifier.gainChannel g hg).toLinearMap (A ((Real.sqrt g)⁻¹ • y)) := by
  filter_upwards [fibreChannel_ae volume (Cloning.MultimodeAmplifier.gainChannel g hg)
    (classicalDilationChannel (k := k) (Real.sqrt g) (Real.sqrt_pos.mpr (by linarith : 0 < g)) |>.map A),
    classicalDilation_ae (Real.sqrt g) (Real.sqrt_pos.mpr (by linarith : 0 < g)) A]
    with y h₁ h₂
  change (fibreChannel volume (Cloning.MultimodeAmplifier.gainChannel g hg)).map
    (classicalDilation (Real.sqrt g) (Real.sqrt_pos.mpr (by linarith : 0 < g)) A) y = _
  change (fibreChannel volume (Cloning.MultimodeAmplifier.gainChannel g hg)).map
    (classicalDilation (Real.sqrt g) (Real.sqrt_pos.mpr (by linarith : 0 < g)) A) y =
    (Cloning.MultimodeAmplifier.gainChannel g hg).toLinearMap
      (classicalDilation (Real.sqrt g) (Real.sqrt_pos.mpr (by linarith : 0 < g)) A y) at h₁
  rw [h₁, h₂, map_smul]

end Cloning.Hybrid
