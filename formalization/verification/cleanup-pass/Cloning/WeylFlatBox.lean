import Cloning.WeylFlatPrior
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-! The literal rectangular phase-space boxes used by flat-prior averaging. -/
noncomputable section
open scoped Topology
open Filter MeasureTheory
namespace Cloning.MultimodeCoherent
variable {d : ℕ}

/-- The unit box in all real and imaginary phase-space coordinates. -/
def phaseSpaceUnitBox (d : ℕ) : Set (Fin d → ℂ) :=
  {z | ∀ i, |(z i).re| ≤ 1 ∧ |(z i).im| ≤ 1}

lemma phaseSpaceUnitBox_closed (d : ℕ) : IsClosed (phaseSpaceUnitBox d) := by
  simp only [phaseSpaceUnitBox, Set.setOf_forall]
  apply isClosed_iInter
  intro i
  exact (isClosed_le ((Complex.continuous_re.comp (continuous_apply i)).abs) continuous_const).inter
    (isClosed_le ((Complex.continuous_im.comp (continuous_apply i)).abs) continuous_const)

lemma phaseSpaceUnitBox_compact (d : ℕ) : IsCompact (phaseSpaceUnitBox d) := by
  apply (isCompact_closedBall (0 : Fin d → ℂ) 2).of_isClosed_subset
    (phaseSpaceUnitBox_closed d)
  intro z hz
  rw [Metric.mem_closedBall, dist_zero_right]
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)).mpr
  intro i
  exact (Complex.norm_le_abs_re_add_abs_im (z i)).trans (by linarith [(hz i).1, (hz i).2])

lemma phaseSpaceUnitBox_volume_pos (d : ℕ) : 0 < volume (phaseSpaceUnitBox d) := by
  apply Measure.measure_pos_of_nonempty_interior volume
  refine ⟨0, mem_interior_iff_mem_nhds.mpr ?_⟩
  apply mem_of_superset (Metric.ball_mem_nhds (0 : Fin d → ℂ) (by norm_num : (0 : ℝ) < 1))
  intro z hz i
  have hn : ‖z‖ < 1 := by simpa only [Metric.mem_ball, dist_zero_right] using hz
  exact ⟨(Complex.abs_re_le_norm (z i)).trans ((norm_le_pi_norm z i).trans hn.le),
    (Complex.abs_im_le_norm (z i)).trans ((norm_le_pi_norm z i).trans hn.le)⟩

/-- An explicit normalized flat-box prior with all measurability, positivity,
normalization and finite-volume obligations discharged. -/
def flatBoxDensity (d : ℕ) : PhaseSpaceDensity d :=
  flatRegionDensity (phaseSpaceUnitBox d) (phaseSpaceUnitBox_closed d).measurableSet
    (phaseSpaceUnitBox_volume_pos d).ne' (phaseSpaceUnitBox_compact d).measure_ne_top

/-- The actual flat-box average over all amplitudes with real and imaginary
coordinates between `-(n+1)` and `n+1`, written by exact dilation of the unit box. -/
theorem integral_flatBox_expandingPrior {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (d n : ℕ) (f : (Fin d → ℂ) → E) (hf : Continuous f) :
    (∫ a, f a ∂(flatBoxDensity d).expandingPrior n) =
      (volume.real (phaseSpaceUnitBox d))⁻¹ •
        ∫ z in phaseSpaceUnitBox d, f (((n : ℝ) + 1) • z) :=
  integral_flatRegion_expandingPrior _ _ _ _ n f hf

/-- The physical rectangular box of amplitude radius `L`. -/
def phaseSpaceBox (d : ℕ) (L : ℝ) : Set (Fin d → ℂ) :=
  {z | ∀ i, |(z i).re| ≤ L ∧ |(z i).im| ≤ L}

lemma phaseSpaceBox_closed (d : ℕ) (L : ℝ) : IsClosed (phaseSpaceBox d L) := by
  simp only [phaseSpaceBox, Set.setOf_forall]
  apply isClosed_iInter
  intro i
  exact (isClosed_le ((Complex.continuous_re.comp (continuous_apply i)).abs) continuous_const).inter
    (isClosed_le ((Complex.continuous_im.comp (continuous_apply i)).abs) continuous_const)

lemma smul_mem_phaseSpaceBox_iff {L : ℝ} (hL : 0 < L) (z : Fin d → ℂ) :
    L • z ∈ phaseSpaceBox d L ↔ z ∈ phaseSpaceUnitBox d := by
  have he (t : ℝ) : |L * t| ≤ L ↔ |t| ≤ 1 := by
    rw [abs_mul, abs_of_pos hL]
    simpa only [mul_one] using (mul_le_mul_iff_right₀ hL : L * |t| ≤ L * 1 ↔ |t| ≤ 1)
  simp only [phaseSpaceBox, phaseSpaceUnitBox, Set.mem_setOf_eq, Pi.smul_apply,
    Complex.smul_re, Complex.smul_im, smul_eq_mul, he]

/-- Exact Lebesgue change of variables between unit-box coordinates and the
physical expanding box. The Jacobian is the real phase-space dimension. -/
lemma integral_unitBox_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {L : ℝ} (hL : 0 < L) (f : (Fin d → ℂ) → E) :
    (∫ z in phaseSpaceUnitBox d, f (L • z)) =
      (L ^ Module.finrank ℝ (Fin d → ℂ))⁻¹ • ∫ z in phaseSpaceBox d L, f z := by
  classical
  have he : (fun z => (phaseSpaceBox d L).indicator f (L • z)) =
      (phaseSpaceUnitBox d).indicator (fun z => f (L • z)) := by
    funext z
    by_cases hz : z ∈ phaseSpaceUnitBox d
    · simp only [Set.indicator_of_mem hz,
        Set.indicator_of_mem ((smul_mem_phaseSpaceBox_iff hL z).mpr hz)]
    · simp only [Set.indicator_of_notMem hz,
        Set.indicator_of_notMem (mt (smul_mem_phaseSpaceBox_iff hL z).mp hz)]
  have h := Measure.integral_comp_smul_of_nonneg volume ((phaseSpaceBox d L).indicator f) L
    (hR := hL.le)
  calc
    _ = ∫ z, (phaseSpaceUnitBox d).indicator (fun z => f (L • z)) z :=
      (integral_indicator (phaseSpaceUnitBox_closed d).measurableSet).symm
    _ = ∫ z, (phaseSpaceBox d L).indicator f (L • z) :=
      (congrArg (fun g : (Fin d → ℂ) → E => ∫ z, g z) he).symm
    _ = _ := h
    _ = _ := congrArg (fun v : E => (L ^ Module.finrank ℝ (Fin d → ℂ))⁻¹ • v)
      (integral_indicator (phaseSpaceBox_closed d L).measurableSet)

/-- The normalized unit-box dilation is exactly the normalized Lebesgue
integral on the physical box, including zero quantum modes. -/
theorem normalized_unitBox_smul_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {L : ℝ} (hL : 0 < L) (f : (Fin d → ℂ) → E) :
    (volume.real (phaseSpaceUnitBox d))⁻¹ • (∫ z in phaseSpaceUnitBox d, f (L • z)) =
      (volume.real (phaseSpaceBox d L))⁻¹ • ∫ z in phaseSpaceBox d L, f z := by
  have hv := integral_unitBox_smul hL (fun _ : Fin d → ℂ => (1 : ℝ))
  simp only [integral_const, Measure.restrict_apply_univ, measureReal_def,
    smul_eq_mul, mul_one] at hv
  have hc : (L ^ Module.finrank ℝ (Fin d → ℂ)) ≠ 0 := pow_ne_zero _ hL.ne'
  rw [integral_unitBox_smul hL f, smul_smul]
  congr 1
  change (volume.real (phaseSpaceUnitBox d))⁻¹ * (L ^ Module.finrank ℝ (Fin d → ℂ))⁻¹ = _
  change volume.real (phaseSpaceUnitBox d) =
    (L ^ Module.finrank ℝ (Fin d → ℂ))⁻¹ * volume.real (phaseSpaceBox d L) at hv
  rw [hv, mul_inv_rev, inv_inv]
  rw [mul_assoc, mul_inv_cancel₀ hc, mul_one]

end Cloning.MultimodeCoherent
