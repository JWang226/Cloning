import Cloning.HybridPrior
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-! Literal rectangular flat priors on the full joint classical and quantum
phase space, with exact normalization and real-radius change of variables. -/

noncomputable section
open scoped Topology
open Filter MeasureTheory
namespace Cloning.Hybrid
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {k s : ℕ}

instance phaseSpaceVolume_isAddHaarMeasure :
    (volume : Measure (PhaseSpace k s)).IsAddHaarMeasure where
  toIsFiniteMeasureOnCompacts := inferInstance
  toIsAddLeftInvariant := inferInstance
  toIsOpenPosMeasure := inferInstance

/-- All classical coordinates, and real and imaginary quantum coordinates,
lie in the same centered physical interval. -/
def phaseSpaceBox (k s : ℕ) (L : ℝ) : Set (PhaseSpace k s) :=
  {ξ | (∀ i, |ξ.1 i| ≤ L) ∧ (∀ j, |(ξ.2 j).re| ≤ L ∧ |(ξ.2 j).im| ≤ L)}

def phaseSpaceUnitBox (k s : ℕ) : Set (PhaseSpace k s) := phaseSpaceBox k s 1

theorem phaseSpaceBox_closed (k s : ℕ) (L : ℝ) : IsClosed (phaseSpaceBox k s L) := by
  simp only [phaseSpaceBox, Set.setOf_and, Set.setOf_forall]
  apply IsClosed.inter
  · apply isClosed_iInter
    intro i
    exact isClosed_le (((continuous_apply i).comp continuous_fst).abs) continuous_const
  · apply isClosed_iInter
    intro j
    exact (isClosed_le ((Complex.continuous_re.comp ((continuous_apply j).comp continuous_snd)).abs)
      continuous_const).inter
      (isClosed_le ((Complex.continuous_im.comp ((continuous_apply j).comp continuous_snd)).abs)
        continuous_const)

theorem phaseSpaceBox_compact (k s : ℕ) (L : ℝ) : IsCompact (phaseSpaceBox k s L) := by
  apply (isCompact_closedBall (0 : PhaseSpace k s) (2 * |L|)).of_isClosed_subset
    (phaseSpaceBox_closed k s L)
  intro ξ hξ
  rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def]
  apply max_le
  · apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ 2 * |L|)).mpr
    intro i
    rw [Real.norm_eq_abs]
    exact (hξ.1 i).trans (by linarith [le_abs_self L, abs_nonneg L])
  · apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ 2 * |L|)).mpr
    intro j
    exact (Complex.norm_le_abs_re_add_abs_im (ξ.2 j)).trans
      (by linarith [(hξ.2 j).1, (hξ.2 j).2, le_abs_self L])

theorem phaseSpaceUnitBox_closed (k s : ℕ) : IsClosed (phaseSpaceUnitBox k s) :=
  phaseSpaceBox_closed k s 1

theorem phaseSpaceUnitBox_compact (k s : ℕ) : IsCompact (phaseSpaceUnitBox k s) :=
  phaseSpaceBox_compact k s 1

theorem phaseSpaceUnitBox_volume_pos (k s : ℕ) : 0 < volume (phaseSpaceUnitBox k s) := by
  apply Measure.measure_pos_of_nonempty_interior volume
  refine ⟨0, mem_interior_iff_mem_nhds.mpr ?_⟩
  apply mem_of_superset (Metric.ball_mem_nhds (0 : PhaseSpace k s) (by norm_num : (0 : ℝ) < 1))
  intro ξ hξ
  have hn : ‖ξ‖ < 1 := by simpa only [Metric.mem_ball, dist_zero_right] using hξ
  constructor
  · intro i
    exact (show |ξ.1 i| = ‖ξ.1 i‖ from (Real.norm_eq_abs _).symm).le.trans
      ((norm_le_pi_norm ξ.1 i).trans ((norm_fst_le ξ).trans hn.le))
  · intro j
    have hq := (norm_le_pi_norm ξ.2 j).trans ((norm_snd_le ξ).trans hn.le)
    exact ⟨(Complex.abs_re_le_norm _).trans hq, (Complex.abs_im_le_norm _).trans hq⟩

theorem phaseSpaceUnitBox_volume_real_pos (k s : ℕ) :
    0 < volume.real (phaseSpaceUnitBox k s) :=
  ENNReal.toReal_pos (phaseSpaceUnitBox_volume_pos k s).ne'
    (phaseSpaceUnitBox_compact k s).measure_ne_top

theorem phaseSpaceBox_mono {L M : ℝ} (h : L ≤ M) :
    phaseSpaceBox k s L ⊆ phaseSpaceBox k s M := by
  intro ξ hξ
  exact ⟨fun i => (hξ.1 i).trans h,
    fun j => ⟨(hξ.2 j).1.trans h, (hξ.2 j).2.trans h⟩⟩

/-- A concrete normalized flat probability density on the joint unit box. -/
def flatBoxDensity (k s : ℕ) : PhaseDensity k s where
  value := (phaseSpaceUnitBox k s).indicator (fun _ => (volume.real (phaseSpaceUnitBox k s))⁻¹)
  measurable := measurable_const.indicator (phaseSpaceUnitBox_closed k s).measurableSet
  nonneg := fun ξ => Set.indicator_nonneg (fun _ _ => inv_nonneg.mpr measureReal_nonneg) ξ
  integral_one := by
    rw [integral_indicator (phaseSpaceUnitBox_closed k s).measurableSet, integral_const]
    simp only [measureReal_restrict_apply_univ, smul_eq_mul]
    exact mul_inv_cancel₀ (phaseSpaceUnitBox_volume_real_pos k s).ne'

theorem integral_flatBox_expandingPrior {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (k s n : ℕ) (f : PhaseSpace k s → E) (hf : Continuous f) :
    (∫ ξ, f ξ ∂(flatBoxDensity k s).expandingPrior n) =
      (volume.real (phaseSpaceUnitBox k s))⁻¹ •
        ∫ z in phaseSpaceUnitBox k s, f (((n : ℝ) + 1) • z) := by
  rw [(flatBoxDensity k s).integral_expandingPrior n f hf]
  change (∫ z, ((phaseSpaceUnitBox k s).indicator
    (fun _ => (volume.real (phaseSpaceUnitBox k s))⁻¹) z) • f (((n : ℝ) + 1) • z)) = _
  rw [← integral_smul]
  rw [← integral_indicator (phaseSpaceUnitBox_closed k s).measurableSet]
  congr 1
  funext z
  by_cases hz : z ∈ phaseSpaceUnitBox k s <;> simp [hz]

theorem smul_mem_phaseSpaceBox_iff {L : ℝ} (hL : 0 < L) (ξ : PhaseSpace k s) :
    L • ξ ∈ phaseSpaceBox k s L ↔ ξ ∈ phaseSpaceUnitBox k s := by
  have he (t : ℝ) : |L * t| ≤ L ↔ |t| ≤ 1 := by
    rw [abs_mul, abs_of_pos hL]
    simpa only [mul_one] using
      (mul_le_mul_iff_right₀ hL : L * |t| ≤ L * 1 ↔ |t| ≤ 1)
  simp only [phaseSpaceBox, phaseSpaceUnitBox, Set.mem_setOf_eq, Prod.smul_fst, Prod.smul_snd,
    Pi.smul_apply, Complex.smul_re, Complex.smul_im, smul_eq_mul, he]

/-- Exact Jacobian for joint real classical and complex quantum coordinates. -/
theorem integral_unitBox_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {L : ℝ} (hL : 0 < L) (f : PhaseSpace k s → E) :
    (∫ z in phaseSpaceUnitBox k s, f (L • z)) =
      (L ^ Module.finrank ℝ (PhaseSpace k s))⁻¹ •
        ∫ z in phaseSpaceBox k s L, f z := by
  classical
  have he : (fun z => (phaseSpaceBox k s L).indicator f (L • z)) =
      (phaseSpaceUnitBox k s).indicator (fun z => f (L • z)) := by
    funext z
    by_cases hz : z ∈ phaseSpaceUnitBox k s
    · simp only [Set.indicator_of_mem hz,
        Set.indicator_of_mem ((smul_mem_phaseSpaceBox_iff hL z).mpr hz)]
    · simp only [Set.indicator_of_notMem hz,
        Set.indicator_of_notMem (mt (smul_mem_phaseSpaceBox_iff hL z).mp hz)]
  have h := Measure.integral_comp_smul_of_nonneg volume ((phaseSpaceBox k s L).indicator f) L
    (hR := hL.le)
  calc
    _ = ∫ z, (phaseSpaceUnitBox k s).indicator (fun z => f (L • z)) z :=
      (integral_indicator (phaseSpaceUnitBox_closed k s).measurableSet).symm
    _ = ∫ z, (phaseSpaceBox k s L).indicator f (L • z) :=
      (congrArg (fun g : PhaseSpace k s → E => ∫ z, g z) he).symm
    _ = _ := h
    _ = _ := congrArg (fun v : E => (L ^ Module.finrank ℝ (PhaseSpace k s))⁻¹ • v)
      (integral_indicator (phaseSpaceBox_closed k s L).measurableSet)

theorem phaseSpaceBox_volume_real {L : ℝ} (hL : 0 < L) :
    volume.real (phaseSpaceBox k s L) =
      L ^ Module.finrank ℝ (PhaseSpace k s) * volume.real (phaseSpaceUnitBox k s) := by
  have hv := integral_unitBox_smul hL (fun _ : PhaseSpace k s => (1 : ℝ))
  simp only [integral_const, Measure.restrict_apply_univ, measureReal_def, smul_eq_mul, mul_one] at hv
  change volume.real (phaseSpaceUnitBox k s) =
    (L ^ Module.finrank ℝ (PhaseSpace k s))⁻¹ * volume.real (phaseSpaceBox k s L) at hv
  rw [hv, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hL.ne'), one_mul]

theorem normalized_unitBox_smul_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {L : ℝ} (hL : 0 < L) (f : PhaseSpace k s → E) :
    (volume.real (phaseSpaceUnitBox k s))⁻¹ • (∫ z in phaseSpaceUnitBox k s, f (L • z)) =
      (volume.real (phaseSpaceBox k s L))⁻¹ • ∫ z in phaseSpaceBox k s L, f z := by
  rw [integral_unitBox_smul hL f, smul_smul, phaseSpaceBox_volume_real hL, mul_inv_rev]

end Cloning.Hybrid
