import Cloning.YoungFlatMoment

/-! Uniform tightness of the actual smoothed flat laws, from the physical Casimir moment. -/
noncomputable section
open scoped BigOperators Topology Classical
open MeasureTheory Filter
namespace Cloning.YoungFlat
open Cloning.TensorLie Cloning.YoungHyperplane Cloning.YoungGeneral
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000

theorem cellCenter_error_norm_sq_le (d N : ℕ) (hN : 0 < N) (x : rootSpace d) :
    ‖x-cellCenter d N x‖^2 ≤ ((d+1 : ℕ) : ℝ)^3 := by
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hs : (1 : ℝ) ≤ Real.sqrt N := by
    simpa using Real.sqrt_le_sqrt hn
  have hc i : |x.1 i-(cellCenter d N x).1 i| ≤ ((d+1 : ℕ) : ℝ) := by
    have hh := sampleCenter_coordinate_distance d N (by exact_mod_cast hN)
      (flatSpectrum (d+1)) (flatSpectrum_sum _ (by omega))
      (sampleLabel d N (flatSpectrum (d+1)) x) x
      (mem_sampleCell_sampleLabel d N (flatSpectrum (d+1)) x) i
    rw [abs_sub_comm] at hh
    refine hh.trans ?_
    norm_cast
    have ht : (0 : ℝ) < 2*Real.sqrt N := by positivity
    apply (div_le_iff₀ ht).mpr
    have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    nlinarith
  change ‖(x-cellCenter d N x).1‖^2 ≤ _
  rw [EuclideanSpace.real_norm_sq_eq]
  calc
    _ ≤ ∑ _i : Fin (d+1), (((d+1 : ℕ) : ℝ)^2) := by
      apply Finset.sum_le_sum
      intro i _
      change (x.1 i-(cellCenter d N x).1 i)^2 ≤ _
      have hh := (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr (hc i)
      simpa only [sq_abs] using hh
    _ = _ := by simp; ring

theorem norm_sq_le_cellCenter (d N : ℕ) (hN : 0 < N) (x : rootSpace d) :
    ‖x‖^2 ≤ 2*‖cellCenter d N x‖^2+2*((d+1 : ℕ) : ℝ)^3 := by
  have ht : ‖x‖ ≤ ‖x-cellCenter d N x‖+‖cellCenter d N x‖ := by
    simpa using norm_add_le (x-cellCenter d N x) (cellCenter d N x)
  have he := cellCenter_error_norm_sq_le d N hN x
  have hn := norm_nonneg x
  have hn₁ := norm_nonneg (x-cellCenter d N x)
  have hn₂ := norm_nonneg (cellCenter d N x)
  nlinarith [sq_nonneg (‖x-cellCenter d N x‖-‖cellCenter d N x‖)]

theorem integrable_norm_sq (d N : ℕ) (hN : 0 < N) :
    Integrable (fun x : rootSpace d ↦ ‖x‖^2) (smoothedMeasure d N) := by
  letI : IsProbabilityMeasure (smoothedMeasure d N) :=
    physicalSmoothedMeasure_isProbability d N hN _ _ _
  apply ((integrable_cellCenter_norm_sq d N hN).const_mul 2 |>.add
    (integrable_const (2*((d+1 : ℕ) : ℝ)^3))).mono'
    (by fun_prop)
  exact ae_of_all _ fun x ↦ by
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact norm_sq_le_cellCenter d N hN x

set_option backward.isDefEq.respectTransparency true in
theorem integral_norm_sq_le (d N : ℕ) (hN : 0 < N) :
    (∫ x : rootSpace d, ‖x‖^2 ∂smoothedMeasure d N) ≤
      2*((d+1 : ℕ) : ℝ)+2*((d+1 : ℕ) : ℝ)^3 := by
  letI : IsProbabilityMeasure (smoothedMeasure d N) :=
    physicalSmoothedMeasure_isProbability d N hN _ _ _
  calc
    _ ≤ ∫ x, 2*‖cellCenter d N x‖^2+2*((d+1 : ℕ) : ℝ)^3 ∂smoothedMeasure d N :=
      integral_mono (μ := smoothedMeasure d N)
        (f := fun x : rootSpace d ↦ ‖x‖^2)
        (g := fun x : rootSpace d ↦ 2*‖cellCenter d N x‖^2+2*((d+1 : ℕ) : ℝ)^3)
        (integrable_norm_sq d N hN)
        (((integrable_cellCenter_norm_sq d N hN).const_mul 2).add'' (integrable_const (μ := smoothedMeasure d N) (2*((d+1 : ℕ) : ℝ)^3)))
        (norm_sq_le_cellCenter d N hN)
    _ = 2*(∫ x, ‖cellCenter d N x‖^2 ∂smoothedMeasure d N)+2*((d+1 : ℕ) : ℝ)^3 := by
      rw [integral_add ((integrable_cellCenter_norm_sq d N hN).const_mul 2) (integrable_const (μ := smoothedMeasure d N) (2*((d+1 : ℕ) : ℝ)^3)),
        integral_const_mul, integral_const]
      rw [measureReal_univ_eq_one]
      simp only [one_smul]
    _ ≤ _ := by linarith [integral_cellCenter_norm_sq_le d N hN]

theorem smoothedMeasure_real_eq_integral (d N : ℕ) (hN : 0 < N)
    (A : Set (rootSpace d)) (hA : MeasurableSet A) :
    (smoothedMeasure d N).real A = ∫ x in A, flatDensity d N x := by
  rw [measureReal_def, smoothedMeasure,
    physicalSmoothedMeasure_apply d N hN _ _ _ A hA]
  exact ENNReal.toReal_ofReal (integral_nonneg fun x ↦ flatDensity_nonneg d N x)

theorem flatDensity_tail_le (d N : ℕ) (hN : 0 < N) (R : ℝ) (hR : 0 < R) :
    (∫ x in (Metric.closedBall (0 : rootSpace d) R)ᶜ, flatDensity d N x) ≤
      (2*((d+1 : ℕ) : ℝ)+2*((d+1 : ℕ) : ℝ)^3)/R^2 := by
  letI : IsProbabilityMeasure (smoothedMeasure d N) :=
    physicalSmoothedMeasure_isProbability d N hN _ _ _
  rw [← smoothedMeasure_real_eq_integral d N hN _ Metric.isClosed_closedBall.measurableSet.compl]
  have hs : (Metric.closedBall (0 : rootSpace d) R)ᶜ ⊆
      {x : rootSpace d | R^2 ≤ ‖x‖^2} := by
    intro x hx
    simp only [Set.mem_compl_iff, Metric.mem_closedBall, dist_zero_right, not_le] at hx
    change R^2 ≤ ‖x‖^2
    nlinarith [norm_nonneg x]
  have hm := mul_meas_ge_le_integral_of_nonneg
    (ae_of_all (smoothedMeasure d N) fun x : rootSpace d ↦ sq_nonneg ‖x‖)
    (integrable_norm_sq d N hN) (R^2)
  apply (le_div_iff₀ (sq_pos_of_pos hR)).mpr
  calc
    _ = R^2*(smoothedMeasure d N).real (Metric.closedBall (0 : rootSpace d) R)ᶜ := by ring
    _ ≤ R^2*(smoothedMeasure d N).real {x : rootSpace d | R^2 ≤ ‖x‖^2} :=
      mul_le_mul_of_nonneg_left (measureReal_mono hs) (sq_nonneg R)
    _ ≤ _ := hm.trans (integral_norm_sq_le d N hN)

/-- Fixed compact sets capture uniformly all but any prescribed amount of physical mass. -/
theorem flatDensity_tight (d : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ K : Set (rootSpace d), IsCompact K ∧
      ∀ N : ℕ, 0 < N → (∫ x in Kᶜ, flatDensity d N x) < ε := by
  let C : ℝ := 2*((d+1 : ℕ) : ℝ)+2*((d+1 : ℕ) : ℝ)^3
  let R : ℝ := Real.sqrt (C/ε+1)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hR : 0 < R := by dsimp [R]; positivity
  have hsq : R^2=C/ε+1 := Real.sq_sqrt (by positivity)
  refine ⟨Metric.closedBall 0 R, isCompact_closedBall _ _, fun N hN ↦ ?_⟩
  refine (flatDensity_tail_le d N hN R hR).trans_lt ?_
  change C/R^2 < ε
  apply (div_lt_iff₀ (sq_pos_of_pos hR)).mpr
  rw [hsq]
  have he : ε*(C/ε)=C := mul_div_cancel₀ C hε.ne'
  nlinarith

end Cloning.YoungFlat
