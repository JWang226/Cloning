import Cloning.InfiniteTraceClassCutoffConvergence
import Cloning.InfiniteHilbertSchmidt

/-! A quantitative gentle-compression estimate in the genuine trace norm.
It follows from the actual positive rank-one series and scalar Cauchy–Schwarz. -/
noncomputable section
open scoped BigOperators ComplexOrder InnerProductSpace Topology
namespace Cloning.InfiniteTraceClass
open HilbertSchmidt
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem norm_projection_apply_le {P : H →L[ℂ] H} (hP : IsStarProjection P) (x : H) :
    ‖P x‖ ≤ ‖x‖ := (P.le_opNorm x).trans (by nlinarith [hP.norm_le, norm_nonneg x])

theorem norm_vectorProjector_sub_projection_le {P : H →L[ℂ] H}
    (hP : IsStarProjection P) (x : H) :
    ‖vectorProjector x - vectorProjector (P x)‖ ≤ 2 * (‖x‖ * ‖(1-P) x‖) := by
  have h := norm_vectorProjector_sub_le x (P x)
  have hPx := norm_projection_apply_le hP x
  have he : (1-P) x = x - P x := by simp
  rw [he]
  exact h.trans (by nlinarith [norm_nonneg (x-P x)])

/-- Compression costs at most twice the square root of total mass times
mass outside the projection, for arbitrary positive trace-class operators. -/
theorem norm_sub_sandwich_projection_le {P : H →L[ℂ] H} (hP : IsStarProjection P)
    (A : TraceClass H) (hA : 0 ≤ A.1) :
    ‖A - sandwichCLM P P A‖ ≤
      2 * Real.sqrt ‖A‖ * Real.sqrt ‖sandwichCLM (1-P) (1-P) A‖ := by
  obtain ⟨w, b, _⟩ := exists_hilbertBasis ℂ H
  let v : w → H := fun i ↦ CFC.sqrt A.1 (b i)
  have hs : HasSum (fun i ↦ vectorProjector (v i)) A := positive_rankOne_series hA A.2 b
  have hc : HasSum (fun i ↦ vectorProjector (P (v i))) (sandwichCLM P P A) := by
    simpa only [sandwichCLM_vectorProjector P hP.isSelfAdjoint] using
      hs.mapL (sandwichCLM P P)
  have hd : HasSum (fun i ↦ vectorProjector ((1-P) (v i))) (sandwichCLM (1-P) (1-P) A) := by
    have he : (fun i : w ↦ sandwichCLM (1-P) (1-P) (vectorProjector (v i))) =
        (fun i : w ↦ vectorProjector ((1-P) (v i))) :=
      funext fun i ↦ sandwichCLM_vectorProjector (1-P) hP.one_sub.isSelfAdjoint (v i)
    rw [← he]
    exact hs.mapL (sandwichCLM (1-P) (1-P))
  have hm : HasSum (fun i ↦ ‖v i‖^2) ‖A‖ := by
    simpa only [v, norm_vectorProjector, TraceClass.norm_eq_trace_re_of_nonneg A hA] using
      positive_rankOne_mass hA A.2 b
  have hmd : HasSum (fun i ↦ ‖(1-P) (v i)‖^2) ‖sandwichCLM (1-P) (1-P) A‖ := by
    have h := Complex.hasSum_re (hd.mapL traceCLM)
    simpa only [traceCLM_vectorProjector, Complex.ofReal_re,
      TraceClass.norm_eq_trace_re_of_nonneg _ (sandwichCLM_nonneg hP.one_sub.isSelfAdjoint A hA)] using h
  have hprod := summable_norm_mul_of_square_sums (fun i ↦ ‖v i‖) (fun i ↦ ‖(1-P) (v i)‖)
    hm.summable hmd.summable (fun _ ↦ norm_nonneg _) (fun _ ↦ norm_nonneg _)
  have hnorm : Summable (fun i ↦ ‖vectorProjector (v i) - vectorProjector (P (v i))‖) :=
    (hprod.mul_left 2).of_nonneg_of_le (fun _ ↦ norm_nonneg _)
      (fun i ↦ norm_vectorProjector_sub_projection_le hP (v i))
  have hcs := tsum_mul_le_sqrt_mul_sqrt hm.summable hmd.summable
    (fun _ ↦ norm_nonneg _) (fun _ ↦ norm_nonneg _)
  rw [hm.tsum_eq, hmd.tsum_eq] at hcs
  calc
    _ = ‖(∑' i, (vectorProjector (v i) - vectorProjector (P (v i))))‖ := by rw [(hs.sub hc).tsum_eq]
    _ ≤ ∑' i, ‖vectorProjector (v i) - vectorProjector (P (v i))‖ := norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' i, 2 * (‖v i‖ * ‖(1-P) (v i)‖) :=
      hnorm.tsum_le_tsum (fun i ↦ norm_vectorProjector_sub_projection_le hP (v i)) (hprod.mul_left 2)
    _ = 2 * ∑' i, ‖v i‖ * ‖(1-P) (v i)‖ := tsum_mul_left
    _ ≤ _ := by nlinarith

theorem norm_sandwich_complement_eq {P : H →L[ℂ] H} (hP : IsStarProjection P)
    (A : TraceClass H) (hA : 0 ≤ A.1) :
    ‖sandwichCLM (1-P) (1-P) A‖ = ‖A‖ - ‖sandwichCLM P P A‖ := by
  rw [TraceClass.norm_eq_trace_re_of_nonneg _ (sandwichCLM_nonneg hP.one_sub.isSelfAdjoint A hA),
    TraceClass.norm_eq_trace_re_of_nonneg _ hA,
    TraceClass.norm_eq_trace_re_of_nonneg _ (sandwichCLM_nonneg hP.isSelfAdjoint A hA)]
  have h := congrArg Complex.re (traceCLM_projection_split hP A)
  simp only [Complex.add_re, traceCLM_apply] at h
  linarith

/-- The standard quantitative gentle bound with discarded trace written as
the difference of positive trace norms. -/
theorem gentle_compression {P : H →L[ℂ] H} (hP : IsStarProjection P)
    (A : TraceClass H) (hA : 0 ≤ A.1) :
    ‖A - sandwichCLM P P A‖ ≤
      2 * Real.sqrt (‖A‖ * (‖A‖ - ‖sandwichCLM P P A‖)) := by
  have h := norm_sub_sandwich_projection_le hP A hA
  rw [norm_sandwich_complement_eq hP A hA] at h
  rw [Real.sqrt_mul (norm_nonneg A)]
  simpa only [mul_assoc] using h

theorem gentle_compression_unit {P : H →L[ℂ] H} (hP : IsStarProjection P)
    (A : TraceClass H) (hA : 0 ≤ A.1) (hunit : ‖A‖ = 1) :
    ‖A - sandwichCLM P P A‖ ≤ 2 * Real.sqrt (1 - ‖sandwichCLM P P A‖) := by
  simpa only [hunit, one_mul] using gentle_compression hP A hA

end Cloning.InfiniteTraceClass
