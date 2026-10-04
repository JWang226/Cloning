import Cloning.TensorCartanStateCoefficients
import Cloning.TensorCartanStateOccupation

/-! Actual physical Cartan output coefficients converge to the amplified thermal law. -/
noncomputable section
open scoped BigOperators InnerProductSpace Topology
open Filter
namespace Cloning.TensorLie
open Cloning.PCT Cloning.InfiniteTraceClass Cloning.TensorLAN
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {d : ℕ}
local instance (n d : ℕ) : FiniteDimensional ℂ (TensorRegister n (Fin d)) :=
  (registerBasis (Fin n → Fin d)).toOrthonormalBasis.toBasis.finiteDimensional_of_finite

theorem cutoffIndex_double_sum (R : ℕ) (f : HeightOccupation d R → HeightOccupation d R → ℂ) :
    (∑ j : CutoffIndex d R, ∑ k : CutoffIndex d R,
      f (cutoffOccupation d R j) (cutoffOccupation d R k)) = ∑ j, ∑ k, f j k := by
  simp_rw [(cutoffOccupation d R).sum_comp]
  exact (cutoffOccupation d R).sum_comp (fun j => ∑ k, f j k)

theorem occupationSplit_thermal_cutoff_matrix
    (t : PositiveRoot d → ℝ) (ht0 : ∀ a, 0 ≤ t a) (ht1 : ∀ a, t a ≤ 1)
    (p : Fin d → ℝ) (R : ℕ) (i l : CutoffIndex d R) :
    ((∏ a, t a : ℝ) : ℂ) *
      (∑ j : CutoffIndex d R, ∑ k : CutoffIndex d R,
        starRingEnd ℂ (occupationSplitMatrixElement t (cutoffWord d R i)
          (cutoffWord d R j) (cutoffWord d R k)) *
        (bosonicOccupationWeight p (cutoffOccupation d R j).val : ℂ) *
        occupationSplitMatrixElement t (cutoffWord d R l) (cutoffWord d R j) (cutoffWord d R k)) =
      if i = l then (amplifiedOccupationWeight t (rootBoltzmann p) (cutoffOccupation d R i).val : ℂ)
      else 0 := by
  simp only [cutoffWord, occupationSplitMatrixElement_eq_cutoffSplitAmplitude t ht0 ht1,
    bosonicOccupationWeight, wordBoltzmann_canonicalWord]
  rw [cutoffIndex_double_sum R (fun j k =>
    starRingEnd ℂ (cutoffSplitAmplitude t (cutoffOccupation d R i) j k) *
      (((∏ a, (1 - rootBoltzmann p a)) * ∏ a, rootBoltzmann p a ^ j.val a : ℝ) : ℂ) *
      cutoffSplitAmplitude t (cutoffOccupation d R l) j k),
    cutoffSplitAmplitude_thermal_matrix t (rootBoltzmann p) ht0 ht1]
  simp only [Equiv.apply_eq_iff_eq]

/-- Every fixed physical cutoff matrix coefficient converges to its explicit
amplified geometric coefficient. All sector dimensions, weights and frames are actual. -/
theorem cartanGibbsOutput_cutoff_coefficient_tendsto
    (mu nu : ℕ → Fin d → ℕ) (hmu : ∀ N, Antitone (mu N)) (hnu : ∀ N, Antitone (nu N))
    (δmu δnu : ℕ → ℝ) (hδmu : Tendsto δmu atTop atTop) (hδnu : Tendsto δnu atTop atTop)
    (hmuGap : ∀ᶠ N in atTop, ∀ a : PositiveRoot d, δmu N ≤ rootGap (mu N) a)
    (hnuGap : ∀ᶠ N in atTop, ∀ a : PositiveRoot d, δnu N ≤ rootGap (nu N) a)
    (t : PositiveRoot d → ℝ) (ht0 : ∀ a, 0 ≤ t a) (ht1 : ∀ a, t a ≤ 1)
    (ht : ∀ a, Tendsto (fun N => rootFraction (mu N) (nu N) a) atTop (𝓝 (t a)))
    (pN : ℕ → Fin d → ℝ) (p : Fin d → ℝ) (hp : ∀ a, 0 < p a) (hord : StrictAnti p)
    (hlim : ∀ a, Tendsto (fun N => pN N a) atTop (𝓝 (p a)))
    (R : ℕ) (i l : CutoffIndex d R) :
    Tendsto (fun N =>
      ⟪cutoffSectorFrame (partitionHighestTensor _ (sumPartition_antitone (mu N) (nu N) (hmu N) (hnu N)))
          (fun a => mu N a + nu N a) R i,
        (cartanGibbsOutput (mu N) (nu N) (hmu N) (hnu N) (pN N)).1
          (cutoffSectorFrame (partitionHighestTensor _ (sumPartition_antitone (mu N) (nu N) (hmu N) (hnu N)))
            (fun a => mu N a + nu N a) R l)⟫_ℂ)
      atTop (𝓝 (if i = l then
        (amplifiedOccupationWeight t (rootBoltzmann p) (cutoffOccupation d R i).val : ℂ) else 0)) := by
  have hd := partitionDimension_ratio_tendsto_of_inputGap mu nu hmu hnu t
    (fun a => tendsto_atTop_mono' atTop (hmuGap.mono (fun N hN => hN a)) hδmu) ht
  have hcoef (j k : CutoffIndex d R) :=
    ((cartanCutoffFrameMatrixElement_tendsto mu nu hmu hnu δmu δnu hδmu hδnu
      hmuGap hnuGap t ht R i j k).star.mul
      (Complex.continuous_ofReal.continuousAt.tendsto.comp
        (sectorOccupationWeight_tendsto mu hmu δmu hδmu hmuGap pN p hp hord hlim
          (cutoffOccupation d R j).val))).mul
      (cartanCutoffFrameMatrixElement_tendsto mu nu hmu hnu δmu δnu hδmu hδnu
        hmuGap hnuGap t ht R l j k)
  have hsum := tendsto_finset_sum Finset.univ (fun j _ =>
    tendsto_finset_sum Finset.univ (fun k _ => hcoef j k))
  have hall := (Complex.continuous_ofReal.continuousAt.tendsto.comp hd).mul hsum
  have he := occupationSplit_thermal_cutoff_matrix t ht0 ht1 p R i l
  simp only [starRingEnd_apply] at he
  rw [he] at hall
  apply hall.congr'
  have hpN : ∀ᶠ N in atTop, ∀ a, 0 < pN N a :=
    Filter.eventually_all.mpr (fun a => (hlim a).eventually (eventually_gt_nhds (hp a)))
  filter_upwards [partition_eventually_CutoffReady mu hmu δmu hδmu hmuGap R,
    partition_eventually_CutoffReady nu hnu δnu hδnu hnuGap R, hpN] with N hm hn hpN
  simpa only [Function.comp_apply, starRingEnd_apply, Complex.ofReal_div, RCLike.ofReal_div] using
    (cartanGibbsOutput_cutoff_coefficient (mu N) (nu N) (hmu N) (hnu N)
    (pN N) hpN R hm.1 hn.1 hm.2 hn.2 i l).symm

end Cloning.TensorLie
