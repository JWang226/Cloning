import Cloning.WeylCharacterDimensionPhysical
import Cloning.TensorCartanSplitCoefficients

/-! Actual sector dimension ratios from the proved physical Weyl formula. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace Cloning.TensorLie
open Cloning.WeylCharacter
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {d : ℕ}

def rootHeightReal (a : PositiveRoot d) : ℝ := (a.val.2.val : ℝ) - a.val.1.val

theorem rootHeightReal_pos (a : PositiveRoot d) : 0 < rootHeightReal a := by
  unfold rootHeightReal
  apply sub_pos.mpr
  exact_mod_cast Fin.lt_def.mp a.property

/-- Exact quotient of actual Cartan source and target dimensions. -/
theorem partitionDimension_ratio_eq_rootProduct (mu nu : Fin d → ℕ)
    (hmu : Antitone mu) (hnu : Antitone nu) :
    (partitionDimension mu hmu : ℝ) /
      (partitionDimension (fun i => mu i + nu i) (sumPartition_antitone mu nu hmu hnu) : ℝ) =
    ∏ a : PositiveRoot d, (rootGap mu a + rootHeightReal a) /
      (rootGap mu a + rootGap nu a + rootHeightReal a) := by
  rw [partitionDimension_eq_dimensionProduct, partitionDimension_eq_dimensionProduct]
  unfold dimensionProduct
  rw [← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro a _
  have ha : rootHeightReal a ≠ 0 := (rootHeightReal_pos a).ne'
  change ((_ + _ - _)/(_ - _)) / ((_ + _ - _)/(_ - _)) = _
  simp only [Nat.cast_add]
  dsimp only [rootGap, rootHeightReal] at ha ⊢
  field_simp
  <;> ring

/-- Each shifted Weyl factor has the same limit as its unshifted root fraction. -/
theorem shifted_rootFraction_tendsto (mu nu : ℕ → Fin d → ℕ)
    (a : PositiveRoot d) (t : ℝ)
    (hgap : Tendsto (fun N => rootGap (mu N) a + rootGap (nu N) a) atTop atTop)
    (hfrac : Tendsto (fun N => rootFraction (mu N) (nu N) a) atTop (𝓝 t)) :
    Tendsto (fun N => (rootGap (mu N) a + rootHeightReal a) /
      (rootGap (mu N) a + rootGap (nu N) a + rootHeightReal a)) atTop (𝓝 t) := by
  have hz := (tendsto_inv_atTop_zero.comp hgap).const_mul (rootHeightReal a)
  simp only [mul_zero] at hz
  have hlim := (hfrac.add hz).div ((tendsto_const_nhds (x := (1:ℝ))).add hz) (by norm_num : (1:ℝ)+0 ≠ 0)
  simp only [mul_zero, add_zero, div_one] at hlim
  apply hlim.congr'
  filter_upwards [hgap.eventually (eventually_gt_atTop 0)] with N hN
  dsimp only [rootFraction, Pi.div_apply, Function.comp_apply]
  have hN0 : rootGap (mu N) a + rootGap (nu N) a ≠ 0 := hN.ne'
  field_simp
  <;> ring

/-- No dimension-ratio premise is supplied: the actual dimensions converge
from root fractions and diverging combined gaps. -/
theorem partitionDimension_ratio_tendsto (mu nu : ℕ → Fin d → ℕ)
    (hmu : ∀ N, Antitone (mu N)) (hnu : ∀ N, Antitone (nu N))
    (t : PositiveRoot d → ℝ)
    (hgap : ∀ a, Tendsto (fun N => rootGap (mu N) a + rootGap (nu N) a) atTop atTop)
    (hfrac : ∀ a, Tendsto (fun N => rootFraction (mu N) (nu N) a) atTop (𝓝 (t a))) :
    Tendsto (fun N => (partitionDimension (mu N) (hmu N) : ℝ) /
      (partitionDimension (fun i => mu N i + nu N i)
        (sumPartition_antitone (mu N) (nu N) (hmu N) (hnu N)) : ℝ))
      atTop (𝓝 (∏ a, t a)) := by
  have hp := tendsto_finset_prod Finset.univ (fun a _ => shifted_rootFraction_tendsto mu nu a (t a) (hgap a) (hfrac a))
  exact hp.congr' (Eventually.of_forall (fun N =>
    (partitionDimension_ratio_eq_rootProduct (mu N) (nu N) (hmu N) (hnu N)).symm))

/-- Divergence of the input gaps alone suffices for partitions. -/
theorem partitionDimension_ratio_tendsto_of_inputGap (mu nu : ℕ → Fin d → ℕ)
    (hmu : ∀ N, Antitone (mu N)) (hnu : ∀ N, Antitone (nu N))
    (t : PositiveRoot d → ℝ)
    (hgap : ∀ a, Tendsto (fun N => rootGap (mu N) a) atTop atTop)
    (hfrac : ∀ a, Tendsto (fun N => rootFraction (mu N) (nu N) a) atTop (𝓝 (t a))) :
    Tendsto (fun N => (partitionDimension (mu N) (hmu N) : ℝ) /
      (partitionDimension (fun i => mu N i + nu N i)
        (sumPartition_antitone (mu N) (nu N) (hmu N) (hnu N)) : ℝ))
      atTop (𝓝 (∏ a, t a)) := by
  apply partitionDimension_ratio_tendsto mu nu hmu hnu t _ hfrac
  intro a
  apply tendsto_atTop_mono (fun N => ?_) (hgap a)
  have hv : 0 ≤ rootGap (nu N) a := by
    unfold rootGap
    exact sub_nonneg.mpr (by exact_mod_cast hnu N a.property.le)
  exact le_add_of_nonneg_right hv

end Cloning.TensorLie
