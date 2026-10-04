import Cloning.YoungFlatCouplingPhysical

/-! Compatibility with probability tending to one for the actual exact-marginal
flat Young coupling. -/
noncomputable section
open scoped BigOperators Topology Classical ENNReal
open MeasureTheory Filter
namespace Cloning.YoungFlatCoupling
open Cloning.YoungHyperplane Cloning.YoungGeneral Cloning.TensorLie Cloning.YoungFlat Cloning.TensorCloning
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

def flatBadPair (d N M : ℕ) (s : Shape (d+1) N) (t : Shape (d+1) M) : Prop :=
  ¬PartitionCompatible (fun i => (s i).val) (fun i => (t i).val)

def commonPointBad (d N M : ℕ) (x : rootSpace d) : Prop :=
  flatBadPair d N M (sampleShape d N (flatSpectrum (d+1)) x)
    (sampleShape d M (flatSpectrum (d+1)) x)

theorem measurableSet_commonPointBad (d N M : ℕ) :
    MeasurableSet {x | commonPointBad d N M x} :=
  measurableSet_relation _ _ (measurable_sampleShape d N _) (measurable_sampleShape d M _)
    (flatBadPair d N M)

theorem positiveFlatCoupling_incompatible_le (d N M : ℕ) (hN : 0<N) (hM : 0<M) :
    incompatibleMass (d+1) N M (positiveFlatCoupling d N M hN hM) ≤
      (∫ x, if commonPointBad d N M x then min (flatDensity d N x) (flatDensity d M x) else 0) +
        (1/2 : ℝ) * ∫ x, |flatDensity d N x-flatDensity d M x| := by
  have he := densityCoupling_event_le volume (sampleShape d N (flatSpectrum (d+1)))
    (sampleShape d M (flatSpectrum (d+1))) (flatDensity d N) (flatDensity d M)
    (measurable_sampleShape d N _) (measurable_sampleShape d M _)
    (integrable_flatDensity d N hN) (integrable_flatDensity d M hM)
    (flatDensity_nonneg d N) (flatDensity_nonneg d M)
    (integral_flatDensity d N hN) (integral_flatDensity d M hM) (flatBadPair d N M)
  have hs : incompatibleMass (d+1) N M (positiveFlatCoupling d N M hN hM) =
      ∑ z, if flatBadPair d N M z.1 z.2 then (positiveFlatCoupling d N M hN hM z).toReal else 0 := by
    unfold incompatibleMass
    apply Finset.sum_congr rfl
    intro z _
    unfold flatBadPair
    split_ifs <;> simp_all
  rw [hs]
  exact he

theorem flatCoupling_incompatible_le (d N M : ℕ) (hN : 0<N) (hM : 0<M) :
    incompatibleMass (d+1) N M (flatCoupling d N M) ≤
      ((∫ x, if commonPointBad d N M x then limitDensity d x else 0) +
        ∫ x, |flatDensity d N x-limitDensity d x|) +
      (1/2 : ℝ) * ((∫ x, |flatDensity d N x-limitDensity d x|) +
        ∫ x, |flatDensity d M x-limitDensity d x|) := by
  rw [flatCoupling_eq_positive d N M hN hM]
  apply (positiveFlatCoupling_incompatible_le d N M hN hM).trans
  exact add_le_add (overlap_event_le_limit volume _ _ _
      (integrable_flatDensity d N hN) (integrable_flatDensity d M hM) (integrable_limitDensity d)
      _ (measurableSet_commonPointBad d N M))
    (mul_le_mul_of_nonneg_left (l1_between_le volume _ _ _
      (integrable_flatDensity d N hN) (integrable_flatDensity d M hM) (integrable_limitDensity d)) (by norm_num))

/-- The two physical marginals are exact for every sample size, while the mass
of pairs without a literal Cartan inclusion tends to zero. -/
theorem flatCoupling_incompatibleMass_tendsto (d : ℕ) (m : ℕ → ℕ)
    (hm : Tendsto m atTop atTop) (γ : ℝ) (hγ : 1<γ)
    (hratio : Tendsto (fun N : ℕ => (m N : ℝ)/(N : ℝ)) atTop (𝓝 γ)) :
    Tendsto (fun N => incompatibleMass (d+1) N (m N) (flatCoupling d N (m N))) atTop (𝓝 0) := by
  have hbad : Tendsto (fun N => ∫ x, if commonPointBad d N (m N) x then limitDensity d x else 0)
      atTop (𝓝 0) := by
    apply limit_bad_event_tendsto_zero volume _ (integrable_limitDensity d) (limitDensity_nonneg d)
      _ (fun N => measurableSet_commonPointBad d N (m N))
    intro x hx
    have hstrict : StrictAnti (fun i => x.1 i) := by
      by_contra hn
      exact hx (limitDensity_eq_zero_of_not_strictAnti d x hn)
    filter_upwards [eventually_flat_sampleShape_compatible d m hm γ hγ hratio x hstrict] with N hN
    exact not_not.mpr hN
  have hsource := flatDensity_l1_tendsto d
  have htarget := (flatDensity_l1_tendsto d).comp hm
  have hbound : Tendsto (fun N =>
      ((∫ x, if commonPointBad d N (m N) x then limitDensity d x else 0) +
        ∫ x, |flatDensity d N x-limitDensity d x|) +
      (1/2 : ℝ)*((∫ x, |flatDensity d N x-limitDensity d x|) +
        ∫ x, |flatDensity d (m N) x-limitDensity d x|)) atTop (𝓝 0) := by
    simpa only [add_zero, zero_add, mul_zero] using (hbad.add hsource).add ((hsource.add htarget).const_mul (1/2 : ℝ))
  apply squeeze_zero' (Eventually.of_forall fun N => Finset.sum_nonneg fun z _ => by
    split_ifs <;> positivity) ?_ hbound
  filter_upwards [eventually_gt_atTop 0, hm.eventually (eventually_gt_atTop 0)] with N hN hM
  exact flatCoupling_incompatible_le d N (m N) hN hM

end Cloning.YoungFlatCoupling
