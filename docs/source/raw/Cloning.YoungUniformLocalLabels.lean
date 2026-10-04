import Cloning.YoungUniformLocalCells
import Cloning.YoungUniformLocalPhysicalLattice

/-! Actual rounded lattice labels and their moving-parameter central limits. -/
noncomputable section
open scoped BigOperators Topology Classical
open Filter
namespace Cloning.YoungHyperplane
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

/-- The unique concrete cell label of a root-space point. -/
def sampleLabel (d N : ℕ) (p : Fin (d + 1) → ℝ) (x : rootSpace d) : Lattice d (N : ℤ) :=
  latticeCoordinates d N (YoungRounding.round
    (fun i ↦ Real.sqrt (N : ℝ) * x.1 i.castSucc + (N : ℝ) * p i.castSucc))

theorem mem_sampleCell_sampleLabel (d N : ℕ) (p : Fin (d + 1) → ℝ) (x : rootSpace d) :
    x ∈ sampleCell d N p (sampleLabel d N p x) := by
  unfold sampleCell sampleLabel
  simp only [Set.mem_setOf_eq, Equiv.symm_apply_apply]
  exact (YoungRounding.round_eq_iff _ _).mp rfl

/-- Cell centers converge to the sampled point, uniformly enough to allow an
arbitrary moving spectrum and arbitrary divergent sample sizes. -/
theorem sampleLabel_center_tendsto (d : ℕ) (n : ℕ → ℕ) (hn : Tendsto n atTop atTop)
    (p : ℕ → Fin (d + 1) → ℝ) (hp : ∀ k, ∑ i, p k i = 1) (x : rootSpace d)
    (i : Fin (d + 1)) :
    Tendsto (fun k ↦ (sampleCenter d (n k) (p k) (sampleLabel d (n k) (p k) x)).1 i)
      atTop (𝓝 (x.1 i)) := by
  apply tendsto_sub_nhds_zero_iff.mp
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _) ?_
    ((sample_mesh_tendsto_zero d).comp hn)
  filter_upwards [hn.eventually (eventually_gt_atTop 0)] with k hk
  simpa only [Real.norm_eq_abs, Int.cast_natCast] using
    sampleCenter_coordinate_distance d (n k) (by exact_mod_cast hk) (p k) (hp k)
      (sampleLabel d (n k) (p k) x) x (mem_sampleCell_sampleLabel d (n k) (p k) x) i

theorem lattice_ratio_eq_center (d N : ℕ) (hN : 0 < N)
    (p : Fin (d + 1) → ℝ) (hp : ∑ i, p i = 1) (μ : Lattice d (N : ℤ))
    (i : Fin (d + 1)) :
    (μ.1 i : ℝ) / N = p i + (sampleCenter d N p μ).1 i / Real.sqrt (N : ℝ) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  rw [sampleCenter_apply d N p hp μ]
  simp only [Int.cast_natCast]
  rw [div_div, ← pow_two, Real.sq_sqrt hn.le]
  field_simp
  ring

/-- Actual rounded counts divided by sample size track every moving spectrum
with a positive limiting normalization. -/
theorem sampleLabel_ratio_tendsto (d : ℕ) (n : ℕ → ℕ) (hn : Tendsto n atTop atTop)
    (p : ℕ → Fin (d + 1) → ℝ) (hp : ∀ k, ∑ i, p k i = 1)
    (p₀ : Fin (d + 1) → ℝ) (hlim : ∀ i, Tendsto (fun k ↦ p k i) atTop (𝓝 (p₀ i)))
    (x : rootSpace d) (i : Fin (d + 1)) :
    Tendsto (fun k ↦ ((sampleLabel d (n k) (p k) x).1 i : ℝ) / (n k : ℝ))
      atTop (𝓝 (p₀ i)) := by
  have hc := (sampleLabel_center_tendsto d n hn p hp x i).mul
    (YoungMultinomial.inv_sqrt_nat_tendsto_zero.comp hn)
  simp only [mul_zero] at hc
  have ht := (hlim i).add hc
  simp only [add_zero] at ht
  apply ht.congr'
  filter_upwards [hn.eventually (eventually_gt_atTop 0)] with k hk
  rw [lattice_ratio_eq_center d (n k) hk (p k) (hp k)]
  rfl

/-- Strict limiting positivity and ordering become genuine integer partition
constraints on all sufficiently fine sampled cells. -/
theorem eventually_sampleLabel_partition (d : ℕ) (n : ℕ → ℕ) (hn : Tendsto n atTop atTop)
    (p : ℕ → Fin (d + 1) → ℝ) (hp : ∀ k, ∑ i, p k i = 1)
    (p₀ : Fin (d + 1) → ℝ) (hp₀ : ∀ i, 0 < p₀ i) (hord : StrictAnti p₀)
    (hlim : ∀ i, Tendsto (fun k ↦ p k i) atTop (𝓝 (p₀ i))) (x : rootSpace d) :
    ∀ᶠ k in atTop,
      (∀ i, 0 ≤ (sampleLabel d (n k) (p k) x).1 i) ∧
      Antitone (sampleLabel d (n k) (p k) x).1 := by
  have hpos : ∀ᶠ k in atTop, ∀ i,
      0 < ((sampleLabel d (n k) (p k) x).1 i : ℝ) / (n k : ℝ) :=
    eventually_all.mpr fun i ↦ (sampleLabel_ratio_tendsto d n hn p hp p₀ hlim x i).eventually
      (eventually_gt_nhds (hp₀ i))
  have hanti : ∀ᶠ k in atTop, ∀ i j, i < j →
      ((sampleLabel d (n k) (p k) x).1 j : ℝ) / (n k : ℝ) <
        ((sampleLabel d (n k) (p k) x).1 i : ℝ) / (n k : ℝ) := by
    apply eventually_all.mpr
    intro i
    apply eventually_all.mpr
    intro j
    by_cases hij : i < j
    · have hd := (sampleLabel_ratio_tendsto d n hn p hp p₀ hlim x i).sub
        (sampleLabel_ratio_tendsto d n hn p hp p₀ hlim x j)
      filter_upwards [hd.eventually (eventually_gt_nhds (sub_pos.mpr (hord hij)))] with k hk
      intro _
      exact sub_pos.mp hk
    · exact Eventually.of_forall fun _ h ↦ (hij h).elim
  filter_upwards [hpos, hanti, hn.eventually (eventually_gt_atTop 0)] with k hkpos hkant hk
  have hnk : (0 : ℝ) < n k := by exact_mod_cast hk
  constructor
  · intro i
    exact_mod_cast (le_of_lt ((div_pos_iff_of_pos_right hnk).mp (hkpos i)))
  · intro i j hij
    rcases eq_or_lt_of_le hij with rfl | hlt
    · rfl
    · have h := (div_lt_div_iff_of_pos_right hnk).mp (hkant i j hlt)
      exact_mod_cast h.le

end Cloning.YoungHyperplane
