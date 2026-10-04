import Cloning.YoungHyperplaneSampling
import Cloning.YoungMultinomialLocalLimit

/-! Quantitative control of every rescaled lattice cell in the actual root
hyperplane, including its dependent final coordinate. -/

noncomputable section
open scoped BigOperators Topology Classical
open Filter
namespace Cloning.YoungHyperplane
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

/-- Head coordinates of the cell center are within half the scaled mesh. -/
theorem sampleCenter_head_distance (d : ℕ) (N : ℤ) (hN : 0 < (N : ℝ))
    (p : Fin (d + 1) → ℝ) (hp : ∑ i, p i = 1) (μ : Lattice d N)
    (x : rootSpace d) (hx : x ∈ sampleCell d N p μ) (i : Fin d) :
    |(sampleCenter d N p μ).1 i.castSucc - x.1 i.castSucc| ≤ 1 / (2 * Real.sqrt (N : ℝ)) := by
  have hs : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hN
  have hi : (μ.1 i.castSucc : ℝ) - 1 / 2 ≤
      Real.sqrt (N : ℝ) * x.1 i.castSucc + (N : ℝ) * p i.castSucc ∧
      Real.sqrt (N : ℝ) * x.1 i.castSucc + (N : ℝ) * p i.castSucc <
        (μ.1 i.castSucc : ℝ) + 1 / 2 := hx i (Set.mem_univ i)
  rw [sampleCenter_apply d N p hp μ]
  have heq : ((μ.1 i.castSucc : ℝ) - N * p i.castSucc) / Real.sqrt (N : ℝ) - x.1 i.castSucc =
      ((μ.1 i.castSucc : ℝ) - N * p i.castSucc - Real.sqrt (N : ℝ) * x.1 i.castSucc) /
        Real.sqrt (N : ℝ) := by field_simp
  rw [heq, abs_div, abs_of_pos hs]
  have hb : |(μ.1 i.castSucc : ℝ) - N * p i.castSucc - Real.sqrt (N : ℝ) * x.1 i.castSucc| ≤ 1 / 2 :=
    abs_le.mpr ⟨by linarith [hi.2], by linarith [hi.1]⟩
  calc
    _ ≤ (1 / 2) / Real.sqrt (N : ℝ) := div_le_div_of_nonneg_right hb hs.le
    _ = _ := by ring

/-- The dependent last coordinate has the sum of the head mesh errors. -/
theorem sampleCenter_last_distance (d : ℕ) (N : ℤ) (hN : 0 < (N : ℝ))
    (p : Fin (d + 1) → ℝ) (hp : ∑ i, p i = 1) (μ : Lattice d N)
    (x : rootSpace d) (hx : x ∈ sampleCell d N p μ) :
    |(sampleCenter d N p μ).1 (Fin.last d) - x.1 (Fin.last d)| ≤
      (d : ℝ) / (2 * Real.sqrt (N : ℝ)) := by
  have hz := (sampleCenter d N p μ).2
  have hxx := x.2
  change (∑ i, (sampleCenter d N p μ).1 i) = 0 at hz
  change (∑ i, x.1 i) = 0 at hxx
  rw [Fin.sum_univ_castSucc] at hz hxx
  have heq : (sampleCenter d N p μ).1 (Fin.last d) - x.1 (Fin.last d) =
      -(∑ i : Fin d, ((sampleCenter d N p μ).1 i.castSucc - x.1 i.castSucc)) := by
    rw [Finset.sum_sub_distrib]
    linarith
  rw [heq, abs_neg]
  calc
    _ ≤ ∑ i : Fin d, |(sampleCenter d N p μ).1 i.castSucc - x.1 i.castSucc| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin d, 1 / (2 * Real.sqrt (N : ℝ)) := by
      exact Finset.sum_le_sum fun i _ ↦ sampleCenter_head_distance d N hN p hp μ x hx i
    _ = _ := by simp; ring

/-- A single bound controls every coordinate, with no discarded last row. -/
theorem sampleCenter_coordinate_distance (d : ℕ) (N : ℤ) (hN : 0 < (N : ℝ))
    (p : Fin (d + 1) → ℝ) (hp : ∑ i, p i = 1) (μ : Lattice d N)
    (x : rootSpace d) (hx : x ∈ sampleCell d N p μ) (i : Fin (d + 1)) :
    |(sampleCenter d N p μ).1 i - x.1 i| ≤
      ((d : ℝ) + 1) / (2 * Real.sqrt (N : ℝ)) := by
  refine Fin.lastCases ?_ (fun j ↦ ?_) i
  · exact (sampleCenter_last_distance d N hN p hp μ x hx).trans
      (div_le_div_of_nonneg_right (by linarith) (by positivity))
  · exact (sampleCenter_head_distance d N hN p hp μ x hx j).trans
      (div_le_div_of_nonneg_right (show (1 : ℝ) ≤ (d : ℝ) + 1 from le_add_of_nonneg_left (Nat.cast_nonneg d)) (by positivity))

/-- A bounded set of cell points gives a bounded set of centers. -/
theorem sampleCenter_coordinate_bound (d : ℕ) (N : ℤ) (hN : 0 < (N : ℝ))
    (p : Fin (d + 1) → ℝ) (hp : ∑ i, p i = 1) (μ : Lattice d N)
    (x : rootSpace d) (hx : x ∈ sampleCell d N p μ) (R : ℝ)
    (hR : ∀ i, |x.1 i| ≤ R) (i : Fin (d + 1)) :
    |(sampleCenter d N p μ).1 i| ≤ R + ((d : ℝ) + 1) / (2 * Real.sqrt (N : ℝ)) := by
  calc
    _ ≤ |(sampleCenter d N p μ).1 i - x.1 i| + |x.1 i| := by
      simpa only [sub_add_cancel] using
        abs_add_le ((sampleCenter d N p μ).1 i - x.1 i) (x.1 i)
    _ ≤ ((d : ℝ) + 1) / (2 * Real.sqrt (N : ℝ)) + R :=
      add_le_add (sampleCenter_coordinate_distance d N hN p hp μ x hx i) (hR i)
    _ = _ := by ring

theorem sample_mesh_tendsto_zero (d : ℕ) :
    Tendsto (fun N : ℕ ↦ ((d : ℝ) + 1) / (2 * Real.sqrt (N : ℝ))) atTop (𝓝 0) := by
  simpa only [div_mul_eq_div_mul_one_div, one_div, mul_zero] using
    YoungMultinomial.inv_sqrt_nat_tendsto_zero.const_mul (((d : ℝ) + 1) / 2)

end Cloning.YoungHyperplane
