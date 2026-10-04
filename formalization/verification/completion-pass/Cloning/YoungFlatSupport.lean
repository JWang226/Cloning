import Cloning.YoungFlatUniform

/-! The explicit flat limiting density is supported on strictly ordered shapes. -/
noncomputable section
open scoped BigOperators Topology Classical
open MeasureTheory Filter
namespace Cloning.YoungFlat
open Cloning.TensorLie Cloning.YoungHyperplane
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

theorem vandermondeFactor_eq_zero_of_not_strictAnti {r : ℕ} (x : Fin r → ℝ)
    (hx : ¬ StrictAnti x) : vandermondeFactor x = 0 := by
  simp only [StrictAnti] at hx
  push_neg at hx
  obtain ⟨i,j,hij,hle⟩ := hx
  unfold vandermondeFactor
  apply Finset.prod_eq_zero (Finset.mem_univ (⟨(i,j),hij⟩ : PositiveRoot r))
  simp only [max_eq_right (sub_nonpos.mpr hle), ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, zero_div]

theorem limitDensity_eq_zero_of_not_strictAnti (d : ℕ) (x : rootSpace d)
    (hx : ¬ StrictAnti (fun i ↦ x.1 i)) : limitDensity d x = 0 := by
  rw [limitDensity, vandermondeFactor_eq_zero_of_not_strictAnti _ hx, mul_zero]

theorem isOpen_strictChamber (d : ℕ) :
    IsOpen {x : rootSpace d | StrictAnti (fun i ↦ x.1 i)} := by
  have he : {x : rootSpace d | StrictAnti (fun i ↦ x.1 i)} =
      ⋂ i : Fin (d+1), ⋂ j : Fin (d+1), {x : rootSpace d | i<j → x.1 j<x.1 i} := by
    ext x
    simp [StrictAnti]
  rw [he]
  apply isOpen_iInter_of_finite
  intro i
  apply isOpen_iInter_of_finite
  intro j
  by_cases hij : i<j
  · simp only [hij, true_implies]
    exact isOpen_lt ((PiLp.continuous_apply 2 _ j).comp continuous_subtype_val)
      ((PiLp.continuous_apply 2 _ i).comp continuous_subtype_val)
  · simp [hij]

/-- The limiting density assigns zero mass to every collision wall and to every unordered point. -/
theorem integral_limitDensity_outside_strictChamber (d : ℕ) :
    (∫ x in {x : rootSpace d | ¬ StrictAnti (fun i ↦ x.1 i)}, limitDensity d x) = 0 := by
  apply integral_eq_zero_of_ae
  filter_upwards [ae_restrict_mem (isOpen_strictChamber d).measurableSet.compl] with x hx
  exact limitDensity_eq_zero_of_not_strictAnti d x hx

end Cloning.YoungFlat
