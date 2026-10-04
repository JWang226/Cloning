import Cloning.WeylMultimodeDisplacement
import Cloning.WeylContinuity

/-! Strong continuity and vacuum generation for the constructed Weyl unitaries. -/

noncomputable section
open scoped InnerProductSpace Topology BigOperators

namespace Cloning.MultimodeCoherent
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

variable {d : ℕ}

@[simp] theorem displacement_dist (a : Fin d → ℂ) (v w : (Fock d)) :
    dist (displacement a v) (displacement a w) = dist v w := by
  simp only [dist_eq_norm, ← map_sub, displacement_norm]

theorem continuous_displacementPhase (z : Fin d → ℂ) : Continuous (fun a => displacementPhase a z) := by
  unfold displacementPhase
  exact continuous_finset_prod _ (fun i _ =>
    (ComplexCoherent.continuous_displacementPhase (z i)).comp (continuous_apply i))

theorem continuous_displacement_coherentVector (z : Fin d → ℂ) :
    Continuous (fun a => displacement a (coherentVector z)) := by
  simp_rw [displacement_coherentVector]
  exact (continuous_displacementPhase z).smul
    ((continuous_coherentVector d).comp (continuous_id.add continuous_const))

theorem continuous_displacement_combination (c : (Fin d → ℂ) →₀ ℂ) :
    Continuous (fun a => displacement a (coherentCombination c)) := by
  simp only [coherentCombination, Finsupp.linearCombination_apply, Finsupp.sum, map_sum, map_smul]
  exact continuous_finset_sum _ (fun z _ =>
    continuous_const.smul (continuous_displacement_coherentVector z))

/-- Weyl displacement is strongly continuous on every actual multimode Fock vector.
The proof upgrades continuity on coherent superpositions using their density
and the uniform isometric norm bound. -/
theorem continuous_displacement (v : (Fock d)) : Continuous (fun a => displacement a v) := by
  rw [Metric.continuous_iff]
  intro a ε hε
  obtain ⟨c, hc⟩ := coherentCombination_dense.exists_dist_lt v (show 0 < ε / 4 by positivity)
  obtain ⟨δ, hδ, hd⟩ := Metric.continuous_iff.mp (continuous_displacement_combination c)
    a (ε / 2) (by positivity)
  refine ⟨δ, hδ, fun b hb => ?_⟩
  have hb' := hd b hb
  calc
    dist (displacement b v) (displacement a v) ≤
        dist (displacement b v) (displacement b (coherentCombination c)) +
          dist (displacement b (coherentCombination c)) (displacement a (coherentCombination c)) +
          dist (displacement a (coherentCombination c)) (displacement a v) :=
      dist_triangle4 _ _ _ _
    _ < ε := by
      rw [displacement_dist, displacement_dist, dist_comm (coherentCombination c) v]
      linarith

/-- The vacuum's Weyl orbit is exactly the family of normalized coherent vectors. -/
@[simp] theorem displacement_vacuum (a : Fin d → ℂ) :
    displacement a (coherentVector 0) = coherentVector a := by
  simp [displacement_coherentVector]

/-- The vacuum is cyclic for the constructed Weyl representation. -/
theorem displacement_vacuum_cyclic :
    (Submodule.span ℂ (Set.range (fun a : Fin d → ℂ => displacement a (coherentVector 0)))).topologicalClosure
      = ⊤ := by
  simpa only [displacement_vacuum] using coherentVector_dense_span d

/-- The multimode vacuum characteristic function is the product Gaussian,
with the exact normalization in every mode. -/
theorem vacuum_characteristic (a : Fin d → ℂ) :
    ⟪coherentVector 0, displacement a (coherentVector 0)⟫_ℂ =
      ∏ i, (Real.exp (-‖a i‖ ^ 2 / 2) : ℂ) := by
  rw [displacement_vacuum]
  simp only [coherentVector, inner_tensorVector, Pi.zero_apply]
  apply Finset.prod_congr rfl
  intro i _
  simpa only [ComplexCoherent.displacement_vacuum] using
    ComplexCoherent.vacuum_characteristic (a i)

end Cloning.MultimodeCoherent
