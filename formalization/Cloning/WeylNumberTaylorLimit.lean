import Cloning.WeylNumberBounds
import Cloning.TensorLocalUnitaryTail

/-! Uniform actual Weyl Taylor approximation in bounded displacement windows. -/
noncomputable section
open scoped InnerProductSpace Topology BigOperators
open Filter
namespace Cloning.MultimodeCoherent
open Cloning.MultimodeCoherentGaussianMixture
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {d : ℕ}

def numberTaylor (a : Fin d → ℂ) (k : Fin d → ℕ) (m : ℕ) : Fock d :=
  ∑ j ∈ Finset.range (m+1), ((j.factorial : ℝ)⁻¹) • numberPower a k j

theorem displacement_number_taylor_bound
    (B : ℝ) (hB : 0 ≤ B) (K m : ℕ)
    (a : Fin d → ℂ) (ha : ∑ i, ‖a i‖ ≤ B)
    (k : Fin d → ℕ) (hk : ∀ i, k i ≤ K) :
    ‖displacement a (numberBasis d k) - numberTaylor a k m‖ ≤
      Cloning.TensorLocalUnitary.uniformTaylorBound B K 1 m := by
  have h := displacement_taylor_vector_remainder a (Finsupp.single k 1) m
  simp only [numberVector_single, one_smul] at h
  change ‖displacement a (numberBasis d k) - numberTaylor a k m‖ ≤
    ‖numberPower a k (m+1)‖ / (m.factorial : ℝ) at h
  refine h.trans ?_
  unfold Cloning.TensorLocalUnitary.uniformTaylorBound
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  refine (numberPower_norm_le a (m+1) K k hk).trans ?_
  apply pow_le_pow_left₀ (by positivity)
  apply mul_le_mul
  · exact mul_le_mul_of_nonneg_left ha (by norm_num)
  · apply Real.sqrt_le_sqrt
    push_cast
    nlinarith [Nat.cast_nonneg (α := ℝ) K, Nat.cast_nonneg (α := ℝ) m]
  · positivity
  · positivity

/-- One Taylor order works for every amplitude in a fixed sum-norm ball and
every number state in a fixed occupation box. -/
theorem exists_uniform_weyl_taylor_order
    (B : ℝ) (hB : 0 ≤ B) (K : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ M : ℕ, ∀ m ≥ M, ∀ a : Fin d → ℂ, (∑ i, ‖a i‖) ≤ B →
      ∀ k : Fin d → ℕ, (∀ i, k i ≤ K) →
        ‖displacement a (numberBasis d k) - numberTaylor a k m‖ < ε := by
  obtain ⟨M, hM⟩ := Metric.tendsto_atTop.mp
    (Cloning.TensorLocalUnitary.uniformTaylorBound_tendsto B hB K 1) ε hε
  refine ⟨M, fun m hm a ha k hk => ?_⟩
  have he := hM m hm
  rw [Real.dist_eq, sub_zero, abs_of_nonneg
    (Cloning.TensorLocalUnitary.uniformTaylorBound_nonneg B hB K 1 m)] at he
  exact (displacement_number_taylor_bound B hB K m a ha k hk).trans_lt he

theorem numberTaylor_tendsto_displacement (a : Fin d → ℂ) (k : Fin d → ℕ) :
    Tendsto (numberTaylor a k) atTop (𝓝 (displacement a (numberBasis d k))) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨M, hM⟩ := exists_uniform_weyl_taylor_order
    (∑ i, ‖a i‖) (Finset.sum_nonneg fun _ _ => norm_nonneg _) (∑ i, k i) ε hε
  refine ⟨M, fun m hm => ?_⟩
  rw [dist_eq_norm, norm_sub_rev]
  exact hM m hm a le_rfl k (fun i => Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i))

end Cloning.MultimodeCoherent
