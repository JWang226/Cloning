import Cloning.TensorHighestExtractionBasic

/-! Actual highest tensors in every nonzero invariant physical subspace. -/
noncomputable section
open scoped BigOperators InnerProductSpace
namespace Cloning.TensorLie
open Cloning.PCT
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {n d : ℕ}

local instance : FiniteDimensional ℂ (TensorRegister n (Fin d)) :=
  (registerBasis (Fin n → Fin d)).toOrthonormalBasis.toBasis.finiteDimensional_of_finite

/-- Minimum height among nonzero projected computational basis vectors yields
an actual joint highest vector. No spectral or representation premise is used. -/
theorem exists_highest_projection_basis
    (W : Submodule ℂ (TensorRegister n (Fin d)))
    (hW : ∀ a b x, x ∈ W → collectiveGenerator n a b x ∈ W)
    (hWne : W ≠ ⊥) :
    ∃ w : Fin n → Fin d, W.starProjection (registerBasis _ w) ≠ 0 ∧
      ∀ a b, a < b → collectiveGenerator n a b (W.starProjection (registerBasis _ w)) = 0 := by
  classical
  let S := Finset.univ.filter (fun w : Fin n → Fin d => W.starProjection (registerBasis _ w) ≠ 0)
  have hS : S.Nonempty := by
    obtain ⟨w, hw⟩ := invariant_exists_projection_basis_ne_zero W hWne
    exact ⟨w, by simpa only [S, Finset.mem_filter, Finset.mem_univ, true_and] using hw⟩
  obtain ⟨w, hw, hmin⟩ := S.exists_min_image physicalWordHeight hS
  have hwne : W.starProjection (registerBasis _ w) ≠ 0 := (Finset.mem_filter.mp hw).2
  refine ⟨w, hwne, ?_⟩
  intro a b hab
  let Ω := W.starProjection (registerBasis (Fin n → Fin d) w)
  have hweight : ∀ i, collectiveGenerator n i i Ω = (occupancy w i : ℂ) • Ω :=
    invariant_projection_basis_cartan W hW w
  by_contra hz
  obtain ⟨v, hv⟩ : ∃ v : Fin n → Fin d, collectiveGenerator n a b Ω v ≠ 0 := by
    by_contra! hn
    apply hz
    ext v
    exact hn v
  have hvW : collectiveGenerator n a b Ω ∈ W :=
    hW a b Ω (W.starProjection_apply_mem _)
  have hvS : v ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    projection_basis_ne_zero_of_coefficient W hvW v hv⟩
  rw [collectiveGenerator_apply] at hv
  obtain ⟨t, _, ht⟩ := Finset.exists_ne_zero_of_sum_ne_zero hv
  have hva : v t = a := by
    by_contra h
    simp only [h, if_false, ne_eq, not_true_eq_false] at ht
  have hu : Ω (Function.update v t b) ≠ 0 := by simpa only [hva, if_true] using ht
  have hocc := cartan_weight_coefficient Ω (occupancy w) hweight (Function.update v t b) hu
  have hheight : physicalWordHeight (Function.update v t b) = physicalWordHeight w := by
    simp only [physicalWordHeight_eq_occupancy, hocc]
  have he := physicalWordHeight_update v t b
  rw [hheight, hva] at he
  have hle := hmin v hvS
  have habv : a.val < b.val := hab
  omega

/-- Every nonzero subspace invariant under the actual tensor matrix units
contains a unit highest tensor of a genuine natural partition of `n`. -/
theorem exists_partitionHighest_in_invariant
    (W : Submodule ℂ (TensorRegister n (Fin d)))
    (hW : ∀ a b x, x ∈ W → collectiveGenerator n a b x ∈ W)
    (hWne : W ≠ ⊥) :
    ∃ mu : Fin d → ℕ, Antitone mu ∧ (∑ a, mu a) = n ∧
      ∃ Ω : TensorRegister n (Fin d), Ω ∈ W ∧ ‖Ω‖ = 1 ∧
        (∀ a, collectiveGenerator n a a Ω = (mu a : ℂ) • Ω) ∧
        (∀ a b, a < b → collectiveGenerator n a b Ω = 0) := by
  obtain ⟨w, hw, hraise⟩ := exists_highest_projection_basis W hW hWne
  let x := W.starProjection (registerBasis (Fin n → Fin d) w)
  let Ω := (‖x‖⁻¹ : ℂ) • x
  have hΩ : ‖Ω‖ = 1 := norm_smul_inv_norm hw
  have hweight : ∀ a, collectiveGenerator n a a Ω = (occupancy w a : ℂ) • Ω := by
    intro a
    simp only [Ω, map_smul, invariant_projection_basis_cartan W hW, x]
    exact smul_comm _ _ _
  have hΩraise : ∀ a b, a < b → collectiveGenerator n a b Ω = 0 := by
    intro a b hab
    simp only [Ω, x, map_smul, hraise a b hab, smul_zero]
  refine ⟨occupancy w, highest_weight_antitone Ω (occupancy w) hweight hΩraise hΩ,
    sum_occupancy w, Ω, W.smul_mem _ (W.starProjection_apply_mem _), hΩ, hweight, hΩraise⟩

end Cloning.TensorLie
