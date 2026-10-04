import Cloning.TensorCyclicSector

/-! Actual invariant-subspace irreducibility of finite physical cyclic sectors. -/
noncomputable section
open scoped InnerProductSpace
namespace Cloning.TensorLie
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {n d : ℕ}

local instance : FiniteDimensional ℂ (TensorRegister n (Fin d)) :=
  (Cloning.PCT.registerBasis (Fin n → Fin d)).toOrthonormalBasis.toBasis.finiteDimensional_of_finite

/-- Invariance under all matrix units also gives invariance under their
adjoints, so the actual orthogonal projection commutes with every generator. -/
theorem invariant_starProjection_commutes
    (W : Submodule ℂ (TensorRegister n (Fin d)))
    (hW : ∀ a b x, x ∈ W → collectiveGenerator n a b x ∈ W)
    (a b : Fin d) (x : TensorRegister n (Fin d)) :
    W.starProjection (collectiveGenerator n a b x) =
      collectiveGenerator n a b (W.starProjection x) := by
  apply Submodule.eq_starProjection_of_mem_orthogonal
  · exact hW a b _ (W.starProjection_apply_mem x)
  · rw [← map_sub]
    apply (W.mem_orthogonal _).mpr
    intro y hy
    rw [← ContinuousLinearMap.adjoint_inner_left, collectiveGenerator_adjoint]
    exact W.inner_right_of_mem_orthogonal (hW b a y hy)
      (Submodule.sub_starProjection_mem_orthogonal x)

/-- A nonzero normalized highest tensor generates an irreducible physical
matrix-unit module. Every invariant subspace is zero or the full cyclic sector. -/
theorem cyclicSector_irreducible
    (Ω : TensorRegister n (Fin d)) (hΩ : ‖Ω‖ = 1)
    (hraise : ∀ a b, a < b → collectiveGenerator n a b Ω = 0)
    (W : Submodule ℂ (TensorRegister n (Fin d))) (hWS : W ≤ cyclicSector Ω)
    (hW : ∀ a b x, x ∈ W → collectiveGenerator n a b x ∈ W) :
    W = ⊥ ∨ W = cyclicSector Ω := by
  obtain ⟨c, hc⟩ := cyclicSector_commutant_scalar Ω hΩ hraise W.starProjection.toLinearMap
    (fun x _ => hWS (W.starProjection_apply_mem x))
    (fun a b x _ => invariant_starProjection_commutes W hW a b x)
  by_cases hzero : W = ⊥
  · exact Or.inl hzero
  · right
    obtain ⟨x, hxW, hx0⟩ := W.ne_bot_iff.mp hzero
    have hcx : c • x = x := (hc x (hWS hxW)).symm.trans
      (Submodule.starProjection_eq_self_iff.mpr hxW)
    have hc1 : c = 1 := by
      have he : (c - 1) • x = 0 := by rw [sub_smul, one_smul, hcx, sub_self]
      exact sub_eq_zero.mp ((smul_eq_zero.mp he).resolve_right hx0)
    apply le_antisymm hWS
    intro y hy
    have he : W.starProjection y = y := by simpa only [hc1, one_smul] using hc y hy
    exact Submodule.starProjection_eq_self_iff.mp he

/-- The constructed highest tensor of every finite partition generates an
irreducible actual tensor sector, including the one-dimensional empty tensor. -/
theorem partition_cyclicSector_irreducible {d : ℕ}
    (mu : Fin d → ℕ) (hmu : Antitone mu)
    (W : Submodule ℂ (TensorRegister (∑ i, mu i) (Fin d)))
    (hWS : W ≤ cyclicSector (partitionHighestTensor mu hmu))
    (hW : ∀ a b x, x ∈ W → collectiveGenerator (∑ i, mu i) a b x ∈ W) :
    W = ⊥ ∨ W = cyclicSector (partitionHighestTensor mu hmu) :=
  cyclicSector_irreducible _ (partitionHighestTensor_norm mu hmu)
    (partitionHighestTensor_raising_zero mu hmu) W hWS hW

/-- No matrix-unit-invariant sector copy constructed here is the zero space. -/
theorem partition_cyclicSector_ne_bot {d : ℕ} (mu : Fin d → ℕ) (hmu : Antitone mu) :
    cyclicSector (partitionHighestTensor mu hmu) ≠ ⊥ := by
  intro h
  have hz : partitionHighestTensor mu hmu = 0 := by
    simpa only [h, Submodule.mem_bot] using highest_mem_cyclicSector (partitionHighestTensor mu hmu)
  have hn := partitionHighestTensor_norm mu hmu
  rw [hz, norm_zero] at hn
  norm_num at hn

end Cloning.TensorLie
