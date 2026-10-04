import Cloning.TensorFundamentalBranchingHighest

/-! Each possible one-box branch has at most one physical highest line. -/
noncomputable section
open scoped BigOperators InnerProductSpace
namespace Cloning.TensorLie
open Cloning.YoungGeneral
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
variable {n d : ℕ}

/-- The actual simultaneous highest-weight kernel inside the physical product. -/
def fundamentalHighestSpace (Ω : TensorRegister n (Fin d)) (lambda : Fin d → ℕ) :
    Submodule ℂ (TensorRegister (n + 1) (Fin d)) where
  carrier := {x | x ∈ tensorProductSector (cyclicSector Ω)
      (⊤ : Submodule ℂ (TensorRegister 1 (Fin d))) ∧
    (∀ a, collectiveGenerator (n + 1) a a x = (lambda a : ℂ) • x) ∧
    (∀ a b, a < b → collectiveGenerator (n + 1) a b x = 0)}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    refine ⟨Submodule.add_mem _ hx.1 hy.1, ?_, ?_⟩
    · intro a
      simp only [map_add, hx.2.1 a, hy.2.1 a, smul_add]
    · intro a b hab
      simp only [map_add, hx.2.2 a b hab, hy.2.2 a b hab, add_zero]
  smul_mem' := by
    intro c x hx
    refine ⟨Submodule.smul_mem _ c hx.1, ?_, ?_⟩
    · intro a
      rw [map_smul, hx.2.1 a, smul_comm]
    · intro a b hab
      rw [map_smul, hx.2.2 a b hab, smul_zero]

/-- A single leading highest coefficient detects zero on the whole physical
highest-weight kernel, not just on selected basis vectors. -/
theorem highest_onebox_zero_of_coefficient_zero
    (Ω : TensorRegister n (Fin d)) (mu : Fin d → ℕ)
    (hΩnorm : ‖Ω‖ = 1)
    (hΩweight : ∀ a, collectiveGenerator n a a Ω = (mu a : ℂ) • Ω)
    (hΩraise : ∀ a b, a < b → collectiveGenerator n a b Ω = 0)
    (r : Fin d) (x : TensorRegister (n + 1) (Fin d))
    (hx : x ∈ fundamentalHighestSpace Ω (addBox mu r))
    (hzero : ⟪Ω, lastSlice r x⟫_ℂ = 0) : x = 0 := by
  apply highest_onebox_zero_of_lastSlice_zero Ω mu hΩnorm hΩweight hΩraise x r hx.1 hx.2.1 hx.2.2
  rw [maximal_lastSlice_highest Ω hΩnorm hΩraise x hx.1 hx.2.2 r
    (highest_onebox_lastSlice_vanish_above Ω mu hΩnorm hΩweight hΩraise x r hx.1 hx.2.1 hx.2.2),
    hzero, zero_smul]

/-- The highest-space dimension of every one-box candidate is at most one.
The proof constructs an injective complex-linear leading-coefficient map. -/
theorem fundamentalHighestSpace_finrank_le_one
    (Ω : TensorRegister n (Fin d)) (mu : Fin d → ℕ)
    (hΩnorm : ‖Ω‖ = 1)
    (hΩweight : ∀ a, collectiveGenerator n a a Ω = (mu a : ℂ) • Ω)
    (hΩraise : ∀ a b, a < b → collectiveGenerator n a b Ω = 0) (r : Fin d) :
    Module.finrank ℂ (fundamentalHighestSpace Ω (addBox mu r)) ≤ 1 := by
  let f : fundamentalHighestSpace Ω (addBox mu r) →ₗ[ℂ] ℂ := {
    toFun x := ⟪Ω, lastSlice r x⟫_ℂ
    map_add' x y := by simp only [Submodule.coe_add, map_add, inner_add_right]
    map_smul' c x := by
      simp only [Submodule.coe_smul, map_smul, inner_smul_right, RingHom.id_apply, smul_eq_mul] }
  have hf : Function.Injective f := by
    intro x y hxy
    apply sub_eq_zero.mp
    apply Subtype.ext
    apply highest_onebox_zero_of_coefficient_zero Ω mu hΩnorm hΩweight hΩraise r
      (x - y : fundamentalHighestSpace Ω (addBox mu r)) (x - y).property
    change f (x - y) = 0
    rw [map_sub, hxy, sub_self]
  simpa only [Module.finrank_self] using LinearMap.finrank_le_finrank_of_injective hf

/-- A weight which is not obtained by adding one box has no physical highest
vectors in the product, including no zero-support exceptional branch. -/
theorem fundamentalHighestSpace_eq_bot_of_not_addBox
    (Ω : TensorRegister n (Fin d)) (mu : Fin d → ℕ)
    (hΩnorm : ‖Ω‖ = 1)
    (hΩweight : ∀ a, collectiveGenerator n a a Ω = (mu a : ℂ) • Ω)
    (hΩraise : ∀ a b, a < b → collectiveGenerator n a b Ω = 0)
    (lambda : Fin d → ℕ) (hnot : ∀ r, lambda ≠ addBox mu r) :
    fundamentalHighestSpace Ω lambda = ⊥ := by
  classical
  apply le_antisymm _ bot_le
  intro x hx
  change x = 0
  by_contra hx0
  obtain ⟨r, he, _, _⟩ := highest_onebox_classification Ω mu hΩnorm hΩweight hΩraise
    x lambda hx.1 hx.2.1 hx.2.2 hx0
  exact hnot r he

end Cloning.TensorLie
