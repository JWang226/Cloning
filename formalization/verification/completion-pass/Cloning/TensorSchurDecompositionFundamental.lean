import Cloning.TensorSchurDecomposition
import Cloning.TensorFundamentalBranchingMultiplicity

/-! Exhaustive multiplicity-free one-particle branching, with actual branch labels. -/
noncomputable section
open scoped BigOperators InnerProductSpace
namespace Cloning.TensorLie
open Cloning.PCT Cloning.YoungGeneral
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {n d : ℕ}

local instance : FiniteDimensional ℂ (TensorRegister n (Fin d)) :=
  (registerBasis (Fin n → Fin d)).toOrthonormalBasis.toBasis.finiteDimensional_of_finite

/-- Orthogonal unit highest vectors cannot occupy the same one-box highest line. -/
theorem fundamental_highest_not_orthogonal
    (Ω : TensorRegister n (Fin d)) (mu : Fin d → ℕ)
    (hΩnorm : ‖Ω‖ = 1)
    (hΩweight : ∀ a, collectiveGenerator n a a Ω = (mu a : ℂ) • Ω)
    (hΩraise : ∀ a b, a < b → collectiveGenerator n a b Ω = 0)
    (r : Fin d) (x y : TensorRegister (n + 1) (Fin d))
    (hx : x ∈ fundamentalHighestSpace Ω (addBox mu r))
    (hy : y ∈ fundamentalHighestSpace Ω (addBox mu r))
    (hxnorm : ‖x‖ = 1) (hynorm : ‖y‖ = 1) : ⟪x, y⟫_ℂ ≠ 0 := by
  intro horth
  let cx := ⟪Ω, lastSlice r x⟫_ℂ
  let cy := ⟪Ω, lastSlice r y⟫_ℂ
  have hcy : cy ≠ 0 := by
    intro hz
    have hy0 := highest_onebox_zero_of_coefficient_zero Ω mu hΩnorm hΩweight hΩraise r y hy hz
    simp only [hy0, norm_zero, zero_ne_one] at hynorm
  let z := cy • x - cx • y
  have hzmem : z ∈ fundamentalHighestSpace Ω (addBox mu r) :=
    (fundamentalHighestSpace Ω (addBox mu r)).sub_mem
      ((fundamentalHighestSpace Ω (addBox mu r)).smul_mem cy hx)
      ((fundamentalHighestSpace Ω (addBox mu r)).smul_mem cx hy)
  have hz : z = 0 := by
    apply highest_onebox_zero_of_coefficient_zero Ω mu hΩnorm hΩweight hΩraise r z hzmem
    simp only [z, map_sub, map_smul, inner_sub_right, inner_smul_right, cx, cy]
    ring
  have he := congrArg (fun v : TensorRegister (n + 1) (Fin d) => ⟪x, v⟫_ℂ) hz
  simp only [z, inner_sub_right, inner_smul_right, horth, mul_zero, sub_zero,
    inner_zero_right, inner_self_eq_norm_sq_to_K, hxnorm] at he
  norm_num at he
  exact hcy he

/-- The already constructed exhaustive physical decomposition of `S_mu ⊗ C^d`
has distinct one-box labels. Branch existence is not assumed here. -/
theorem exists_fundamental_multiplicityFree_decomposition
    (Ω : TensorRegister n (Fin d)) (mu : Fin d → ℕ)
    (hΩnorm : ‖Ω‖ = 1)
    (hΩweight : ∀ a, collectiveGenerator n a a Ω = (mu a : ℂ) • Ω)
    (hΩraise : ∀ a b, a < b → collectiveGenerator n a b Ω = 0) :
    ∃ L : List (PhysicalHighestTensor (n + 1) d), ∃ rows : Fin L.length ↪ Fin d,
      (∀ i, (L.get i).weight = addBox mu (rows i)) ∧
      L.Pairwise (fun H K => H.sector ⟂ K.sector) ∧
      physicalSectorListSpan L = tensorProductSector (cyclicSector Ω)
        (⊤ : Submodule ℂ (TensorRegister 1 (Fin d))) := by
  classical
  let W := tensorProductSector (cyclicSector Ω) (⊤ : Submodule ℂ (TensorRegister 1 (Fin d)))
  have hW : ∀ a b x, x ∈ W → collectiveGenerator (n + 1) a b x ∈ W := by
    intro a b x hx
    exact tensorProductSector_generator_invariant _ _
      (fun a b y hy => cyclicSector_generator_invariant Ω (fun a => (mu a : ℂ)) hΩweight hΩraise a b hy)
      (fun _ _ _ _ => Submodule.mem_top) a b hx
  obtain ⟨L, hLorth, hLspan⟩ := exists_physical_cyclic_decomposition W hW
  have hmem (i : Fin L.length) : (L.get i).vector ∈ W :=
    (physicalSector_le_listSpan (List.get_mem L i)).trans (le_of_eq hLspan) (L.get i).vector_mem
  have hrow (i : Fin L.length) : ∃ r : Fin d, (L.get i).weight = addBox mu r := by
    have hn : (L.get i).vector ≠ 0 := by
      intro hz
      have hh := (L.get i).norm_one
      simp only [hz, norm_zero, zero_ne_one] at hh
    obtain ⟨r, hr, _, _⟩ := highest_onebox_classification Ω mu hΩnorm hΩweight hΩraise
      (L.get i).vector (L.get i).weight (hmem i) (L.get i).cartan (L.get i).raising hn
    exact ⟨r, hr⟩
  choose rows hrows using hrow
  have hinj : Function.Injective rows := by
    intro i j hij
    by_contra hne
    have hOrth : (L.get i).sector ⟂ (L.get j).sector := by
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · exact hLorth.rel_get_of_lt hlt
      · exact (hLorth.rel_get_of_lt hgt).symm
    have hxi : (L.get i).vector ∈ fundamentalHighestSpace Ω (addBox mu (rows i)) := by
      refine ⟨hmem i, ?_, (L.get i).raising⟩
      intro a
      rw [← hrows i]
      exact (L.get i).cartan a
    have hxj : (L.get j).vector ∈ fundamentalHighestSpace Ω (addBox mu (rows i)) := by
      refine ⟨hmem j, ?_, (L.get j).raising⟩
      intro a
      rw [hij, ← hrows j]
      exact (L.get j).cartan a
    exact fundamental_highest_not_orthogonal Ω mu hΩnorm hΩweight hΩraise (rows i)
      (L.get i).vector (L.get j).vector hxi hxj (L.get i).norm_one (L.get j).norm_one
      (hOrth.inner_eq (L.get i).vector_mem (L.get j).vector_mem)
  exact ⟨L, ⟨rows, hinj⟩, hrows, hLorth, hLspan⟩

end Cloning.TensorLie
