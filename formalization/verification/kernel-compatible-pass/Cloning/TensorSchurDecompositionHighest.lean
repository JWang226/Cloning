import Cloning.TensorSchurDecompositionFundamental

/-! Detecting highest weights in an exhaustive physical sector decomposition. -/
noncomputable section
open scoped BigOperators InnerProductSpace
namespace Cloning.TensorLie
open Cloning.YoungGeneral
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {n d : ℕ}

theorem highest_inner_eq_zero_of_weight_ne
    (H : PhysicalHighestTensor n d) (x : TensorRegister n (Fin d)) (lambda : Fin d → ℕ)
    (hweight : ∀ a, collectiveGenerator n a a x = (lambda a : ℂ) • x)
    (hne : H.weight ≠ lambda) : ⟪H.vector, x⟫_ℂ = 0 := by
  classical
  obtain ⟨a, ha⟩ : ∃ a, H.weight a ≠ lambda a := by
    by_contra! h
    exact hne (funext h)
  have he := collectiveGenerator_inner_adjoint a a H.vector x
  rw [H.cartan, hweight, inner_smul_left, inner_smul_right] at he
  simp only [map_natCast] at he
  have hc : ((H.weight a : ℂ) - lambda a) * ⟪H.vector, x⟫_ℂ = 0 := by
    rw [sub_mul, he, sub_self]
  have hn : (H.weight a : ℂ) - lambda a ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast ha)
  exact (mul_eq_zero.mp hc).resolve_left hn

theorem highest_mem_orthogonal_cyclic_of_weight_ne
    (H : PhysicalHighestTensor n d) (x : TensorRegister n (Fin d)) (lambda : Fin d → ℕ)
    (hweight : ∀ a, collectiveGenerator n a a x = (lambda a : ℂ) • x)
    (hraise : ∀ a b, a < b → collectiveGenerator n a b x = 0)
    (hne : H.weight ≠ lambda) : x ∈ H.sectorᗮ := by
  apply (H.sector.mem_orthogonal x).mpr
  intro y hy
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨w, rfl⟩ := hy
    cases w with
    | nil => exact highest_inner_eq_zero_of_weight_ne H x lambda hweight hne
    | cons a w => exact inner_loweringWord_cons_eq_zero H.vector x hraise a w
  | zero => simp
  | add y z hy hz ihy ihz => simp only [inner_add_left, ihy, ihz, add_zero]
  | smul c y hy ih => simp only [inner_smul_left, ih, mul_zero]

/-- A nonzero highest vector in an exhaustive sector sum has a label actually
present in that sum. This also handles repeated labels. -/
theorem highest_weight_occurs_in_list
    (L : List (PhysicalHighestTensor n d)) (x : TensorRegister n (Fin d)) (lambda : Fin d → ℕ)
    (hx : x ∈ physicalSectorListSpan L) (hx0 : x ≠ 0)
    (hweight : ∀ a, collectiveGenerator n a a x = (lambda a : ℂ) • x)
    (hraise : ∀ a b, a < b → collectiveGenerator n a b x = 0) :
    ∃ H ∈ L, H.weight = lambda := by
  classical
  by_contra! hn
  have ho : x ∈ (physicalSectorListSpan L)ᗮ := by
    clear hx
    induction L with
    | nil => simp [physicalSectorListSpan]
    | cons H L ih =>
      have hhead := highest_mem_orthogonal_cyclic_of_weight_ne H x lambda hweight hraise
        (hn H (by simp))
      have htail := ih (fun K hK => hn K (by simp [hK]))
      apply ((H.sector ⊔ physicalSectorListSpan L).mem_orthogonal x).mpr
      intro y hy
      obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.mp hy
      rw [inner_add_left, (H.sector.mem_orthogonal x).mp hhead u hu,
        ((physicalSectorListSpan L).mem_orthogonal x).mp htail v hv, add_zero]
  have he := ((physicalSectorListSpan L).mem_orthogonal x).mp ho x hx
  exact hx0 (inner_self_eq_zero.mp he)

/-- Actual branch witnesses force the injective row labels of an exhaustive
one-box decomposition to cover exactly all addable rows. -/
theorem fundamental_decomposition_row_coverage
    (Ω : TensorRegister n (Fin d)) (mu : Fin d → ℕ)
    (L : List (PhysicalHighestTensor (n + 1) d)) (rows : Fin L.length ↪ Fin d)
    (hrows : ∀ i, (L.get i).weight = addBox mu (rows i))
    (hspan : physicalSectorListSpan L = tensorProductSector (cyclicSector Ω)
      (⊤ : Submodule ℂ (TensorRegister 1 (Fin d))))
    (hexists : ∀ r, Antitone (addBox mu r) →
      ∃ x ∈ fundamentalHighestSpace Ω (addBox mu r), x ≠ 0) (r : Fin d) :
    Antitone (addBox mu r) ↔ ∃ i, rows i = r := by
  constructor
  · intro hr
    obtain ⟨x, hx, hx0⟩ := hexists r hr
    have hxspan : x ∈ physicalSectorListSpan L := by rw [hspan]; exact hx.1
    obtain ⟨H, hH, hweight⟩ := highest_weight_occurs_in_list L x (addBox mu r)
      hxspan hx0 hx.2.1 hx.2.2
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hH
    exact ⟨i, addBox_injective mu ((hrows i).symm.trans hweight)⟩
  · rintro ⟨i, rfl⟩
    rw [← hrows i]
    exact (L.get i).weight_antitone

end Cloning.TensorLie
