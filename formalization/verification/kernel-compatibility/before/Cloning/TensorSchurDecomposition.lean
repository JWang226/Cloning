import Cloning.TensorSchurDecompositionData

/-! Exhaustive finite orthogonal decomposition into actual irreducible highest sectors. -/
noncomputable section
open scoped BigOperators InnerProductSpace
namespace Cloning.TensorLie
open Cloning.PCT
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {n d : ℕ}

local instance : FiniteDimensional ℂ (TensorRegister n (Fin d)) :=
  (registerBasis (Fin n → Fin d)).toOrthonormalBasis.toBasis.finiteDimensional_of_finite

/-- Finite orthogonal sector sums, allowing repeated partition labels. -/
def physicalSectorListSpan : List (PhysicalHighestTensor n d) → Submodule ℂ (TensorRegister n (Fin d))
  | [] => ⊥
  | H :: L => H.sector ⊔ physicalSectorListSpan L

theorem physicalSector_le_listSpan {L : List (PhysicalHighestTensor n d)}
    {H : PhysicalHighestTensor n d} (hH : H ∈ L) : H.sector ≤ physicalSectorListSpan L := by
  induction L with
  | nil => simp at hH
  | cons K L ih =>
      rcases List.mem_cons.mp hH with rfl | hH
      · exact le_sup_left
      · exact (ih hH).trans le_sup_right

theorem physicalSectorListSpan_le_iff (L : List (PhysicalHighestTensor n d))
    (W : Submodule ℂ (TensorRegister n (Fin d))) :
    physicalSectorListSpan L ≤ W ↔ ∀ H ∈ L, H.sector ≤ W := by
  induction L with
  | nil => simp [physicalSectorListSpan]
  | cons H L ih => simp only [physicalSectorListSpan, sup_le_iff, ih, List.forall_mem_cons]

/-- Repeatedly extracting an actual highest tensor strictly lowers the
remaining dimension and exhausts every invariant physical subspace. -/
theorem exists_physical_cyclic_decomposition
    (W : Submodule ℂ (TensorRegister n (Fin d)))
    (hW : ∀ a b x, x ∈ W → collectiveGenerator n a b x ∈ W) :
    ∃ L : List (PhysicalHighestTensor n d),
      L.Pairwise (fun H K => H.sector ⟂ K.sector) ∧ physicalSectorListSpan L = W := by
  classical
  have aux : ∀ k : ℕ, ∀ W : Submodule ℂ (TensorRegister n (Fin d)),
      Module.finrank ℂ W = k →
      (∀ a b x, x ∈ W → collectiveGenerator n a b x ∈ W) →
      ∃ L : List (PhysicalHighestTensor n d),
        L.Pairwise (fun H K => H.sector ⟂ K.sector) ∧ physicalSectorListSpan L = W := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro W hdim hW
      by_cases hz : W = ⊥
      · exact ⟨[], by simp, hz.symm⟩
      · obtain ⟨H, hH⟩ := exists_physicalHighestTensor_le W hW hz
        let R : Submodule ℂ (TensorRegister n (Fin d)) := H.sectorᗮ ⊓ W
        have hR : ∀ a b x, x ∈ R → collectiveGenerator n a b x ∈ R := by
          intro a b x hx
          exact ⟨generatorInvariant_orthogonal H.sector
            (fun a b y hy => H.generator_invariant a b hy) a b hx.1, hW a b x hx.2⟩
        have hRne : R ≠ W := by
          intro he
          have hm : H.vector ∈ R := by rw [he]; exact hH H.vector_mem
          have hi := (H.sector.mem_orthogonal H.vector).mp hm.1 H.vector H.vector_mem
          have hv : H.vector = 0 := inner_self_eq_zero.mp hi
          have hn := H.norm_one
          simp only [hv, norm_zero, zero_ne_one] at hn
        have hlt : Module.finrank ℂ R < k := by
          rw [← hdim]
          exact Submodule.finrank_lt_finrank_of_lt
            (lt_iff_le_and_ne.mpr ⟨inf_le_right, hRne⟩)
        obtain ⟨L, hLorth, hLspan⟩ := ih (Module.finrank ℂ R) hlt R rfl hR
        refine ⟨H :: L, List.pairwise_cons.mpr ⟨?_, hLorth⟩, ?_⟩
        · intro K hK
          have hKR : K.sector ≤ R := (physicalSector_le_listSpan hK).trans (le_of_eq hLspan)
          exact (Submodule.isOrtho_orthogonal_right H.sector).mono_right
            (hKR.trans inf_le_left)
        · rw [physicalSectorListSpan, hLspan]
          exact Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection hH
  exact aux (Module.finrank ℂ W) W rfl hW

theorem physicalSectorListSpan_eq_iSup (L : List (PhysicalHighestTensor n d)) :
    physicalSectorListSpan L = ⨆ i : Fin L.length, (L.get i).sector := by
  apply le_antisymm
  · apply (physicalSectorListSpan_le_iff L _).mpr
    intro H hH
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hH
    exact le_iSup (fun j : Fin L.length => (L.get j).sector) i
  · apply iSup_le
    intro i
    exact physicalSector_le_listSpan (List.get_mem L i)

theorem physicalSectorList_orthogonalFamily (L : List (PhysicalHighestTensor n d))
    (hL : L.Pairwise (fun H K => H.sector ⟂ K.sector)) :
    OrthogonalFamily ℂ (fun i : Fin L.length => (L.get i).sector)
      (fun i => (L.get i).sector.subtypeₗᵢ) := by
  apply OrthogonalFamily.of_pairwise
  intro i j hij
  rcases lt_or_gt_of_ne hij with hij | hji
  · exact hL.rel_get_of_lt hij
  · exact (hL.rel_get_of_lt hji).symm

/-- The full physical tensor register is exhausted by finitely many orthogonal
actual highest sectors. Labels are partitions, with multiplicities retained. -/
theorem exists_tensor_cyclic_decomposition (n d : ℕ) :
    ∃ L : List (PhysicalHighestTensor n d),
      OrthogonalFamily ℂ (fun i : Fin L.length => (L.get i).sector)
        (fun i => (L.get i).sector.subtypeₗᵢ) ∧
      (⨆ i : Fin L.length, (L.get i).sector) = ⊤ := by
  obtain ⟨L, hLorth, hLspan⟩ := exists_physical_cyclic_decomposition
    (⊤ : Submodule ℂ (TensorRegister n (Fin d))) (fun _ _ _ _ => Submodule.mem_top)
  exact ⟨L, physicalSectorList_orthogonalFamily L hLorth,
    (physicalSectorListSpan_eq_iSup L).symm.trans hLspan⟩

end Cloning.TensorLie
