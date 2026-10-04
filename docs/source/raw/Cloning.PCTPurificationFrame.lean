import Cloning.PCTTensorFrame

/-! Existence of physical purification frames through every unit vector and
the exact normalized local-state formula in that frame. -/
noncomputable section
open scoped BigOperators InnerProductSpace ComplexOrder Topology
open Cloning.InfiniteTraceClass
namespace Cloning.PCT
open GeneralCoherent
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
variable {C : Type*} [Fintype C] [DecidableEq C]

/-- Any normalized purification is the first vector of an actual full
orthonormal frame; the frame is constructed by finite-dimensional completion. -/
theorem exists_purification_frame {s : ℕ} (hcard : Fintype.card C = s + 1)
    (ψ : Register C) (hψ : ‖ψ‖ = 1) :
    ∃ b : OrthonormalBasis (Fin (s + 1)) ℂ (Register C), b 0 = ψ := by
  classical
  letI : FiniteDimensional ℂ (Register C) :=
    (registerBasis C).toOrthonormalBasis.toBasis.finiteDimensional_of_finite
  have hc : Module.finrank ℂ (Register C) = Fintype.card (Fin (s + 1)) := by
    rw [Module.finrank_eq_card_basis (registerBasis C).toOrthonormalBasis.toBasis]
    simpa using hcard
  let v : Fin (s + 1) → Register C := fun _ => ψ
  have hv : Orthonormal ℂ (({0} : Set (Fin (s + 1))).restrict v) := by
    rw [orthonormal_iff_ite]
    intro i j
    have hi : i = j := Subtype.ext (i.property.trans j.property.symm)
    simp only [hi, ite_true, Set.restrict_apply, v, inner_self_eq_norm_sq_to_K, hψ]
    norm_num
  obtain ⟨b, hb⟩ := hv.exists_orthonormalBasis_extension_of_card_eq hc
  exact ⟨b, hb 0 (Set.mem_singleton 0)⟩

/-- The physical tangent vector lies in the orthogonal complement of the
reference purification. -/
def frameTangent {s : ℕ} (u : Fin (s + 1) → Register C) (z : Fin s → ℂ) :
    Register C := ∑ i, z i • u i.succ

theorem frameTangent_orthogonal {s : ℕ} {u : Fin (s + 1) → Register C}
    (hu : Orthonormal ℂ u) (z : Fin s → ℂ) :
    ⟪u 0, frameTangent u z⟫_ℂ = 0 := by
  have hn (i : Fin s) : (0 : Fin (s + 1)) ≠ i.succ := by
    intro h
    have hv := congrArg Fin.val h
    simp at hv
  simp [frameTangent, inner_sum, inner_smul_right, orthonormal_iff_ite.mp hu, hn]

/-- The actual vector being integrated has exactly the manuscript's local
purification form `(ψ + Z/√L)/√(1+‖z‖²/L)`. -/
theorem frameParticle_eq_normalized {s : ℕ} (u : Fin (s + 1) → Register C)
    (z : Fin s → ℂ) (L : ℕ) :
    frameParticle u z L = (1 / (Real.sqrt (1 + energy z / L) : ℂ)) •
      (u 0 + (1 / (Real.sqrt (L : ℝ) : ℂ)) • frameTangent u z) := by
  rw [frameParticle, Fin.sum_univ_succ, smul_add, frameTangent, Finset.smul_sum]
  simp only [oneParticle_zero, oneParticle_succ, smul_smul]
  simp only [Finset.smul_sum, smul_smul]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  simp only [div_eq_mul_inv]
  ring

theorem frameParticle_norm {s : ℕ} {u : Fin (s + 1) → Register C}
    (hu : Orthonormal ℂ u) (z : Fin s → ℂ) (L : ℕ) :
    ‖frameParticle u z L‖ = 1 := by
  let v : Register (Fin (s + 1)) := ⟨oneParticle z L, memℓp_gen (by
    simp only [ENNReal.toReal_ofNat]; exact (hasSum_fintype _).summable)⟩
  have he : frameParticle u z L = hu.orthogonalFamily.linearIsometry v := by
    rw [OrthogonalFamily.linearIsometry_apply, tsum_fintype]
    rfl
  rw [he, LinearIsometry.norm_map]
  have hv : ‖v‖ ^ (2 : ℕ) = 1 := by
    calc
      _ = ∑ j, ‖oneParticle z L j‖ ^ (2 : ℕ) := by
        simpa only [ENNReal.toReal_ofNat, Real.rpow_two, tsum_fintype] using
          lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ENNReal).toReal) v
      _ = 1 := oneParticle_norm_sq_sum z L
  nlinarith [norm_nonneg v]

end Cloning.PCT
