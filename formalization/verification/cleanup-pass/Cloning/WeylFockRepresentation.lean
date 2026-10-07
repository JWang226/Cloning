import Cloning.WeylFockDecomposition
import Cloning.WeylFockState

/-! Every vector state of a regular finite-mode Weyl representation is an
actual trace-class state on the standard multimode Fock space. -/
noncomputable section
open scoped BigOperators Topology InnerProductSpace ComplexOrder ENNReal
namespace Cloning.WeylGNS
open MultimodeCoherent InfiniteTraceClass
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
variable {d : ℕ} {ι : Type*}

def diagonalDisplacement (a : Fin d → ℂ) (v : lp (fun _ : ι => Fock d) 2) :
    lp (fun _ : ι => Fock d) 2 := by
  refine ⟨fun i => displacement a (v i), memℓp_gen ?_⟩
  simpa only [displacement_norm, ENNReal.toReal_ofNat, Real.rpow_two] using
    (component_norm_sq_hasSum v).summable

@[simp] theorem diagonalDisplacement_apply (a : Fin d → ℂ)
    (v : lp (fun _ : ι => Fock d) 2) (i : ι) :
    diagonalDisplacement a v i = displacement a (v i) := rfl

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (W : RegularWeyl d H)

def RegularWeyl.fockCoordinates (b : HilbertBasis ι ℂ W.vacuumSpace) :
    H ≃ₗᵢ[ℂ] lp (fun _ : ι => Fock d) 2 :=
  (W.fockCopies_isHilbertSum b).linearIsometryEquiv

theorem RegularWeyl.fockCoordinates_action (b : HilbertBasis ι ℂ W.vacuumSpace)
    (a : Fin d → ℂ) (v : H) :
    W.fockCoordinates b (W.operator a v)=diagonalDisplacement a (W.fockCoordinates b v) := by
  let E := W.fockCoordinates b
  let c := E v
  apply E.symm.injective
  rw [LinearIsometryEquiv.symm_apply_apply]
  have hs := ((W.fockCopies_isHilbertSum b).hasSum_linearIsometryEquiv_symm c).mapL
    (W.operator a)
  have hs' : HasSum (fun i => W.fockCopies b i (displacement a (c i))) (W.operator a v) := by
    have he (i : ι) : W.operator a (W.fockCopies b i (c i))=
        W.fockCopies b i (displacement a (c i)) :=
      (W.vacuumEmbedding_intertwines (b i) (b.orthonormal.1 i) a (c i)).symm
    simp_rw [he] at hs
    simpa only [c, E, RegularWeyl.fockCoordinates,
      LinearIsometryEquiv.symm_apply_apply] using hs
  exact hs'.unique ((W.fockCopies_isHilbertSum b).hasSum_linearIsometryEquiv_symm
    (diagonalDisplacement a c))

theorem RegularWeyl.componentState_characteristic (b : HilbertBasis ι ℂ W.vacuumSpace)
    (v : H) (a : Fin d → ℂ) :
    tracePairing (componentState (W.fockCoordinates b v)) (displacement a)=
      ⟪v,W.operator a v⟫_ℂ := by
  rw [componentState_pairing]
  change (∑' i, ⟪W.fockCoordinates b v i,
    diagonalDisplacement a (W.fockCoordinates b v) i⟫_ℂ)=_
  rw [← lp.inner_eq_tsum, ← W.fockCoordinates_action, LinearIsometryEquiv.inner_map_map]

/-- The density is constructed by a trace-norm summable partial trace of the
actual Hilbert-sum coordinates of the vector. -/
theorem RegularWeyl.exists_density_characteristic (v : H) (hv : ‖v‖=1) :
    ∃ σ : TraceClass (Fock d), 0≤σ.1 ∧ traceCLM σ=1 ∧
      ∀ a : Fin d → ℂ, tracePairing σ (displacement a)=⟪v,W.operator a v⟫_ℂ := by
  obtain ⟨ι,b,_⟩ := exists_hilbertBasis ℂ W.vacuumSpace
  refine ⟨componentState (W.fockCoordinates b v), componentState_nonneg _, ?_,
    W.componentState_characteristic b v⟩
  rw [componentState_trace, (W.fockCoordinates b).norm_map, hv]
  norm_num

end Cloning.WeylGNS
