import Cloning.WeylFockVacuum
import Cloning.WeylGaussianTotality
import Mathlib.Analysis.InnerProductSpace.l2Space

/-! Orthogonal Fock copies associated to a vacuum Hilbert basis exhaust every
regular Weyl representation, by the proved Gaussian projection totality. -/
noncomputable section
open scoped BigOperators Topology InnerProductSpace ComplexOrder
namespace Cloning.WeylGNS
open MultimodeCoherent
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
variable {d : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (W : RegularWeyl d H)

theorem RegularWeyl.inner_vacuumEmbedding (x y : W.vacuumSpace)
    (hx : ‖(x : H)‖=1) (hy : ‖(y : H)‖=1) (v w : Fock d) :
    ⟪W.vacuumEmbedding x hx v,W.vacuumEmbedding y hy w⟫_ℂ=
      ⟪v,w⟫_ℂ*⟪(x : H),(y : H)⟫_ℂ := by
  refine coherentCombination_dense.induction_on
    (p := fun v => ⟪W.vacuumEmbedding x hx v,W.vacuumEmbedding y hy w⟫_ℂ=
      ⟪v,w⟫_ℂ*⟪(x : H),(y : H)⟫_ℂ) v (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro c
  refine coherentCombination_dense.induction_on
    (p := fun w => ⟪W.vacuumEmbedding x hx (coherentCombination c),W.vacuumEmbedding y hy w⟫_ℂ=
      ⟪coherentCombination c,w⟫_ℂ*⟪(x : H),(y : H)⟫_ℂ) w
      (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro e
  change ⟪W.vacuumEmbeddingMap x (coherentCombination c),
    W.vacuumEmbeddingMap y (coherentCombination e)⟫_ℂ=_
  rw [W.vacuumEmbeddingMap_combination x hx, W.vacuumEmbeddingMap_combination y hy,
    W.inner_vacuumCombination]

theorem RegularWeyl.vacuumEmbedding_intertwines (x : W.vacuumSpace)
    (hx : ‖(x : H)‖=1) (a : Fin d → ℂ) (v : Fock d) :
    W.vacuumEmbedding x hx (displacement a v)=W.operator a (W.vacuumEmbedding x hx v) := by
  have hc (z : Fin d → ℂ) :
      W.vacuumEmbedding x hx (displacement a (coherentVector z))=
        W.operator a (W.vacuumEmbedding x hx (coherentVector z)) := by
    rw [displacement_coherentVector, map_smul, W.vacuumEmbedding_coherent,
      W.vacuumEmbedding_coherent]
    exact (W.mul_apply a z (x : H)).symm
  have he : (fun v => W.vacuumEmbedding x hx (displacement a v))=
      (fun v => W.operator a (W.vacuumEmbedding x hx v)) := by
    apply coherentCombination_dense.equalizer (by fun_prop) (by fun_prop)
    funext c
    simp only [Function.comp_apply, coherentCombination, Finsupp.linearCombination_apply,
      Finsupp.sum, map_sum, map_smul, hc]
  exact congrFun he v

variable {ι : Type*}

def RegularWeyl.fockCopies (b : HilbertBasis ι ℂ W.vacuumSpace) (i : ι) : Fock d →ₗᵢ[ℂ] H :=
  W.vacuumEmbedding (b i) (b.orthonormal.1 i)

theorem RegularWeyl.fockCopies_orthogonal (b : HilbertBasis ι ℂ W.vacuumSpace) :
    OrthogonalFamily ℂ (fun _ : ι => Fock d) (W.fockCopies b) := by
  intro i j hij v w
  rw [RegularWeyl.fockCopies, RegularWeyl.fockCopies, W.inner_vacuumEmbedding]
  have hz : ⟪(b i : H),(b j : H)⟫_ℂ=0 := b.orthonormal.2 hij
  rw [hz, mul_zero]

/-- Every regular Weyl representation is an actual Hilbert sum of standard
Fock representations. Completeness follows from Gaussian totality, not from a
representation-classification assumption. -/
theorem RegularWeyl.fockCopies_isHilbertSum (b : HilbertBasis ι ℂ W.vacuumSpace) :
    IsHilbertSum ℂ (fun _ : ι => Fock d) (W.fockCopies b) := by
  apply IsHilbertSum.mk (W.fockCopies_orthogonal b)
  rw [top_le_iff, Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
  intro v hv
  apply W.gaussianProjection_translates_total v
  intro a x
  let x' : W.vacuumSpace := ⟨W.gaussianProjection x, ⟨x,rfl⟩⟩
  let L : W.vacuumSpace →L[ℂ] ℂ :=
    (innerSL ℂ v).comp ((W.operator a).comp W.vacuumSpace.subtypeL)
  have hz (i : ι) : L (b i)=0 := by
    change ⟪v,W.operator a (b i : H)⟫_ℂ=0
    apply inner_eq_zero_symm.mp
    apply Submodule.inner_right_of_mem_orthogonal _ hv
    apply Submodule.mem_iSup_of_mem i
    refine ⟨coherentVector a, ?_⟩
    exact W.vacuumEmbedding_coherent (b i) (b.orthonormal.1 i) a
  have hs := (b.hasSum_repr x').mapL L
  simp only [map_smul, hz, smul_zero] at hs
  have he : L x'=0 := hs.unique hasSum_zero
  exact inner_eq_zero_symm.mp he

end Cloning.WeylGNS
