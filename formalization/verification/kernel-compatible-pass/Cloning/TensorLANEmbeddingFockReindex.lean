import Cloning.TensorLANEmbeddingPhysical
import Cloning.WeylMultimodeDisplacement
import Cloning.TensorGibbsThermalIdentification

/-! Exact changes of the arbitrary finite mode enumeration. -/
noncomputable section
open scoped BigOperators Topology Classical InnerProductSpace
namespace Cloning.TensorLAN
open Cloning.MultimodeCoherent Cloning.MultimodeCoherentGaussianMixture
open Cloning.InfiniteTraceClass
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
variable {a b : ℕ}

def modeOccupationEquiv (e : Fin a ≃ Fin b) : (Fin b → ℕ) ≃ (Fin a → ℕ) where
  toFun k i := k (e i)
  invFun k j := k (e.symm j)
  left_inv k := by funext j; simp
  right_inv k := by funext i; simp

def reindexedNumberBasis (e : Fin a ≃ Fin b) : HilbertBasis (Fin b → ℕ) ℂ (Fock a) :=
  HilbertBasis.mk ((numberBasis a).orthonormal.comp (modeOccupationEquiv e)
    (modeOccupationEquiv e).injective) (by
      simp only [Function.comp_def]
      rw [show Set.range (fun k => numberBasis a (modeOccupationEquiv e k)) =
        Set.range (numberBasis a) by
          exact (modeOccupationEquiv e).surjective.range_comp (numberBasis a)]
      rw [(numberBasis a).dense_span])

/-- The actual occupation-space unitary relabeling all modes. -/
def fockReindex (e : Fin a ≃ Fin b) : Fock a ≃ₗᵢ[ℂ] Fock b :=
  (reindexedNumberBasis e).repr

@[simp] theorem fockReindex_apply (e : Fin a ≃ Fin b) (x : Fock a) (k : Fin b → ℕ) :
    fockReindex e x k = x (fun i => k (e i)) := by
  rw [fockReindex, HilbertBasis.repr_apply_apply]
  change ⟪reindexedNumberBasis e k, x⟫_ℂ = _
  rw [reindexedNumberBasis, HilbertBasis.coe_mk]
  simp only [Function.comp_apply]
  rw [inner_numberBasis]
  rfl

@[simp] theorem fockReindex_numberBasis (e : Fin a ≃ Fin b) (k : Fin a → ℕ) :
    fockReindex e (numberBasis a k) = numberBasis b (fun j => k (e.symm j)) := by
  apply lp.ext
  funext j
  rw [fockReindex_apply, numberBasis_eq_single, numberBasis_eq_single]
  simp only [lp.single_apply, Pi.single_apply]
  by_cases h : (fun i => j (e i)) = k
  · have hj : j = (fun i => k (e.symm i)) := by
      funext i
      simpa only [Equiv.apply_symm_apply] using congrFun h (e.symm i)
    simp [h, hj]
  · have hj : j ≠ (fun i => k (e.symm i)) := by
      intro he
      apply h
      funext i
      simpa only [Equiv.symm_apply_apply] using congrFun he (e i)
    simp [h, hj, Ne.symm h, Ne.symm hj]


/-- Coherent amplitudes are relabeled by exactly the same mode permutation. -/
theorem fockReindex_coherentVector (e : Fin a ≃ Fin b) (z : Fin a → ℂ) :
    fockReindex e (coherentVector z) = coherentVector (fun j => z (e.symm j)) := by
  apply lp.ext
  funext k
  simp only [fockReindex_apply, coherentVector_apply]
  have h := e.prod_comp (fun j => ComplexCoherent.coherentVector (z (e.symm j)) (k j))
  simpa only [Equiv.symm_apply_apply] using h

/-- The canonical root enumeration is connected to any requested physical
orbital enumeration by this literal unitary. -/
def rootFockReindex {d s : ℕ} (e : Fin s ≃ TensorLie.PositiveRoot d) :
    RootFock d ≃ₗᵢ[ℂ] Fock s :=
  fockReindex ((Fintype.equivFin (TensorLie.PositiveRoot d)).symm.trans e.symm)

end Cloning.TensorLAN
