import Cloning.WeylSqueezerIrreducible
import Cloning.WeylIrreducibleRepresentation

/-! A full unitary squeeze on arbitrary doubled-Fock vectors, constructed from
the actual symplectic Weyl action and the proved irreducible reconstruction.
The signed cross coefficient fixes the idler phase convention explicitly. -/
noncomputable section
open scoped InnerProductSpace
namespace Cloning.WeylSqueezer
open Cloning.MultimodeCoherent Cloning.WeylGNS
set_option backward.isDefEq.respectTransparency false
variable {d : ℕ}

theorem exists_implementer (c s : Fin d → ℝ) (hcs : ∀i,c i^2-s i^2=1) :
    ∃ V : Fock (d+d) ≃ₗᵢ[ℂ] Fock (d+d), ∀a v,
      displacement (transform c s a) (V v)=V (displacement a v) := by
  letI : Nontrivial (Fock (d+d)) := by
    refine ⟨⟨coherentVector 0,0,?_⟩⟩
    intro hh
    have hn := coherentVector_norm (z := (0 : Fin (d+d) → ℂ))
    rw [hh,norm_zero] at hn
    norm_num at hn
  simpa only [regularWeyl_operator] using
    (regularWeyl c s hcs).exists_fock_equiv (regularWeyl_exists_scalar c s hcs)

def implementer (c s : Fin d → ℝ) (hcs : ∀i,c i^2-s i^2=1) :
    Fock (d+d) ≃ₗᵢ[ℂ] Fock (d+d) :=
  (exists_implementer c s hcs).choose

theorem implementer_intertwines (c s : Fin d → ℝ) (hcs : ∀i,c i^2-s i^2=1)
    (a : Fin (d+d) → ℂ) (v : Fock (d+d)) :
    displacement (transform c s a) (implementer c s hcs v)=
      implementer c s hcs (displacement a v) :=
  (exists_implementer c s hcs).choose_spec a v

/-- The Schrödinger unitary with Heisenberg action `D(a) ↦ D(Ba)`.
Positive `s` gives the idler characteristic at `s * conj(a)`. -/
def squeeze (c s : Fin d → ℝ) (hcs : ∀i,c i^2-s i^2=1) :
    Fock (d+d) ≃ₗᵢ[ℂ] Fock (d+d) := (implementer c s hcs).symm

theorem squeeze_heisenberg_apply (c s : Fin d → ℝ) (hcs : ∀i,c i^2-s i^2=1)
    (a : Fin (d+d) → ℂ) (v : Fock (d+d)) :
    (squeeze c s hcs).symm (displacement a (squeeze c s hcs v))=
      displacement (transform c s a) v := by
  change implementer c s hcs (displacement a ((implementer c s hcs).symm v))=_
  rw [← implementer_intertwines, LinearIsometryEquiv.apply_symm_apply]

theorem squeeze_heisenberg (c s : Fin d → ℝ) (hcs : ∀i,c i^2-s i^2=1)
    (a : Fin (d+d) → ℂ) :
    (squeeze c s hcs : Fock (d+d) →L[ℂ] Fock (d+d)).adjoint.comp
      ((displacement a).comp (squeeze c s hcs : Fock (d+d) →L[ℂ] Fock (d+d)))=
      displacement (transform c s a) := by
  rw [LinearIsometryEquiv.adjoint_eq_symm]
  apply ContinuousLinearMap.ext
  intro v
  exact squeeze_heisenberg_apply c s hcs a v

theorem squeeze_signal_heisenberg (c s : Fin d → ℝ) (hcs : ∀i,c i^2-s i^2=1)
    (a : Fin d → ℂ) :
    (squeeze c s hcs : Fock (d+d) →L[ℂ] Fock (d+d)).adjoint.comp
      ((displacement (Fin.append a 0)).comp
        (squeeze c s hcs : Fock (d+d) →L[ℂ] Fock (d+d)))=
      displacement (Fin.append (fun i => (c i : ℂ)*a i)
        (fun i => (s i : ℂ)*(starRingEnd ℂ) (a i))) := by
  rw [squeeze_heisenberg,transform_signal]

end Cloning.WeylSqueezer
