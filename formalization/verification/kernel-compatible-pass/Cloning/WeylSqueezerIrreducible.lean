import Cloning.WeylSqueezerPhase
import Cloning.WeylIrreducibleMultimode

/-! The concrete Bogoliubov-pulled Fock representation is irreducible because
its real-linear phase map is surjective. -/
noncomputable section
open scoped InnerProductSpace
namespace Cloning.WeylSqueezer
open Cloning.MultimodeCoherent Cloning.WeylGNS
set_option backward.isDefEq.respectTransparency false
variable {d : ℕ}

theorem regularWeyl_commutant_scalar (c s : Fin d → ℝ) (hcs : ∀i,c i^2-s i^2=1)
    (T : Fock (d+d) →L[ℂ] Fock (d+d))
    (hT : ∀z,T.comp ((regularWeyl c s hcs).operator z)=
      ((regularWeyl c s hcs).operator z).comp T) :
    T=⟪coherentVector 0,T (coherentVector 0)⟫_ℂ • ContinuousLinearMap.id ℂ (Fock (d+d)) := by
  apply displacement_commutant_scalar
  intro z
  obtain ⟨a,ha⟩ := (phaseEquiv c s hcs).surjective z
  change transform c s a=z at ha
  simpa only [regularWeyl_operator,ha] using hT a

theorem regularWeyl_exists_scalar (c s : Fin d → ℝ) (hcs : ∀i,c i^2-s i^2=1)
    (T : Fock (d+d) →L[ℂ] Fock (d+d))
    (hT : ∀z,T.comp ((regularWeyl c s hcs).operator z)=
      ((regularWeyl c s hcs).operator z).comp T) :
    ∃w : ℂ,T=w • ContinuousLinearMap.id ℂ (Fock (d+d)) :=
  ⟨_,regularWeyl_commutant_scalar c s hcs T hT⟩

end Cloning.WeylSqueezer
