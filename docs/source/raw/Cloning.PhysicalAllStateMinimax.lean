import Cloning.PCTPrescribedFull
import Cloning.PCTRankAdaptedFlat
import Cloning.PhysicalCloningUniversalTheorem

/-! The literal minimax fidelity over all finite-dimensional density matrices.
The competitors are all physical CPTP maps; neither spectrum nor rank is
supplied to a competitor. -/
noncomputable section
open scoped BigOperators Topology Classical Matrix
open Filter
namespace Cloning.PhysicalAllStateMinimax
open Cloning.PCT Cloning.PCTPhysicalState Cloning.TensorCloning Cloning.InfiniteTraceClass
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 200000

local instance stateNonempty (d : ℕ) : Nonempty (Cloning.MatrixFidelity.State (Fin (d+1))) :=
  ⟨Cloning.PCTRankAdapted.flatInternalState d⟩
local instance channelNonempty (d n m : ℕ) :
    Nonempty (QuantumChannel (Register (Fin n→Fin (d+1))) (Register (Fin m→Fin (d+1)))) :=
  ⟨Cloning.PCTPrescribed.fullChannel d n m⟩

/-- Dimension is d+1, covering every nonzero finite-dimensional system. -/
def value (d n m : ℕ) : ℝ :=
  LAN.minimaxValue (fun Φ (ρ : Cloning.MatrixFidelity.State (Fin (d+1))) => statePayoff n m Φ ρ)

theorem value_nonneg (d n m : ℕ) : 0≤value d n m := by
  exact LAN.candidate_le_minimaxValue _ (Cloning.PCTPrescribed.fullChannel d n m) 0
    (statePayoff_le_one n m) (statePayoff_nonneg n m _) (statePayoff_nonneg n m)

theorem value_le_one (d n m : ℕ) : value d n m≤1 := by
  unfold value LAN.minimaxValue
  apply ciSup_le
  intro Φ
  have hb : BddBelow (Set.range (statePayoff n m Φ)) :=
    ⟨0,by rintro _ ⟨ρ,rfl⟩; exact statePayoff_nonneg n m Φ ρ⟩
  exact (ciInf_le hb (Cloning.PCTRankAdapted.flatInternalState d)).trans
    (statePayoff_le_one n m Φ _)

/-- Restricting the adversary to any nonempty simple-spectrum family can only
increase its optimal guaranteed fidelity. The channel class stays unchanged. -/
theorem value_le_unknownSpectrumValue (d n m : ℕ)
    (S : Set (SimpleSpectrum (d+1))) (hS : S.Nonempty) :
    value d n m≤unknownSpectrumValue n m S := by
  obtain ⟨p,hp⟩ := hS
  letI : Nonempty S := ⟨⟨p,hp⟩⟩
  have hb : BddAbove (Set.range (fun Φ : QuantumChannel
      (Register (Fin n→Fin (d+1))) (Register (Fin m→Fin (d+1))) =>
      ⨅θ : S×unitary (Matrix (Fin (d+1)) (Fin (d+1)) ℂ),
        spectrumPayoff n m Φ θ.1.val θ.2)) := by
    refine ⟨1,?_⟩
    rintro _ ⟨Φ,rfl⟩
    have hl : BddBelow (Set.range (fun θ : S×unitary (Matrix (Fin (d+1)) (Fin (d+1)) ℂ) =>
        spectrumPayoff n m Φ θ.1.val θ.2)) :=
      ⟨0,by rintro _ ⟨θ,rfl⟩; exact spectrumPayoff_nonneg n m Φ _ _⟩
    exact (ciInf_le hl (⟨p,hp⟩,1)).trans (spectrumPayoff_le_one n m Φ p 1)
  unfold value unknownSpectrumValue LAN.minimaxValue
  apply ciSup_le
  intro Φ
  refine le_trans (le_ciInf (fun θ => ?_)) (le_ciSup hb Φ)
  exact ciInf_le ⟨0,by rintro _ ⟨ρ,rfl⟩; exact statePayoff_nonneg n m Φ ρ⟩
    (orbitState θ.1.val θ.2)

/-- The genuine unknown-spectrum converse applies at every simple positive
base spectrum, including when all ranks and spectra are admitted adversarially. -/
theorem limsup_value_le_universalValue (d : ℕ) (p : SimpleSpectrum (d+1))
    (m : ℕ→ℕ) (γ : ℝ) (hγ : 1<γ)
    (hgain : Tendsto (fun n => (m n:ℝ)/n) atTop (𝓝 γ)) :
    limsup (fun n => value d n (m n)) atTop≤universalValue γ p := by
  have hS : (Set.univ : Set (SimpleSpectrum (d+1))).Nonempty := ⟨p,Set.mem_univ p⟩
  have hcomp := limsup_le_limsup
    (Eventually.of_forall (fun n => value_le_unknownSpectrumValue d n (m n) Set.univ hS))
    (isCoboundedUnder_le_of_le atTop (fun n => value_nonneg d n (m n)))
    (Filter.isBoundedUnder_of_eventually_le (Eventually.of_forall (fun n =>
      unknownSpectrumValue_le_one n (m n) Set.univ hS)))
  exact hcomp.trans (Cloning.PhysicalCloningConverse.limsup_unknownSpectrumValue_le
    Set.univ p (by simp) m γ hγ hgain)

/-- The all-state upper bound is the infimum of the universal, unknown-spectrum
Gaussian value, rather than the easier known-spectrum orbit value. -/
theorem limsup_value_le_universal_infimum (d : ℕ) [Nonempty (SimpleSpectrum (d+1))]
    (m : ℕ→ℕ) (γ : ℝ) (hγ : 1<γ)
    (hgain : Tendsto (fun n => (m n:ℝ)/n) atTop (𝓝 γ)) :
    limsup (fun n => value d n (m n)) atTop≤⨅p : SimpleSpectrum (d+1),universalValue γ p :=
  le_ciInf (fun p => limsup_value_le_universalValue d p m γ hγ hgain)

end Cloning.PhysicalAllStateMinimax
