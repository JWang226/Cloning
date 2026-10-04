import Cloning.WeylSqueezerChannel
import Cloning.WeylDiagonalRepresentation

/-! The full unitary-dilation classification of diagonal-gain covariant
amplifiers. The joint idler is reconstructed from the supplied physical
channel, then the actual channels agree on the entire trace class. -/
noncomputable section
namespace Cloning.WeylSqueezer
open Cloning.MultimodeCoherent Cloning.InfiniteTraceClass
set_option backward.isDefEq.respectTransparency false
variable {d : ℕ}

/-- Every physical amplifier with independent mode gains has an actual
full-squeezer dilation with one joint density idler, including correlated idlers. -/
theorem covariantChannel_exists_dilation (Φ : QuantumChannel (Fock d) (Fock d))
    (G : Fin d → ℝ) (hG : ∀i,1<G i)
    (hΦ : ∀a T,Φ.toLinearMap (displacementTraceMap a T)=
      displacementTraceMap (diagonalScale (diagonalGainAmplitude G) a) (Φ.toLinearMap T)) :
    ∃σ : DensityState (Fock d),Φ.toLinearMap=
      (channel (diagonalGainAmplitude G) (diagonalNoiseAmplitude G)
        (gain_hyperbolic G (fun i => (hG i).le)) σ).toLinearMap := by
  obtain ⟨τ,hτ,htτ,_,hrep⟩ := quantumChannel_diagonal_idler_representation Φ G hG hΦ
  let σ : DensityState (Fock d) := ⟨τ.1,hτ,τ.2,htτ⟩
  refine ⟨σ,?_⟩
  apply LinearMap.ext
  intro T
  apply characteristic_injective
  funext a
  dsimp only
  rw [channel_characteristic]
  exact hrep T a

end Cloning.WeylSqueezer
