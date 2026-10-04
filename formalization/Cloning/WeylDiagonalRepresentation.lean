import Cloning.WeylDiagonalIdler
import Cloning.WeylQuantumBochner

/-! Arbitrary independent amplifying gains admit a unique actual joint idler.
The Schrödinger characteristic identity holds on all complex trace-class
inputs. No idler, product structure or Gaussian hypothesis is supplied. -/

noncomputable section
open scoped ComplexOrder InnerProductSpace Topology BigOperators

namespace Cloning.MultimodeCoherent
open Cloning.InfiniteTraceClass
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

variable {d : ℕ}

/-- Independent nonzero noise amplitudes retain characteristic injectivity. -/
theorem diagonal_idler_characteristic_injective (s : Fin d → ℝ)
    (hs : ∀ i, s i ≠ 0) :
    Function.Injective (fun σ : TraceClass (Fock d) => fun a : Fin d → ℂ =>
      tracePairing σ (displacement (diagonalScale s (star a)))) := by
  intro σ τ h
  apply characteristic_injective
  funext b
  have hh := congrFun h (diagonalScale (fun i => (s i)⁻¹) (star b))
  simpa only [diagonal_idler_frequency_inverse s hs] using hh

/-- The actual diagonal-covariant channel determines one unique joint idler
state. The stated identity is the physical noise-frequency convention. -/
theorem quantumChannel_diagonal_existsUnique_idler
    (Φ : QuantumChannel (Fock d) (Fock d))
    (G : Fin d → ℝ) (hG : ∀ i, 1 < G i)
    (hΦ : ∀ a T, Φ.toLinearMap (displacementTraceMap a T) =
      displacementTraceMap (diagonalScale (diagonalGainAmplitude G) a) (Φ.toLinearMap T)) :
    ∃! σ : TraceClass (Fock d), 0 ≤ σ.1 ∧ traceCLM σ = 1 ∧
      ∀ a, diagonalWeylMultiplier Φ.heisenberg (diagonalGainAmplitude G) a =
        tracePairing σ (displacement (diagonalScale (diagonalNoiseAmplitude G) (star a))) := by
  obtain ⟨_, hg0, hgcont, hgpos, _, hrecover⟩ :=
    quantumChannel_diagonal_idler_characteristic_data Φ G hG hΦ
  obtain ⟨σ, hσ, ht, hc⟩ := Cloning.WeylGNS.exists_density_characteristic _ hg0 hgcont hgpos
  have hrep (a) : diagonalWeylMultiplier Φ.heisenberg (diagonalGainAmplitude G) a =
      tracePairing σ (displacement (diagonalScale (diagonalNoiseAmplitude G) (star a))) :=
    (hrecover a).trans (hc _).symm
  refine ⟨σ, ⟨hσ, ht, hrep⟩, ?_⟩
  intro τ hτ
  apply diagonal_idler_characteristic_injective (diagonalNoiseAmplitude G)
    (fun i => ne_of_gt (Real.sqrt_pos.mpr (sub_pos.mpr (hG i))))
  funext a
  exact (hτ.2.2 a).symm.trans (hrep a)

/-- The amplifier representation applies to the supplied channel on every
complex trace-class input, with a positive trace-one idler constructed above. -/
theorem quantumChannel_diagonal_idler_representation
    (Φ : QuantumChannel (Fock d) (Fock d))
    (G : Fin d → ℝ) (hG : ∀ i, 1 < G i)
    (hΦ : ∀ a T, Φ.toLinearMap (displacementTraceMap a T) =
      displacementTraceMap (diagonalScale (diagonalGainAmplitude G) a) (Φ.toLinearMap T)) :
    ∃ σ : TraceClass (Fock d), 0 ≤ σ.1 ∧ traceCLM σ = 1 ∧
      (∀ a, Φ.heisenberg (displacement a) =
        tracePairing σ (displacement (diagonalScale (diagonalNoiseAmplitude G) (star a))) •
          displacement (diagonalScale (diagonalGainAmplitude G) a)) ∧
      (∀ T a, tracePairing (Φ.toLinearMap T) (displacement a) =
        tracePairing σ (displacement (diagonalScale (diagonalNoiseAmplitude G) (star a))) *
          tracePairing T (displacement (diagonalScale (diagonalGainAmplitude G) a))) := by
  obtain ⟨σ, hσ, _⟩ := quantumChannel_diagonal_existsUnique_idler Φ G hG hΦ
  obtain ⟨hmult, _, _⟩ := quantumChannel_diagonal_weyl_multiplier Φ (diagonalGainAmplitude G) hΦ
  have hact (a) : Φ.heisenberg (displacement a) =
      tracePairing σ (displacement (diagonalScale (diagonalNoiseAmplitude G) (star a))) •
        displacement (diagonalScale (diagonalGainAmplitude G) a) := by
    rw [hmult a, hσ.2.2 a]
  refine ⟨σ, hσ.1, hσ.2.1, hact, ?_⟩
  intro T a
  rw [← Φ.heisenberg_pairing, hact a, map_smul, smul_eq_mul]

end Cloning.MultimodeCoherent
