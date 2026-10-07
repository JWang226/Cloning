import Cloning.WeylDiagonalRepresentation

/-! The reflected idler convention is reconstructed directly, allowing the
positive-amplitude seeded squeezing isometry to use its negative Weyl argument. -/
noncomputable section
open scoped BigOperators Topology InnerProductSpace ComplexOrder
namespace Cloning.MultimodeCoherent
open InfiniteTraceClass
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
variable {d : ℕ}

theorem displacementPhase_neg_neg (a b : Fin d → ℂ) :
    displacementPhase (-a) (-b)=displacementPhase a b := by
  simp only [displacementPhase, Pi.neg_apply, ComplexCoherent.displacementPhase,
    map_neg, neg_mul_neg]

theorem IsWeylCharacteristicPositive.neg {g : (Fin d → ℂ) → ℂ}
    (hg : IsWeylCharacteristicPositive g) : IsWeylCharacteristicPositive (fun a => g (-a)) := by
  intro n b c
  have h := hg n (fun i => -(b i)) c
  simpa only [displacementPhase_neg_neg, neg_sub_neg, neg_sub] using h

/-- The same covariant channel also has an actual idler in the opposite Weyl
sign convention. This convention matches positive number-basis squeezing amplitudes. -/
theorem quantumChannel_diagonal_negative_idler_representation
    (Φ : QuantumChannel (Fock d) (Fock d))
    (G : Fin d → ℝ) (hG : ∀ i,1<G i)
    (hΦ : ∀ a T, Φ.toLinearMap (displacementTraceMap a T)=
      displacementTraceMap (diagonalScale (diagonalGainAmplitude G) a) (Φ.toLinearMap T)) :
    ∃ σ : TraceClass (Fock d), 0≤σ.1 ∧ traceCLM σ=1 ∧
      ∀ T a, tracePairing (Φ.toLinearMap T) (displacement a)=
        tracePairing σ (displacement (-(diagonalScale (diagonalNoiseAmplitude G) (star a)))) *
          tracePairing T (displacement (diagonalScale (diagonalGainAmplitude G) a)) := by
  obtain ⟨hmult,hg0,hgc,hgp,_,hrecover⟩ :=
    quantumChannel_diagonal_idler_characteristic_data Φ G hG hΦ
  let g := diagonalAmplifierIdlerFunction
    (diagonalWeylMultiplier Φ.heisenberg (diagonalGainAmplitude G)) G
  obtain ⟨σ,hσ,ht,hc⟩ := Cloning.WeylGNS.exists_density_characteristic
    (fun a => g (-a)) (by simpa [g] using hg0) (hgc.comp continuous_neg) hgp.neg
  have hrep (a) : diagonalWeylMultiplier Φ.heisenberg (diagonalGainAmplitude G) a=
      tracePairing σ (displacement (-(diagonalScale (diagonalNoiseAmplitude G) (star a)))) := by
    have hh := hc (-(diagonalScale (diagonalNoiseAmplitude G) (star a)))
    simp only [neg_neg] at hh
    exact (hrecover a).trans hh.symm
  refine ⟨σ,hσ,ht,?_⟩
  intro T a
  rw [← Φ.heisenberg_pairing, hmult a, hrep a, map_smul, smul_eq_mul]

end Cloning.MultimodeCoherent
