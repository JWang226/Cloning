import Cloning.CovariantAmplifierComposite
import Cloning.WeylDiagonalRepresentation

/-! The actual thermal output of an arbitrary covariant amplifier has the
joint-idler characteristic representation with the exact composite gains. -/
noncomputable section
open scoped BigOperators Topology InnerProductSpace ComplexOrder
namespace Cloning.CovariantAmplifier
open InfiniteTraceClass MultimodeCoherent MultimodeCoherentGaussianMixture ThermalWitness
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
variable {d : ℕ}

/-- The composite classification applied to the literal thermal input.
The joint idler may be correlated, non-Gaussian and non-diagonal. -/
theorem thermalOutput_exists_idler (Λ : QuantumChannel (Fock d) (Fock d))
    (γ : ℝ) (hγ : 1<γ)
    (hΛ : ∀ a A, Λ.toLinearMap (displacementTraceMap a A)=
      displacementTraceMap (Real.sqrt γ • a) (Λ.toLinearMap A))
    (q : Fin d → ℝ) (hq0 : ∀ i,0≤q i) (hq1 : ∀ i,q i<1) :
    ∃ σ : TraceClass (Fock d), 0≤σ.1 ∧ traceCLM σ=1 ∧
      ∀ a : Fin d → ℂ,
        tracePairing (Λ.toLinearMap (vectorMixture (numberBasis d) (productGeometric q)))
          (displacement a)=
        tracePairing σ (displacement (fun i =>
          (Real.sqrt (modeGain γ (q i)-1) : ℂ)*star (a i))) *
          ∏ i, (Real.exp (-(modeGain γ (q i)*‖a i‖^2)/2) : ℂ) := by
  let G : Fin d → ℝ := fun i => modeGain γ (q i)
  have hG (i : Fin d) : 1<G i := modeGain_gt_one hγ (hq0 i) (hq1 i)
  have hcov : ∀ a A, (compositeChannel Λ q hq0 hq1).toLinearMap (displacementTraceMap a A)=
      displacementTraceMap (diagonalScale (diagonalGainAmplitude G) a)
        ((compositeChannel Λ q hq0 hq1).toLinearMap A) :=
    compositeChannel_covariant Λ γ (by linarith) hΛ q hq0 hq1
  obtain ⟨σ,hσ,ht,_,hc⟩ := quantumChannel_diagonal_idler_representation
    (compositeChannel Λ q hq0 hq1) G hG hcov
  refine ⟨σ,hσ,ht,fun a => ?_⟩
  have hh := hc (coherentProjector (0 : Fin d → ℂ)) a
  rw [compositeChannel_vacuum] at hh
  have hv : tracePairing (coherentProjector (0 : Fin d → ℂ))
      (displacement (diagonalScale (diagonalGainAmplitude G) a))=
      ∏ i, (Real.exp (-(G i*‖a i‖^2)/2) : ℂ) := by
    change tracePairing (rankOneOperator (coherentVector 0) (coherentVector 0)) _=_
    rw [tracePairing_rankOneOperator, vacuum_characteristic]
    apply Finset.prod_congr rfl
    intro i _
    congr 2
    simp only [diagonalScale, diagonalGainAmplitude, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), mul_pow,
      Real.sq_sqrt (le_trans zero_le_one (hG i).le)]
  rw [hv] at hh
  exact hh

end Cloning.CovariantAmplifier
