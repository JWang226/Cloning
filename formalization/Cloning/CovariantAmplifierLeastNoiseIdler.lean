import Cloning.CovariantAmplifierCompositeReflected
import Cloning.CovariantAmplifierLeastNoiseParameters

/-! The competing thermal output has the exact characteristic function of a
seeded negative-binomial channel, with an actual normalized joint idler. -/
noncomputable section
open scoped ComplexOrder InnerProductSpace Topology BigOperators
namespace Cloning.CovariantAmplifier
open InfiniteTraceClass MultimodeCoherent MultimodeCoherentGaussianMixture ThermalWitness
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
variable {d : ℕ}

theorem productThermal_trace_one (q : Fin d → ℝ)
    (hq0 : ∀ i,0≤q i) (hq1 : ∀ i,q i<1) :
    traceCLM (vectorMixture (numberBasis d) (productGeometric q))=1 := by
  rw [traceCLM_vectorMixture _ (numberBasis d).orthonormal.norm_eq_one _
    (productGeometric_hasSum hq0 hq1).summable, (productGeometric_hasSum hq0 hq1).tsum_eq]
  rfl

/-- An arbitrary competing covariant channel determines a genuine joint
idler for the exact amplified thermal parameters. No number-diagonal or
product assumption is made on that idler. -/
theorem thermalOutput_exists_seeded_characteristic
    (Λ : QuantumChannel (Fock d) (Fock d)) (γ : ℝ) (hγ : 1<γ)
    (hΛ : ∀ a A, Λ.toLinearMap (displacementTraceMap a A)=
      displacementTraceMap (Real.sqrt γ • a) (Λ.toLinearMap A))
    (q : Fin d → ℝ) (hq0 : ∀ i,0≤q i) (hq1 : ∀ i,q i<1) :
    ∃ σ : TraceClass (Fock d), 0≤σ.1 ∧ traceCLM σ=1 ∧
      ∀ a : Fin d → ℂ,
        tracePairing (Λ.toLinearMap (vectorMixture (numberBasis d) (productGeometric q)))
          (displacement a)=
        (∏ i, (Real.exp (-‖a i‖^2/(2*(1-Thermal.amplified γ (q i)))) : ℂ)) *
          tracePairing σ (displacement (-(diagonalScale
            (fun i => Real.sqrt (Thermal.amplified γ (q i))/
              Real.sqrt (1-Thermal.amplified γ (q i))) (star a)))) := by
  obtain ⟨σ,hσ,ht,hc⟩ := thermalOutput_exists_reflected_idler Λ γ hγ hΛ q hq0 hq1
  refine ⟨σ,hσ,ht,fun a => ?_⟩
  rw [hc]
  have hb : (fun i => (Real.sqrt (modeGain γ (q i)-1) : ℂ)*star (a i))=
      diagonalScale (fun i => Real.sqrt (Thermal.amplified γ (q i))/
        Real.sqrt (1-Thermal.amplified γ (q i))) (star a) := by
    funext i
    simp only [diagonalScale, amplified_sqrt_odds hγ (hq0 i) (hq1 i), Pi.star_apply]
  have he : (∏ i, (Real.exp (-(modeGain γ (q i)*‖a i‖^2)/2) : ℂ))=
      ∏ i, (Real.exp (-‖a i‖^2/(2*(1-Thermal.amplified γ (q i)))) : ℂ) := by
    apply Finset.prod_congr rfl
    intro i _
    rw [amplified_gaussian_exponent hγ (hq1 i)]
  rw [hb,he,mul_comm]

end Cloning.CovariantAmplifier
