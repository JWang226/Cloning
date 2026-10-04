import Cloning.CovariantAmplifierLeastNoiseIdler
import Cloning.CovariantAmplifierTraceLoss
import Cloning.MultimodeIdlerCharacteristic
import Cloning.MultimodeLeastNoise

/-! The least-noise moment inequality for every actual covariant CP
trace-nonincreasing map. The normalized idler and the output number law are
derived from the map, and its exact success trace is retained. -/
noncomputable section
open scoped ComplexOrder InnerProductSpace Topology BigOperators
namespace Cloning.CovariantAmplifier
open InfiniteTraceClass MultimodeCoherent MultimodeCoherentGaussianMixture ThermalWitness
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
variable {d : ℕ}

/-- Equality with the literal seeded channel follows from the actual
characteristic law, not from an assumed idler representation. -/
theorem thermalOutput_exists_seeded_idler
    (Λ : QuantumChannel (Fock d) (Fock d)) (γ : ℝ) (hγ : 1<γ)
    (hΛ : ∀ a A, Λ.toLinearMap (displacementTraceMap a A)=
      displacementTraceMap (Real.sqrt γ • a) (Λ.toLinearMap A))
    (q : Fin d → ℝ) (hq0 : ∀ i,0≤q i) (hq1 : ∀ i,q i<1) :
    ∃ σ : TraceClass (Fock d), 0≤σ.1 ∧ traceCLM σ=1 ∧
      Λ.toLinearMap (vectorMixture (numberBasis d) (productGeometric q))=
        (MultimodeIdler.channel (fun i => Thermal.amplified γ (q i))
          (fun i => Thermal.amplified_nonneg hγ (hq0 i) (hq1 i))
          (fun i => Thermal.amplified_lt_one (lt_trans zero_lt_one hγ) (hq1 i))).toLinearMap σ := by
  obtain ⟨σ,hσ,ht,hc⟩ := thermalOutput_exists_seeded_characteristic Λ γ hγ hΛ q hq0 hq1
  refine ⟨σ,hσ,ht,?_⟩
  apply characteristic_injective
  funext a
  exact (hc a).trans (MultimodeIdler.channel_characteristic (fun i => Thermal.amplified γ (q i))
    (fun i => amplified_pos hγ (hq0 i) (hq1 i))
    (fun i => Thermal.amplified_lt_one (lt_trans zero_lt_one hγ) (hq1 i)) σ a).symm

/-- Every bounded observable with a nonnegative antitone product number
spectrum satisfies the sharp amplified-thermal comparison. -/
theorem quantumChannel_moment_le_of_diagonal
    (Λ : QuantumChannel (Fock d) (Fock d)) (γ : ℝ) (hγ : 1<γ)
    (hΛ : ∀ a A, Λ.toLinearMap (displacementTraceMap a A)=
      displacementTraceMap (Real.sqrt γ • a) (Λ.toLinearMap A))
    (q : Fin d → ℝ) (hq0 : ∀ i,0≤q i) (hq1 : ∀ i,q i<1)
    (w : Fin d → ℕ → ℝ) (hw0 : ∀ i k,0≤w i k) (hw : ∀ i,Antitone (w i))
    (W : Fock d →L[ℂ] Fock d)
    (hW : ∀ k, W (numberBasis d k)=((∏ i,w i (k i) : ℝ) : ℂ) • numberBasis d k) :
    (tracePairing (Λ.toLinearMap (vectorMixture (numberBasis d) (productGeometric q))) W).re≤
      (tracePairing (vectorMixture (numberBasis d)
        (productGeometric (fun i => Thermal.amplified γ (q i)))) W).re := by
  obtain ⟨σ,hσ,ht,he⟩ := thermalOutput_exists_seeded_idler Λ γ hγ hΛ q hq0 hq1
  rw [he]
  have ht' : (trace σ.1 σ.2).re=1 := congrArg Complex.re ht
  simpa only [ht',one_mul] using MultimodeLeastNoise.moment_le_of_diagonal σ hσ
    (fun i => Thermal.amplified γ (q i))
    (fun i => Thermal.amplified_nonneg hγ (hq0 i) (hq1 i))
    (fun i => Thermal.amplified_lt_one (lt_trans zero_lt_one hγ) (hq1 i)) w hw0 hw W hW

/-- The concrete product observable requires only nonnegativity and
antitonicity; boundedness follows automatically from its value at zero. -/
theorem quantumChannel_product_moment_le
    (Λ : QuantumChannel (Fock d) (Fock d)) (γ : ℝ) (hγ : 1<γ)
    (hΛ : ∀ a A, Λ.toLinearMap (displacementTraceMap a A)=
      displacementTraceMap (Real.sqrt γ • a) (Λ.toLinearMap A))
    (q : Fin d → ℝ) (hq0 : ∀ i,0≤q i) (hq1 : ∀ i,q i<1)
    (w : Fin d → ℕ → ℝ) (hw0 : ∀ i k,0≤w i k) (hw : ∀ i,Antitone (w i)) :
    (tracePairing (Λ.toLinearMap (vectorMixture (numberBasis d) (productGeometric q)))
      (MultimodeLeastNoise.productObservable w hw0 hw)).re≤
      (tracePairing (vectorMixture (numberBasis d)
        (productGeometric (fun i => Thermal.amplified γ (q i))))
          (MultimodeLeastNoise.productObservable w hw0 hw)).re :=
  quantumChannel_moment_le_of_diagonal Λ γ hγ hΛ q hq0 hq1 w hw0 hw _
    (MultimodeLeastNoise.productObservable_apply_basis w hw0 hw)

/-- The full covariant CP/TNI comparison retains the exact output trace,
including the zero-success case. -/
theorem covariant_cpTNI_moment_le_of_diagonal
    (Γ : TraceClass (Fock d) →ₗ[ℂ] TraceClass (Fock d))
    (hCP : IsCompletelyPositive Γ)
    (htrace : ∀ A,0≤A.1 → (traceCLM (Γ A)).re≤(traceCLM A).re)
    (γ : ℝ) (hγ : 1<γ)
    (hΓ : ∀ a A, Γ (displacementTraceMap a A)=displacementTraceMap (Real.sqrt γ • a) (Γ A))
    (q : Fin d → ℝ) (hq0 : ∀ i,0≤q i) (hq1 : ∀ i,q i<1)
    (w : Fin d → ℕ → ℝ) (hw0 : ∀ i k,0≤w i k) (hw : ∀ i,Antitone (w i))
    (W : Fock d →L[ℂ] Fock d)
    (hW : ∀ k, W (numberBasis d k)=((∏ i,w i (k i) : ℝ) : ℂ) • numberBasis d k) :
    (tracePairing (Γ (vectorMixture (numberBasis d) (productGeometric q))) W).re≤
      (traceCLM (Γ (vectorMixture (numberBasis d) (productGeometric q)))).re *
        (tracePairing (vectorMixture (numberBasis d)
          (productGeometric (fun i => Thermal.amplified γ (q i)))) W).re := by
  apply covariant_tni_trace_scaled_moment_le (Real.sqrt γ) _
    (productThermal_trace_one q hq0 hq1) W _ ?_ Γ hCP htrace hΓ
  intro Λ hΛ
  exact quantumChannel_moment_le_of_diagonal Λ γ hγ hΛ q hq0 hq1 w hw0 hw W hW

/-- Least-noise moment for arbitrary antitone product tests and every actual
covariant completely positive trace-nonincreasing map. No normalized-channel,
idler, number-law, Gaussian-output, or positive-success assumption is supplied. -/
theorem covariant_cpTNI_product_moment_le
    (Γ : TraceClass (Fock d) →ₗ[ℂ] TraceClass (Fock d))
    (hCP : IsCompletelyPositive Γ)
    (htrace : ∀ A,0≤A.1 → (traceCLM (Γ A)).re≤(traceCLM A).re)
    (γ : ℝ) (hγ : 1<γ)
    (hΓ : ∀ a A, Γ (displacementTraceMap a A)=displacementTraceMap (Real.sqrt γ • a) (Γ A))
    (q : Fin d → ℝ) (hq0 : ∀ i,0≤q i) (hq1 : ∀ i,q i<1)
    (w : Fin d → ℕ → ℝ) (hw0 : ∀ i k,0≤w i k) (hw : ∀ i,Antitone (w i)) :
    (tracePairing (Γ (vectorMixture (numberBasis d) (productGeometric q)))
      (MultimodeLeastNoise.productObservable w hw0 hw)).re≤
      (traceCLM (Γ (vectorMixture (numberBasis d) (productGeometric q)))).re *
        (tracePairing (vectorMixture (numberBasis d)
          (productGeometric (fun i => Thermal.amplified γ (q i))))
            (MultimodeLeastNoise.productObservable w hw0 hw)).re :=
  covariant_cpTNI_moment_le_of_diagonal Γ hCP htrace γ hγ hΓ q hq0 hq1 w hw0 hw _
    (MultimodeLeastNoise.productObservable_apply_basis w hw0 hw)

end Cloning.CovariantAmplifier
