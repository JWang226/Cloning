import Cloning.AmplifierWeylThermal

/-! The literal composite amplifier used in the least-noise argument.
Its vacuum output and modewise gains are proved for every competing
covariant channel. No idler representation is assumed or asserted. -/
noncomputable section
open scoped BigOperators InnerProductSpace Topology ComplexOrder
namespace Cloning.CovariantAmplifier
open Cloning.InfiniteTraceClass Cloning.MultimodeCoherent
open Cloning.MultimodeCoherentGaussianMixture Cloning.ThermalWitness
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
variable {d : ℕ}

def modeGain (γ q : ℝ) : ℝ := γ/(1-q)

theorem modeGain_gt_one {γ q : ℝ} (hγ : 1<γ) (hq0 : 0≤q) (hq1 : q<1) :
    1<modeGain γ q := by
  apply (lt_div_iff₀ (sub_pos.mpr hq1)).mpr
  linarith

theorem modeGain_noise {γ q : ℝ} (hγ : γ≠0) (hq1 : q<1) :
    1-(modeGain γ q)⁻¹=Cloning.Thermal.amplified γ q := by
  unfold modeGain Cloning.Thermal.amplified
  rw [inv_div]

theorem sqrt_modeGain {γ q : ℝ} (hγ : 0≤γ) :
    Real.sqrt (modeGain γ q)=Real.sqrt γ*(Real.sqrt (1-q))⁻¹ := by
  rw [modeGain,Real.sqrt_div hγ,div_eq_mul_inv]

/-- The physical pre-amplification followed by an arbitrary physical channel. -/
def compositeChannel (Λ : QuantumChannel (Fock d) (Fock d)) (q : Fin d → ℝ)
    (hq0 : ∀ i,0≤q i) (hq1 : ∀ i,q i<1) : QuantumChannel (Fock d) (Fock d) :=
  Λ.comp (Cloning.MultimodeAmplifier.channel q hq0 hq1)

/-- The composite sends the joint vacuum to the competing channel's actual
product-thermal output, including every coherence in that output. -/
theorem compositeChannel_vacuum (Λ : QuantumChannel (Fock d) (Fock d)) (q : Fin d → ℝ)
    (hq0 : ∀ i,0≤q i) (hq1 : ∀ i,q i<1) :
    (compositeChannel Λ q hq0 hq1).toLinearMap (coherentProjector (0 : Fin d → ℂ)) =
      Λ.toLinearMap (vectorMixture (numberBasis d) (productGeometric q)) := by
  change Λ.toLinearMap ((Cloning.MultimodeAmplifier.channel q hq0 hq1).toLinearMap
    (coherentProjector (0 : Fin d → ℂ))) = _
  rw [Cloning.MultimodeAmplifier.channel_vacuum]

/-- All-complex-input modewise covariance of the genuine composite. -/
theorem compositeChannel_covariant (Λ : QuantumChannel (Fock d) (Fock d))
    (γ : ℝ) (hγ : 0≤γ)
    (hΛ : ∀ a A, Λ.toLinearMap (displacementTraceMap a A) =
      displacementTraceMap (Real.sqrt γ • a) (Λ.toLinearMap A))
    (q : Fin d → ℝ) (hq0 : ∀ i,0≤q i) (hq1 : ∀ i,q i<1)
    (a : Fin d → ℂ) (A : TraceClass (Fock d)) :
    (compositeChannel Λ q hq0 hq1).toLinearMap (displacementTraceMap a A) =
      displacementTraceMap (fun i => (Real.sqrt (modeGain γ (q i)) : ℂ)*a i)
        ((compositeChannel Λ q hq0 hq1).toLinearMap A) := by
  change Λ.toLinearMap ((Cloning.MultimodeAmplifier.channel q hq0 hq1).toLinearMap
    (displacementTraceMap a A)) = _
  rw [Cloning.MultimodeAmplifier.channel_weyl_covariant,hΛ]
  have he : Real.sqrt γ • (fun i => (((Real.sqrt (1-q i))⁻¹ : ℝ) : ℂ)*a i) =
      (fun i => (Real.sqrt (modeGain γ (q i)) : ℂ)*a i) := by
    funext i
    rw [sqrt_modeGain hγ]
    simp only [Pi.smul_apply,Complex.real_smul,Complex.ofReal_mul,mul_assoc]
  rw [he]
  rfl

/-- The complete concrete composite-gain reduction in the manuscript's
strictly amplifying regime. The remaining idler classification is separate. -/
theorem composite_amplifier_reduction (Λ : QuantumChannel (Fock d) (Fock d))
    (γ : ℝ) (hγ : 1<γ)
    (hΛ : ∀ a A, Λ.toLinearMap (displacementTraceMap a A) =
      displacementTraceMap (Real.sqrt γ • a) (Λ.toLinearMap A))
    (q : Fin d → ℝ) (hq0 : ∀ i,0≤q i) (hq1 : ∀ i,q i<1) :
    ((compositeChannel Λ q hq0 hq1).toLinearMap (coherentProjector (0 : Fin d → ℂ)) =
      Λ.toLinearMap (vectorMixture (numberBasis d) (productGeometric q))) ∧
    (∀ a A, (compositeChannel Λ q hq0 hq1).toLinearMap (displacementTraceMap a A) =
      displacementTraceMap (fun i => (Real.sqrt (modeGain γ (q i)) : ℂ)*a i)
        ((compositeChannel Λ q hq0 hq1).toLinearMap A)) ∧
    (∀ i,1<modeGain γ (q i)) ∧
    (∀ i,1-(modeGain γ (q i))⁻¹=Cloning.Thermal.amplified γ (q i)) :=
  ⟨compositeChannel_vacuum Λ q hq0 hq1,
    compositeChannel_covariant Λ γ (by linarith) hΛ q hq0 hq1,
    fun i => modeGain_gt_one hγ (hq0 i) (hq1 i),
    fun i => modeGain_noise (by linarith) (hq1 i)⟩

end Cloning.CovariantAmplifier
