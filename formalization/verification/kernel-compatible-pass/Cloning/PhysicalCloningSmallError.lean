import Cloning.CloningValueExpansionTarget
import Cloning.PhysicalCloningKnownTheorem
import Cloning.PhysicalCloningPCTTheorem
import Cloning.TensorCloningUniversalAchievability
import Cloning.TensorCloningPrescribedLimits

/-! Small-error targets for the physical channels and physical optimum.
The order of quantifiers is the manuscript's iterated limit: the sample
cutoff can depend on the error tolerance. -/
noncomputable section
open scoped Topology Matrix ComplexOrder
open Filter
namespace Cloning.ValueExpansion
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

/-- Transfer concrete scalar target brackets to a finite-sample fidelity
whose fixed-gain limit is known. -/
theorem physical_target_brackets_of_tendsto {F : ℝ → ℕ → ℝ} {f : ℝ → ℝ}
    {a η : ℝ} (ha : 0 < a) (hη : 0 < η) (hη1 : η < 1)
    (hlim : Tendsto (fun δ => (1-f δ)/δ^2) (𝓝[>] (0:ℝ)) (𝓝 a))
    (hphysical : ∀ δ, 0 < δ → Tendsto (F δ) atTop (𝓝 (f δ))) :
    ∀ᶠ ε in 𝓝[>] (0:ℝ), ∀ᶠ n in atTop,
      1-ε < F ((1-η)*Real.sqrt (ε/a)) n ∧
      F ((1+η)*Real.sqrt (ε/a)) n < 1-ε := by
  filter_upwards [fidelity_target_brackets ha hη hη1 hlim,
    self_mem_nhdsWithin] with ε hε hεpos
  have hroot : 0 < Real.sqrt (ε/a) := Real.sqrt_pos.mpr (div_pos hεpos ha)
  exact ((hphysical _ (mul_pos (sub_pos.mpr hη1) hroot)).eventually_const_lt hε.1).and
    ((hphysical _ (mul_pos (by linarith) hroot)).eventually_lt_const hε.2)

/-- Actual optimum over all physical CPTP maps at a fixed simple spectrum:
the predicted gain straddles the squared-fidelity target. -/
theorem known_physical_target_brackets {k : ℕ} (hk : 1 ≤ k)
    (p : SimpleSpectrum (k+1)) (m : ℝ → ℕ → ℕ)
    (hgain : ∀ δ, 0 < δ →
      Tendsto (fun n => (m δ n : ℝ)/n) atTop (𝓝 (1+δ)))
    {η : ℝ} (hη : 0 < η) (hη1 : η < 1) :
    ∀ᶠ ε in 𝓝[>] (0:ℝ), ∀ᶠ n in atTop,
      1-ε < TensorCloning.knownSpectrumValue n
        (m ((1-η)*Real.sqrt (ε/knownCoefficient p)) n) p ^ 2 ∧
      TensorCloning.knownSpectrumValue n
        (m ((1+η)*Real.sqrt (ε/knownCoefficient p)) n) p ^ 2 < 1-ε := by
  apply physical_target_brackets_of_tendsto
    (F := fun δ n => TensorCloning.knownSpectrumValue n (m δ n) p ^ 2)
    (knownCoefficient_pos (by omega) p)
    hη hη1 (known_infidelity_div_sq_tendsto p)
  intro δ hδ
  exact (TensorCloning.knownSpectrumValue_tendsto p (m δ) (1+δ)
    (by linarith) (hgain δ hδ)).pow 2

/-- The actual state-independent PCT channel has the larger small-error
coefficient at every full-rank density matrix with distinct eigenvalues. -/
theorem pct_physical_target_brackets {k : ℕ} (hk : 1 ≤ k)
    (ρ : MatrixFidelity.State (Fin (k+1))) (hpos : ρ.matrix.PosDef)
    (hsimple : Function.Injective ρ.positive.isHermitian.eigenvalues)
    (r : ℝ → ℕ → ℕ)
    (hgain : ∀ δ, 0 < δ →
      Tendsto (fun n => ((n+r δ n : ℕ):ℝ)/n) atTop (𝓝 (1+δ)))
    {η : ℝ} (hη : 0 < η) (hη1 : η < 1) :
    let p := PCTPhysicalState.densitySpectrum ρ hpos hsimple
    ∀ᶠ ε in 𝓝[>] (0:ℝ), ∀ᶠ n in atTop,
      1-ε < ((PCTPhysicalState.physicalPCTOutput ρ n
        (r ((1-η)*Real.sqrt (ε/pctCoefficient p)) n)).rootFidelity
        (PCTPhysicalState.tensorState ρ
          (n+r ((1-η)*Real.sqrt (ε/pctCoefficient p)) n))) ^ 2 ∧
      ((PCTPhysicalState.physicalPCTOutput ρ n
        (r ((1+η)*Real.sqrt (ε/pctCoefficient p)) n)).rootFidelity
        (PCTPhysicalState.tensorState ρ
          (n+r ((1+η)*Real.sqrt (ε/pctCoefficient p)) n))) ^ 2 < 1-ε := by
  dsimp only
  apply physical_target_brackets_of_tendsto
    (F := fun δ n => ((PCTPhysicalState.physicalPCTOutput ρ n (r δ n)).rootFidelity
      (PCTPhysicalState.tensorState ρ (n+r δ n))) ^ 2)
    (pctCoefficient_pos (by omega) (PCTPhysicalState.densitySpectrum ρ hpos hsimple))
    hη hη1 (pct_infidelity_div_sq_tendsto _)
  intro δ hδ
  exact (PCTPhysicalState.physical_pct_fidelity hk ρ hpos hsimple (r δ)
    (1+δ) (by linarith) (hgain δ hδ)).pow 2

/-- The explicit state-independent universal channel attains the lower
small-error bracket uniformly over every eigenbasis. -/
theorem universal_physical_target_achievable {k : ℕ} (hk : 1 ≤ k)
    (p : SimpleSpectrum (k+1)) (m : ℝ → ℕ → ℕ)
    (hgain : ∀ δ, 0 < δ →
      Tendsto (fun n => (m δ n : ℝ)/n) atTop (𝓝 (1+δ)))
    {η : ℝ} (hη : 0 < η) (hη1 : η < 1) :
    ∀ᶠ ε in 𝓝[>] (0:ℝ), ∀ᶠ n in atTop,
      ∀ U : unitary (Matrix (Fin (k+1)) (Fin (k+1)) ℂ),
      let M := m ((1-η)*Real.sqrt (ε/universalCoefficient p)) n
      1-ε < TensorCloning.spectrumPayoff n M
        (TensorCloning.universalChannel n M k) p U ^ 2 := by
  have hid : Tendsto (fun ε:ℝ => ε) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  have heps : ∀ᶠ ε in 𝓝[>] (0:ℝ), ε < 1 := hid.eventually_lt_const (by norm_num)
  filter_upwards [universal_target_brackets (by omega) p hη hη1,
    self_mem_nhdsWithin, heps] with ε hbracket hε hε1
  let δ := (1-η)*Real.sqrt (ε/universalCoefficient p)
  have hδ : 0 < δ := mul_pos (sub_pos.mpr hη1)
    (Real.sqrt_pos.mpr (div_pos hε (universalCoefficient_pos (by omega) p)))
  have hpos := universalValue_pos (by linarith : 1 < 1+δ) p
  have hs : (Real.sqrt (1-ε))^2 = 1-ε := Real.sq_sqrt (by linarith)
  have hmargin : 0 < universalValue (1+δ) p-Real.sqrt (1-ε) := by
    have h := hbracket.1
    change 1-ε < universalValue (1+δ) p^2 at h
    nlinarith [Real.sqrt_nonneg (1-ε)]
  have h := TensorCloning.eventually_universalChannel_payoff_lower hk {p}
    (isCompact_singleton) (m δ) (1+δ) (by linarith) (hgain δ hδ)
    (universalValue (1+δ) p-Real.sqrt (1-ε)) hmargin
  filter_upwards [h] with n hn U
  have hh := hn p (Set.mem_singleton p) U
  dsimp only
  change 1-ε < TensorCloning.spectrumPayoff n (m δ n)
    (TensorCloning.universalChannel n (m δ n) k) p U ^ 2
  have hnonneg := TensorCloning.spectrumPayoff_nonneg n (m δ n)
    (TensorCloning.universalChannel n (m δ n) k) p U
  nlinarith [Real.sqrt_nonneg (1-ε)]

/-- Two-sided small-error brackets for the exact prescribed universal
protocol, uniformly over the entire unitary orbit. -/
theorem universal_physical_target_brackets {k : ℕ} (hk : 1 ≤ k)
    (p : SimpleSpectrum (k+1)) (m : ℝ → ℕ → ℕ)
    (hgain : ∀ δ, 0 < δ →
      Tendsto (fun n => (m δ n : ℝ)/n) atTop (𝓝 (1+δ)))
    {η : ℝ} (hη : 0 < η) (hη1 : η < 1) :
    ∀ᶠ ε in 𝓝[>] (0:ℝ), ∀ᶠ n in atTop,
      ∀ U : unitary (Matrix (Fin (k+1)) (Fin (k+1)) ℂ),
      let L := m ((1-η)*Real.sqrt (ε/universalCoefficient p)) n
      let H := m ((1+η)*Real.sqrt (ε/universalCoefficient p)) n
      1-ε < TensorCloning.spectrumPayoff n L
        (TensorCloning.prescribedUniversalChannel n L k) p U ^ 2 ∧
      TensorCloning.spectrumPayoff n H
        (TensorCloning.prescribedUniversalChannel n H k) p U ^ 2 < 1-ε := by
  have hlim (δ : ℝ) (hδ : 0 < δ) :
      Tendsto (fun n => TensorCloning.spectrumPayoff n (m δ n)
        (TensorCloning.prescribedUniversalChannel n (m δ n) k) p 1)
        atTop (𝓝 (universalValue (1+δ) p)) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    filter_upwards [TensorCloning.eventually_uniform_prescribedUniversalChannel_payoff
      hk {p} isCompact_singleton (m δ) (1+δ) (by linarith) (hgain δ hδ) ε hε] with n hn
    simpa only [Real.dist_eq] using hn p (Set.mem_singleton p) 1
  have h := physical_target_brackets_of_tendsto
    (F := fun δ n => TensorCloning.spectrumPayoff n (m δ n)
      (TensorCloning.prescribedUniversalChannel n (m δ n) k) p 1 ^ 2)
    (universalCoefficient_pos (by omega) p) hη hη1
    (universal_infidelity_div_sq_tendsto p) (fun δ hδ => (hlim δ hδ).pow 2)
  filter_upwards [h] with ε hε
  filter_upwards [hε] with n hn U
  have hc (M : ℕ) : TensorCloning.spectrumPayoff n M
      (TensorCloning.prescribedUniversalChannel n M k) p U =
      TensorCloning.spectrumPayoff n M (TensorCloning.prescribedUniversalChannel n M k) p 1 :=
    TensorCloning.spectrumPayoff_unitary_of_covariant n M _ p U
      (TensorCloning.prescribedUniversalChannel_covariant n M k U
        (Unitary.star_mul_self_of_mem U.property))
  dsimp only
  simpa only [hc] using hn

end Cloning.ValueExpansion
