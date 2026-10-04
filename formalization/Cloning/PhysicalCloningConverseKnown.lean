import Cloning.PhysicalCloningConverseUnknown
import Cloning.PhysicalCloningConverseQuantumReduction

/-! The sharp known-spectrum physical cloning converse: the classical
register is removed by actual CPTP maps, leaving the orbital Gaussian value. -/
noncomputable section
open scoped BigOperators Topology Classical
open Filter MeasureTheory
namespace Cloning.PhysicalCloningConverse
open Cloning.PCT Cloning.PCTLocalChart Cloning.PCTPhysicalFidelity
open Cloning.PCTPhysicalState Cloning.PCTUnitaryTransport Cloning.TensorCloning Cloning.Hybrid
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
variable {k s : ℕ}

theorem orbitState_orbitalParameters_matrix (p : SimpleSpectrum (k+1))
    (e : Fin s ≃ PairIndex (k+1)) (ξ : PhaseSpace 0 s) (n : ℕ) :
    (orbitState p (localUnitary p (orbitalParameters e ξ) n)).matrix =
      chartMatrix p (orbitalParameters e ξ) n := by
  change _ * _ * _ = _
  rw [localUnitary_star]
  simp only [chartMatrix, orbitalParameters, Pi.zero_apply, mul_zero, add_zero]
  rfl

theorem known_fixedWindow_errors
    (p : SimpleSpectrum (k+1)) (b : Fin (k+1) → EuclideanSpace ℝ (Fin (k+1)))
    (e : Fin s ≃ PairIndex (k+1)) (lan : CompactWindowLAN p b e)
    (m : ℕ → ℕ) (g : ℝ) (hg : 0 < g)
    (hratio : Tendsto (fun n => (m n : ℝ)/(n : ℝ)) atTop (𝓝 g)) (L : ℕ) :
    ∃ δ η : ℕ → ℝ, Tendsto δ atTop (𝓝 0) ∧ Tendsto η atTop (𝓝 0) ∧
      ∀ᶠ n in atTop, ∀ ξ ∈ phaseSpaceBox 0 s ((L : ℝ)+1),
        let U := localUnitary p (orbitalParameters e ξ) n
        (‖(removeClassicalReverse (lan.reverse n)).map (translatedPositive ξ (orbitalReference p e)).1 -
          (tensorState (orbitState p U) n).1‖ ≤ δ n) ∧
        (‖(removeClassicalForward (lan.forward (m n))).map (tensorState (orbitState p U) (m n)).1 -
          (translatedPositive (Real.sqrt g • ξ) (orbitalReference p e)).1‖ ≤ η n) := by
  let K := orbitalParameters e '' phaseSpaceBox 0 s ((L : ℝ)+1)
  have hK : IsCompact K := (phaseSpaceBox_compact 0 s _).image (continuous_orbitalParameters e)
  have hz : ∀ θ ∈ K, ∑ i, θ.1 i = 0 := by
    rintro θ ⟨ξ,hξ,rfl⟩
    exact orbitalParameters_sum_zero e ξ
  have hm := output_size_tendsto m g hg hratio
  obtain ⟨δ,η,hδ,hη,hbound⟩ := scaled_window_approximations p b e lan m hm
    (fun n => sampleRatio n (m n)) (Real.sqrt g) (sampleRatio_tendsto m g hratio) K hK hz
  refine ⟨δ,η,hδ,hη,?_⟩
  filter_upwards [hbound,hm.eventually (eventually_gt_atTop 0)] with n hn hmn ξ hξ
  let θ := orbitalParameters e ξ
  let U := localUnitary p θ n
  have hθ : θ ∈ K := ⟨ξ,hξ,rfl⟩
  have hinput : (tensorState (orbitState p U) n).1 = chartTensor p θ n := by
    change matrixTensorPower _ n = _
    rw [orbitState_orbitalParameters_matrix]
    rfl
  have houtput : (tensorState (orbitState p U) (m n)).1 =
      chartTensor p (sampleRatio n (m n) • θ) (m n) := by
    change matrixTensorPower _ (m n) = matrixTensorPower _ (m n)
    rw [orbitState_orbitalParameters_matrix, chartMatrix_rescale p θ n (m n) hmn]
  have hmodel := model_orbitalParameters_eq_prepare p b e ξ
  have hmodelout := model_orbitalParameters_eq_prepare p b e (Real.sqrt g • ξ)
  rw [orbitalParameters_smul] at hmodelout
  constructor
  · rw [translated_orbitalReference_eq_prepare, removeClassicalReverse_prepare, ← hmodel, hinput]
    exact (hn θ hθ).1
  · rw [translated_orbitalReference_eq_prepare]
    apply (removeClassicalForward_error (lan.forward (m n)) _
      (displacedProductThermal p e (Real.sqrt g • ξ).2)).trans
    rw [← hmodelout, houtput]
    exact (hn θ hθ).2

/-- The all-physical-channel known-spectrum minimax upper bound. Its sole
analytic input is the explicit genuine mixed-LAN construction. -/
theorem limsup_knownSpectrumValue_le_of_compactWindowLAN
    (p : SimpleSpectrum (k+1)) (b : Fin (k+1) → EuclideanSpace ℝ (Fin (k+1)))
    (e : Fin s ≃ PairIndex (k+1)) (lan : CompactWindowLAN p b e)
    (m : ℕ → ℕ) (g : ℝ) (hg : 1 < g)
    (hratio : Tendsto (fun n => (m n : ℝ)/(n : ℝ)) atTop (𝓝 g)) :
    limsup (fun n => knownSpectrumValue n (m n) p) atTop ≤ orbitalValue g p := by
  choose δ η hδ hη hbound using fun L =>
    known_fixedWindow_errors p b e lan m g (by linarith) hratio L
  have hd : ∀ L, ∀ᶠ n in atTop, ∀ᵐ ξ ∂(flatBoxDensity 0 s).expandingPrior L,
      ‖(removeClassicalReverse (lan.reverse n)).map (translatedPositive ξ (orbitalReference p e)).1 -
        (tensorState (orbitState p (localUnitary p (orbitalParameters e ξ) n)) n).1‖ ≤ δ L n := by
    intro L
    filter_upwards [hbound L] with n hn
    exact (ae_flatBox_mem L).mono fun ξ hξ => (hn ξ hξ).1
  have he : ∀ L, ∀ᶠ n in atTop, ∀ᵐ ξ ∂(flatBoxDensity 0 s).expandingPrior L,
      ‖(removeClassicalForward (lan.forward (m n))).map
        (tensorState (orbitState p (localUnitary p (orbitalParameters e ξ) n)) (m n)).1 -
        (translatedPositive (Real.sqrt g • ξ) (orbitalReference p e)).1‖ ≤ η L n := by
    intro L
    filter_upwards [hbound L] with n hn
    exact (ae_flatBox_mem L).mono fun ξ hξ => (hn ξ hξ).2
  have h := limsup_statePayoff_le_modeFactor_of_approximations (orbitState p)
    m (flatBoxDensity 0 s) (fun _ : Fin 0 => 1/2) (fun _ => by norm_num) g hg
    (fun i => p.ratio (e i)) (fun i => (p.ratio_pos (e i)).le) (fun i => p.ratio_lt_one (e i))
    (fun n => removeClassicalReverse (lan.reverse n))
    (fun n => removeClassicalForward (lan.forward (m n)))
    (fun n ξ => localUnitary p (orbitalParameters e ξ) n) δ η hd he hδ hη
  have hprod := e.prod_comp (fun ij => Thermal.modeFactor g (p.ratio ij))
  simpa only [knownSpectrumValue, spectrumPayoff, orbitalValue, Nat.cast_zero, zero_div,
    Real.rpow_zero, one_mul, hprod] using h

end Cloning.PhysicalCloningConverse
