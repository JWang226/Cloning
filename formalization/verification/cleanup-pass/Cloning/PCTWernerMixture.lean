import Cloning.GeneralCoherentMixture
import Cloning.WernerPhysicalAgreement

/-! Gaussian pure-product mixtures approximate the actual physical Werner
output in trace norm. This joins the independently proved occupation law,
thermal limit, actual two-way occupation channels, and unbounded Gaussian
integration. It is the pure-state precursor of the PCT mixture formula. -/
noncomputable section
open scoped BigOperators InnerProductSpace ComplexOrder Topology
open Filter MeasureTheory Cloning.InfiniteTraceClass
namespace Cloning.GeneralCoherent
open GeneralSymmetricOccupation MultimodeCoherentGaussianMixture
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

theorem occupationChannel_numberVector (L s : ℕ) (q : Occupation L (s + 1)) :
    (occupationChannel L s).toLinearMap (vectorProjector (numberVector (excitation q))) =
      vectorProjector (column q) := by
  rw [← occupationPad_single L s q]
  change (QuantumChannel.ofIsometry (isometry L (s + 1))).toLinearMap
    ((QuantumChannel.isometricRecovery (occupationPad L s) (vacuumRegister L s)).toLinearMap
      (vectorProjector (occupationPad L s (lp.single 2 q 1)))) = _
  rw [QuantumChannel.isometricRecovery_vectorProjector,
    QuantumChannel.ofIsometry_vectorProjector, isometry_single]

/-- The actual forward occupation channel restores the physical Werner output
exactly. In particular the replacement term carries zero mass on that output. -/
theorem occupationChannel_recovery_wernerOutput {L s : ℕ} (S : Finset (Fin L)) :
    (occupationChannel L s).toLinearMap
      ((GeneralSymmetricOccupation.occupationRecovery L s).toLinearMap
        (wernerOutput (s := s) S)) = wernerOutput (s := s) S := by
  simp only [wernerOutput, map_sum, map_smul, occupationRecovery_column,
    occupationChannel_numberVector]

/-- The Gaussian with variance `γ-1` in each excitation coordinate is exactly
the thermal operator appearing in the physical Werner limit. -/
theorem coherentMixture_gaussian_eq_thermal {s : ℕ} {γ : ℝ} (hγ : 1 < γ) :
    coherentMixture (gaussianProductMeasure (fun _ : Fin s => γ - 1)) =
      InfiniteOccupationStates.thermalOperator (@numberVector s) γ := by
  unfold coherentMixture
  rw [integral_coherentProjector_gaussian_eq_productThermal (fun _ => by linarith)]
  congr 1
  · funext k
    exact numberBasis_eq_single k
  · funext k
    simp only [WernerAsymptotics.thermalLaw, show 1 + (γ - 1) = γ by ring]

theorem wernerOutput_thermal_distance_le {L s : ℕ} (S : Finset (Fin L))
    {γ : ℝ} (hγ : 1 < γ) :
    ‖wernerOutput (s := s) S - (occupationChannel L s).toLinearMap
      (InfiniteOccupationStates.thermalOperator (@numberVector s) γ)‖ ≤
      ‖(GeneralSymmetricOccupation.occupationRecovery L s).toLinearMap
        (wernerOutput (s := s) S) -
        InfiniteOccupationStates.thermalOperator (@numberVector s) γ‖ := by
  have hc := (occupationChannel L s).toPositiveTracePreservingMap.norm_map_sub_le
    ((GeneralSymmetricOccupation.occupationRecovery L s).toLinearMap (wernerOutput (s := s) S))
    (InfiniteOccupationStates.thermalOperator (@numberVector s) γ)
    ((GeneralSymmetricOccupation.occupationRecovery L s).map_nonneg _ (wernerOutput_nonneg S))
    (InfiniteOccupationStates.thermalOperator_nonneg _ numberVector_norm hγ)
  simpa only [occupationChannel_recovery_wernerOutput] using hc

/-- The full unbounded Gaussian mixture of literal finite tensor-power states
approximates the actual physical Werner output. All three approximation steps
are proved; the only asymptotic premise is the cloning ratio. -/
theorem physical_werner_gaussian_product_mixture {s : ℕ} (hs : 1 ≤ s)
    (m : ℕ → ℕ) (hm : ∀ n, n ≤ m n) {γ : ℝ} (hγ : 1 < γ)
    (h : Tendsto (fun n ↦ (m n : ℝ) / n) atTop (𝓝 γ)) :
    Tendsto (fun n => ‖wernerOutput (s := s) (inputSlots n (m n) (hm n)) -
      productMixture (m n) (gaussianProductMeasure (fun _ : Fin s => γ - 1))‖)
      atTop (𝓝 0) := by
  let μ := gaussianProductMeasure (fun _ : Fin s => γ - 1)
  letI : IsProbabilityMeasure μ := gaussianProductMeasure_probability (fun _ => by linarith)
  have hmTop : Tendsto m atTop atTop := tendsto_atTop_mono hm tendsto_id
  have ht := physical_werner_traceNorm_limit hs m hm hγ h
  have hg := (occupationChannel_mixture_tendsto μ).comp hmTop
  have hsum : Tendsto (fun n =>
      ‖(GeneralSymmetricOccupation.occupationRecovery (m n) s).toLinearMap
        (wernerOutput (s := s) (inputSlots n (m n) (hm n))) -
        InfiniteOccupationStates.thermalOperator (@numberVector s) γ‖ +
      ‖(occupationChannel (m n) s).toLinearMap (coherentMixture μ) -
        productMixture (m n) μ‖) atTop (𝓝 0) := by
    simpa only [Function.comp_def, add_zero] using ht.add hg
  apply squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) hsum
  calc
    _ ≤ ‖wernerOutput (s := s) (inputSlots n (m n) (hm n)) -
        (occupationChannel (m n) s).toLinearMap (coherentMixture μ)‖ +
      ‖(occupationChannel (m n) s).toLinearMap (coherentMixture μ) -
        productMixture (m n) μ‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ _ := by
      apply add_le_add_left
      have he : coherentMixture μ = InfiniteOccupationStates.thermalOperator (@numberVector s) γ :=
        coherentMixture_gaussian_eq_thermal hγ
      rw [he]
      exact wernerOutput_thermal_distance_le _ hγ

/-- The same end-to-end result starts from the constructed full CPTP Werner
channel on its pure reference input, not an assumed diagonal state. -/
theorem wernerChannel_gaussian_product_mixture {s : ℕ} (hs : 1 ≤ s)
    (r : ℕ → ℕ) {γ : ℝ} (hγ : 1 < γ)
    (h : Tendsto (fun n ↦ ((n + r n : ℕ) : ℝ) / n) atTop (𝓝 γ)) :
    Tendsto (fun n => ‖InfiniteFiniteCorner.matrixLift (@column (n + r n) (s + 1))
      ((wernerChannel n (r n) s).toFun (pureInputMatrix n (s + 1) 0)) -
      productMixture (n + r n) (gaussianProductMeasure (fun _ : Fin s => γ - 1))‖)
      atTop (𝓝 0) := by
  simp only [wernerChannel_pure_output]
  exact physical_werner_gaussian_product_mixture hs (fun n => n + r n)
    (fun n => Nat.le_add_right n (r n)) hγ h

/-- The approximation survives arbitrary output channels, even with a
changing output Hilbert space. The Gaussian integral commutes with the actual
channel; no pointwise integrability or continuity premise is left to prove. -/
theorem physical_werner_gaussian_mixture_after_channels {s : ℕ} (hs : 1 ≤ s)
    (m : ℕ → ℕ) (hm : ∀ n, n ≤ m n) {γ : ℝ} (hγ : 1 < γ)
    (h : Tendsto (fun n ↦ (m n : ℝ) / n) atTop (𝓝 γ))
    {K : ℕ → Type*} [∀ n, NormedAddCommGroup (K n)]
    [∀ n, InnerProductSpace ℂ (K n)] [∀ n, CompleteSpace (K n)]
    (Φ : ∀ n, QuantumChannel (TensorSpace (m n) (s + 1)) (K n)) :
    Tendsto (fun n => ‖(Φ n).toLinearMap
      (wernerOutput (s := s) (inputSlots n (m n) (hm n))) -
      ∫ z, (Φ n).toLinearMap (vectorProjector (productTensor z (m n)))
        ∂gaussianProductMeasure (fun _ : Fin s => γ - 1)‖) atTop (𝓝 0) := by
  let μ := gaussianProductMeasure (fun _ : Fin s => γ - 1)
  letI : IsProbabilityMeasure μ := gaussianProductMeasure_probability (fun _ => by linarith)
  have ht := (physical_werner_gaussian_product_mixture hs m hm hγ h).const_mul 2
  have ht' : Tendsto (fun n => 2 * ‖wernerOutput (s := s) (inputSlots n (m n) (hm n)) -
      productMixture (m n) μ‖) atTop (𝓝 0) := by simpa using ht
  apply squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) ht'
  let C := (Φ n).toPositiveTracePreservingMap.toContinuousLinearMap
  have he : (∫ z, (Φ n).toLinearMap (vectorProjector (productTensor z (m n))) ∂μ) =
      (Φ n).toLinearMap (productMixture (m n) μ) :=
    C.integral_comp_comm (integrable_productProjector (m n) μ)
  change ‖(Φ n).toLinearMap _ - ∫ z, (Φ n).toLinearMap
    (vectorProjector (productTensor z (m n))) ∂μ‖ ≤ _
  rw [he, ← map_sub]
  exact (Φ n).toPositiveTracePreservingMap.norm_map_le_two_mul _

end Cloning.GeneralCoherent
