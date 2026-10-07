import Cloning.YoungUniformLocalPhysicalL1

/-! Exact recovery of the physical lattice law by quantization, and the
Gaussian reverse approximation obtained from actual density convergence. -/

noncomputable section
open scoped BigOperators Topology Classical ENNReal
open Filter MeasureTheory
namespace Cloning.YoungHyperplane
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

instance latticeMeasurableSpace (d : ℕ) (N : ℤ) : MeasurableSpace (Lattice d N) := by
  unfold Lattice
  infer_instance

instance latticeMeasurableSingletonClass (d : ℕ) (N : ℤ) :
    MeasurableSingletonClass (Lattice d N) := by
  change MeasurableSingletonClass {μ : Fin (d + 1) → ℤ // ∑ i, μ i = N}
  infer_instance

instance latticeCountable (d : ℕ) (N : ℤ) : Countable (Lattice d N) := by
  unfold Lattice
  infer_instance

theorem measurable_sampleLabel (d N : ℕ) (p : Fin (d + 1) → ℝ) :
    Measurable (sampleLabel d N p) := by
  unfold sampleLabel
  apply (measurable_of_countable (latticeCoordinates d (N : ℤ))).comp
  apply YoungRounding.measurable_round.comp
  apply measurable_pi_lambda
  intro i
  exact measurable_const.mul
    ((measurable_pi_apply i).comp (coordinatesContinuous d).symm.continuous.measurable) |>.add_const _

theorem sampleLabel_fiber (d N : ℕ) (p : Fin (d + 1) → ℝ) (μ : Lattice d (N : ℤ)) :
    (sampleLabel d N p) ⁻¹' {μ} = sampleCell d N p μ := by
  ext x
  simp only [Set.mem_preimage, Set.mem_singleton_iff, sampleLabel, sampleCell, Set.mem_setOf_eq,
    Int.cast_natCast, ← YoungRounding.round_eq_iff]
  constructor
  · intro h
    simpa only [Equiv.symm_apply_apply] using congrArg (latticeCoordinates d (N : ℤ)).symm h
  · intro h
    rw [h, Equiv.apply_symm_apply]

/-- Integrating one genuine interpolated physical cell recovers its exact
original label probability. -/
theorem binMass_tensorYoungDensity (d N : ℕ) (hN : 0 < N)
    (p : Fin (d + 1) → ℝ) (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1)
    (μ : Lattice d (N : ℤ)) :
    YoungRounding.binMass volume (sampleLabel d N p) (tensorYoungDensity d N p hp hs) μ =
      (tensorYoungLatticePMF d N p hp hs μ).toReal := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hnz : Real.sqrt (N : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hn).ne'
  have hdz : Real.sqrt ((d : ℝ) + 1) ≠ 0 := by positivity
  rw [YoungRounding.binMass, sampleLabel_fiber, tensorYoungDensity]
  rw [setIntegral_congr_fun (measurableSet_sampleCell d N p μ)
    (fun x hx ↦ sampleInterpolate_eq_on_cell d N (by exact_mod_cast hN) p
      (fun μ ↦ (tensorYoungLatticePMF d N p hp hs μ).toReal) μ x hx), setIntegral_const]
  simp only [Measure.real, volume_sampleCell d N (by exact_mod_cast hN),
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity : 0 ≤ Real.sqrt ((d : ℝ) + 1)),
    ENNReal.toReal_ofReal (by positivity : 0 ≤ ((Real.sqrt (N : ℝ)) ^ d)⁻¹),
    smul_eq_mul, Int.cast_natCast]
  field_simp

/-- Quantizing the actual covariance Gaussian approximates the actual Young
label law, with no independently assumed discrete approximation. -/
theorem quantized_covarianceGaussian_l1_le (d N : ℕ) (hN : 0 < N)
    (p : Fin (d + 1) → ℝ) (hp : ∀ i, 0 < p i) (hs : ∑ i, p i = 1) :
    (∑' μ : Lattice d (N : ℤ),
      |(tensorYoungLatticePMF d N p (fun i ↦ (hp i).le) hs μ).toReal -
        YoungRounding.binMass volume (sampleLabel d N p) (covarianceGaussian d p hs) μ|) ≤
      ∫ x, |tensorYoungDensity d N p (fun i ↦ (hp i).le) hs x - covarianceGaussian d p hs x| ∂volume := by
  have h := YoungRounding.binMass_l1_contraction volume (measurable_sampleLabel d N p)
    (integrable_tensorYoungDensity d N hN p (fun i ↦ (hp i).le) hs)
    (integrable_covarianceGaussian d p hs hp)
  simpa only [binMass_tensorYoungDensity d N hN p (fun i ↦ (hp i).le) hs] using h

/-- Compact-uniform reverse quantization for the physical Young measurement. -/
theorem uniform_quantized_covarianceGaussian_l1 (d : ℕ) (K : Set (Fin (d + 1) → ℝ))
    (hK : IsCompact K) (hp : ∀ p ∈ K, ∑ i, p i = 1)
    (hp0 : ∀ p ∈ K, ∀ i, 0 < p i) (hord : ∀ p ∈ K, StrictAnti p)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (p : Fin (d + 1) → ℝ) (hpK : p ∈ K),
      (∑' μ : Lattice d (N : ℤ),
        |(tensorYoungLatticePMF d N p (fun i ↦ (hp0 p hpK i).le) (hp p hpK) μ).toReal -
          YoungRounding.binMass volume (sampleLabel d N p) (covarianceGaussian d p (hp p hpK)) μ|) < ε := by
  obtain ⟨N₀, hN₀⟩ := uniform_tensorYoungDensity_l1 d K hK hp hp0 hord ε hε
  refine ⟨max N₀ 1, ?_⟩
  intro N hN p hpK
  exact (quantized_covarianceGaussian_l1_le d N (by omega) p (hp0 p hpK) (hp p hpK)).trans_lt
    (hN₀ N (by omega) p hpK)

end Cloning.YoungHyperplane
