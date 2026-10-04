import Cloning.GeneralCoherentLimits

/-! Compact-uniform, two-way quantum approximation of the explicit pure-state
model in arbitrary finite dimension. Both channels act on the whole operator
spaces and are independent of the local amplitude. -/
noncomputable section
open scoped BigOperators InnerProductSpace ComplexOrder Topology
open Filter Cloning.InfiniteTraceClass
namespace Cloning.GeneralCoherent
open GeneralSymmetricOccupation
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

/-- Uniform Hilbert convergence of the physical occupation vectors on every
compact parameter window. No uniformity or equicontinuity assumption remains. -/
theorem productVector_uniform_on_compact {s : ℕ} {K : Set (Fin s → ℂ)}
    (hK : IsCompact K) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ L in atTop, ∀ z ∈ K,
      ‖productVector z L - MultimodeCoherent.coherentVector z‖ < ε := by
  classical
  by_contra h
  rw [eventually_atTop] at h
  push_neg at h
  choose L hL z hz hbad using h
  have hLtop : Tendsto L atTop atTop := tendsto_atTop_mono hL tendsto_id
  obtain ⟨w, hw, φ, hφ, ht⟩ := hK.tendsto_subseq hz
  have hp := productVector_moving_tendsto (L ∘ φ) (hLtop.comp hφ.tendsto_atTop) (z ∘ φ) ht
  have hc := (MultimodeCoherent.continuous_coherentVector s).tendsto w |>.comp ht
  have he : Tendsto (fun n => ‖productVector (z (φ n)) (L (φ n)) -
      MultimodeCoherent.coherentVector (z (φ n))‖) atTop (𝓝 0) := by
    simpa only [Function.comp_def, sub_self, norm_zero] using (hp.sub hc).norm
  obtain ⟨n, hn⟩ := (he.eventually (gt_mem_nhds hε)).exists
  exact (not_lt_of_ge (hbad (φ n))) hn

theorem productVector_tendstoUniformlyOn_compact {s : ℕ} {K : Set (Fin s → ℂ)}
    (hK : IsCompact K) :
    TendstoUniformlyOn (fun L z => productVector z L) MultimodeCoherent.coherentVector atTop K := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  simpa only [dist_eq_norm, norm_sub_rev] using productVector_uniform_on_compact hK ε hε

/-- A CPTP forward map from multimode Fock space to the entire computational
tensor space; the truncated occupation complement is replaced by vacuum. -/
def occupationChannel (L s : ℕ) : QuantumChannel (FockSpace s) (TensorSpace L (s + 1)) :=
  (QuantumChannel.ofIsometry (isometry L (s + 1))).comp
    (QuantumChannel.isometricRecovery (occupationPad L s) (vacuumRegister L s))

theorem occupationChannel_productVector {s : ℕ} (z : Fin s → ℂ) (L : ℕ) :
    (occupationChannel L s).toLinearMap (vectorProjector (productVector z L)) =
      vectorProjector (productTensor z L) := by
  change (QuantumChannel.ofIsometry (isometry L (s + 1))).toLinearMap
    ((QuantumChannel.isometricRecovery (occupationPad L s) (vacuumRegister L s)).toLinearMap
      (vectorProjector (occupationPad L s (finiteProductVector z L)))) = _
  rw [QuantumChannel.isometricRecovery_vectorProjector,
    QuantumChannel.ofIsometry_vectorProjector, isometry_finiteProductVector]

theorem occupationRecovery_productTensor {s : ℕ} (z : Fin s → ℂ) (L : ℕ) :
    (GeneralSymmetricOccupation.occupationRecovery L s).toLinearMap
      (vectorProjector (productTensor z L)) = vectorProjector (productVector z L) := by
  rw [← isometry_finiteProductVector z L]
  change (QuantumChannel.ofIsometry (occupationPad L s)).toLinearMap
    ((QuantumChannel.isometricRecovery (isometry L (s + 1)) (vacuumRegister L s)).toLinearMap
      (vectorProjector (isometry L (s + 1) (finiteProductVector z L)))) = _
  rw [QuantumChannel.isometricRecovery_vectorProjector, QuantumChannel.ofIsometry_vectorProjector]
  rfl

theorem product_projector_distance_le {s : ℕ} (z : Fin s → ℂ) (L : ℕ) :
    ‖vectorProjector (productVector z L) - vectorProjector (MultimodeCoherent.coherentVector z)‖ ≤
      2 * ‖productVector z L - MultimodeCoherent.coherentVector z‖ := by
  simpa only [productVector_norm, MultimodeCoherent.coherentVector_norm,
    show (1 : ℝ) + 1 = 2 by norm_num] using
    norm_vectorProjector_sub_le (productVector z L) (MultimodeCoherent.coherentVector z)

theorem occupationChannel_coherent_distance_le {s : ℕ} (z : Fin s → ℂ) (L : ℕ) :
    ‖(occupationChannel L s).toLinearMap (vectorProjector (MultimodeCoherent.coherentVector z)) -
      vectorProjector (productTensor z L)‖ ≤
      2 * ‖productVector z L - MultimodeCoherent.coherentVector z‖ := by
  rw [← occupationChannel_productVector z L]
  have hpos (x : FockSpace s) : 0 ≤ (vectorProjector x).1 :=
    (InnerProductSpace.rankOne ℂ x x).nonneg_iff_isPositive.mpr
      (InnerProductSpace.isPositive_rankOne_self x)
  refine ((occupationChannel L s).toPositiveTracePreservingMap.norm_map_sub_le _ _
    (hpos _) (hpos _)).trans ?_
  simpa only [norm_sub_rev] using product_projector_distance_le z L

theorem occupationRecovery_coherent_distance_le {s : ℕ} (z : Fin s → ℂ) (L : ℕ) :
    ‖(GeneralSymmetricOccupation.occupationRecovery L s).toLinearMap
      (vectorProjector (productTensor z L)) - vectorProjector (MultimodeCoherent.coherentVector z)‖ ≤
      2 * ‖productVector z L - MultimodeCoherent.coherentVector z‖ := by
  rw [occupationRecovery_productTensor]
  exact product_projector_distance_le z L

/-- The actual general-dimensional pure tensor model and the multimode
coherent-state model are equivalent in both directions, uniformly on every
compact local-parameter window. -/
theorem twoWay_coherent_product_uniform_on_compact {s : ℕ} {K : Set (Fin s → ℂ)}
    (hK : IsCompact K) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ L in atTop, ∀ z ∈ K,
      (‖(occupationChannel L s).toLinearMap (vectorProjector (MultimodeCoherent.coherentVector z)) -
        vectorProjector (productTensor z L)‖ < ε) ∧
      (‖(GeneralSymmetricOccupation.occupationRecovery L s).toLinearMap
        (vectorProjector (productTensor z L)) - vectorProjector (MultimodeCoherent.coherentVector z)‖ < ε) := by
  filter_upwards [productVector_uniform_on_compact hK (ε / 2) (by positivity)] with L hL z hz
  have hb : 2 * ‖productVector z L - MultimodeCoherent.coherentVector z‖ < ε := by
    linarith [hL z hz]
  exact ⟨lt_of_le_of_lt (occupationChannel_coherent_distance_le z L) hb,
    lt_of_le_of_lt (occupationRecovery_coherent_distance_le z L) hb⟩

/-- The channels are fixed before selecting the unknown local amplitude or
any compact parameter window. This is a proved finite-dimensional pure-state
LAN instance, including zero modes and zero amplitudes. -/
theorem exists_twoWay_coherent_product_channels (s : ℕ) :
    ∃ (forward : ∀ L, QuantumChannel (FockSpace s) (TensorSpace L (s + 1)))
      (reverse : ∀ L, QuantumChannel (TensorSpace L (s + 1)) (FockSpace s)),
      ∀ K : Set (Fin s → ℂ), IsCompact K → ∀ ε : ℝ, 0 < ε →
        ∀ᶠ L in atTop, ∀ z ∈ K,
          (‖(forward L).toLinearMap (vectorProjector (MultimodeCoherent.coherentVector z)) -
            vectorProjector (productTensor z L)‖ < ε) ∧
          (‖(reverse L).toLinearMap (vectorProjector (productTensor z L)) -
            vectorProjector (MultimodeCoherent.coherentVector z)‖ < ε) := by
  exact ⟨fun L => occupationChannel L s, fun L => GeneralSymmetricOccupation.occupationRecovery L s,
    fun _ hK ε hε => twoWay_coherent_product_uniform_on_compact hK ε hε⟩

end Cloning.GeneralCoherent
