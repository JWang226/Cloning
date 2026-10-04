import Cloning.UniformCoherent
import Cloning.OccupationRecovery

/-! Two parameter-independent channels give compact-uniform equivalence between
the normalized pure two-level tensor model and the coherent-state model. This
is a concrete pure-qubit local approximation; it does not assert mixed-state
quantum LAN or any representation-theoretic identification for general spectra. -/
noncomputable section
open scoped Topology
open Filter Cloning.InfiniteTraceClass
namespace Cloning.ComplexCoherent
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

/-- The actual reverse channel has a uniform error controlled by the same
coherent-product Hilbert approximation as the forward channel. -/
theorem occupationRecovery_product_coherent_distance_le (z : ℂ) (L : ℕ) :
    ‖(SymmetricOccupation.occupationRecovery L).toLinearMap
      (vectorProjector (productTensor z L)) - vectorProjector (coherentVector z)‖ ≤
        2 * ‖productVector z L - coherentVector z‖ := by
  rw [SymmetricOccupation.occupationRecovery_productTensor]
  exact product_projector_distance_le z L

/-- The reverse occupation channel converges uniformly on every bounded
amplitude set in the genuine trace-class norm. -/
theorem occupationRecovery_product_tendstoUniformlyOn
    {K : Set ℂ} (hK : Bornology.IsBounded K) :
    TendstoUniformlyOn (fun L z => (SymmetricOccupation.occupationRecovery L).toLinearMap
      (vectorProjector (productTensor z L)))
      (fun z => vectorProjector (coherentVector z)) atTop K := by
  simp_rw [SymmetricOccupation.occupationRecovery_productTensor]
  exact product_projector_tendstoUniformlyOn hK

/-- Both parameter-independent CPTP maps approximate the two pure-state
experiments uniformly on a fixed amplitude ball, with one sample threshold
working in both directions. -/
theorem twoWay_coherent_product_uniform_on_closedBall
    (R : ℝ) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ L in atTop, ∀ z : ℂ, ‖z‖ ≤ R →
      (‖(SymmetricOccupation.occupationChannel L).toLinearMap
        (vectorProjector (coherentVector z)) - vectorProjector (productTensor z L)‖ < ε) ∧
      (‖(SymmetricOccupation.occupationRecovery L).toLinearMap
        (vectorProjector (productTensor z L)) - vectorProjector (coherentVector z)‖ < ε) := by
  filter_upwards [productVector_coherentVector_uniform_on_closedBall R (ε / 2) (by positivity)]
    with L hL z hz
  have herror : 2 * ‖productVector z L - coherentVector z‖ < ε := by
    linarith [hL z hz]
  exact ⟨lt_of_le_of_lt (occupationChannel_coherent_product_distance_le z L) herror,
    lt_of_le_of_lt (occupationRecovery_product_coherent_distance_le z L) herror⟩

/-- Compact-window, two-way trace-norm equivalence for the explicit pure-qubit
product model and the bosonic coherent-state model. -/
theorem twoWay_coherent_product_uniform_on_compact
    {K : Set ℂ} (hK : IsCompact K) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ L in atTop, ∀ z ∈ K,
      (‖(SymmetricOccupation.occupationChannel L).toLinearMap
        (vectorProjector (coherentVector z)) - vectorProjector (productTensor z L)‖ < ε) ∧
      (‖(SymmetricOccupation.occupationRecovery L).toLinearMap
        (vectorProjector (productTensor z L)) - vectorProjector (coherentVector z)‖ < ε) := by
  obtain ⟨R, hR⟩ := hK.isBounded.exists_norm_le
  filter_upwards [twoWay_coherent_product_uniform_on_closedBall R ε hε] with L hL z hz
  exact hL z (hR z hz)

/-- The channels are chosen once for every sample size, independently of the
unknown amplitude, the compact parameter window, and the requested error. -/
theorem exists_twoWay_coherent_product_channels :
    ∃ (forward : ∀ L, QuantumChannel Fock (SymmetricOccupation.TensorSpace L))
      (reverse : ∀ L, QuantumChannel (SymmetricOccupation.TensorSpace L) Fock),
      ∀ (K : Set ℂ), IsCompact K → ∀ ε : ℝ, 0 < ε →
        ∀ᶠ L in atTop, ∀ z ∈ K,
          (‖(forward L).toLinearMap (vectorProjector (coherentVector z)) -
            vectorProjector (productTensor z L)‖ < ε) ∧
          (‖(reverse L).toLinearMap (vectorProjector (productTensor z L)) -
            vectorProjector (coherentVector z)‖ < ε) := by
  exact ⟨SymmetricOccupation.occupationChannel, SymmetricOccupation.occupationRecovery,
    fun _ hK ε hε => twoWay_coherent_product_uniform_on_compact hK ε hε⟩

end Cloning.ComplexCoherent
