import Cloning.IsometricRecovery
import Cloning.ComplexCoherent

/-! Reverse occupation compression as an actual channel on the entire tensor
space. Its action on normalized product states is exactly the padded binomial
projector, so the reverse coherent limit has no approximation premise. -/
noncomputable section
open scoped ComplexOrder InnerProductSpace Topology BigOperators
open Filter
namespace Cloning.SymmetricOccupation
open Cloning.InfiniteTraceClass
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

theorem finite_number_orthonormal (L : ℕ) :
    Orthonormal ℂ (fun j : Fin (L + 1) => (lp.single 2 j.val 1 : Fock)) := by
  rw [orthonormal_iff_ite]
  intro i j
  rw [lp.inner_single_left]
  simp only [RCLike.inner_apply, lp.single_apply, Pi.single_apply]
  by_cases h : i = j
  · simp [h]
  · simp [h, show i.val ≠ j.val from fun hij => h (Fin.ext hij)]

/-- Zero-padding from the finite occupation register into the Fock register. -/
def occupationPad (L : ℕ) : OccupationSpace L →ₗᵢ[ℂ] Fock :=
  (finite_number_orthonormal L).orthogonalFamily.linearIsometry

theorem occupationPad_apply (L : ℕ) (x : OccupationSpace L) (n : ℕ) :
    occupationPad L x n = if h : n < L + 1 then x ⟨n, h⟩ else 0 := by
  classical
  rw [occupationPad, OrthogonalFamily.linearIsometry_apply, tsum_fintype]
  simp only [LinearIsometry.toSpanSingleton_apply, lp.coeFn_sum, Finset.sum_apply,
    lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, lp.single_apply, Pi.single_apply]
  split_ifs with hn
  · rw [Finset.sum_eq_single (⟨n, hn⟩ : Fin (L + 1))]
    · simp
    · intro j hj hne
      have hval : n ≠ j.val := fun h => hne (Fin.ext h.symm)
      simp [hval]
    · simp
  · apply Finset.sum_eq_zero
    intro j hj
    have hval : n ≠ j.val := by intro h; exact hn (h ▸ j.isLt)
    simp [hval]

theorem occupationPad_restrict (L : ℕ) (y : Fock)
    (hy : ∀ j, L < j → y j = 0) : occupationPad L (restrict L y) = y := by
  ext j
  rw [occupationPad_apply]
  split_ifs with hj
  · rfl
  · rw [hy j (by omega)]

/-- This channel is defined on nonsymmetric inputs too, replacing their
discarded mass in the Fock vacuum. -/
def occupationRecovery (L : ℕ) : QuantumChannel (TensorSpace L) Fock :=
  (QuantumChannel.ofIsometry (occupationPad L)).comp
    (QuantumChannel.isometricRecovery (isometry L)
      (DensityState.pure (lp.single 2 (0 : Fin (L + 1)) 1)
        (by rw [lp.norm_single (by norm_num)]; simp)))

theorem occupationRecovery_productTensor (z : ℂ) (L : ℕ) :
    (occupationRecovery L).toLinearMap
      (vectorProjector (Cloning.ComplexCoherent.productTensor z L)) =
        vectorProjector (Cloning.ComplexCoherent.productVector z L) := by
  change (QuantumChannel.ofIsometry (occupationPad L)).toLinearMap
    ((QuantumChannel.isometricRecovery (isometry L) _).toLinearMap
      (vectorProjector (isometry L (Cloning.ComplexCoherent.finiteProductVector z L)))) = _
  rw [QuantumChannel.isometricRecovery_vectorProjector,
    QuantumChannel.ofIsometry_vectorProjector,
    ← Cloning.ComplexCoherent.restrict_productVector,
    occupationPad_restrict L _ (Cloning.ComplexCoherent.productVector_eq_zero_of_lt z L)]

/-- A physical reverse channel sends the literal two-level product states
to their coherent Fock limits. -/
theorem occupationRecovery_product_coherent_tendsto (z : ℂ) :
    Tendsto (fun L => (occupationRecovery L).toLinearMap
      (vectorProjector (Cloning.ComplexCoherent.productTensor z L))) atTop
      (𝓝 (vectorProjector (Cloning.ComplexCoherent.coherentVector z))) := by
  simp_rw [occupationRecovery_productTensor]
  exact Cloning.ComplexCoherent.product_projector_tendsto z

end Cloning.SymmetricOccupation
