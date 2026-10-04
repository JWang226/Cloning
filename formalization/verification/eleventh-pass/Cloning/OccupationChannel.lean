import Cloning.OccupationCompression
import Cloning.InfiniteRectangularKraus

/-! The actual occupation compression channel, including vacuum tail replacement. -/
noncomputable section
open scoped BigOperators InnerProductSpace Topology
open Filter Cloning.InfiniteTraceClass
namespace Cloning.SymmetricOccupation
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000

/-- A genuine channel from full Fock space to the finite symmetric computational
space, preserving the retained amplitudes and replacing the tail by vacuum. -/
def occupationChannel (L : ℕ) : QuantumChannel Fock (TensorSpace L) :=
  QuantumChannel.ofRectangularKraus (occupationKraus L) (occupationKraus_norm_sq_hasSum L)

private theorem projector_smul {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (c : ℂ) (x : H) :
    vectorProjector (c • x) = ((‖c‖ ^ 2 : ℝ) : ℂ) • vectorProjector x := by
  apply Subtype.ext
  ext y
  change ⟪c • x, y⟫_ℂ • (c • x) = ((‖c‖ ^ 2 : ℝ) : ℂ) • (⟪x, y⟫_ℂ • x)
  rw [inner_smul_left, smul_smul, smul_smul]
  congr 1
  calc
    _ = (c * (starRingEnd ℂ) c) * ⟪x, y⟫_ℂ := by ring
    _ = _ := by rw [Complex.mul_conj]; rw [Complex.normSq_eq_norm_sq]

private theorem tailKraus_projector (L j : ℕ) (x : Fock) :
    vectorProjector (tailKraus L j x) = ((‖tailKraus L j x‖ ^ 2 : ℝ) : ℂ) •
      vectorProjector (column L 0) := by
  rw [tailKraus_norm_sq, tailKraus_apply]
  split_ifs
  · exact projector_smul _ _
  · simp only [Complex.ofReal_zero, zero_smul]
    apply Subtype.ext
    change InnerProductSpace.rankOne ℂ (0 : TensorSpace L) 0 = 0
    ext1 y
    simp only [InnerProductSpace.rankOne_apply, inner_zero_left, zero_smul, ContinuousLinearMap.zero_apply]

/-- The Kraus construction has exactly the manuscript's compression-plus-tail
formula on every pure input, with no normalization requirement. -/
theorem occupationChannel_vectorProjector (L : ℕ) (x : Fock) :
    (occupationChannel L).toLinearMap (vectorProjector x) =
      vectorProjector (compression L x) +
        ((‖x‖ ^ 2 - ‖restrict L x‖ ^ 2 : ℝ) : ℂ) • vectorProjector (column L 0) := by
  have htail := (Complex.hasSum_ofReal.mpr (tailKraus_norm_sq_hasSum L x)).smul_const
    (vectorProjector (column L 0))
  have htail' : HasSum (fun j => vectorProjector (tailKraus L j x))
      (((‖x‖ ^ 2 - ‖restrict L x‖ ^ 2 : ℝ) : ℂ) • vectorProjector (column L 0)) := by
    simpa only [tailKraus_projector] using htail
  have hs := (hasSum_nat_add_iff 1 (f := fun j => vectorProjector (occupationKraus L j x))).mp
    (by simpa only [occupationKraus] using htail')
  have hchannel := QuantumChannel.ofRectangularKraus_vectorProjector_hasSum
    (occupationKraus L) (occupationKraus_norm_sq_hasSum L) x
  have heq := hchannel.unique hs
  simpa only [occupationChannel, Finset.sum_range_one, occupationKraus, add_comm] using heq

/-- The previously explicit positive output family is exactly the output of
an actual completely positive trace-preserving occupation channel. -/
theorem occupationChannel_coherent (t : ℝ) (ht : 0 ≤ t) (L : ℕ) :
    (occupationChannel L).toLinearMap
      (vectorProjector (Cloning.CoherentCoefficients.coherentVector t ht)) =
      occupationCoherentOutput t ht L := by
  rw [occupationChannel_vectorProjector]
  simp only [Cloning.CoherentCoefficients.coherentVector_norm, one_pow,
    occupationCoherentOutput, tailMass, embeddedCoherent, LinearIsometry.norm_map,
    compression_apply]

/-- The manuscript's coherent-product limit, now using a constructed CPTP
occupation channel and the literal finite product coefficients. -/
theorem occupationChannel_coherent_product_tendsto (t : ℝ) (ht : 0 ≤ t) :
    Tendsto (fun L => ‖(occupationChannel L).toLinearMap
      (vectorProjector (Cloning.CoherentCoefficients.coherentVector t ht)) -
        vectorProjector (productTensor t ht L)‖) atTop (𝓝 0) := by
  simp_rw [occupationChannel_coherent]
  exact occupation_coherent_product_traceNorm_tendsto t ht


/-- No norm is lost when all occupations of a vector are retained. -/
theorem restrict_norm_eq_of_support (L : ℕ) (y : Fock)
    (hy : ∀ j, L < j → y j = 0) : ‖restrict L y‖ = ‖y‖ := by
  have hall : HasSum (fun j : ℕ => ‖y j‖ ^ 2) (‖y‖ ^ 2) := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      lp.hasSum_norm (show 0 < (2 : ENNReal).toReal by norm_num) y
  have hfinite : HasSum (fun j : ℕ => ‖y j‖ ^ 2)
      (∑ j ∈ Finset.range (L + 1), ‖y j‖ ^ 2) := by
    apply hasSum_sum_of_ne_finset_zero
    intro j hj
    have hLj : L < j := by simpa only [Finset.mem_range, not_lt, Nat.succ_le_iff] using hj
    simp [hy j hLj]
  have heq := hall.unique hfinite
  rw [← restrict_norm_sq] at heq
  nlinarith [norm_nonneg y, norm_nonneg (restrict L y)]

/-- Trace-norm contraction transfers any coefficient-vector approximation to
the actual finite output, for every retained product vector and arbitrary phases. -/
theorem occupationChannel_pure_distance_le (L : ℕ) (x y : Fock)
    (hy : ‖restrict L y‖ = ‖y‖) :
    ‖(occupationChannel L).toLinearMap (vectorProjector x) -
      vectorProjector (compression L y)‖ ≤ (‖x‖ + ‖y‖) * ‖x - y‖ := by
  have houtput : (occupationChannel L).toLinearMap (vectorProjector y) =
      vectorProjector (compression L y) := by
    rw [occupationChannel_vectorProjector, hy]
    simp
  rw [← houtput]
  exact ((occupationChannel L).toPositiveTracePreservingMap.norm_map_sub_le
    (vectorProjector x) (vectorProjector y)
    ((InnerProductSpace.rankOne ℂ x x).nonneg_iff_isPositive.mpr
      (InnerProductSpace.isPositive_rankOne_self x))
    ((InnerProductSpace.rankOne ℂ y y).nonneg_iff_isPositive.mpr
      (InnerProductSpace.isPositive_rankOne_self y))).trans (norm_vectorProjector_sub_le x y)

end Cloning.SymmetricOccupation
