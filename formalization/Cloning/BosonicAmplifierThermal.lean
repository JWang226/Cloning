import Cloning.BosonicAmplifierChannel
import Cloning.BosonicNumberLaw
import Cloning.InfiniteDiagonalFidelity

/-!
# Actual thermal output of the bosonic amplifier

Continuity in the trace norm transports the number-projector channel formula
to summable diagonal operators. The finite binomial convolution then identifies
the genuine amplifier output with the amplified thermal density operator.
-/

noncomputable section
open scoped ComplexOrder InnerProductSpace Topology BigOperators

namespace Cloning.BosonicAmplifier

open Cloning Cloning.InfiniteTraceClass BosonicNumberLaw
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

/-- Every geometric thermal operator is the actual amplified vacuum. -/
theorem channel_vacuum (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    (channel r hr0 hr1).toLinearMap (vectorProjector (numberBasis 0)) =
      vectorMixture numberBasis (Thermal.geometric r) := by
  rw [channel_numberProjector]
  simp only [Nat.zero_add]
  congr 1
  funext k
  simp [weight, Thermal.geometric]

/-- The output of a number input has the padded negative-binomial spectrum. -/
theorem channel_numberProjector_apply_basis (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (n t : ℕ) :
    ((channel r hr0 hr1).toLinearMap (vectorProjector (numberBasis n))).1 (numberBasis t) =
      (transition r n t : ℂ) • numberBasis t := by
  classical
  rw [channel_numberProjector]
  let L : TraceClass Fock →L[ℂ] Fock :=
    (ContinuousLinearMap.apply ℂ Fock (numberBasis t)).comp inclusionCLM
  change L (vectorMixture (fun k => numberBasis (n + k)) (weight r n)) = _
  rw [vectorMixture, L.map_tsum (summable_weighted_projectors _
    (fun k => numberBasis.orthonormal.norm_eq_one (n + k)) _ (weight_hasSum hr0 hr1 n).summable)]
  have hterm (k : ℕ) : L (vectorProjector (numberBasis (n + k))) =
      if n + k = t then numberBasis t else 0 := by
    change InnerProductSpace.rankOne ℂ (numberBasis (n + k)) (numberBasis (n + k))
      (numberBasis t) = _
    rw [InnerProductSpace.rankOne_apply,
      orthonormal_iff_ite.mp numberBasis.orthonormal (n + k) t]
    split_ifs with h
    · simp [h]
    · simp
  simp only [map_smul, hterm]
  by_cases hnt : n ≤ t
  · rw [tsum_eq_single (t - n)]
    · simp only [Nat.add_sub_of_le hnt, transition, if_pos hnt]
      rfl
    · intro k hk
      have hne : n + k ≠ t := by omega
      simp only [if_neg hne, smul_zero]
  · have hne (k : ℕ) : n + k ≠ t := by omega
    simp only [hne, if_false, smul_zero, tsum_zero, transition, if_neg hnt, Complex.ofReal_zero,
      zero_smul]

/-- Exact action on every summable diagonal input, proved using continuity of
the actual channel. Each output coefficient is a finite convolution. -/
theorem channel_vectorMixture_apply_basis (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (p : ℕ → ℝ) (hp : Summable p) (t : ℕ) :
    ((channel r hr0 hr1).toLinearMap (vectorMixture numberBasis p)).1 (numberBasis t) =
      ((∑ n ∈ Finset.range (t + 1), p n * seededLaw r n (t - n) : ℝ) : ℂ) • numberBasis t := by
  classical
  let Φ := (channel r hr0 hr1).toPositiveTracePreservingMap.toContinuousLinearMap
  let L : TraceClass Fock →L[ℂ] Fock :=
    ((ContinuousLinearMap.apply ℂ Fock (numberBasis t)).comp inclusionCLM).comp Φ
  change L (vectorMixture numberBasis p) = _
  rw [vectorMixture, L.map_tsum
    (summable_weighted_projectors _ numberBasis.orthonormal.norm_eq_one p hp)]
  have hterm (n : ℕ) : L (vectorProjector (numberBasis n)) =
      (transition r n t : ℂ) • numberBasis t :=
    channel_numberProjector_apply_basis r hr0 hr1 n t
  simp only [map_smul, hterm, smul_smul, ← Complex.ofReal_mul]
  rw [tsum_eq_sum (s := Finset.range (t + 1))]
  · rw [← Finset.sum_smul, ← Complex.ofReal_sum]
    congr 2
    apply Finset.sum_congr rfl
    intro n hn
    simp only [transition, if_pos (Nat.lt_succ_iff.mp (Finset.mem_range.mp hn))]
  · intro n hn
    have hnt : ¬ n ≤ t := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hn
    simp only [transition, if_neg hnt, mul_zero, Complex.ofReal_zero, zero_smul]

theorem thermalOutput_parameter_nonneg {r q : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hq0 : 0 ≤ q) : 0 ≤ r + (1 - r) * q :=
  add_nonneg hr0 (mul_nonneg (sub_nonneg.mpr hr1.le) hq0)

theorem thermalOutput_parameter_lt_one {r q : ℝ} (hr1 : r < 1) (hq1 : q < 1) :
    r + (1 - r) * q < 1 := by
  have h := mul_pos (sub_pos.mpr hr1) (sub_pos.mpr hq1)
  nlinarith

/-- The genuine infinite-dimensional quantum-limited amplifier sends a
thermal diagonal operator to the thermal operator with the derived parameter. -/
theorem channel_thermalOperator (r q : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hq0 : 0 ≤ q) (hq1 : q < 1) :
    (channel r hr0 hr1).toLinearMap (vectorMixture numberBasis (Thermal.geometric q)) =
      vectorMixture numberBasis (Thermal.geometric (r + (1 - r) * q)) := by
  apply Subtype.ext
  have hbasis (t : ℕ) :
      ((channel r hr0 hr1).toLinearMap (vectorMixture numberBasis (Thermal.geometric q))).1
          (numberBasis t) =
        (vectorMixture numberBasis (Thermal.geometric (r + (1 - r) * q))).1 (numberBasis t) := by
    rw [channel_vectorMixture_apply_basis r hr0 hr1 _ (Thermal.geometric_hasSum hq0 hq1).summable,
      InfiniteOccupationStates.vectorMixture_apply_basis _ _
        (Thermal.geometric_hasSum (thermalOutput_parameter_nonneg hr0 hr1 hq0)
          (thermalOutput_parameter_lt_one hr1 hq1)).summable]
    change (thermalOutput r q t : ℂ) • numberBasis t = _
    rw [thermalOutput_eq]
  apply ContinuousLinearMap.ext
  intro v
  have h₁ := ((channel r hr0 hr1).toLinearMap
    (vectorMixture numberBasis (Thermal.geometric q))).1.hasSum (numberBasis.hasSum_repr v)
  have h₂ := (vectorMixture numberBasis (Thermal.geometric (r + (1 - r) * q))).1.hasSum
    (numberBasis.hasSum_repr v)
  simp only [map_smul, hbasis] at h₁ h₂
  exact h₁.unique h₂

private theorem densityState_eq_of_op_eq {ρ σ : DensityState Fock}
    (h : ρ.op = σ.op) : ρ = σ := by
  cases ρ
  cases σ
  cases h
  rfl

/-- Equality of actual normalized density states after amplification. -/
theorem channel_geometricState (r q : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hq0 : 0 ≤ q) (hq1 : q < 1) :
    (channel r hr0 hr1).toPositiveTracePreservingMap.mapState
      (InfiniteDiagonalFidelity.geometricState numberBasis q hq0 hq1) =
    InfiniteDiagonalFidelity.geometricState numberBasis (r + (1 - r) * q)
      (thermalOutput_parameter_nonneg hr0 hr1 hq0) (thermalOutput_parameter_lt_one hr1 hq1) := by
  apply densityState_eq_of_op_eq
  exact congrArg Subtype.val (channel_thermalOperator r q hr0 hr1 hq0 hq1)

/-- Exact achieved thermal fidelity for the actual channel. -/
theorem stateFidelity_channel_geometric (r q : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hq0 : 0 ≤ q) (hq1 : q < 1) :
    InfiniteFidelity.stateFidelity (InfiniteDiagonalFidelity.geometricState numberBasis q hq0 hq1)
      ((channel r hr0 hr1).toPositiveTracePreservingMap.mapState
        (InfiniteDiagonalFidelity.geometricState numberBasis q hq0 hq1)) =
      Thermal.fidelity q (r + (1 - r) * q) := by
  rw [channel_geometricState, InfiniteDiagonalFidelity.stateFidelity_geometric]

theorem gainNoise_nonneg {g : ℝ} (hg : 1 < g) : 0 ≤ 1 - 1 / g :=
  sub_nonneg.mpr ((div_le_one (by linarith : 0 < g)).mpr hg.le)

theorem gainNoise_lt_one {g : ℝ} (hg : 1 < g) : 1 - 1 / g < 1 := by
  have h : 0 < 1 / g := one_div_pos.mpr (by linarith)
  linarith

/-- Gain-parametrized actual channel output, with the manuscript's amplified
thermal parameter and no asserted input/output identification. -/
theorem channel_thermalOperator_gain (g q : ℝ) (hg : 1 < g)
    (hq0 : 0 ≤ q) (hq1 : q < 1) :
    (channel (1 - 1 / g) (gainNoise_nonneg hg) (gainNoise_lt_one hg)).toLinearMap
      (vectorMixture numberBasis (Thermal.geometric q)) =
    vectorMixture numberBasis (Thermal.geometric (Thermal.amplified g q)) := by
  rw [channel_thermalOperator _ _ _ _ hq0 hq1]
  congr 2
  unfold Thermal.amplified
  ring

/-- The actual physical amplifier realizes the exact one-mode factor. -/
theorem stateFidelity_channel_gain (g q : ℝ) (hg : 1 < g)
    (hq0 : 0 ≤ q) (hq1 : q < 1) :
    InfiniteFidelity.stateFidelity (InfiniteDiagonalFidelity.geometricState numberBasis q hq0 hq1)
      ((channel (1 - 1 / g) (gainNoise_nonneg hg) (gainNoise_lt_one hg)).toPositiveTracePreservingMap.mapState
        (InfiniteDiagonalFidelity.geometricState numberBasis q hq0 hq1)) =
      Thermal.modeFactor g q := by
  rw [stateFidelity_channel_geometric]
  have h : (1 - 1 / g) + (1 - (1 - 1 / g)) * q = Thermal.amplified g q := by
    unfold Thermal.amplified
    ring
  rw [h, Thermal.fidelity_amplified_eq_modeFactor hg hq0 hq1]

end Cloning.BosonicAmplifier
