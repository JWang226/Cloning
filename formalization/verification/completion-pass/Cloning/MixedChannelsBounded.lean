import Cloning.MixedChannels

/-! A channel-independent norm bound for reverse mixed channels. Simple-function
density avoids assuming a measurable field of Jordan decompositions. -/

noncomputable section
open scoped ComplexOrder Topology ENNReal
open MeasureTheory Filter Cloning.InfiniteTraceClass
namespace Cloning.Hybrid
set_option backward.isDefEq.respectTransparency false

variable {Ω H K : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

private def indicatorLinear {s : Set Ω} (hs : MeasurableSet s) (hμs : μ s ≠ ∞) :
    TraceClass H →ₗ[ℂ] Lp (TraceClass H) 1 μ where
  toFun A := indicatorConstLp 1 hs hμs A
  map_add' A B := indicatorConstLp_add.symm
  map_smul' c A := by
    apply Lp.ext
    filter_upwards [indicatorConstLp_coeFn (c := c • A),
      indicatorConstLp_coeFn (p := 1) (hs := hs) (hμs := hμs) (c := A),
      Lp.coeFn_smul c (indicatorConstLp 1 hs hμs A)] with y hy hz hw
    change _ = (c • indicatorConstLp 1 hs hμs A) y
    rw [hy, hw, Pi.smul_apply, hz]
    by_cases h : y ∈ s <;> simp [h]

private lemma indicatorLinear_nonneg {s : Set Ω} (hs : MeasurableSet s)
    (hμs : μ s ≠ ∞) (A : TraceClass H) (hA : 0 ≤ A.1) :
    ∀ᵐ y ∂μ, 0 ≤ (indicatorLinear hs hμs A y).1 := by
  filter_upwards [indicatorConstLp_coeFn (p := 1) (hs := hs) (hμs := hμs) (c := A)] with y hy
  change 0 ≤ (indicatorConstLp 1 hs hμs A y).1
  rw [hy]
  by_cases h : y ∈ s <;> simp [h, hA]

/-- A positive-cone contraction has a universal bound on complex operator-valued L¹. -/
theorem norm_le_two_of_positive_L1_bound {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] (T : Lp (TraceClass H) 1 μ →L[ℂ] E)
    (hp : ∀ A, (∀ᵐ y ∂μ, 0 ≤ (A y).1) → ‖T A‖ ≤ ‖A‖)
    (A : Lp (TraceClass H) 1 μ) : ‖T A‖ ≤ 2 * ‖A‖ := by
  refine Lp.induction (p := 1) (by simp) (fun A => ‖T A‖ ≤ 2 * ‖A‖) ?_ ?_ ?_ A
  · intro c s hs hμs
    have hpos : ∀ B : TraceClass H, 0 ≤ B.1 →
        ‖(T.toLinearMap.comp (indicatorLinear hs hμs.ne)) B‖ ≤ μ.real s * ‖B‖ := by
      intro B hB
      have h := hp (indicatorLinear hs hμs.ne B) (indicatorLinear_nonneg hs hμs.ne B hB)
      change ‖T (indicatorConstLp 1 hs hμs.ne B)‖ ≤ _ at h ⊢
      simpa [indicatorLinear,
        norm_indicatorConstLp (by simp : (1 : ℝ≥0∞) ≠ 0) (by simp), mul_comm] using h
    have h := norm_map_two_mul_of_positive_bound
      (T.toLinearMap.comp (indicatorLinear hs hμs.ne)) ENNReal.toReal_nonneg hpos c
    simpa [indicatorLinear, norm_indicatorConstLp (by simp : (1 : ℝ≥0∞) ≠ 0) (by simp),
      mul_comm, mul_left_comm, mul_assoc] using h
  · intro f g hf hg hfg hF hG
    have hn : ‖hf.toLp f + hg.toLp g‖ = ‖hf.toLp f‖ + ‖hg.toLp g‖ := by
      rw [L1.norm_eq_integral_norm, L1.norm_eq_integral_norm, L1.norm_eq_integral_norm,
        ← integral_add (L1.integrable_coeFn (hf.toLp f)).norm
          (L1.integrable_coeFn (hg.toLp g)).norm]
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_add (hf.toLp f) (hg.toLp g), hf.coeFn_toLp, hg.coeFn_toLp]
        with y hy hfy hgy
      rw [hy, Pi.add_apply, hfy, hgy]
      have hd : f y = 0 ∨ g y = 0 := by
        by_cases h : f y = 0
        · exact Or.inl h
        · exact Or.inr (by
            by_contra hh
            exact Set.disjoint_left.mp hfg h hh)
      rcases hd with h | h <;> simp [h]
    rw [map_add, hn, mul_add]
    exact (norm_add_le _ _).trans (add_le_add hF hG)
  · exact isClosed_le T.continuous.norm (continuous_const.mul continuous_norm)

theorem HybridToQuantum.norm_le_two (S : HybridToQuantum H K μ)
    (A : Lp (TraceClass H) 1 μ) : ‖S.map A‖ ≤ 2 * ‖A‖ :=
  norm_le_two_of_positive_L1_bound S.map
    (fun B hB => le_of_eq (S.norm_map_of_nonneg B hB)) A

theorem HybridToQuantum.opNorm_le_two (S : HybridToQuantum H K μ) : ‖S.map‖ ≤ 2 :=
  ContinuousLinearMap.opNorm_le_bound _ (by norm_num) S.norm_le_two

theorem QuantumToHybrid.opNorm_le_two (T : QuantumToHybrid H K μ) : ‖T.map‖ ≤ 2 :=
  ContinuousLinearMap.opNorm_le_bound _ (by norm_num) T.norm_le_two

end Cloning.Hybrid
