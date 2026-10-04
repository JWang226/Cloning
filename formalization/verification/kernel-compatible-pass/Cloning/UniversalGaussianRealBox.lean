import Cloning.UniversalGaussianConverse

/-! The universal orbital converse for arbitrary real box radii. Positive
orbit fidelities allow interpolation from integer boxes; the volume loss
vanishes uniformly over all competing channels. -/
noncomputable section
open scoped ComplexOrder InnerProductSpace Topology BigOperators
open Filter MeasureTheory Cloning.InfiniteTraceClass Cloning.InfiniteFidelity
open Cloning.Hybrid Cloning.ThermalWitness Cloning.MultimodeCoherentGaussianMixture
namespace Cloning.MultimodeCoherent
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {d : ℕ}

lemma phaseSpaceUnitBox_volume_real_pos (d : ℕ) :
    0 < volume.real (phaseSpaceUnitBox d) :=
  ENNReal.toReal_pos (phaseSpaceUnitBox_volume_pos d).ne'
    (phaseSpaceUnitBox_compact d).measure_ne_top

lemma phaseSpaceBox_compact (d : ℕ) (L : ℝ) : IsCompact (phaseSpaceBox d L) := by
  apply (isCompact_closedBall (0 : Fin d → ℂ) (2 * |L|)).of_isClosed_subset
    (phaseSpaceBox_closed d L)
  intro z hz
  rw [Metric.mem_closedBall, dist_zero_right]
  apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ 2 * |L|)).mpr
  intro i
  exact (Complex.norm_le_abs_re_add_abs_im (z i)).trans
    (by linarith [(hz i).1, (hz i).2, le_abs_self L])

lemma phaseSpaceBox_mono {L M : ℝ} (h : L ≤ M) :
    phaseSpaceBox d L ⊆ phaseSpaceBox d M :=
  fun _ hz i => ⟨(hz i).1.trans h, (hz i).2.trans h⟩

lemma phaseSpaceBox_volume_real {L : ℝ} (hL : 0 < L) :
    volume.real (phaseSpaceBox d L) =
      L ^ Module.finrank ℝ (Fin d → ℂ) * volume.real (phaseSpaceUnitBox d) := by
  have hv := integral_unitBox_smul hL (fun _ : Fin d → ℂ => (1 : ℝ))
  simp only [integral_const, Measure.restrict_apply_univ, measureReal_def,
    smul_eq_mul, mul_one] at hv
  change volume.real (phaseSpaceUnitBox d) =
    (L ^ Module.finrank ℝ (Fin d → ℂ))⁻¹ * volume.real (phaseSpaceBox d L) at hv
  rw [hv, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hL.ne'), one_mul]

/-- The flat orbit-root-fidelity average at an arbitrary real radius.
For positive radii this is exactly the normalized Lebesgue box integral. -/
def realFlatBoxPayoff (gain : ℝ) (Φ : QuantumChannel (Fock d) (Fock d))
    (A B : PositiveTraceClass (Fock d)) (L : ℝ) : ℝ :=
  (volume.real (phaseSpaceUnitBox d))⁻¹ * ∫ z in phaseSpaceUnitBox d,
    orbitPayoff gain Φ A B (L • z)

lemma realFlatBoxPayoff_eq_normalized_box (gain : ℝ)
    (Φ : QuantumChannel (Fock d) (Fock d)) (A B : PositiveTraceClass (Fock d))
    {L : ℝ} (hL : 0 < L) :
    realFlatBoxPayoff gain Φ A B L =
      (volume.real (phaseSpaceBox d L))⁻¹ *
        ∫ a in phaseSpaceBox d L, orbitPayoff gain Φ A B a :=
  normalized_unitBox_smul_eq hL (orbitPayoff gain Φ A B)

lemma realFlatBoxPayoff_nonneg (gain : ℝ)
    (Φ : QuantumChannel (Fock d) (Fock d)) (A B : PositiveTraceClass (Fock d)) (L : ℝ) :
    0 ≤ realFlatBoxPayoff gain Φ A B L := by
  apply mul_nonneg (inv_nonneg.mpr (measureReal_nonneg))
  exact integral_nonneg (fun _ => PositiveTraceClass.rootFidelity_nonneg _ _)

lemma realFlatBoxPayoff_le_sqrt (gain : ℝ)
    (Φ : QuantumChannel (Fock d) (Fock d)) (A B : PositiveTraceClass (Fock d)) (L : ℝ) :
    realFlatBoxPayoff gain Φ A B L ≤ Real.sqrt ‖A.1‖ * Real.sqrt ‖B.1‖ := by
  have hint : IntegrableOn (fun z => orbitPayoff gain Φ A B (L • z))
      (phaseSpaceUnitBox d) :=
    ((continuous_orbitPayoff gain Φ A B).comp
      (continuous_const.smul continuous_id)).continuousOn.integrableOn_compact
        (phaseSpaceUnitBox_compact d)
  have hp (z : Fin d → ℂ) : orbitPayoff gain Φ A B (L • z) ≤
      Real.sqrt ‖A.1‖ * Real.sqrt ‖B.1‖ := by
    rw [orbitPayoff_eq_translated]
    simpa only [PositiveTraceClass.norm_map] using
      PositiveTraceClass.rootFidelity_le_sqrt
        (PositiveTraceClass.map (translatedChannel gain Φ (L • z)).toPositiveTracePreservingMap A) B
  have hi := integral_mono hint (integrableOn_const (hs :=
    (phaseSpaceUnitBox_compact d).measure_ne_top)) hp
  change (volume.real (phaseSpaceUnitBox d))⁻¹ * _ ≤ _
  calc
    _ ≤ (volume.real (phaseSpaceUnitBox d))⁻¹ *
        ∫ _z in phaseSpaceUnitBox d, Real.sqrt ‖A.1‖ * Real.sqrt ‖B.1‖ :=
      mul_le_mul_of_nonneg_left hi (inv_nonneg.mpr measureReal_nonneg)
    _ = _ := by
      simp only [integral_const, measureReal_def, Measure.restrict_apply_univ, smul_eq_mul]
      change (volume.real (phaseSpaceUnitBox d))⁻¹ *
        (volume.real (phaseSpaceUnitBox d) * (Real.sqrt ‖A.1‖ * Real.sqrt ‖B.1‖)) = _
      rw [← mul_assoc, inv_mul_cancel₀ (phaseSpaceUnitBox_volume_real_pos d).ne', one_mul]

/-- Enlarging the physical box only incurs the exact volume ratio. -/
lemma realFlatBoxPayoff_le_integer (gain : ℝ)
    (Φ : QuantumChannel (Fock d) (Fock d)) (A B : PositiveTraceClass (Fock d))
    {L : ℝ} (hL : 0 < L) (n : ℕ) (hLn : L ≤ (n : ℝ) + 1) :
    realFlatBoxPayoff gain Φ A B L ≤
      (((n : ℝ) + 1) / L) ^ Module.finrank ℝ (Fin d → ℂ) *
        flatBoxPayoff gain Φ A B n := by
  have hN : 0 < (n : ℝ) + 1 := by positivity
  have hi : (∫ a in phaseSpaceBox d L, orbitPayoff gain Φ A B a) ≤
      ∫ a in phaseSpaceBox d ((n : ℝ) + 1), orbitPayoff gain Φ A B a :=
    setIntegral_mono_set
      ((continuous_orbitPayoff gain Φ A B).continuousOn.integrableOn_compact
        (phaseSpaceBox_compact d _))
      (Eventually.of_forall fun _ => PositiveTraceClass.rootFidelity_nonneg _ _)
      (phaseSpaceBox_mono hLn).eventuallyLE
  rw [realFlatBoxPayoff_eq_normalized_box gain Φ A B hL,
    flatBoxPayoff_eq_normalized_box, phaseSpaceBox_volume_real hL,
    phaseSpaceBox_volume_real hN]
  calc
    _ ≤ (L ^ Module.finrank ℝ (Fin d → ℂ) * volume.real (phaseSpaceUnitBox d))⁻¹ *
        ∫ a in phaseSpaceBox d ((n : ℝ) + 1), orbitPayoff gain Φ A B a :=
      mul_le_mul_of_nonneg_left hi (by positivity)
    _ = _ := by
      rw [div_pow]
      field_simp [hL.ne', hN.ne', (phaseSpaceUnitBox_volume_real_pos d).ne']

/-- The interpolation overhead tends to one in the real radius, including
zero quantum modes. -/
lemma realFlatBox_overhead_tendsto_one (d : ℕ) :
    Tendsto (fun L : ℝ => (1 + L⁻¹) ^ Module.finrank ℝ (Fin d → ℂ)) atTop (𝓝 1) := by
  have ht : Tendsto (fun L : ℝ => 1 + L⁻¹) atTop (𝓝 (1 + 0 : ℝ)) :=
    tendsto_const_nhds.add tendsto_inv_atTop_zero
  simpa using ht.pow (Module.finrank ℝ (Fin d → ℂ))

/-- An integer-radius bound uniform over channels remains uniform at every
sufficiently large real radius. No continuity in the choice of channel is needed. -/
lemma eventually_forall_realFlatBox_le_of_integer (gain : ℝ)
    (A B : PositiveTraceClass (Fock d)) {C : ℝ}
    (h : ∀ ε > 0, ∀ᶠ n in atTop, ∀ Φ : QuantumChannel (Fock d) (Fock d),
      flatBoxPayoff gain Φ A B n ≤ C + ε) :
    ∀ ε > 0, ∀ᶠ L : ℝ in atTop, ∀ Φ : QuantumChannel (Fock d) (Fock d),
      realFlatBoxPayoff gain Φ A B L ≤ C + ε := by
  intro ε hε
  have hfloor : Tendsto (Nat.floor : ℝ → ℕ) atTop atTop :=
    Nat.floor_mono.tendsto_atTop_atTop (fun n => ⟨(n : ℝ), by simp⟩)
  have hint := hfloor.eventually (h (ε / 2) (by linarith))
  have ht : Tendsto (fun L : ℝ =>
      (1 + L⁻¹) ^ Module.finrank ℝ (Fin d → ℂ) * (C + ε / 2)) atTop
      (𝓝 (C + ε / 2)) := by
    simpa using (realFlatBox_overhead_tendsto_one d).mul_const (C + ε / 2)
  have hnear := ht.eventually_lt_const (by linarith : C + ε / 2 < C + ε)
  filter_upwards [hint, hnear, eventually_gt_atTop (0 : ℝ)] with L hLi hnear hL
  intro Φ
  have hc := realFlatBoxPayoff_le_integer gain Φ A B hL (Nat.floor L)
    (Nat.lt_floor_add_one L).le
  have hr : (((Nat.floor L : ℕ) : ℝ) + 1) / L ≤ 1 + L⁻¹ := by
    apply (div_le_iff₀ hL).mpr
    have hf := Nat.floor_le hL.le
    rw [add_mul, one_mul, inv_mul_cancel₀ hL.ne']
    linarith
  calc
    realFlatBoxPayoff gain Φ A B L ≤
        ((((Nat.floor L : ℕ) : ℝ) + 1) / L) ^ Module.finrank ℝ (Fin d → ℂ) *
          flatBoxPayoff gain Φ A B (Nat.floor L) := hc
    _ ≤ (1 + L⁻¹) ^ Module.finrank ℝ (Fin d → ℂ) *
          flatBoxPayoff gain Φ A B (Nat.floor L) := by
      apply mul_le_mul_of_nonneg_right _ (flatBoxPayoff_nonneg gain Φ A B _)
      exact pow_le_pow_left₀ (by positivity) hr _
    _ ≤ (1 + L⁻¹) ^ Module.finrank ℝ (Fin d → ℂ) * (C + ε / 2) :=
      mul_le_mul_of_nonneg_left (hLi Φ) (by positivity)
    _ ≤ C + ε := hnear.le

/-- The channel supremum at each real physical box radius. -/
def realFlatBoxOptimalPayoff (gain : ℝ) (A B : PositiveTraceClass (Fock d)) (L : ℝ) : ℝ :=
  sSup (Set.range (fun Φ : QuantumChannel (Fock d) (Fock d) => realFlatBoxPayoff gain Φ A B L))

lemma realFlatBoxOptimalPayoff_nonneg (gain : ℝ) (A B : PositiveTraceClass (Fock d)) (L : ℝ) :
    0 ≤ realFlatBoxOptimalPayoff gain A B L := by
  have hb : BddAbove (Set.range (fun Φ : QuantumChannel (Fock d) (Fock d) =>
      realFlatBoxPayoff gain Φ A B L)) := by
    refine ⟨Real.sqrt ‖A.1‖ * Real.sqrt ‖B.1‖, ?_⟩
    rintro _ ⟨Φ, rfl⟩
    exact realFlatBoxPayoff_le_sqrt gain Φ A B L
  exact (realFlatBoxPayoff_nonneg gain (displacementChannel 0) A B L).trans
    (le_csSup hb (Set.mem_range_self (displacementChannel 0)))

lemma limsup_realFlatBoxOptimalPayoff_le (gain : ℝ) (A B : PositiveTraceClass (Fock d))
    {C : ℝ} (h : ∀ ε > 0, ∀ᶠ L : ℝ in atTop, ∀ Φ : QuantumChannel (Fock d) (Fock d),
      realFlatBoxPayoff gain Φ A B L ≤ C + ε) :
    Filter.limsup (realFlatBoxOptimalPayoff gain A B) atTop ≤ C := by
  apply le_of_forall_pos_le_add
  intro ε hε
  apply limsup_le_of_le
    (isCoboundedUnder_le_of_le atTop (realFlatBoxOptimalPayoff_nonneg gain A B))
  filter_upwards [h ε hε] with L hL
  apply csSup_le (show (Set.range (fun Φ : QuantumChannel (Fock d) (Fock d) =>
    realFlatBoxPayoff gain Φ A B L)).Nonempty from ⟨_, Set.mem_range_self (displacementChannel 0)⟩)
  rintro _ ⟨Φ, rfl⟩
  exact hL Φ

/-- The universal orbital converse, uniformly over channels and all sufficiently
large real radii, for the same mixed thermal input and target orbit. -/
theorem eventually_forall_realFlatBox_thermal_le
    (r : ℝ) (hr : 1 < r ^ 2) {q : Fin d → ℝ}
    (hq0 : ∀ i, 0 < q i) (hq1 : ∀ i, q i < 1) :
    ∀ ε > 0, ∀ᶠ L : ℝ in atTop, ∀ Φ : QuantumChannel (Fock d) (Fock d),
      realFlatBoxPayoff r Φ (thermalPositive q (fun i => (hq0 i).le) hq1)
        (thermalPositive q (fun i => (hq0 i).le) hq1) L ≤
          (∏ i, Thermal.fidelity (q i) (Thermal.amplified (r ^ 2) (q i))) + ε :=
  eventually_forall_realFlatBox_le_of_integer r _ _
    (eventually_forall_flatBox_thermal_le r hr hq0 hq1)

/-- Arbitrary real expanding boxes in the required order `limsup sup_channel`. -/
theorem limsup_realFlatBox_thermal_le
    (r : ℝ) (hr : 1 < r ^ 2) {q : Fin d → ℝ}
    (hq0 : ∀ i, 0 < q i) (hq1 : ∀ i, q i < 1) :
    Filter.limsup (realFlatBoxOptimalPayoff r
      (thermalPositive q (fun i => (hq0 i).le) hq1)
      (thermalPositive q (fun i => (hq0 i).le) hq1)) atTop ≤
        ∏ i, Thermal.fidelity (q i) (Thermal.amplified (r ^ 2) (q i)) :=
  limsup_realFlatBoxOptimalPayoff_le r _ _
    (eventually_forall_realFlatBox_thermal_le r hr hq0 hq1)

/-- The manuscript orbital factor at physical amplitude gain `sqrt γ`, for
all real radii tending to infinity. The payoff is average root fidelity. -/
theorem limsup_realFlatBox_thermal_le_modeFactor
    (γ : ℝ) (hγ : 1 < γ) {q : Fin d → ℝ}
    (hq0 : ∀ i, 0 < q i) (hq1 : ∀ i, q i < 1) :
    Filter.limsup (realFlatBoxOptimalPayoff (Real.sqrt γ)
      (thermalPositive q (fun i => (hq0 i).le) hq1)
      (thermalPositive q (fun i => (hq0 i).le) hq1)) atTop ≤
        ∏ i, Thermal.modeFactor γ (q i) := by
  have hs : Real.sqrt γ ^ 2 = γ := Real.sq_sqrt (by linarith)
  have h := limsup_realFlatBox_thermal_le (Real.sqrt γ) (by rwa [hs]) hq0 hq1
  simp_rw [hs, Thermal.fidelity_amplified_eq_modeFactor hγ (hq0 _).le (hq1 _)] at h
  exact h

end Cloning.MultimodeCoherent
