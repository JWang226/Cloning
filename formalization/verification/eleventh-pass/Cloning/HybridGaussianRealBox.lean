import Cloning.HybridFlatBox
import Cloning.HybridGaussianConverse

/-! The full hybrid Gaussian converse on literal rectangular Lebesgue boxes
of every real radius, with the channel supremum taken before the large-box limit. -/

noncomputable section
open scoped ComplexOrder InnerProductSpace Topology BigOperators
open Filter MeasureTheory
namespace Cloning.Hybrid
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {k s : ℕ}

/-- The normalized physical orbit-fidelity average at integer radius `n+1`. -/
def flatBoxPayoff (r : ℝ) (Λ : HybridChannel k s) (A B : HybridPositive k s) (n : ℕ) : ℝ :=
  (volume.real (phaseSpaceUnitBox k s))⁻¹ * ∫ z in phaseSpaceUnitBox k s,
    orbitPayoff r Λ A B (((n : ℝ) + 1) • z)

theorem flatBoxPayoff_eq_integral (r : ℝ) (Λ : HybridChannel k s)
    (A B : HybridPositive k s) (n : ℕ) :
    flatBoxPayoff r Λ A B n =
      ∫ ξ, orbitPayoff r Λ A B ξ ∂(flatBoxDensity k s).expandingPrior n :=
  (integral_flatBox_expandingPrior k s n _ (continuous_orbitPayoff r Λ A B)).symm

theorem flatBoxPayoff_eq_normalized_box (r : ℝ) (Λ : HybridChannel k s)
    (A B : HybridPositive k s) (n : ℕ) :
    flatBoxPayoff r Λ A B n =
      (volume.real (phaseSpaceBox k s ((n : ℝ) + 1)))⁻¹ *
        ∫ ξ in phaseSpaceBox k s ((n : ℝ) + 1), orbitPayoff r Λ A B ξ :=
  normalized_unitBox_smul_eq (by positivity : 0 < (n : ℝ) + 1) _

theorem flatBoxPayoff_nonneg (r : ℝ) (Λ : HybridChannel k s)
    (A B : HybridPositive k s) (n : ℕ) : 0 ≤ flatBoxPayoff r Λ A B n := by
  rw [flatBoxPayoff_eq_integral]
  exact integral_nonneg fun _ => PositiveL1.rootFidelity_nonneg _ _

/-- Flat average over the full physical box at an arbitrary real radius. -/
def realFlatBoxPayoff (r : ℝ) (Λ : HybridChannel k s) (A B : HybridPositive k s) (L : ℝ) : ℝ :=
  (volume.real (phaseSpaceUnitBox k s))⁻¹ * ∫ z in phaseSpaceUnitBox k s,
    orbitPayoff r Λ A B (L • z)

theorem realFlatBoxPayoff_eq_normalized_box (r : ℝ) (Λ : HybridChannel k s)
    (A B : HybridPositive k s) {L : ℝ} (hL : 0 < L) :
    realFlatBoxPayoff r Λ A B L =
      (volume.real (phaseSpaceBox k s L))⁻¹ *
        ∫ ξ in phaseSpaceBox k s L, orbitPayoff r Λ A B ξ :=
  normalized_unitBox_smul_eq hL _

theorem realFlatBoxPayoff_nonneg (r : ℝ) (Λ : HybridChannel k s)
    (A B : HybridPositive k s) (L : ℝ) : 0 ≤ realFlatBoxPayoff r Λ A B L := by
  apply mul_nonneg (inv_nonneg.mpr measureReal_nonneg)
  exact integral_nonneg fun _ => PositiveL1.rootFidelity_nonneg _ _

theorem realFlatBoxPayoff_le_sqrt (r : ℝ) (Λ : HybridChannel k s)
    (A B : HybridPositive k s) (L : ℝ) :
    realFlatBoxPayoff r Λ A B L ≤ Real.sqrt ‖A.1‖ * Real.sqrt ‖B.1‖ := by
  have hint : IntegrableOn (fun z => orbitPayoff r Λ A B (L • z)) (phaseSpaceUnitBox k s) :=
    ((continuous_orbitPayoff r Λ A B).comp
      (continuous_id.const_smul L)).continuousOn.integrableOn_compact (phaseSpaceUnitBox_compact k s)
  have hp (z : PhaseSpace k s) : orbitPayoff r Λ A B (L • z) ≤
      Real.sqrt ‖A.1‖ * Real.sqrt ‖B.1‖ := by
    rw [orbitPayoff_eq_translated]
    simpa only [PositiveL1.norm_map] using
      PositiveL1.rootFidelity_le_sqrt (A.map (translatedChannel r Λ (L • z))) B
  have hi := integral_mono hint
    (integrableOn_const (hs := (phaseSpaceUnitBox_compact k s).measure_ne_top)) hp
  change (volume.real (phaseSpaceUnitBox k s))⁻¹ * _ ≤ _
  calc
    _ ≤ (volume.real (phaseSpaceUnitBox k s))⁻¹ *
        ∫ _z in phaseSpaceUnitBox k s, Real.sqrt ‖A.1‖ * Real.sqrt ‖B.1‖ :=
      mul_le_mul_of_nonneg_left hi (inv_nonneg.mpr measureReal_nonneg)
    _ = _ := by
      simp only [integral_const, measureReal_restrict_apply_univ, smul_eq_mul]
      rw [← mul_assoc, inv_mul_cancel₀ (phaseSpaceUnitBox_volume_real_pos k s).ne', one_mul]

theorem realFlatBoxPayoff_eq_of_orbitPayoff_const (r : ℝ) (Λ : HybridChannel k s)
    (A B : HybridPositive k s) {C : ℝ} (hC : ∀ ξ, orbitPayoff r Λ A B ξ = C) (L : ℝ) :
    realFlatBoxPayoff r Λ A B L = C := by
  unfold realFlatBoxPayoff
  simp_rw [hC]
  rw [integral_const]
  simp only [measureReal_restrict_apply_univ, smul_eq_mul]
  rw [← mul_assoc, inv_mul_cancel₀ (phaseSpaceUnitBox_volume_real_pos k s).ne', one_mul]

/-- Positive orbit fidelity compares nested boxes with exactly their volume ratio. -/
theorem realFlatBoxPayoff_le_integer (r : ℝ) (Λ : HybridChannel k s)
    (A B : HybridPositive k s) {L : ℝ} (hL : 0 < L) (n : ℕ) (hLn : L ≤ (n : ℝ) + 1) :
    realFlatBoxPayoff r Λ A B L ≤
      (((n : ℝ) + 1) / L) ^ Module.finrank ℝ (PhaseSpace k s) * flatBoxPayoff r Λ A B n := by
  have hN : 0 < (n : ℝ) + 1 := by positivity
  have hi : (∫ ξ in phaseSpaceBox k s L, orbitPayoff r Λ A B ξ) ≤
      ∫ ξ in phaseSpaceBox k s ((n : ℝ) + 1), orbitPayoff r Λ A B ξ :=
    setIntegral_mono_set
      ((continuous_orbitPayoff r Λ A B).continuousOn.integrableOn_compact
        (phaseSpaceBox_compact k s _))
      (Eventually.of_forall fun _ => PositiveL1.rootFidelity_nonneg _ _)
      (phaseSpaceBox_mono hLn).eventuallyLE
  rw [realFlatBoxPayoff_eq_normalized_box r Λ A B hL, flatBoxPayoff_eq_normalized_box,
    phaseSpaceBox_volume_real hL, phaseSpaceBox_volume_real hN]
  calc
    _ ≤ (L ^ Module.finrank ℝ (PhaseSpace k s) * volume.real (phaseSpaceUnitBox k s))⁻¹ *
        ∫ ξ in phaseSpaceBox k s ((n : ℝ) + 1), orbitPayoff r Λ A B ξ :=
      mul_le_mul_of_nonneg_left hi (by positivity)
    _ = _ := by
      rw [div_pow]
      field_simp [hL.ne', hN.ne', (phaseSpaceUnitBox_volume_real_pos k s).ne']

theorem realFlatBox_overhead_tendsto_one (k s : ℕ) :
    Tendsto (fun L : ℝ => (1 + L⁻¹) ^ Module.finrank ℝ (PhaseSpace k s)) atTop (𝓝 1) := by
  have ht : Tendsto (fun L : ℝ => 1 + L⁻¹) atTop (𝓝 (1 + 0 : ℝ)) :=
    tendsto_const_nhds.add tendsto_inv_atTop_zero
  simpa using ht.pow (Module.finrank ℝ (PhaseSpace k s))

/-- The radius threshold remains independent of the competitor when passing
from integer to arbitrary real radii. -/
theorem eventually_forall_realFlatBox_le_of_integer (r : ℝ)
    (A B : HybridPositive k s) {C : ℝ}
    (h : ∀ ε > 0, ∀ᶠ n in atTop, ∀ Λ : HybridChannel k s, flatBoxPayoff r Λ A B n ≤ C + ε) :
    ∀ ε > 0, ∀ᶠ L : ℝ in atTop, ∀ Λ : HybridChannel k s, realFlatBoxPayoff r Λ A B L ≤ C + ε := by
  intro ε hε
  have hfloor : Tendsto (Nat.floor : ℝ → ℕ) atTop atTop :=
    Nat.floor_mono.tendsto_atTop_atTop (fun n => ⟨(n : ℝ), by simp⟩)
  have hint := hfloor.eventually (h (ε / 2) (by linarith))
  have ht : Tendsto (fun L : ℝ =>
      (1 + L⁻¹) ^ Module.finrank ℝ (PhaseSpace k s) * (C + ε / 2)) atTop (𝓝 (C + ε / 2)) := by
    simpa using (realFlatBox_overhead_tendsto_one k s).mul_const (C + ε / 2)
  have hnear := ht.eventually_lt_const (by linarith : C + ε / 2 < C + ε)
  filter_upwards [hint, hnear, eventually_gt_atTop (0 : ℝ)] with L hLi hnear hL
  intro Λ
  have hc := realFlatBoxPayoff_le_integer r Λ A B hL (Nat.floor L) (Nat.lt_floor_add_one L).le
  have hr : (((Nat.floor L : ℕ) : ℝ) + 1) / L ≤ 1 + L⁻¹ := by
    apply (div_le_iff₀ hL).mpr
    have hf := Nat.floor_le hL.le
    rw [add_mul, one_mul, inv_mul_cancel₀ hL.ne']
    linarith
  calc
    realFlatBoxPayoff r Λ A B L ≤
        ((((Nat.floor L : ℕ) : ℝ) + 1) / L) ^ Module.finrank ℝ (PhaseSpace k s) *
          flatBoxPayoff r Λ A B (Nat.floor L) := hc
    _ ≤ (1 + L⁻¹) ^ Module.finrank ℝ (PhaseSpace k s) * flatBoxPayoff r Λ A B (Nat.floor L) := by
      apply mul_le_mul_of_nonneg_right _ (flatBoxPayoff_nonneg r Λ A B _)
      exact pow_le_pow_left₀ (by positivity) hr _
    _ ≤ (1 + L⁻¹) ^ Module.finrank ℝ (PhaseSpace k s) * (C + ε / 2) :=
      mul_le_mul_of_nonneg_left (hLi Λ) (by positivity)
    _ ≤ C + ε := hnear.le

/-- A fresh arbitrary hybrid channel may be chosen separately at every real radius. -/
def realFlatBoxOptimalPayoff (r : ℝ) (A B : HybridPositive k s) (L : ℝ) : ℝ :=
  sSup (Set.range (fun Λ : HybridChannel k s => realFlatBoxPayoff r Λ A B L))

theorem realFlatBoxPayoff_le_optimal (r : ℝ) (Λ : HybridChannel k s)
    (A B : HybridPositive k s) (L : ℝ) :
    realFlatBoxPayoff r Λ A B L ≤ realFlatBoxOptimalPayoff r A B L := by
  apply le_csSup _ (Set.mem_range_self Λ)
  refine ⟨Real.sqrt ‖A.1‖ * Real.sqrt ‖B.1‖, ?_⟩
  rintro _ ⟨Γ, rfl⟩
  exact realFlatBoxPayoff_le_sqrt r Γ A B L

theorem realFlatBoxOptimalPayoff_nonneg (r : ℝ) (A B : HybridPositive k s) (L : ℝ) :
    0 ≤ realFlatBoxOptimalPayoff r A B L := by
  have hb : BddAbove (Set.range (fun Λ : HybridChannel k s => realFlatBoxPayoff r Λ A B L)) := by
    refine ⟨Real.sqrt ‖A.1‖ * Real.sqrt ‖B.1‖, ?_⟩
    rintro _ ⟨Λ, rfl⟩
    exact realFlatBoxPayoff_le_sqrt r Λ A B L
  exact (realFlatBoxPayoff_nonneg r (translationChannel 0) A B L).trans
    (le_csSup hb (Set.mem_range_self (translationChannel 0)))

theorem limsup_realFlatBoxOptimalPayoff_le (r : ℝ) (A B : HybridPositive k s) {C : ℝ}
    (h : ∀ ε > 0, ∀ᶠ L : ℝ in atTop, ∀ Λ : HybridChannel k s, realFlatBoxPayoff r Λ A B L ≤ C + ε) :
    Filter.limsup (realFlatBoxOptimalPayoff r A B) atTop ≤ C := by
  apply le_of_forall_pos_le_add
  intro ε hε
  apply limsup_le_of_le
    (isCoboundedUnder_le_of_le atTop (realFlatBoxOptimalPayoff_nonneg r A B))
  filter_upwards [h ε hε] with L hL
  apply csSup_le (show (Set.range (fun Λ : HybridChannel k s => realFlatBoxPayoff r Λ A B L)).Nonempty
    from ⟨_, Set.mem_range_self (translationChannel 0)⟩)
  rintro _ ⟨Λ, rfl⟩
  exact hL Λ

/-- The full Gaussian classical--quantum converse, uniformly over channels
at every sufficiently large real physical box radius. -/
theorem eventually_forall_realFlatBox_gaussian_le_modeFactor
    (a : Fin k → ℝ) (ha : ∀ i, 0 < a i) (g : ℝ) (hg : 1 < g)
    (q : Fin s → ℝ) (hq0 : ∀ i, 0 < q i) (hq1 : ∀ i, q i < 1) :
    ∀ ε > 0, ∀ᶠ L : ℝ in atTop, ∀ Λ : HybridChannel k s,
      realFlatBoxPayoff (Real.sqrt g) Λ
        (gaussianThermalPositive a ha q (fun i => (hq0 i).le) hq1)
        (gaussianThermalPositive a ha q (fun i => (hq0 i).le) hq1) L ≤
      Thermal.classicalBase g ^ ((k : ℝ) / 2) * (∏ i, Thermal.modeFactor g (q i)) + ε := by
  apply eventually_forall_realFlatBox_le_of_integer
  simpa only [flatBoxPayoff_eq_integral] using
    (flatBoxDensity k s).eventually_forall_gaussian_orbitPayoff_le_modeFactor a ha g hg q hq0 hq1

/-- Literal normalized Lebesgue boxes, with the required `limsup sup_channel`
order. All classical and quantum noise correlations are allowed. -/
theorem limsup_realFlatBox_gaussian_le_modeFactor
    (a : Fin k → ℝ) (ha : ∀ i, 0 < a i) (g : ℝ) (hg : 1 < g)
    (q : Fin s → ℝ) (hq0 : ∀ i, 0 < q i) (hq1 : ∀ i, q i < 1) :
    Filter.limsup (realFlatBoxOptimalPayoff (Real.sqrt g)
      (gaussianThermalPositive a ha q (fun i => (hq0 i).le) hq1)
      (gaussianThermalPositive a ha q (fun i => (hq0 i).le) hq1)) atTop ≤
      Thermal.classicalBase g ^ ((k : ℝ) / 2) * (∏ i, Thermal.modeFactor g (q i)) :=
  limsup_realFlatBoxOptimalPayoff_le _ _ _
    (eventually_forall_realFlatBox_gaussian_le_modeFactor a ha g hg q hq0 hq1)

end Cloning.Hybrid
