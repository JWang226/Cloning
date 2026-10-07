import Cloning.HybridFlatBody
import Cloning.HybridGaussianAttainmentBoundary

/-! Real-radius Gaussian amplification optimality on every compact convex
flat-prior body, including the whitened score-hyperplane polytope. -/
noncomputable section
open scoped ComplexOrder InnerProductSpace Topology BigOperators
open Filter MeasureTheory Cloning.InfiniteTraceClass Cloning.MultimodeCoherent
namespace Cloning.Hybrid.PhaseBody
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
variable {k s : ℕ} (B : PhaseBody k s)

def payoff (r : ℝ) (Λ : HybridChannel k s) (A Z : HybridPositive k s) (L : ℝ) : ℝ :=
  (volume.real B.carrier)⁻¹ * ∫ z in B.carrier,orbitPayoff r Λ A Z (L • z)

theorem payoff_eq_normalized_dilate (r : ℝ) (Λ : HybridChannel k s)
    (A Z : HybridPositive k s) {L : ℝ} (hL : 0<L) :
    B.payoff r Λ A Z L=(volume.real (B.dilate L))⁻¹ *
      ∫ ξ in B.dilate L,orbitPayoff r Λ A Z ξ :=
  B.normalized_dilate hL _

theorem payoff_integer (r : ℝ) (Λ : HybridChannel k s)
    (A Z : HybridPositive k s) (n : ℕ) :
    B.payoff r Λ A Z ((n : ℝ)+1)=
      ∫ ξ,orbitPayoff r Λ A Z ξ ∂B.density.expandingPrior n :=
  (B.integral_expandingPrior n _ (continuous_orbitPayoff r Λ A Z)).symm

theorem payoff_nonneg (r : ℝ) (Λ : HybridChannel k s)
    (A Z : HybridPositive k s) (L : ℝ) : 0≤B.payoff r Λ A Z L :=
  mul_nonneg (inv_nonneg.mpr measureReal_nonneg)
    (integral_nonneg fun _ => PositiveL1.rootFidelity_nonneg _ _)

theorem payoff_le_sqrt (r : ℝ) (Λ : HybridChannel k s)
    (A Z : HybridPositive k s) (L : ℝ) :
    B.payoff r Λ A Z L≤Real.sqrt ‖A.1‖*Real.sqrt ‖Z.1‖ := by
  have hi : IntegrableOn (fun ξ => orbitPayoff r Λ A Z (L • ξ)) B.carrier :=
    ((continuous_orbitPayoff r Λ A Z).comp (continuous_id.const_smul L)).continuousOn.integrableOn_compact B.compact
  have hp ξ : orbitPayoff r Λ A Z (L • ξ)≤Real.sqrt ‖A.1‖*Real.sqrt ‖Z.1‖ := by
    rw [orbitPayoff_eq_translated]
    simpa only [PositiveL1.norm_map] using
      PositiveL1.rootFidelity_le_sqrt (A.map (translatedChannel r Λ (L • ξ))) Z
  have hh := integral_mono hi (integrableOn_const (hs:=B.compact.measure_ne_top)) hp
  change (volume.real B.carrier)⁻¹ * _ ≤ _
  calc
    _ ≤ (volume.real B.carrier)⁻¹ * ∫ _ξ in B.carrier,Real.sqrt ‖A.1‖*Real.sqrt ‖Z.1‖ :=
      mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr measureReal_nonneg)
    _ = _ := by
      simp only [integral_const,measureReal_restrict_apply_univ,smul_eq_mul]
      rw [← mul_assoc,inv_mul_cancel₀ B.volume_real_pos.ne',one_mul]

theorem payoff_le_integer (r : ℝ) (Λ : HybridChannel k s)
    (A Z : HybridPositive k s) {L : ℝ} (hL : 0<L) (n : ℕ) (hLn : L≤(n : ℝ)+1) :
    B.payoff r Λ A Z L≤(((n : ℝ)+1)/L)^Module.finrank ℝ (PhaseSpace k s)*
      B.payoff r Λ A Z ((n : ℝ)+1) := by
  have hN : 0<(n : ℝ)+1 := by positivity
  have hi : (∫ ξ in B.dilate L,orbitPayoff r Λ A Z ξ)≤
      ∫ ξ in B.dilate ((n : ℝ)+1),orbitPayoff r Λ A Z ξ :=
    setIntegral_mono_set
      ((continuous_orbitPayoff r Λ A Z).continuousOn.integrableOn_compact (B.dilate_compact _))
      (Eventually.of_forall fun _ => PositiveL1.rootFidelity_nonneg _ _)
      (B.dilate_mono hL.le hN hLn).eventuallyLE
  rw [B.payoff_eq_normalized_dilate r Λ A Z hL,B.payoff_eq_normalized_dilate r Λ A Z hN,
    B.dilate_volume_real hL,B.dilate_volume_real hN]
  calc
    _ ≤ (L^Module.finrank ℝ (PhaseSpace k s)*volume.real B.carrier)⁻¹ *
        ∫ ξ in B.dilate ((n : ℝ)+1),orbitPayoff r Λ A Z ξ :=
      mul_le_mul_of_nonneg_left hi (by positivity)
    _ = _ := by
      rw [div_pow]
      field_simp [hL.ne',hN.ne',B.volume_real_pos.ne']

theorem eventually_forall_payoff_le_of_integer (r : ℝ) (A Z : HybridPositive k s) {C : ℝ}
    (h : ∀ ε>0,∀ᶠ (n : ℕ) in atTop,∀ Λ : HybridChannel k s,
      B.payoff r Λ A Z ((n : ℝ)+1)≤C+ε) :
    ∀ ε>0,∀ᶠ L : ℝ in atTop,∀ Λ : HybridChannel k s,B.payoff r Λ A Z L≤C+ε := by
  intro ε hε
  have hfloor : Tendsto (Nat.floor : ℝ→ℕ) atTop atTop :=
    Nat.floor_mono.tendsto_atTop_atTop (fun n => ⟨(n : ℝ),by simp⟩)
  have hint := hfloor.eventually (h (ε/2) (by linarith))
  have ht : Tendsto (fun L : ℝ =>
      (1+L⁻¹)^Module.finrank ℝ (PhaseSpace k s)*(C+ε/2)) atTop (𝓝 (C+ε/2)) := by
    simpa using (realFlatBox_overhead_tendsto_one k s).mul_const (C+ε/2)
  filter_upwards [hint,ht.eventually_lt_const (by linarith : C+ε/2<C+ε),
    eventually_gt_atTop (0 : ℝ)] with L hLi hnear hL
  intro Λ
  have hc := B.payoff_le_integer r Λ A Z hL (Nat.floor L) (Nat.lt_floor_add_one L).le
  have hr : (((Nat.floor L : ℕ):ℝ)+1)/L≤1+L⁻¹ := by
    apply (div_le_iff₀ hL).mpr
    have hf := Nat.floor_le hL.le
    rw [add_mul,one_mul,inv_mul_cancel₀ hL.ne']
    linarith
  calc
    _ ≤ ((((Nat.floor L : ℕ):ℝ)+1)/L)^Module.finrank ℝ (PhaseSpace k s)*
        B.payoff r Λ A Z (((Nat.floor L : ℕ):ℝ)+1) := hc
    _ ≤ (1+L⁻¹)^Module.finrank ℝ (PhaseSpace k s)*
        B.payoff r Λ A Z (((Nat.floor L : ℕ):ℝ)+1) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hr _)
        (B.payoff_nonneg r Λ A Z _)
    _ ≤ (1+L⁻¹)^Module.finrank ℝ (PhaseSpace k s)*(C+ε/2) :=
      mul_le_mul_of_nonneg_left (hLi Λ) (by positivity)
    _ ≤ C+ε := hnear.le

def optimalPayoff (r : ℝ) (A Z : HybridPositive k s) (L : ℝ) : ℝ :=
  sSup (Set.range fun Λ : HybridChannel k s => B.payoff r Λ A Z L)

theorem payoff_le_optimal (r : ℝ) (Λ : HybridChannel k s)
    (A Z : HybridPositive k s) (L : ℝ) : B.payoff r Λ A Z L≤B.optimalPayoff r A Z L := by
  apply le_csSup _ (Set.mem_range_self Λ)
  refine ⟨Real.sqrt ‖A.1‖*Real.sqrt ‖Z.1‖,?_⟩
  rintro _ ⟨Γ,rfl⟩
  exact B.payoff_le_sqrt r Γ A Z L

/-- The radius threshold is before every arbitrary CPTP competitor. -/
theorem eventually_forall_gaussian_payoff_le
    (a : Fin k→ℝ) (ha : ∀ i,0<a i) (g : ℝ) (hg : 1<g)
    (q : Fin s→ℝ) (hq0 : ∀ i,0≤q i) (hq1 : ∀ i,q i<1) :
    ∀ ε>0,∀ᶠ L : ℝ in atTop,∀ Λ : HybridChannel k s,
      B.payoff (Real.sqrt g) Λ (gaussianThermalPositive a ha q hq0 hq1)
        (gaussianThermalPositive a ha q hq0 hq1) L≤
        Thermal.classicalBase g^((k : ℝ)/2)*(∏ i,Thermal.modeFactor g (q i))+ε := by
  apply B.eventually_forall_payoff_le_of_integer
  simpa only [B.payoff_integer] using
    B.density.eventually_forall_gaussian_orbitPayoff_le_modeFactor_nonneg a ha g hg q hq0 hq1

/-- Exact physical Gaussian optimum for every real-radius convex-body prior.
The value is independent of the prior body's shape. -/
theorem gaussian_optimalPayoff_tendsto
    (a : Fin k→ℝ) (ha : ∀ i,0<a i) (g : ℝ) (hg : 1<g)
    (q : Fin s→ℝ) (hq0 : ∀ i,0≤q i) (hq1 : ∀ i,q i<1) :
    Tendsto (B.optimalPayoff (Real.sqrt g)
      (gaussianThermalPositive a ha q hq0 hq1) (gaussianThermalPositive a ha q hq0 hq1))
      atTop (𝓝 (Thermal.classicalBase g^((k : ℝ)/2)*∏ i,Thermal.modeFactor g (q i))) := by
  let A := gaussianThermalPositive a ha q hq0 hq1
  let F := Thermal.classicalBase g^((k : ℝ)/2)*∏ i,Thermal.modeFactor g (q i)
  have hattain (L : ℝ) : B.payoff (Real.sqrt g) (gaussianAmplifierChannel g hg) A A L=F := by
    unfold payoff
    dsimp only [A]
    simp_rw [gaussianAmplifierChannel_orbitPayoff a ha g hg q hq0 hq1]
    rw [integral_const]
    simp only [measureReal_restrict_apply_univ,smul_eq_mul]
    rw [← mul_assoc,inv_mul_cancel₀ B.volume_real_pos.ne',one_mul]
  apply tendsto_order.mpr
  constructor
  · intro c hc
    exact Eventually.of_forall fun L => hc.trans_le
      ((hattain L).symm.trans_le (B.payoff_le_optimal _ _ A A L))
  · intro c hc
    filter_upwards [B.eventually_forall_gaussian_payoff_le a ha g hg q hq0 hq1
      ((c-F)/2) (by change F<c at hc; linarith)] with L hL
    have hu : B.optimalPayoff (Real.sqrt g) A A L≤F+(c-F)/2 := by
      apply csSup_le ⟨_,Set.mem_range_self (gaussianAmplifierChannel g hg)⟩
      rintro _ ⟨Λ,rfl⟩
      exact hL Λ
    change F<c at hc
    linarith

end Cloning.Hybrid.PhaseBody
