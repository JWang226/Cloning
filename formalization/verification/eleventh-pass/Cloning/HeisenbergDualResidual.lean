import Cloning.HeisenbergDualWeyl
import Cloning.InfiniteTraceBoundedMaps

/-! A covariant positive trace-nonincreasing map has one constant success
probability. Every nonzero completely positive such map normalizes to an
actual CPTP channel; no residual-instrument normalization is assumed. -/

noncomputable section
open scoped ComplexOrder InnerProductSpace Topology BigOperators

namespace Cloning.InfiniteTraceClass
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- A positive map with identically zero trace is zero on every complex input. -/
theorem positiveMap_eq_zero_of_trace_zero (Φ : TraceClass H →ₗ[ℂ] TraceClass K)
    (hpos : ∀ T, 0 ≤ T.1 → 0 ≤ (Φ T).1)
    (htrace : ∀ T, traceCLM (Φ T) = 0) : Φ = 0 := by
  ext T
  apply norm_eq_zero.mp
  apply le_antisymm _ (norm_nonneg _)
  have hb := norm_map_le_two_mul_of_trace_bound Φ hpos (c := 0) le_rfl
    (fun T _ => by rw [htrace T]; simp) T
  simpa using hb

/-- Positive rescaling preserves complete positivity. -/
theorem IsCompletelyPositive.real_smul
    {Φ : TraceClass H →ₗ[ℂ] TraceClass K} (hΦ : IsCompletelyPositive Φ)
    {c : ℝ} (hc : 0 ≤ c) : IsCompletelyPositive ((c : ℂ) • Φ) := by
  intro n A hA x
  have h := hΦ n A hA x
  have hc' : (0 : ℂ) ≤ (c : ℂ) := by exact_mod_cast hc
  change 0 ≤ ∑ i, ∑ j, ⟪x i, (c : ℂ) • (Φ (A i j)).1 (x j)⟫_ℂ
  simpa only [inner_smul_right, Finset.mul_sum] using mul_nonneg hc' h

/-- The normalization is the genuine original map divided by its success
probability; its positivity, complete positivity and exact trace law are proved. -/
def normalizedQuantumChannel
    (Φ : TraceClass H →ₗ[ℂ] TraceClass K)
    (hpos : ∀ T, 0 ≤ T.1 → 0 ≤ (Φ T).1)
    (hCP : IsCompletelyPositive Φ) (c : ℝ) (hc : 0 < c)
    (htrace : ∀ T, traceCLM (Φ T) = (c : ℂ) * traceCLM T) :
    QuantumChannel H K where
  toLinearMap := ((c⁻¹ : ℝ) : ℂ) • Φ
  map_nonneg := by
    intro T hT
    change 0 ≤ (((c⁻¹ : ℝ) : ℂ) • (Φ T).1)
    have heq : (((c⁻¹ : ℝ) : ℂ) • (Φ T).1) = c⁻¹ • (Φ T).1 := by
      ext x
      simp only [ContinuousLinearMap.smul_apply, RCLike.real_smul_eq_coe_smul (K := ℂ)]
      rfl
    rw [heq]
    exact smul_nonneg (inv_nonneg.mpr hc.le) (hpos T hT)
  trace_preserving := by
    intro T
    change traceCLM (((c⁻¹ : ℝ) : ℂ) • Φ T) = traceCLM T
    rw [map_smul, htrace, smul_eq_mul, ← mul_assoc,
      ← Complex.ofReal_mul, inv_mul_cancel₀ hc.ne', Complex.ofReal_one, one_mul]
  completelyPositive := hCP.real_smul (inv_nonneg.mpr hc.le)

@[simp] theorem normalizedQuantumChannel_scale
    (Φ : TraceClass H →ₗ[ℂ] TraceClass K)
    (hpos : ∀ T, 0 ≤ T.1 → 0 ≤ (Φ T).1)
    (hCP : IsCompletelyPositive Φ) (c : ℝ) (hc : 0 < c)
    (htrace : ∀ T, traceCLM (Φ T) = (c : ℂ) * traceCLM T) :
    (c : ℂ) • (normalizedQuantumChannel Φ hpos hCP c hc htrace).toLinearMap = Φ := by
  change (c : ℂ) • (((c⁻¹ : ℝ) : ℂ) • Φ) = Φ
  rw [smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hc.ne', Complex.ofReal_one, one_smul]

end Cloning.InfiniteTraceClass

namespace Cloning.MultimodeCoherent
open Cloning.InfiniteTraceClass
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
variable {d : ℕ}

/-- The scalar success mass of an actual map, evaluated on the vacuum state. -/
def covariantTraceMass (Φ : TraceClass (Fock d) →L[ℂ] TraceClass (Fock d)) : ℝ :=
  (traceCLM (Φ (coherentProjector 0))).re

/-- Covariance forces the dual identity observable to be a scalar identity. -/
theorem covariant_heisenbergDual_one
    (Φ : TraceClass (Fock d) →L[ℂ] TraceClass (Fock d)) (r : ℝ)
    (hΦ : ∀ a T, Φ (displacementTraceMap a T) =
      displacementTraceMap (r • a) (Φ T)) :
    heisenbergDual Φ (1 : Fock d →L[ℂ] Fock d) =
      traceCLM (Φ (coherentProjector 0)) • (1 : Fock d →L[ℂ] Fock d) := by
  have h := traceClass_covariant_weyl_multiplier Φ r hΦ 0
  simpa only [smul_zero, neg_zero, displacement_zero, weylMultiplier,
    ContinuousLinearMap.id_apply, heisenbergDual_inner, tracePairing_one] using h

/-- The exact scalar trace law holds on all trace-class operators. -/
theorem covariant_trace_scaling
    (Φ : TraceClass (Fock d) →L[ℂ] TraceClass (Fock d)) (r : ℝ)
    (hΦ : ∀ a T, Φ (displacementTraceMap a T) =
      displacementTraceMap (r • a) (Φ T))
    (hpos : ∀ T, 0 ≤ T.1 → 0 ≤ (Φ T).1) (T : TraceClass (Fock d)) :
    traceCLM (Φ T) = (covariantTraceMass Φ : ℂ) * traceCLM T := by
  have hreal : traceCLM (Φ (coherentProjector 0)) = (covariantTraceMass Φ : ℂ) := by
    apply Complex.ext
    · rfl
    · exact trace_im_eq_zero (hpos _ (coherentProjector_nonneg 0)) _
  calc
    _ = tracePairing T (heisenbergDual Φ 1) := by
      rw [heisenbergDual_pairing, tracePairing_one]
    _ = _ := by rw [covariant_heisenbergDual_one Φ r hΦ, map_smul,
      tracePairing_one, smul_eq_mul, hreal]

/-- A positive trace-nonincreasing covariant map has success probability in
`[0,1]`, fixed by its actual vacuum output. -/
theorem covariantTraceMass_mem_unitInterval
    (Φ : TraceClass (Fock d) →L[ℂ] TraceClass (Fock d))
    (hpos : ∀ T, 0 ≤ T.1 → 0 ≤ (Φ T).1)
    (htrace : ∀ T, 0 ≤ T.1 → (traceCLM (Φ T)).re ≤ (traceCLM T).re) :
    0 ≤ covariantTraceMass Φ ∧ covariantTraceMass Φ ≤ 1 := by
  constructor
  · exact trace_re_nonneg (hpos _ (coherentProjector_nonneg 0)) _
  · have h := htrace (coherentProjector 0) (coherentProjector_nonneg 0)
    simpa only [coherentProjector_trace, Complex.one_re] using h

/-- Every covariant completely positive trace-nonincreasing map is either
zero or a scalar multiple of an actual CPTP map. The scalar and normalized
channel are derived from the given physical map. -/
theorem covariant_cpTNI_zero_or_scaled_channel
    (Γ : TraceClass (Fock d) →ₗ[ℂ] TraceClass (Fock d))
    (hpos : ∀ T, 0 ≤ T.1 → 0 ≤ (Γ T).1)
    (hCP : IsCompletelyPositive Γ)
    (htrace : ∀ T, 0 ≤ T.1 → (traceCLM (Γ T)).re ≤ (traceCLM T).re)
    (r : ℝ)
    (hcov : ∀ a T, Γ (displacementTraceMap a T) =
      displacementTraceMap (r • a) (Γ T)) :
    Γ = 0 ∨ ∃ (c : ℝ) (Φ : QuantumChannel (Fock d) (Fock d)),
      0 < c ∧ c ≤ 1 ∧ Γ = (c : ℂ) • Φ.toLinearMap ∧
      ∀ a T, Φ.toLinearMap (displacementTraceMap a T) =
        displacementTraceMap (r • a) (Φ.toLinearMap T) := by
  let Γc := toContinuousLinearMapOfTraceBound Γ hpos (c := 1) zero_le_one
    (fun T hT => by simpa only [one_mul] using htrace T hT)
  have hb := covariantTraceMass_mem_unitInterval Γc hpos htrace
  have hscale := covariant_trace_scaling Γc r hcov hpos
  by_cases hc : covariantTraceMass Γc = 0
  · left
    apply positiveMap_eq_zero_of_trace_zero Γ hpos
    intro T
    simpa only [hc, Complex.ofReal_zero, zero_mul] using hscale T
  · right
    have hcpos : 0 < covariantTraceMass Γc := lt_of_le_of_ne hb.1 (Ne.symm hc)
    let Φ := normalizedQuantumChannel Γ hpos hCP (covariantTraceMass Γc) hcpos hscale
    refine ⟨covariantTraceMass Γc, Φ, hcpos, hb.2, ?_, ?_⟩
    · exact (normalizedQuantumChannel_scale Γ hpos hCP _ hcpos hscale).symm
    · intro a T
      change (((covariantTraceMass Γc)⁻¹ : ℝ) : ℂ) • Γ (displacementTraceMap a T) =
        displacementTraceMap (r • a) ((((covariantTraceMass Γc)⁻¹ : ℝ) : ℂ) • Γ T)
      rw [hcov, map_smul]

end Cloning.MultimodeCoherent
