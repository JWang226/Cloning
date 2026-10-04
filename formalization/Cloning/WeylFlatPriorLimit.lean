import Cloning.WeylFoelnerPayoff
import Cloning.WeylFlatPrior

/-! Compact-witness control of diffuse-prior fidelity performance for arbitrary
sequences of quantum competitors. The competitors may change at every scale. -/
noncomputable section
open scoped ComplexOrder InnerProductSpace Topology BigOperators
open Filter MeasureTheory Cloning.InfiniteTraceClass Cloning.InfiniteFidelity
open Cloning.Hybrid
namespace Cloning.MultimodeCoherent
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {d : ℕ}
namespace PhaseSpaceDensity
variable (p : PhaseSpaceDensity d)

/-- The covariance estimate is uniform over the competitor. Consequently even
an adversarially changing competitor sequence has vanishing covariance defect. -/
theorem foelnerChannel_sequence_covariance_tendsto (gain : ℝ)
    (Φ : ℕ → QuantumChannel (Fock d) (Fock d))
    (scale : ℕ → ℕ) (hscale : Tendsto scale atTop atTop) (b : Fin d → ℂ)
    (A : TraceClass (Fock d)) :
    Tendsto (fun n => ‖(p.foelnerChannel gain (Φ n) (scale n)).toLinearMap
      (displacementTraceMap b A) - displacementTraceMap (gain • b)
        ((p.foelnerChannel gain (Φ n) (scale n)).toLinearMap A)‖) atTop (𝓝 0) := by
  let D (n : ℕ) := (((p.foelnerChannel gain (Φ n) (scale n)).toPositiveTracePreservingMap.toContinuousLinearMap).comp
    (displacementTraceMap b) - (displacementTraceMap (gain • b)).comp
      (p.foelnerChannel gain (Φ n) (scale n)).toPositiveTracePreservingMap.toContinuousLinearMap)
  have hpos (B : TraceClass (Fock d)) (hB : 0 ≤ B.1) :
      Tendsto (fun n => D n B) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero (fun n => norm_nonneg _) _
      (by simpa only [mul_zero] using ((p.translation_error_tendsto b).comp hscale).const_mul ‖B‖)
    intro n
    exact p.foelnerChannel_covariance_bound gain (Φ n) b B hB (scale n)
  have hself (B : TraceClass (Fock d)) (hB : IsSelfAdjoint B.1) :
      Tendsto (fun n => D n B) atTop (𝓝 0) := by
    have h := (hpos _ (TraceClass.positivePart_nonneg B hB)).sub
      (hpos _ (TraceClass.negativePart_nonneg B hB))
    simpa only [← map_sub, TraceClass.positivePart_sub_negativePart B hB, sub_zero] using h
  have h := (hself _ (TraceClass.realComponent_isSelfAdjoint A)).add
    ((hself _ (TraceClass.imaginaryComponent_isSelfAdjoint A)).const_smul Complex.I)
  have h' : Tendsto (fun n => D n A) atTop (𝓝 0) := by
    simpa only [← map_smul, ← map_add, TraceClass.realComponent_add_I_smul_imaginaryComponent A,
      smul_zero, add_zero] using h
  exact tendsto_zero_iff_norm_tendsto_zero.mp h'

/-- One common covariant CP, trace-nonincreasing limit exists even when the
competitor changes with the scale of the arbitrary expanding prior. This is the uniform
compactness needed when taking a supremum over channels before the prior limit. -/
theorem exists_foelner_sequence_covariant_limit (gain : ℝ)
    (Φ : ℕ → QuantumChannel (Fock d) (Fock d))
    (scale : ℕ → ℕ) (hscale : Tendsto scale atTop atTop) :
    ∃ Ψ : TraceClass (Fock d) →ₗ[ℂ] TraceClass (Fock d),
      IsCompletelyPositive Ψ ∧
      (∀ A, 0 ≤ A.1 → (traceCLM (Ψ A)).re ≤ (traceCLM A).re) ∧
      (∀ (b : Fin d → ℂ) A,
        Ψ (displacementTraceMap b A) = displacementTraceMap (gain • b) (Ψ A)) ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        (∀ A x y, Tendsto (fun n =>
          ⟪x, ((p.foelnerChannel gain (Φ (φ n)) (scale (φ n))).toLinearMap A).1 y⟫_ℂ) atTop
            (𝓝 ⟪x, (Ψ A).1 y⟫_ℂ)) ∧
        (∀ A (O : (Fock d) →L[ℂ] (Fock d)), IsCompactOperator O →
          Tendsto (fun n => tracePairing
            ((p.foelnerChannel gain (Φ (φ n)) (scale (φ n))).toLinearMap A) O) atTop
              (𝓝 (tracePairing (Ψ A) O))) := by
  let L := fun n => (p.foelnerChannel gain (Φ n) (scale n)).toLinearMap
  have ht (n : ℕ) (A : TraceClass (Fock d)) (_hA : 0 ≤ A.1) :
      (traceCLM (L n A)).re ≤ 1 * (traceCLM A).re := by
    simpa only [one_mul] using
      le_of_eq (congrArg Complex.re ((p.foelnerChannel gain (Φ n) (scale n)).trace_preserving A))
  have hd (b : Fin d → ℂ) (A : TraceClass (Fock d)) :
      Tendsto (fun n =>
        ‖L n (sandwichCLM (displacement b) (star (displacement b)) A) -
          sandwichCLM (displacement (gain • b)) (star (displacement (gain • b)))
            (L n A)‖) atTop (𝓝 0) := by
    simpa only [ContinuousLinearMap.star_eq_adjoint, displacement_adjoint,
      displacementTraceMap] using foelnerChannel_sequence_covariance_tendsto p gain Φ scale hscale b A
  simpa only [one_mul, ContinuousLinearMap.star_eq_adjoint, displacement_adjoint,
    displacementTraceMap] using exists_subsequence_covariant_completelyPositive_limit L 1
      zero_le_one (fun n => (p.foelnerChannel gain (Φ n) (scale n)).completelyPositive) ht
      displacement (fun b => displacement (gain • b)) hd

/-- The prior-averaged payoff is asymptotically bounded by the compact witness
moment of the actual limit. This transfers performance through loss of trace
without assuming weak continuity of fidelity. -/
theorem orbitPayoff_eventually_sq_le_compact_limit
    (gain : ℝ) (Φ : ℕ → QuantumChannel (Fock d) (Fock d))
    (scale : ℕ → ℕ) (A B : PositiveTraceClass (Fock d)) (W : (Fock d) →L[ℂ] (Fock d))
    (hW : 0 ≤ W) {M : ℝ} (hM : 0 ≤ M)
    (hInv : ∀ ε : ℝ, 0 < ε →
      (tracePairing B.1 (CFC.rpow (regularizedWeight W ε) (-1))).re ≤ M)
    (Ψ : TraceClass (Fock d) →ₗ[ℂ] TraceClass (Fock d)) (φ : ℕ → ℕ)
    (hlim : Tendsto (fun n => tracePairing
      ((p.foelnerChannel gain (Φ (φ n)) (scale (φ n))).toLinearMap A.1) W)
        atTop (𝓝 (tracePairing (Ψ A.1) W))) :
    ∀ ε > 0, ∀ᶠ n in atTop,
      (∫ a, orbitPayoff gain (Φ (φ n)) A B a ∂p.expandingPrior (scale (φ n))) ^ 2 ≤
        (tracePairing (Ψ A.1) W).re * M + ε := by
  intro ε hε
  have h := ((Complex.continuous_re.tendsto _).comp hlim).mul_const M
  filter_upwards [h.eventually (gt_mem_nhds (lt_add_of_pos_right _ hε))] with n hn
  exact (integral_orbitPayoff_sq_le_weight (p.expandingPrior (scale (φ n))) gain
    (Φ (φ n)) A B W hW hM hInv).trans hn.le

/-- The flat-prior performance reduction, with the supremum over competitors
inside the prior limit. A bound only on covariant CP trace-nonincreasing limit
maps implies an eventual bound simultaneously for every original CPTP
competitor. The covariance and compact-limit passages are proved here. -/
theorem eventually_forall_orbitPayoff_sq_le_of_covariant_moment
    (gain : ℝ) (A B : PositiveTraceClass (Fock d))
    (W : (Fock d) →L[ℂ] (Fock d)) (hW : 0 ≤ W) (hcompact : IsCompactOperator W)
    {M C : ℝ} (hM : 0 ≤ M)
    (hInv : ∀ ε : ℝ, 0 < ε →
      (tracePairing B.1 (CFC.rpow (regularizedWeight W ε) (-1))).re ≤ M)
    (hmoment : ∀ Ψ : TraceClass (Fock d) →ₗ[ℂ] TraceClass (Fock d),
      IsCompletelyPositive Ψ →
      (∀ X, 0 ≤ X.1 → (traceCLM (Ψ X)).re ≤ (traceCLM X).re) →
      (∀ (b : Fin d → ℂ) X,
        Ψ (displacementTraceMap b X) = displacementTraceMap (gain • b) (Ψ X)) →
      (tracePairing (Ψ A.1) W).re ≤ C) :
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ Φ : QuantumChannel (Fock d) (Fock d),
      (∫ a, orbitPayoff gain Φ A B a ∂p.expandingPrior n) ^ 2 ≤ C * M + ε := by
  classical
  intro ε hε
  by_contra h
  have hf : ∃ᶠ n in atTop, ∃ Φ : QuantumChannel (Fock d) (Fock d),
      C * M + ε < (∫ a, orbitPayoff gain Φ A B a ∂p.expandingPrior n) ^ 2 := by
    simpa only [Filter.Frequently, not_exists, not_lt, not_forall, not_le] using h
  obtain ⟨scale, hscale, hbad⟩ := exists_seq_forall_of_frequently hf
  choose Φ hΦ using hbad
  obtain ⟨Ψ, hp, ht, hc, φ, hφ, _, hlim⟩ :=
    p.exists_foelner_sequence_covariant_limit gain Φ scale hscale
  have hm := mul_le_mul_of_nonneg_right (hmoment Ψ hp ht hc) hM
  have he := p.orbitPayoff_eventually_sq_le_compact_limit gain Φ scale A B W hW hM hInv
    Ψ φ (hlim A.1 W hcompact) (ε / 2) (by positivity)
  obtain ⟨n, hn⟩ := he.exists
  have hb := hΦ (φ n)
  linarith

end PhaseSpaceDensity
end Cloning.MultimodeCoherent
