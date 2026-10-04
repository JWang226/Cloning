import Cloning.ThermalWitness
import Cloning.BosonicIdlerChannel

/-! The least-noise thermal witness inequality for the actual arbitrary-idler
bosonic channel. Its number law is derived from the channel's Kraus series, so
no moment, diagonality, or coefficient-law premise appears below. -/

namespace Cloning.ThermalIdlerFidelity

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped ComplexOrder InnerProductSpace Topology BigOperators
open Cloning Cloning.InfiniteTraceClass Cloning.InfiniteFidelity
open BosonicAmplifier ThermalWitness

lemma densityState_ext {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] {ρ σ : DensityState H} (h : ρ.op = σ.op) : ρ = σ := by
  cases ρ
  cases σ
  cases h
  rfl

/-- Arbitrary positive trace-class idlers obey the exact least-noise moment
bound, including idlers of deficient trace and idlers with coherences. -/
lemma idler_witness_moment_le (σ : TraceClass Fock) (hσ : 0 ≤ σ.1)
    {q x : ℝ} (hq0 : 0 < q) (hqx : q < x) (hx1 : x < 1) :
    (tracePairing ((idlerChannel x (hq0.trans hqx).le hx1).toLinearMap σ)
      (witnessOperator numberBasis q x)).re ≤
      (trace σ.1 σ.2).re * Thermal.fidelity q x := by
  apply single_number_law_witness_moment_le numberBasis _ hq0 hqx hx1
    (a := fun l => (⟪numberBasis l, σ.1 (numberBasis l)⟫_ℂ).re)
  · intro l
    exact (σ.1.nonneg_iff_isPositive.mp hσ).re_inner_nonneg_right (numberBasis l)
  · exact trace_real_hasSum_basis numberBasis σ
  · intro k
    exact idlerChannel_diagonal_re x (hq0.trans hqx).le hx1 σ k

/-- Fidelity upper bound for the actual seeded bosonic output. -/
lemma idler_fidelity_sq_le (σ : TraceClass Fock) (hσ : 0 ≤ σ.1)
    {q x : ℝ} (hq0 : 0 < q) (hqx : q < x) (hx1 : x < 1) :
    fidelity ((idlerChannel x (hq0.trans hqx).le hx1).toLinearMap σ).1
      (vectorMixture numberBasis (Thermal.geometric q)).1
      ((idlerChannel x (hq0.trans hqx).le hx1).map_nonneg σ hσ)
      (vectorMixture_nonneg numberBasis numberBasis.orthonormal.norm_eq_one _
        (Thermal.geometric_hasSum hq0.le (hqx.trans hx1)).summable
        (Thermal.geometric_nonneg hq0.le (hqx.trans hx1).le))
      ((idlerChannel x (hq0.trans hqx).le hx1).toLinearMap σ).2
      (vectorMixture numberBasis (Thermal.geometric q)).2 ^ 2 ≤
      (trace σ.1 σ.2).re * Thermal.fidelity q x ^ 2 := by
  apply fidelity_sq_le_of_single_number_law numberBasis _ _ hq0 hqx hx1
    (a := fun l => (⟪numberBasis l, σ.1 (numberBasis l)⟫_ℂ).re)
  · intro l
    exact (σ.1.nonneg_iff_isPositive.mp hσ).re_inner_nonneg_right (numberBasis l)
  · exact trace_real_hasSum_basis numberBasis σ
  · intro k
    exact idlerChannel_diagonal_re x (hq0.trans hqx).le hx1 σ k

/-- Every genuine idler density operator, with arbitrary coherences, has
fidelity at most the quantum-limited thermal affinity. -/
lemma idler_stateFidelity_le (σ : DensityState Fock)
    {q x : ℝ} (hq0 : 0 < q) (hqx : q < x) (hx1 : x < 1) :
    stateFidelity
      ((idlerChannel x (hq0.trans hqx).le hx1).toPositiveTracePreservingMap.mapState σ)
      (InfiniteDiagonalFidelity.geometricState numberBasis q hq0.le (hqx.trans hx1)) ≤
      Thermal.fidelity q x := by
  have h := idler_fidelity_sq_le (TraceClass.ofOperator σ.op σ.traceClass) σ.positive hq0 hqx hx1
  change stateFidelity
      ((idlerChannel x (hq0.trans hqx).le hx1).toPositiveTracePreservingMap.mapState σ)
      (InfiniteDiagonalFidelity.geometricState numberBasis q hq0.le (hqx.trans hx1)) ^ 2 ≤
    (trace σ.op σ.traceClass).re * Thermal.fidelity q x ^ 2 at h
  rw [σ.trace_one, Complex.one_re, one_mul] at h
  exact (sq_le_sq₀ (stateFidelity_nonneg _ _)
    (Thermal.fidelity_pos hq0.le (hqx.trans hx1) (hq0.trans hqx).le hx1).le).mp h

lemma idlerKraus_vacuum (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 1) (m : ℕ) :
    idlerKraus x hx0 hx1 m (numberBasis 0) =
      (Real.sqrt (Thermal.geometric x m) : ℂ) • numberBasis m := by
  ext k
  rw [idlerKraus_numberBasis_apply]
  simp only [numberBasis_eq_single, lp.coeFn_smul, Pi.smul_apply,
    lp.single_apply, Pi.single_apply, zero_add, smul_eq_mul]
  by_cases h : k = m
  · subst k
    simp [weight, Thermal.geometric]
  · simp [h, Ne.symm h]

/-- Vacuum idler attains the quantum-limited thermal output as an operator
identity in the actual trace-class Banach space. -/
lemma idlerChannel_vacuum (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 1) :
    (idlerChannel x hx0 hx1).toLinearMap (vectorProjector (numberBasis 0)) =
      vectorMixture numberBasis (Thermal.geometric x) := by
  have hs := idlerChannel_hasSum x hx0 hx1 (vectorProjector (numberBasis 0))
  have he (m : ℕ) : krausTerm (idlerKraus x hx0 hx1 m) (vectorProjector (numberBasis 0)) =
      (Thermal.geometric x m : ℂ) • vectorProjector (numberBasis m) := by
    rw [krausTerm_vectorProjector, idlerKraus_vacuum, vectorProjector_sqrt_smul]
    exact Thermal.geometric_nonneg hx0 hx1.le m
  simp_rw [he] at hs
  exact hs.tsum_eq.symm

/-- The universal seed-state upper bound is attained by the actual vacuum
idler, whose channel output is the amplified thermal state. -/
lemma idler_vacuum_stateFidelity (x q : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 1)
    (hq0 : 0 ≤ q) (hq1 : q < 1) :
    stateFidelity
      ((idlerChannel x hx0 hx1).toPositiveTracePreservingMap.mapState
        (DensityState.pure (numberBasis 0) (numberBasis.orthonormal.norm_eq_one 0)))
      (InfiniteDiagonalFidelity.geometricState numberBasis q hq0 hq1) =
      Thermal.fidelity x q := by
  have he :
      (idlerChannel x hx0 hx1).toPositiveTracePreservingMap.mapState
        (DensityState.pure (numberBasis 0) (numberBasis.orthonormal.norm_eq_one 0)) =
      InfiniteDiagonalFidelity.geometricState numberBasis x hx0 hx1 := by
    apply densityState_ext
    exact congrArg Subtype.val (idlerChannel_vacuum x hx0 hx1)
  rw [he]
  exact InfiniteDiagonalFidelity.stateFidelity_geometric numberBasis x q hx0 hx1 hq0 hq1

/-- Exact optimum over all actual idler density operators. This theorem is
about the explicitly constructed seeded channel family; it does not assume
or claim that every displacement-covariant channel has this representation. -/
lemma isGreatest_idler_stateFidelity {q x : ℝ}
    (hq0 : 0 < q) (hqx : q < x) (hx1 : x < 1) :
    IsGreatest (Set.range (fun σ : DensityState Fock =>
      stateFidelity
        ((idlerChannel x (hq0.trans hqx).le hx1).toPositiveTracePreservingMap.mapState σ)
        (InfiniteDiagonalFidelity.geometricState numberBasis q hq0.le (hqx.trans hx1))))
      (Thermal.fidelity q x) := by
  constructor
  · refine ⟨DensityState.pure (numberBasis 0) (numberBasis.orthonormal.norm_eq_one 0), ?_⟩
    dsimp only
    rw [idler_vacuum_stateFidelity]
    simp only [Thermal.fidelity, mul_comm]
  · rintro _ ⟨σ, rfl⟩
    exact idler_stateFidelity_le σ hq0 hqx hx1

end
end Cloning.ThermalIdlerFidelity
