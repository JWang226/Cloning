import Cloning.ThermalIdlerFidelity
import Cloning.MultimodeIdler

/-! The concrete multimode least-noise witness and fidelity bounds for the
actual seeded bosonic channel. Arbitrary entanglement and coherence in the
joint idler are allowed; the number-law formula is proved by the channel
construction and is not an assumption of these theorems. -/

namespace Cloning.MultimodeThermalIdlerFidelity

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped ComplexOrder InnerProductSpace Topology BigOperators
open Cloning Cloning.InfiniteTraceClass Cloning.InfiniteFidelity
open MultimodeIdler ThermalWitness

lemma idler_witness_moment_le {s : ℕ} (σ : TraceClass (Fock s)) (hσ : 0 ≤ σ.1)
    {q x : Fin s → ℝ} (hq0 : ∀ i, 0 < q i) (hqx : ∀ i, q i < x i)
    (hx1 : ∀ i, x i < 1) :
    (tracePairing ((channel x (fun i => ((hq0 i).trans (hqx i)).le) hx1).toLinearMap σ)
      (productWitnessOperator (numberBasis s) q x)).re ≤
      (trace σ.1 σ.2).re * ∏ i, Thermal.fidelity (q i) (x i) := by
  apply number_law_witness_moment_le (numberBasis s) _ hq0 hqx hx1
    (a := fun l => (⟪numberBasis s l, σ.1 (numberBasis s l)⟫_ℂ).re)
  · intro l
    exact (σ.1.nonneg_iff_isPositive.mp hσ).re_inner_nonneg_right (numberBasis s l)
  · exact trace_real_hasSum_basis (numberBasis s) σ
  · intro k
    exact channel_diagonal_re x (fun i => ((hq0 i).trans (hqx i)).le) hx1 σ k

lemma idler_fidelity_sq_le {s : ℕ} (σ : TraceClass (Fock s)) (hσ : 0 ≤ σ.1)
    {q x : Fin s → ℝ} (hq0 : ∀ i, 0 < q i) (hqx : ∀ i, q i < x i)
    (hx1 : ∀ i, x i < 1) :
    fidelity ((channel x (fun i => ((hq0 i).trans (hqx i)).le) hx1).toLinearMap σ).1
      (vectorMixture (numberBasis s) (productGeometric q)).1
      ((channel x (fun i => ((hq0 i).trans (hqx i)).le) hx1).map_nonneg σ hσ)
      (vectorMixture_nonneg (numberBasis s) (numberBasis s).orthonormal.norm_eq_one _
        (productGeometric_hasSum (fun i => (hq0 i).le) (fun i => (hqx i).trans (hx1 i))).summable
        (productGeometric_nonneg (fun i => (hq0 i).le) (fun i => (hqx i).trans (hx1 i))))
      ((channel x (fun i => ((hq0 i).trans (hqx i)).le) hx1).toLinearMap σ).2
      (vectorMixture (numberBasis s) (productGeometric q)).2 ^ 2 ≤
      (trace σ.1 σ.2).re * (∏ i, Thermal.fidelity (q i) (x i)) ^ 2 := by
  apply fidelity_sq_le_of_number_law (numberBasis s) _ _ hq0 hqx hx1
    (a := fun l => (⟪numberBasis s l, σ.1 (numberBasis s l)⟫_ℂ).re)
  · intro l
    exact (σ.1.nonneg_iff_isPositive.mp hσ).re_inner_nonneg_right (numberBasis s l)
  · exact trace_real_hasSum_basis (numberBasis s) σ
  · intro k
    exact channel_diagonal_re x (fun i => ((hq0 i).trans (hqx i)).le) hx1 σ k

/-- The product thermal fidelity upper bound for a genuinely arbitrary joint
idler density operator; no product, phase-invariance, or diagonality hypothesis. -/
lemma idler_stateFidelity_le {s : ℕ} (σ : DensityState (Fock s))
    {q x : Fin s → ℝ} (hq0 : ∀ i, 0 < q i) (hqx : ∀ i, q i < x i)
    (hx1 : ∀ i, x i < 1) :
    stateFidelity
      ((channel x (fun i => ((hq0 i).trans (hqx i)).le) hx1).toPositiveTracePreservingMap.mapState σ)
      (InfiniteDiagonalFidelity.productGeometricState (numberBasis s) q
        (fun i => (hq0 i).le) (fun i => (hqx i).trans (hx1 i))) ≤
      ∏ i, Thermal.fidelity (q i) (x i) := by
  have h := idler_fidelity_sq_le (TraceClass.ofOperator σ.op σ.traceClass) σ.positive hq0 hqx hx1
  change stateFidelity
      ((channel x (fun i => ((hq0 i).trans (hqx i)).le) hx1).toPositiveTracePreservingMap.mapState σ)
      (InfiniteDiagonalFidelity.productGeometricState (numberBasis s) q
        (fun i => (hq0 i).le) (fun i => (hqx i).trans (hx1 i))) ^ 2 ≤
    (trace σ.op σ.traceClass).re * (∏ i, Thermal.fidelity (q i) (x i)) ^ 2 at h
  rw [σ.trace_one, Complex.one_re, one_mul] at h
  exact (sq_le_sq₀ (stateFidelity_nonneg _ _)
    (Finset.prod_nonneg (fun i _ => (Thermal.fidelity_pos (hq0 i).le
      ((hqx i).trans (hx1 i)) ((hq0 i).trans (hqx i)).le (hx1 i)).le))).mp h

lemma kraus_vacuum {s : ℕ} (x : Fin s → ℝ)
    (hx0 : ∀ i, 0 ≤ x i) (hx1 : ∀ i, x i < 1) (m : Occupation s) :
    kraus x hx0 hx1 m (numberBasis s 0) =
      (Real.sqrt (productGeometric x m) : ℂ) • numberBasis s m := by
  ext k
  rw [kraus_numberBasis_apply]
  simp only [numberBasis_eq_single, lp.coeFn_smul, Pi.smul_apply,
    lp.single_apply, Pi.single_apply, zero_add, smul_eq_mul]
  by_cases h : k = m
  · subst k
    simp [BosonicNumberLaw.productLaw, BosonicNumberLaw.seededLaw_zero, productGeometric]
  · simp [h, Ne.symm h]

/-- The joint vacuum is sent to the actual product thermal density operator. -/
lemma channel_vacuum {s : ℕ} (x : Fin s → ℝ)
    (hx0 : ∀ i, 0 ≤ x i) (hx1 : ∀ i, x i < 1) :
    (channel x hx0 hx1).toLinearMap (vectorProjector (numberBasis s 0)) =
      vectorMixture (numberBasis s) (productGeometric x) := by
  have hs := channel_hasSum x hx0 hx1 (vectorProjector (numberBasis s 0))
  have he (m : Occupation s) : krausTerm (kraus x hx0 hx1 m) (vectorProjector (numberBasis s 0)) =
      (productGeometric x m : ℂ) • vectorProjector (numberBasis s m) := by
    rw [krausTerm_vectorProjector, kraus_vacuum, BosonicAmplifier.vectorProjector_sqrt_smul]
    exact productGeometric_nonneg hx0 hx1 m
  simp_rw [he] at hs
  exact hs.tsum_eq.symm

lemma vacuum_stateFidelity {s : ℕ} (x q : Fin s → ℝ)
    (hx0 : ∀ i, 0 ≤ x i) (hx1 : ∀ i, x i < 1)
    (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i < 1) :
    stateFidelity
      ((channel x hx0 hx1).toPositiveTracePreservingMap.mapState
        (DensityState.pure (numberBasis s 0) ((numberBasis s).orthonormal.norm_eq_one 0)))
      (InfiniteDiagonalFidelity.productGeometricState (numberBasis s) q hq0 hq1) =
      ∏ i, Thermal.fidelity (x i) (q i) := by
  have he :
      (channel x hx0 hx1).toPositiveTracePreservingMap.mapState
        (DensityState.pure (numberBasis s 0) ((numberBasis s).orthonormal.norm_eq_one 0)) =
      InfiniteDiagonalFidelity.productGeometricState (numberBasis s) x hx0 hx1 := by
    apply ThermalIdlerFidelity.densityState_ext
    exact congrArg Subtype.val (channel_vacuum x hx0 hx1)
  rw [he]
  exact InfiniteDiagonalFidelity.stateFidelity_productGeometric (numberBasis s) x q hx0 hx1 hq0 hq1

/-- Exact optimum over arbitrary correlated/coherent joint idler states for
the concrete seeded multimode channel family. -/
lemma isGreatest_idler_stateFidelity {s : ℕ} {q x : Fin s → ℝ}
    (hq0 : ∀ i, 0 < q i) (hqx : ∀ i, q i < x i) (hx1 : ∀ i, x i < 1) :
    IsGreatest (Set.range (fun σ : DensityState (Fock s) =>
      stateFidelity
        ((channel x (fun i => ((hq0 i).trans (hqx i)).le) hx1).toPositiveTracePreservingMap.mapState σ)
        (InfiniteDiagonalFidelity.productGeometricState (numberBasis s) q
          (fun i => (hq0 i).le) (fun i => (hqx i).trans (hx1 i)))))
      (∏ i, Thermal.fidelity (q i) (x i)) := by
  constructor
  · refine ⟨DensityState.pure (numberBasis s 0) ((numberBasis s).orthonormal.norm_eq_one 0), ?_⟩
    dsimp only
    rw [vacuum_stateFidelity]
    simp only [Thermal.fidelity, mul_comm]
  · rintro _ ⟨σ, rfl⟩
    exact idler_stateFidelity_le σ hq0 hqx hx1

end
end Cloning.MultimodeThermalIdlerFidelity
