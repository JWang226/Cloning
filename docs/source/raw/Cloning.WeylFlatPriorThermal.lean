import Cloning.WeylFlatPriorLimit
import Cloning.WeylFlatBox
import Cloning.MultimodeCoherentGaussianMixture

/-! The orbital flat-box payoff is controlled by a genuine compact thermal
witness of one actual covariant CP trace-nonincreasing limit. All box, averaging,
and witness hypotheses are proved. The universal least-noise moment remains a
separate representation-theoretic obligation. -/
noncomputable section
open scoped ComplexOrder InnerProductSpace Topology BigOperators
open Filter MeasureTheory Cloning.InfiniteTraceClass Cloning.InfiniteFidelity
open Cloning.Hybrid Cloning.ThermalWitness Cloning.MultimodeCoherentGaussianMixture
namespace Cloning.MultimodeCoherent
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {d : ℕ}

/-- The ordinary flat-box average of the physical orbit root fidelity, with
coordinates scaled from the unit box to the box of radius `n+1`. -/
def flatBoxPayoff (gain : ℝ) (Φ : QuantumChannel (Fock d) (Fock d))
    (A B : PositiveTraceClass (Fock d)) (n : ℕ) : ℝ :=
  (volume.real (phaseSpaceUnitBox d))⁻¹ * ∫ z in phaseSpaceUnitBox d,
    orbitPayoff gain Φ A B (((n : ℝ) + 1) • z)

lemma flatBoxPayoff_eq_integral (gain : ℝ) (Φ : QuantumChannel (Fock d) (Fock d))
    (A B : PositiveTraceClass (Fock d)) (n : ℕ) :
    flatBoxPayoff gain Φ A B n =
      ∫ a, orbitPayoff gain Φ A B a ∂(flatBoxDensity d).expandingPrior n := by
  symm
  exact integral_flatBox_expandingPrior d n _ (continuous_orbitPayoff gain Φ A B)

/-- Identification with the manuscript's literal normalized expanding-box
Lebesgue integral, with no change in the fidelity convention. -/
lemma flatBoxPayoff_eq_normalized_box (gain : ℝ) (Φ : QuantumChannel (Fock d) (Fock d))
    (A B : PositiveTraceClass (Fock d)) (n : ℕ) :
    flatBoxPayoff gain Φ A B n =
      (volume.real (phaseSpaceBox d ((n : ℝ) + 1)))⁻¹ *
        ∫ a in phaseSpaceBox d ((n : ℝ) + 1), orbitPayoff gain Φ A B a := by
  exact normalized_unitBox_smul_eq (by positivity : 0 < (n : ℝ) + 1)
    (orbitPayoff gain Φ A B)

lemma flatBoxPayoff_nonneg (gain : ℝ) (Φ : QuantumChannel (Fock d) (Fock d))
    (A B : PositiveTraceClass (Fock d)) (n : ℕ) : 0 ≤ flatBoxPayoff gain Φ A B n := by
  rw [flatBoxPayoff_eq_integral]
  exact integral_nonneg (fun _ => PositiveTraceClass.rootFidelity_nonneg _ _)

lemma flatBoxPayoff_le_sqrt (gain : ℝ) (Φ : QuantumChannel (Fock d) (Fock d))
    (A B : PositiveTraceClass (Fock d)) (n : ℕ) :
    flatBoxPayoff gain Φ A B n ≤ Real.sqrt ‖A.1‖ * Real.sqrt ‖B.1‖ := by
  rw [flatBoxPayoff_eq_integral]
  apply (integral_orbitPayoff_le_average ((flatBoxDensity d).expandingPrior n)
    gain Φ A B).trans
  have h := PositiveTraceClass.rootFidelity_le_sqrt
    (PositiveTraceClass.map (covariantAverage ((flatBoxDensity d).expandingPrior n)
      gain Φ).toPositiveTracePreservingMap A) B
  simpa only [PositiveTraceClass.norm_map] using h

/-- The optimal flat-box root-fidelity payoff, taking the supremum over actual
CPTP channels independently at every box radius. -/
def flatBoxOptimalPayoff (gain : ℝ) (A B : PositiveTraceClass (Fock d)) (n : ℕ) : ℝ :=
  sSup (Set.range (fun Φ : QuantumChannel (Fock d) (Fock d) => flatBoxPayoff gain Φ A B n))

lemma flatBoxOptimalPayoff_nonneg (gain : ℝ) (A B : PositiveTraceClass (Fock d)) (n : ℕ) :
    0 ≤ flatBoxOptimalPayoff gain A B n := by
  have hb : BddAbove (Set.range (fun Φ : QuantumChannel (Fock d) (Fock d) =>
      flatBoxPayoff gain Φ A B n)) := by
    refine ⟨Real.sqrt ‖A.1‖ * Real.sqrt ‖B.1‖, ?_⟩
    rintro _ ⟨Φ, rfl⟩
    exact flatBoxPayoff_le_sqrt gain Φ A B n
  exact (flatBoxPayoff_nonneg gain (displacementChannel 0) A B n).trans
    (le_csSup hb (Set.mem_range_self (displacementChannel 0)))

/-- Uniform eventual bounds imply the manuscript's `limsup sup_channel`
statement, with the supremum taken before the growing-window limit. -/
lemma limsup_flatBoxOptimalPayoff_le (gain : ℝ) (A B : PositiveTraceClass (Fock d))
    {C : ℝ} (h : ∀ ε > 0, ∀ᶠ n in atTop, ∀ Φ : QuantumChannel (Fock d) (Fock d),
      flatBoxPayoff gain Φ A B n ≤ C + ε) :
    Filter.limsup (flatBoxOptimalPayoff gain A B) atTop ≤ C := by
  apply le_of_forall_pos_le_add
  intro ε hε
  apply limsup_le_of_le (isCoboundedUnder_le_of_le atTop (flatBoxOptimalPayoff_nonneg gain A B))
  filter_upwards [h ε hε] with n hn
  apply csSup_le (show (Set.range (fun Φ : QuantumChannel (Fock d) (Fock d) =>
    flatBoxPayoff gain Φ A B n)).Nonempty from ⟨_, Set.mem_range_self (displacementChannel 0)⟩)
  rintro _ ⟨Φ, rfl⟩
  exact hn Φ

/-- An arbitrary thermal product density as an actual positive trace-class
operator on the physical multimode Fock space. -/
def thermalPositive (q : Fin d → ℝ) (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i < 1) :
    PositiveTraceClass (Fock d) :=
  ⟨vectorMixture (numberBasis d) (productGeometric q),
    vectorMixture_nonneg (numberBasis d) (numberBasis d).orthonormal.norm_eq_one _
      (productGeometric_hasSum hq0 hq1).summable (productGeometric_nonneg hq0 hq1)⟩

/-- The actual flat-prior compact-limit reduction. It applies to a different
competitor at every scale, as required by a channel supremum inside the prior
limit. The thermal inverse moment and compactness are conclusions of the
concrete product witness theorems, rather than extra hypotheses. -/
theorem exists_flatBox_thermal_payoff_limit (gain : ℝ)
    (Φ : ℕ → QuantumChannel (Fock d) (Fock d))
    (A : PositiveTraceClass (Fock d)) {q x : Fin d → ℝ}
    (hq0 : ∀ i, 0 < q i) (hqx : ∀ i, q i < x i) (hx1 : ∀ i, x i < 1) :
    ∃ Ψ : TraceClass (Fock d) →ₗ[ℂ] TraceClass (Fock d),
      IsCompletelyPositive Ψ ∧
      (∀ C, 0 ≤ C.1 → (traceCLM (Ψ C)).re ≤ (traceCLM C).re) ∧
      (∀ (b : Fin d → ℂ) C,
        Ψ (displacementTraceMap b C) = displacementTraceMap (gain • b) (Ψ C)) ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        (∀ C (O : (Fock d) →L[ℂ] (Fock d)), IsCompactOperator O →
          Tendsto (fun n => tracePairing
            (((flatBoxDensity d).foelnerChannel gain (Φ (φ n)) (φ n)).toLinearMap C) O)
              atTop (𝓝 (tracePairing (Ψ C) O))) ∧
        (∀ ε > 0, ∀ᶠ n in atTop,
          flatBoxPayoff gain (Φ (φ n)) A
            (thermalPositive q (fun i => (hq0 i).le) (fun i => (hqx i).trans (hx1 i))) (φ n) ^ 2 ≤
          (tracePairing (Ψ A.1) (productWitnessOperator (numberBasis d) q x)).re *
            (∏ i, Cloning.Thermal.fidelity (q i) (x i)) + ε) := by
  obtain ⟨Ψ, hp, ht, hc, φ, hφ, _, hcompact⟩ :=
    (flatBoxDensity d).exists_foelner_sequence_covariant_limit gain Φ id tendsto_id
  refine ⟨Ψ, hp, ht, hc, φ, hφ, hcompact, ?_⟩
  have hM : 0 ≤ ∏ i, Cloning.Thermal.fidelity (q i) (x i) := Finset.prod_nonneg (fun i _ =>
    (Cloning.Thermal.fidelity_pos (hq0 i).le ((hqx i).trans (hx1 i))
      ((hq0 i).trans (hqx i)).le (hx1 i)).le)
  have h := (flatBoxDensity d).orbitPayoff_eventually_sq_le_compact_limit gain Φ id A
    (thermalPositive q (fun i => (hq0 i).le) (fun i => (hqx i).trans (hx1 i)))
    (productWitnessOperator (numberBasis d) q x)
    (productWitnessOperator_nonneg _ hq0 hqx hx1) hM
    (fun ε hε => product_thermal_regularized_inverse_moment _ hq0 hqx hx1 hε)
    Ψ φ (hcompact A.1 _ (productWitnessOperator_compact _ hq0 hqx hx1))
  simpa only [flatBoxPayoff_eq_integral] using h

/-- Once the universal covariant oscillator moment is supplied, the literal
flat-box quantum converse follows uniformly over all original channels, in
the correct order of quantifiers. No averaging, prior, inverse-moment, or
compact-limit assumption is left in this implication. -/
theorem flatBox_thermal_eventually_le_of_covariant_moment (gain : ℝ)
    (A : PositiveTraceClass (Fock d)) {q x : Fin d → ℝ}
    (hq0 : ∀ i, 0 < q i) (hqx : ∀ i, q i < x i) (hx1 : ∀ i, x i < 1)
    (hmoment : ∀ Ψ : TraceClass (Fock d) →ₗ[ℂ] TraceClass (Fock d),
      IsCompletelyPositive Ψ →
      (∀ X, 0 ≤ X.1 → (traceCLM (Ψ X)).re ≤ (traceCLM X).re) →
      (∀ (b : Fin d → ℂ) X,
        Ψ (displacementTraceMap b X) = displacementTraceMap (gain • b) (Ψ X)) →
      (tracePairing (Ψ A.1) (productWitnessOperator (numberBasis d) q x)).re ≤
        ∏ i, Cloning.Thermal.fidelity (q i) (x i)) :
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ Φ : QuantumChannel (Fock d) (Fock d),
      flatBoxPayoff gain Φ A
        (thermalPositive q (fun i => (hq0 i).le) (fun i => (hqx i).trans (hx1 i))) n ≤
        (∏ i, Cloning.Thermal.fidelity (q i) (x i)) + ε := by
  have hM : 0 ≤ ∏ i, Cloning.Thermal.fidelity (q i) (x i) := Finset.prod_nonneg (fun i _ =>
    (Cloning.Thermal.fidelity_pos (hq0 i).le ((hqx i).trans (hx1 i))
      ((hq0 i).trans (hqx i)).le (hx1 i)).le)
  have h := (flatBoxDensity d).eventually_forall_orbitPayoff_sq_le_of_covariant_moment gain A
    (thermalPositive q (fun i => (hq0 i).le) (fun i => (hqx i).trans (hx1 i)))
    (productWitnessOperator (numberBasis d) q x)
    (productWitnessOperator_nonneg _ hq0 hqx hx1)
    (productWitnessOperator_compact _ hq0 hqx hx1) hM
    (fun ε hε => product_thermal_regularized_inverse_moment _ hq0 hqx hx1 hε) hmoment
  intro ε hε
  filter_upwards [h (ε ^ 2) (sq_pos_of_pos hε)] with n hn Φ
  rw [flatBoxPayoff_eq_integral]
  have hb := hn Φ
  by_contra hg
  push_neg at hg
  have hstrict := mul_self_lt_mul_self (add_nonneg hM hε.le) hg
  nlinarith [mul_nonneg hM hε.le]

/-- Direct `limsup sup_channel` form of the orbital thermal converse reduction.
Only the universal covariant oscillator moment is still a hypothesis. -/
theorem limsup_flatBox_thermal_le_of_covariant_moment (gain : ℝ)
    (A : PositiveTraceClass (Fock d)) {q x : Fin d → ℝ}
    (hq0 : ∀ i, 0 < q i) (hqx : ∀ i, q i < x i) (hx1 : ∀ i, x i < 1)
    (hmoment : ∀ Ψ : TraceClass (Fock d) →ₗ[ℂ] TraceClass (Fock d),
      IsCompletelyPositive Ψ →
      (∀ X, 0 ≤ X.1 → (traceCLM (Ψ X)).re ≤ (traceCLM X).re) →
      (∀ (b : Fin d → ℂ) X,
        Ψ (displacementTraceMap b X) = displacementTraceMap (gain • b) (Ψ X)) →
      (tracePairing (Ψ A.1) (productWitnessOperator (numberBasis d) q x)).re ≤
        ∏ i, Cloning.Thermal.fidelity (q i) (x i)) :
    Filter.limsup (flatBoxOptimalPayoff gain A
      (thermalPositive q (fun i => (hq0 i).le) (fun i => (hqx i).trans (hx1 i)))) atTop ≤
      ∏ i, Cloning.Thermal.fidelity (q i) (x i) :=
  limsup_flatBoxOptimalPayoff_le gain A _
    (flatBox_thermal_eventually_le_of_covariant_moment gain A hq0 hqx hx1 hmoment)

end Cloning.MultimodeCoherent
