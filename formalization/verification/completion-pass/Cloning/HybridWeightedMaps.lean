import Cloning.HybridThermalWitness

/-!
# Weighted quantum maps extracted from classical--quantum channels

The classical register is the actual operator-valued L1 Banach space. Preparing
a scalar density, applying any completely positive L1 map, and integrating a
bounded nonnegative weight produces a genuine completely positive quantum map.
-/

noncomputable section
open scoped ComplexOrder InnerProductSpace Topology BigOperators
open MeasureTheory Filter Cloning.InfiniteTraceClass
namespace Cloning.Hybrid
set_option backward.isDefEq.respectTransparency false

variable {Ω H K : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Positivity at every finite quantum ancilla, almost everywhere in the
classical register. This is independent of representatives of L1 classes. -/
def L1CompletelyPositive
    (Λ : Lp (TraceClass H) 1 μ →ₗ[ℂ] Lp (TraceClass K) 1 μ) : Prop :=
  ∀ n : ℕ, ∀ A : Fin n → Fin n → Lp (TraceClass H) 1 μ,
    (∀ᵐ y ∂μ, BlockPositive (fun i j => A i j y)) →
      ∀ᵐ y ∂μ, BlockPositive (fun i j => Λ (A i j) y)

def prepareL1 (g : Ω → ℝ) (hg : Integrable g μ) :
    TraceClass H →ₗ[ℂ] Lp (TraceClass H) 1 μ where
  toFun A := ((Complex.ofRealCLM.integrable_comp hg).smul_const A).toL1
    (fun y => (g y : ℂ) • A)
  map_add' A B := by
    rw [← Integrable.toL1_add]
    apply (Integrable.toL1_eq_toL1_iff _ _ _ _).mpr
    exact Eventually.of_forall fun y => smul_add (g y : ℂ) A B
  map_smul' c A := by
    change _ = c • _
    rw [← Integrable.toL1_smul]
    apply (Integrable.toL1_eq_toL1_iff _ _ _ _).mpr
    exact Eventually.of_forall fun y => smul_comm (g y : ℂ) c A

theorem prepareL1_ae (g : Ω → ℝ) (hg : Integrable g μ) (A : TraceClass H) :
    prepareL1 g hg A =ᵐ[μ] fun y => (g y : ℂ) • A :=
  Integrable.coeFn_toL1 ((Complex.ofRealCLM.integrable_comp hg).smul_const A)

theorem weightedL1_integrable (χ : Ω → ℝ) (hχ : AEStronglyMeasurable χ μ)
    {C : ℝ} (hbound : ∀ y, ‖χ y‖ ≤ C) (A : Lp (TraceClass K) 1 μ) :
    Integrable (fun y => (χ y : ℂ) • A y) μ := by
  apply (L1.integrable_coeFn A).bdd_smul C
    (Complex.continuous_ofReal.comp_aestronglyMeasurable hχ)
  exact Eventually.of_forall fun y => by simpa only [Complex.norm_real] using hbound y

def weightedL1Integral (χ : Ω → ℝ) (hχ : AEStronglyMeasurable χ μ)
    {C : ℝ} (hbound : ∀ y, ‖χ y‖ ≤ C) :
    Lp (TraceClass K) 1 μ →ₗ[ℂ] TraceClass K where
  toFun A := ∫ y, (χ y : ℂ) • A y ∂μ
  map_add' A B := by
    rw [← integral_add (weightedL1_integrable χ hχ hbound A)
      (weightedL1_integrable χ hχ hbound B)]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_add A B] with y hy
    simp only [hy, Pi.add_apply, smul_add]
  map_smul' c A := by
    rw [← integral_smul]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_smul c A] with y hy
    simp only [hy, Pi.smul_apply, RingHom.id_apply]
    exact smul_comm _ _ _

theorem norm_weightedL1Integral_le (χ : Ω → ℝ) (hχ : AEStronglyMeasurable χ μ)
    {C : ℝ} (hbound : ∀ y, ‖χ y‖ ≤ C) (A : Lp (TraceClass K) 1 μ) :
    ‖weightedL1Integral χ hχ hbound A‖ ≤ C * ‖A‖ := by
  calc
    _ ≤ ∫ y, ‖(χ y : ℂ) • A y‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ y, C * ‖A y‖ ∂μ := by
      apply integral_mono (weightedL1_integrable χ hχ hbound A).norm
        ((L1.integrable_coeFn A).norm.const_mul C)
      intro y
      dsimp only
      rw [norm_smul, Complex.norm_real]
      exact mul_le_mul_of_nonneg_right (hbound y) (norm_nonneg _)
    _ = _ := by rw [integral_const_mul, L1.norm_eq_integral_norm]

/-- The actual weighted quantum map, defined on all complex trace-class inputs. -/
def weightedQuantumMap
    (Λ : Lp (TraceClass H) 1 μ →ₗ[ℂ] Lp (TraceClass K) 1 μ)
    (g : Ω → ℝ) (hg : Integrable g μ)
    (χ : Ω → ℝ) (hχ : AEStronglyMeasurable χ μ)
    {C : ℝ} (hbound : ∀ y, ‖χ y‖ ≤ C) : TraceClass H →ₗ[ℂ] TraceClass K :=
  (weightedL1Integral χ hχ hbound).comp (Λ.comp (prepareL1 g hg))

theorem integral_complex_nonneg_ae {f : Ω → ℂ}
    (hf : Integrable f μ) (hpos : ∀ᵐ y ∂μ, 0 ≤ f y) : 0 ≤ ∫ y, f y ∂μ := by
  apply Complex.nonneg_iff.mpr
  constructor
  · change 0 ≤ Complex.reCLM (∫ y, f y ∂μ)
    rw [← Complex.reCLM.integral_comp_comm hf]
    exact integral_nonneg_of_ae (hpos.mono fun y hy => (Complex.nonneg_iff.mp hy).1)
  · change 0 = Complex.imCLM (∫ y, f y ∂μ)
    rw [← Complex.imCLM.integral_comp_comm hf]
    symm
    apply integral_eq_zero_of_ae
    exact hpos.mono fun y hy => (Complex.nonneg_iff.mp hy).2.symm

theorem weightedQuantumMap_completelyPositive
    (Λ : Lp (TraceClass H) 1 μ →ₗ[ℂ] Lp (TraceClass K) 1 μ)
    (hΛ : L1CompletelyPositive Λ) (g : Ω → ℝ) (hg : Integrable g μ)
    (hg0 : ∀ y, 0 ≤ g y) (χ : Ω → ℝ) (hχ : AEStronglyMeasurable χ μ)
    (hχ0 : ∀ y, 0 ≤ χ y) {C : ℝ} (hbound : ∀ y, ‖χ y‖ ≤ C) :
    IsCompletelyPositive (weightedQuantumMap Λ g hg χ hχ hbound) := by
  intro n A hA v
  have hp : ∀ᵐ y ∂μ, BlockPositive (fun i j => prepareL1 g hg (A i j) y) := by
    have he : ∀ᵐ y ∂μ, ∀ i j : Fin n,
        prepareL1 g hg (A i j) y = (g y : ℂ) • A i j :=
      ae_all_iff.mpr fun i => ae_all_iff.mpr fun j => prepareL1_ae g hg (A i j)
    filter_upwards [he] with y hy
    intro u
    simp only [hy]
    change 0 ≤ ∑ i, ∑ j, ⟪u i, ((g y : ℂ) • (A i j).1) (u j)⟫_ℂ
    simp only [ContinuousLinearMap.smul_apply, inner_smul_right,
      ← Finset.mul_sum]
    exact mul_nonneg (by exact_mod_cast hg0 y) (hA u)
  have ho := hΛ n (fun i j => prepareL1 g hg (A i j)) hp
  let F (i j : Fin n) (y : Ω) : TraceClass K :=
    (χ y : ℂ) • Λ (prepareL1 g hg (A i j)) y
  have hF (i j : Fin n) : Integrable (F i j) μ :=
    weightedL1_integrable χ hχ hbound _
  have hi (i j : Fin n) : Integrable (fun y => ⟪v i, (F i j y).1 (v j)⟫_ℂ) μ :=
    (traceClassMatrixCoefficient (v i) (v j)).integrable_comp (hF i j)
  have hs : Integrable (fun y => ∑ i : Fin n, ∑ j : Fin n,
      ⟪v i, (F i j y).1 (v j)⟫_ℂ) μ :=
    integrable_finset_sum _ (fun i _ => integrable_finset_sum _ (fun j _ => hi i j))
  have hn : ∀ᵐ y ∂μ, 0 ≤ ∑ i : Fin n, ∑ j : Fin n,
      ⟪v i, (F i j y).1 (v j)⟫_ℂ := by
    filter_upwards [ho] with y hy
    change 0 ≤ ∑ i, ∑ j, ⟪v i,
      ((χ y : ℂ) • (Λ (prepareL1 g hg (A i j)) y).1) (v j)⟫_ℂ
    simp only [ContinuousLinearMap.smul_apply, inner_smul_right, ← Finset.mul_sum]
    exact mul_nonneg (by exact_mod_cast hχ0 y) (hy v)
  have he (i j : Fin n) :
      ⟪v i, (weightedQuantumMap Λ g hg χ hχ hbound (A i j)).1 (v j)⟫_ℂ =
      ∫ y, ⟪v i, (F i j y).1 (v j)⟫_ℂ ∂μ :=
    ((traceClassMatrixCoefficient (v i) (v j)).integral_comp_comm (hF i j)).symm
  simp_rw [he]
  have h := integral_complex_nonneg_ae hs hn
  rw [integral_finset_sum _ (fun i _ =>
    integrable_finset_sum _ (fun j _ => hi i j))] at h
  simp_rw [integral_finset_sum _ (fun j _ => hi _ j)] at h
  exact h

end Cloning.Hybrid
