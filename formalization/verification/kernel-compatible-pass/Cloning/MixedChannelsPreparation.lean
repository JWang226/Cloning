import Cloning.MixedChannels
import Cloning.HybridCovariantWeighted

/-! Concrete cross-type channels: append a normalized classical density, or
forget the classical register by the actual operator-valued Bochner integral. -/

noncomputable section
open scoped ComplexOrder InnerProductSpace Topology BigOperators
open MeasureTheory Filter Cloning.InfiniteTraceClass
namespace Cloning.Hybrid
set_option backward.isDefEq.respectTransparency false

variable {Ω H : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem prepareL1_blockPositive (g : Ω → ℝ) (hg : Integrable g μ)
    (hg0 : ∀ y, 0 ≤ g y) {n : ℕ} (A : Fin n → Fin n → TraceClass H)
    (hA : BlockPositive A) : L1BlockPositive (fun i j => prepareL1 g hg (A i j)) := by
  have he : ∀ᵐ y ∂μ, ∀ i j : Fin n,
      prepareL1 g hg (A i j) y = (g y : ℂ) • A i j :=
    ae_all_iff.mpr fun i => ae_all_iff.mpr fun j => prepareL1_ae g hg (A i j)
  filter_upwards [he] with y hy
  intro v
  simp only [hy]
  change 0 ≤ ∑ i, ∑ j, ⟪v i, ((g y : ℂ) • (A i j).1) (v j)⟫_ℂ
  simp only [ContinuousLinearMap.smul_apply, inner_smul_right, ← Finset.mul_sum]
  exact mul_nonneg (by exact_mod_cast hg0 y) (hA v)

/-- Appending any actual probability density is a quantum-to-hybrid channel. -/
def QuantumToHybrid.prepare (g : Ω → ℝ) (hg : Integrable g μ)
    (hg0 : ∀ y, 0 ≤ g y) (hprob : ∫ y, g y ∂μ = 1) : QuantumToHybrid H H μ where
  map := (prepareL1 g hg).mkContinuous 1 (fun A =>
    le_of_eq ((norm_prepareL1 g hg hg0 hprob A).trans (one_mul ‖A‖).symm))
  completelyPositive := fun _ A hA => prepareL1_blockPositive g hg hg0 A hA
  tracePreserving := fun A => (integratedTrace_apply _).trans
    (integral_trace_prepareL1 g hg hprob A)

@[simp] theorem QuantumToHybrid.prepare_apply (g : Ω → ℝ) (hg : Integrable g μ)
    (hg0 : ∀ y, 0 ≤ g y) (hprob : ∫ y, g y ∂μ = 1) (A : TraceClass H) :
    (QuantumToHybrid.prepare g hg hg0 hprob).map A = prepareL1 g hg A := rfl

theorem L1BlockPositive.integral {n : ℕ}
    (A : Fin n → Fin n → Lp (TraceClass H) 1 μ) (hA : L1BlockPositive A) :
    BlockPositive (fun i j => ∫ y, A i j y ∂μ) := by
  intro v
  have hi (i j : Fin n) : Integrable (fun y => ⟪v i, (A i j y).1 (v j)⟫_ℂ) μ :=
    (traceClassMatrixCoefficient (v i) (v j)).integrable_comp (L1.integrable_coeFn (A i j))
  have hs : Integrable (fun y => ∑ i : Fin n, ∑ j : Fin n,
      ⟪v i, (A i j y).1 (v j)⟫_ℂ) μ :=
    integrable_finset_sum _ (fun i _ => integrable_finset_sum _ (fun j _ => hi i j))
  have he (i j : Fin n) : ⟪v i, (∫ y, A i j y ∂μ).1 (v j)⟫_ℂ =
      ∫ y, ⟪v i, (A i j y).1 (v j)⟫_ℂ ∂μ :=
    ((traceClassMatrixCoefficient (v i) (v j)).integral_comp_comm
      (L1.integrable_coeFn (A i j))).symm
  simp_rw [he]
  have hp := integral_complex_nonneg_ae hs (hA.mono fun y hy => hy v)
  rw [integral_finset_sum _ (fun i _ =>
    integrable_finset_sum _ (fun j _ => hi i j))] at hp
  simp_rw [integral_finset_sum _ (fun j _ => hi _ j)] at hp
  exact hp

/-- Forgetting the classical register is CPTP for every reference measure. -/
def HybridToQuantum.integrate : HybridToQuantum H H μ where
  map := L1.integralCLM' ℂ
  completelyPositive := fun n A hA => by
    have h := L1BlockPositive.integral A hA
    simpa only [← L1.integral_eq', L1.integral_eq_integral] using h
  tracePreserving := fun _ => rfl

@[simp] theorem HybridToQuantum.integrate_apply (A : Lp (TraceClass H) 1 μ) :
    HybridToQuantum.integrate.map A = ∫ y, A y ∂μ := by
  change L1.integralCLM' ℂ A = _
  rw [← L1.integral_eq', L1.integral_eq_integral]

theorem HybridToQuantum.integrate_norm_le (A : Lp (TraceClass H) 1 μ) :
    ‖HybridToQuantum.integrate.map A‖ ≤ ‖A‖ := by
  rw [integrate_apply, L1.norm_eq_integral_norm]
  exact norm_integral_le_integral_norm _

theorem HybridToQuantum.integrate_prepare (g : Ω → ℝ) (hg : Integrable g μ)
    (hg0 : ∀ y, 0 ≤ g y) (hprob : ∫ y, g y ∂μ = 1) (A : TraceClass H) :
    HybridToQuantum.integrate.map ((QuantumToHybrid.prepare g hg hg0 hprob).map A) = A := by
  rw [integrate_apply, QuantumToHybrid.prepare_apply]
  calc
    _ = ∫ y, (g y : ℂ) • A ∂μ := integral_congr_ae (prepareL1_ae g hg A)
    _ = (∫ y, (g y : ℂ) ∂μ) • A := integral_smul_const _ _
    _ = A := by
      have he := Complex.ofRealCLM.integral_comp_comm hg
      change (∫ y, (g y : ℂ) ∂μ) = ((∫ y, g y ∂μ : ℝ) : ℂ) at he
      rw [he, hprob]
      simp

end Cloning.Hybrid
