import Cloning.MultimodeThermalIdlerFidelity
import Cloning.BosonicMixtureStochasticOrder

/-! The complete least-noise number-test inequality for the constructed
multimode idler channel, with arbitrary positive trace-class idlers. -/

namespace Cloning.MultimodeLeastNoise

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped ComplexOrder InnerProductSpace Topology BigOperators
open Cloning Cloning.InfiniteTraceClass
open MultimodeIdler ThermalWitness

/-- Every bounded diagonal product test satisfies the actual operator
least-noise inequality. The output number law is proved, not assumed. -/
theorem moment_le_of_diagonal {s : ℕ} (σ : TraceClass (Fock s)) (hσ : 0 ≤ σ.1)
    (q : Fin s → ℝ) (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i < 1)
    (w : Fin s → ℕ → ℝ) (hw0 : ∀ i k, 0 ≤ w i k) (hw : ∀ i, Antitone (w i))
    (W : Fock s →L[ℂ] Fock s)
    (hW : ∀ k, W (numberBasis s k) = ((∏ i, w i (k i) : ℝ) : ℂ) • numberBasis s k) :
    (tracePairing ((channel q hq0 hq1).toLinearMap σ) W).re ≤
      (trace σ.1 σ.2).re *
        (tracePairing (vectorMixture (numberBasis s) (productGeometric q)) W).re := by
  rw [tracePairing_re_eq_number_moment (numberBasis s) _ W _ hW,
    diagonalMixture_tracePairing (numberBasis s) _ (productGeometric_hasSum hq0 hq1).summable
      W _ hW]
  simp_rw [channel_diagonal_re]
  exact BosonicStochasticOrder.mixtureLaw_antitone_moment_le_geometric hq0 hq1 hw0 hw
    (fun l => (σ.1.nonneg_iff_isPositive.mp hσ).re_inner_nonneg_right (numberBasis s l))
    (trace_real_hasSum_basis (numberBasis s) σ)

/-- Equivalent comparison with the channel's actual vacuum output. -/
theorem moment_le_vacuum_of_diagonal {s : ℕ} (σ : TraceClass (Fock s)) (hσ : 0 ≤ σ.1)
    (q : Fin s → ℝ) (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i < 1)
    (w : Fin s → ℕ → ℝ) (hw0 : ∀ i k, 0 ≤ w i k) (hw : ∀ i, Antitone (w i))
    (W : Fock s →L[ℂ] Fock s)
    (hW : ∀ k, W (numberBasis s k) = ((∏ i, w i (k i) : ℝ) : ℂ) • numberBasis s k) :
    (tracePairing ((channel q hq0 hq1).toLinearMap σ) W).re ≤
      (trace σ.1 σ.2).re *
        (tracePairing ((channel q hq0 hq1).toLinearMap
          (vectorProjector (numberBasis s 0))) W).re := by
  rw [MultimodeThermalIdlerFidelity.channel_vacuum]
  exact moment_le_of_diagonal σ hσ q hq0 hq1 w hw0 hw W hW

/-- Product number observable eigenvalues. -/
def productWeight {s : ℕ} (w : Fin s → ℕ → ℝ) (k : Occupation s) : ℝ :=
  ∏ i, w i (k i)

theorem productWeight_nonneg {s : ℕ} {w : Fin s → ℕ → ℝ}
    (hw0 : ∀ i k, 0 ≤ w i k) (k : Occupation s) : 0 ≤ productWeight w k :=
  Finset.prod_nonneg (fun i _ => hw0 i (k i))

theorem productWeight_le_zero {s : ℕ} {w : Fin s → ℕ → ℝ}
    (hw0 : ∀ i k, 0 ≤ w i k) (hw : ∀ i, Antitone (w i)) (k : Occupation s) :
    productWeight w k ≤ productWeight w 0 := by
  apply Finset.prod_le_prod
  · intro i hi; exact hw0 i (k i)
  · intro i hi; exact hw i (Nat.zero_le (k i))

private theorem coefficient_bound {s : ℕ} (w : Fin s → ℕ → ℝ)
    (hw0 : ∀ i k, 0 ≤ w i k) (hw : ∀ i, Antitone (w i))
    (x : Fock s) (k : Occupation s) :
    ‖(productWeight w k : ℂ) * x k‖ ^ 2 ≤
      productWeight w 0 ^ 2 * ‖x k‖ ^ 2 := by
  rw [norm_mul, Complex.norm_of_nonneg (productWeight_nonneg hw0 k), mul_pow]
  exact mul_le_mul_of_nonneg_right
    ((sq_le_sq₀ (productWeight_nonneg hw0 k) (productWeight_nonneg hw0 0)).mpr
      (productWeight_le_zero hw0 hw k)) (sq_nonneg _)

/-- Pointwise multiplication is an actual square-summable vector, since the
nonnegative antitone product is automatically bounded by its vacuum value. -/
def productDiagonalVector {s : ℕ} (w : Fin s → ℕ → ℝ)
    (hw0 : ∀ i k, 0 ≤ w i k) (hw : ∀ i, Antitone (w i)) (x : Fock s) : Fock s := by
  have hx : Summable (fun k : Occupation s => ‖x k‖ ^ (2 : ℕ)) := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      (lp.memℓp x).summable (by norm_num)
  have hs : Summable (fun k : Occupation s => ‖(productWeight w k : ℂ) * x k‖ ^ (2 : ℕ)) :=
    (hx.mul_left (productWeight w 0 ^ 2)).of_nonneg_of_le
      (fun k => sq_nonneg _) (coefficient_bound w hw0 hw x)
  refine ⟨fun k => (productWeight w k : ℂ) * x k, memℓp_gen ?_⟩
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using hs

@[simp] theorem productDiagonalVector_apply {s : ℕ} (w : Fin s → ℕ → ℝ)
    (hw0 : ∀ i k, 0 ≤ w i k) (hw : ∀ i, Antitone (w i)) (x : Fock s) (k : Occupation s) :
    productDiagonalVector w hw0 hw x k = (productWeight w k : ℂ) * x k := rfl

theorem productDiagonalVector_norm_le {s : ℕ} (w : Fin s → ℕ → ℝ)
    (hw0 : ∀ i k, 0 ≤ w i k) (hw : ∀ i, Antitone (w i)) (x : Fock s) :
    ‖productDiagonalVector w hw0 hw x‖ ≤ productWeight w 0 * ‖x‖ := by
  apply lp.norm_le_of_tsum_le (by norm_num)
    (mul_nonneg (productWeight_nonneg hw0 0) (norm_nonneg x))
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, productDiagonalVector_apply, mul_pow]
  have hx : Summable (fun k : Occupation s => ‖x k‖ ^ (2 : ℕ)) := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      (lp.memℓp x).summable (by norm_num)
  have hy : Summable (fun k : Occupation s => ‖(productWeight w k : ℂ) * x k‖ ^ (2 : ℕ)) := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two, productDiagonalVector_apply] using
      (lp.memℓp (productDiagonalVector w hw0 hw x)).summable (by norm_num)
  have heq : (∑' k : Occupation s, ‖x k‖ ^ (2 : ℕ)) = ‖x‖ ^ 2 := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      (lp.hasSum_norm (show 0 < (2 : ENNReal).toReal by norm_num) x).tsum_eq
  calc
    _ ≤ ∑' k : Occupation s, productWeight w 0 ^ 2 * ‖x k‖ ^ (2 : ℕ) :=
      hy.tsum_le_tsum (coefficient_bound w hw0 hw x) (hx.mul_left _)
    _ = _ := by rw [tsum_mul_left, heq]

/-- The physical product of bounded decreasing number functions, as a genuine
bounded operator on multimode Fock space. -/
def productObservable {s : ℕ} (w : Fin s → ℕ → ℝ)
    (hw0 : ∀ i k, 0 ≤ w i k) (hw : ∀ i, Antitone (w i)) : Fock s →L[ℂ] Fock s :=
  LinearMap.mkContinuous
    { toFun := productDiagonalVector w hw0 hw
      map_add' := by intro x y; ext k; simp [mul_add]
      map_smul' := by intro c x; ext k; simp [mul_left_comm] }
    (productWeight w 0) (productDiagonalVector_norm_le w hw0 hw)

@[simp] theorem productObservable_apply {s : ℕ} (w : Fin s → ℕ → ℝ)
    (hw0 : ∀ i k, 0 ≤ w i k) (hw : ∀ i, Antitone (w i)) (x : Fock s) (k : Occupation s) :
    productObservable w hw0 hw x k = (productWeight w k : ℂ) * x k := rfl

theorem productObservable_apply_basis {s : ℕ} (w : Fin s → ℕ → ℝ)
    (hw0 : ∀ i k, 0 ≤ w i k) (hw : ∀ i, Antitone (w i)) (k : Occupation s) :
    productObservable w hw0 hw (numberBasis s k) =
      (productWeight w k : ℂ) • numberBasis s k := by
  ext l
  simp only [productObservable_apply, numberBasis_eq_single, lp.coeFn_smul, Pi.smul_apply,
    lp.single_apply, Pi.single_apply, smul_eq_mul]
  by_cases h : l = k
  · subst l; simp
  · simp [h]

/-- The constructed diagonal number observable is positive. -/
theorem productObservable_nonneg {s : ℕ} (w : Fin s → ℕ → ℝ)
    (hw0 : ∀ i k, 0 ≤ w i k) (hw : ∀ i, Antitone (w i)) :
    0 ≤ productObservable w hw0 hw := by
  apply nonneg_of_inner_nonneg
  intro x
  rw [lp.inner_eq_tsum]
  apply tsum_nonneg
  intro k
  change 0 ≤ ⟪x k, (productWeight w k : ℂ) • x k⟫_ℂ
  rw [inner_smul_right, inner_self_eq_norm_sq_to_K]
  apply mul_nonneg (Complex.zero_le_real.mpr (productWeight_nonneg hw0 k))
  simpa only [Complex.ofReal_pow] using Complex.zero_le_real.mpr (sq_nonneg ‖x k‖)

/-- Full product-observable least-noise bound for arbitrary correlated and
coherent positive trace-class idlers. Every channel and observable is constructed. -/
theorem productObservable_moment_le {s : ℕ} (σ : TraceClass (Fock s)) (hσ : 0 ≤ σ.1)
    (q : Fin s → ℝ) (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i < 1)
    (w : Fin s → ℕ → ℝ) (hw0 : ∀ i k, 0 ≤ w i k) (hw : ∀ i, Antitone (w i)) :
    (tracePairing ((channel q hq0 hq1).toLinearMap σ) (productObservable w hw0 hw)).re ≤
      (trace σ.1 σ.2).re *
        (tracePairing (vectorMixture (numberBasis s) (productGeometric q))
          (productObservable w hw0 hw)).re :=
  moment_le_of_diagonal σ hσ q hq0 hq1 w hw0 hw _ (productObservable_apply_basis w hw0 hw)

end
end Cloning.MultimodeLeastNoise
