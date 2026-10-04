import Cloning.TensorLocalUnitaryPhysical
import Cloning.PCTTangentChartSamples

/-! Exact coefficient matching between the physical local spectral chart and
the normalized collective-root displacement. -/
noncomputable section
open scoped BigOperators InnerProductSpace Matrix Topology Matrix.Norms.L2Operator
open NormedSpace Filter
namespace Cloning.TensorLocalUnitary
open Cloning.TensorLie Cloning.PCTLocalChart
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
variable {n d : ℕ}

/-- The arbitrary-matrix collective action is genuinely complex linear. -/
def collectiveMatrixLM : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ]
    (TensorRegister n (Fin d) →L[ℂ] TensorRegister n (Fin d)) where
  toFun := collectiveMatrix
  map_add' := by intro X Y; simp [collectiveMatrix, add_smul, Finset.sum_add_distrib]
  map_smul' := by
    intro c X
    simp only [collectiveMatrix, Matrix.smul_apply, smul_eq_mul, RingHom.id_apply,
      Finset.smul_sum, mul_smul]

@[simp] theorem collectiveMatrixLM_apply (Y : Matrix (Fin d) (Fin d) ℂ) :
    collectiveMatrixLM (n := n) Y = collectiveMatrix Y := rfl

@[simp] theorem collectiveMatrix_single (a b : Fin d) (c : ℂ) :
    collectiveMatrix (n := n) (Matrix.single a b c) = c • collectiveGenerator n a b := by
  simp [collectiveMatrix, Matrix.single, Matrix.of_apply, ite_and, ite_smul]

/-- A positive-root sum in literal one-particle matrix units. -/
def rootSkewMatrix (c : PositiveRoot d → ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  ∑ a, (c a • Matrix.single a.val.2 a.val.1 1 -
    star (c a) • Matrix.single a.val.1 a.val.2 1)

private theorem upperRootSum (c : PositiveRoot d → ℂ) (i j : Fin d) :
    (∑ a : PositiveRoot d, c a • Matrix.single a.val.1 a.val.2 (1 : ℂ)) i j =
      if hij : i < j then c ⟨(i,j),hij⟩ else 0 := by
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  by_cases hij : i < j
  · rw [dif_pos hij, Finset.sum_eq_single (⟨(i,j),hij⟩ : PositiveRoot d)]
    · simp
    · intro a _ ha
      have hne : ¬ (a.val.1 = i ∧ a.val.2 = j) := by
        rintro ⟨h1,h2⟩
        apply ha
        exact Subtype.ext (Prod.ext h1 h2)
      simp [Matrix.single, Matrix.of_apply, hne]
    · simp
  · rw [dif_neg hij]
    apply Finset.sum_eq_zero
    intro a _
    have hne : ¬ (a.val.1 = i ∧ a.val.2 = j) := by
      rintro ⟨h1,h2⟩
      apply hij
      simpa only [← h1, ← h2] using a.property
    simp [Matrix.single, Matrix.of_apply, hne]

private theorem lowerRootSum (c : PositiveRoot d → ℂ) (i j : Fin d) :
    (∑ a : PositiveRoot d, c a • Matrix.single a.val.2 a.val.1 (1 : ℂ)) i j =
      if hji : j < i then c ⟨(j,i),hji⟩ else 0 := by
  have hh := upperRootSum c j i
  convert hh using 1
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro a _
  simp [Matrix.single, Matrix.of_apply, and_comm]

/-- The manuscript orbital generator is exactly the positive-root matrix sum. -/
theorem orbitalGenerator_eq_rootSkewMatrix (p : Fin d → ℝ) (z : PositiveRoot d → ℂ) :
    orbitalGenerator p z = rootSkewMatrix
      (fun a => z a / (Real.sqrt (p a.val.1 - p a.val.2) : ℂ)) := by
  ext i j
  simp only [rootSkewMatrix, Finset.sum_sub_distrib, Matrix.sub_apply,
    upperRootSum, lowerRootSum, orbitalGenerator, star_div₀, Complex.star_def, Complex.conj_ofReal]
  by_cases hij : i < j
  · simp [hij, not_lt_of_gt hij, neg_div]
  · by_cases hji : j < i
    · simp [hij,hji]
    · simp [hij,hji]

/-- The finite-partition root parameter needed at physical sample scale `t`. -/
def scaledRootParameter (p : Fin d → ℝ) (mu : Fin d → ℕ) (t : ℝ)
    (z : PositiveRoot d → ℂ) : PositiveRoot d → ℂ :=
  fun a => ((t * Real.sqrt ((mu a.val.1 : ℝ)-mu a.val.2) /
    Real.sqrt (p a.val.1-p a.val.2) : ℝ) : ℂ) * z a

/-- Exact local-chart coefficient matching on the full physical tensor space. -/
theorem collectiveMatrix_orbitalGenerator (p : Fin d → ℝ) (mu : Fin d → ℕ)
    (hmu : ∀ a : PositiveRoot d, 0 < (mu a.val.1 : ℝ)-mu a.val.2)
    (t : ℝ) (z : PositiveRoot d → ℂ) :
    collectiveMatrix (n := n) (t • orbitalGenerator p z) =
      rootGenerator (n := n) mu (scaledRootParameter p mu t z) := by
  rw [orbitalGenerator_eq_rootSkewMatrix]
  change collectiveMatrixLM (n := n) (t • rootSkewMatrix _) = _
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
  simp only [map_smul, rootSkewMatrix, map_sum, map_sub, collectiveMatrixLM_apply,
    collectiveMatrix_single, one_smul, Finset.smul_sum, rootGenerator]
  apply Finset.sum_congr rfl
  intro a _
  have hs : (Real.sqrt ((mu a.val.1 : ℝ)-mu a.val.2) : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Real.sqrt_pos.mpr (hmu a)))
  simp only [smul_sub, normalizedCreator, normalizedAnnihilator,
    RCLike.real_smul_eq_coe_smul (K := ℂ), smul_smul, scaledRootParameter,
    Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_inv,
    star_mul, star_div₀, Complex.star_def, Complex.conj_ofReal]
  congr 1 <;> congr 1 <;> push_cast <;> field_simp [hs] <;> ac_rfl

/-- The actual tensor power of the physical chart rotation is exactly the
normalized-root unitary used in the bosonic limit. -/
theorem tensorOperator_local_orbital (p : Fin d → ℝ) (mu : Fin d → ℕ)
    (hmu : ∀ a : PositiveRoot d, 0 < (mu a.val.1 : ℝ)-mu a.val.2)
    (t : ℝ) (z : PositiveRoot d → ℂ) :
    tensorOperator n (exp (t • orbitalGenerator p z)) =
      exp (rootGenerator (n := n) mu (scaledRootParameter p mu t z)) := by
  rw [tensorOperator_exp, collectiveMatrix_orbitalGenerator p mu hmu]

/-- At the physical sample scale, the coefficient is the square root of the
empirical spectral gap divided by the base spectral gap. -/
theorem scaledRootParameter_sampleScale (p : Fin d → ℝ) (mu : Fin d → ℕ)
    (hmu : Antitone mu) (L : ℕ) (z : PositiveRoot d → ℂ) (a : PositiveRoot d) :
    scaledRootParameter p mu (sampleScale L) z a =
      ((Real.sqrt (((mu a.val.1 : ℝ)-mu a.val.2) / (L : ℝ)) /
        Real.sqrt (p a.val.1-p a.val.2) : ℝ) : ℂ) * z a := by
  have hnonneg : 0 ≤ (mu a.val.1 : ℝ)-mu a.val.2 :=
    sub_nonneg.mpr (Nat.cast_le.mpr (hmu (le_of_lt a.property)))
  simp only [scaledRootParameter, sampleScale, Real.sqrt_div hnonneg]
  congr 2
  ring

/-- Convergence of the actual local-chart orbital coefficients. The partition
size is the physical sample size `L`; no cloning-ratio factor is introduced. -/
theorem scaledRootParameter_tendsto (p : Fin d → ℝ)
    (hp : ∀ a : PositiveRoot d, 0 < p a.val.1-p a.val.2)
    (mu : ℕ → Fin d → ℕ) (hmu : ∀ N, Antitone (mu N)) (L : ℕ → ℕ)
    (hfreq : Tendsto (fun N => fun a => (mu N a : ℝ)/(L N : ℝ)) atTop (𝓝 p))
    (z : ℕ → PositiveRoot d → ℂ) (z₀ : PositiveRoot d → ℂ)
    (hz : Tendsto z atTop (𝓝 z₀)) :
    Tendsto (fun N => scaledRootParameter p (mu N) (sampleScale (L N)) (z N))
      atTop (𝓝 z₀) := by
  apply tendsto_pi_nhds.mpr
  intro a
  have hf := (tendsto_pi_nhds.mp hfreq a.val.1).sub
    (tendsto_pi_nhds.mp hfreq a.val.2)
  simp only [← sub_div] at hf
  have hcoef := (hf.sqrt).div_const (Real.sqrt (p a.val.1-p a.val.2))
  rw [div_self (ne_of_gt (Real.sqrt_pos.mpr (hp a)))] at hcoef
  have hc := (Complex.continuous_ofReal.tendsto 1).comp hcoef
  have h := hc.mul (tendsto_pi_nhds.mp hz a)
  simpa only [Complex.ofReal_one, one_mul, scaledRootParameter_sampleScale p _ (hmu _) ] using h

end Cloning.TensorLocalUnitary
