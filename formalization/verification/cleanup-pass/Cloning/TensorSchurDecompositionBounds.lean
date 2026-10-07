import Cloning.TensorSchurDecompositionMultiplicity
import Cloning.TensorGibbsHeight
import Cloning.TensorPBWFiniteSector

/-! Highest-monomial domination for the literal physical sector trace. -/
noncomputable section
open scoped BigOperators InnerProductSpace Topology
open Filter
namespace Cloning.TensorLie
open Cloning.PCT
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
variable {n d : ℕ}

local instance : FiniteDimensional ℂ (TensorRegister n (Fin d)) :=
  (registerBasis (Fin n → Fin d)).toOrthonormalBasis.toBasis.finiteDimensional_of_finite

theorem rootBoltzmann_le_one (p : Fin d → ℝ) (hp : ∀ a, 0 < p a)
    (horder : Antitone p) (r : PositiveRoot d) : rootBoltzmann p r ≤ 1 := by
  exact (div_le_one (hp _)).mpr (horder r.property.le)

theorem cyclicSector_coefficient_highest_bound_pos
    (Ω : TensorRegister n (Fin d)) (mu : Fin d → ℕ)
    (hweight : ∀ a, collectiveGenerator n a a Ω = (mu a : ℂ) • Ω)
    (p : Fin d → ℝ) (hp : ∀ a, 0 < p a) (horder : Antitone p)
    {x : TensorRegister n (Fin d)} (hx : x ∈ cyclicSector Ω)
    (v : Fin n → Fin d) (hv : (∏ a, p a ^ mu a) < tensorWordMultiplier p v) : x v = 0 := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, rfl⟩ := hx
    by_contra hn
    have he := tensorWordMultiplier_loweringWord Ω mu hweight p hp w v hn
    have hb := wordBoltzmann_le_pow_height p (fun a => (hp a).le) 1 zero_le_one
      (fun r => by simpa using rootBoltzmann_le_one p hp horder r) w
    simp only [one_pow] at hb
    have hm : (∏ a, p a ^ mu a) * wordBoltzmann p w ≤ (∏ a, p a ^ mu a) * 1 :=
      mul_le_mul_of_nonneg_left hb
        (Finset.prod_nonneg (fun a _ => pow_nonneg (hp a).le (mu a)))
    rw [mul_one, ← he] at hm
    exact (not_lt_of_ge hm) hv
  | zero => rfl
  | add x y hx hy ihx ihy => simp [ihx, ihy]
  | smul c x hx ih => simp [lp.coeFn_smul, ih]

/-- The coefficient bound remains valid at repeated and zero eigenvalues,
by continuity of the finite monomials. -/
theorem cyclicSector_coefficient_highest_bound
    (Ω : TensorRegister n (Fin d)) (mu : Fin d → ℕ)
    (hweight : ∀ a, collectiveGenerator n a a Ω = (mu a : ℂ) • Ω)
    (p : Fin d → ℝ) (hp : ∀ a, 0 ≤ p a) (horder : Antitone p)
    {x : TensorRegister n (Fin d)} (hx : x ∈ cyclicSector Ω)
    (v : Fin n → Fin d) (hv : x v ≠ 0) :
    tensorWordMultiplier p v ≤ ∏ a, p a ^ mu a := by
  have he : ∀ ε : ℝ, 0 < ε →
      (∏ t, (p (v t) + ε)) ≤ ∏ a, (p a + ε) ^ mu a := by
    intro ε hε
    by_contra! h
    exact hv (cyclicSector_coefficient_highest_bound_pos Ω mu hweight
      (fun a => p a + ε) (fun a => by linarith [hp a])
      (fun a b hab => by dsimp; linarith [horder hab]) hx v h)
  have hleft : Tendsto (fun ε : ℝ => ∏ t, (p (v t) + ε))
      (𝓝[>] 0) (𝓝 (tensorWordMultiplier p v)) := by
    have hc : Continuous (fun ε : ℝ => ∏ t, (p (v t) + ε)) := by fun_prop
    simpa [tensorWordMultiplier] using (hc.continuousAt (x := 0)).tendsto.mono_left
      (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
  have hright : Tendsto (fun ε : ℝ => ∏ a, (p a + ε) ^ mu a)
      (𝓝[>] 0) (𝓝 (∏ a, p a ^ mu a)) := by
    have hc : Continuous (fun ε : ℝ => ∏ a, (p a + ε) ^ mu a) := by fun_prop
    simpa using (hc.continuousAt (x := 0)).tendsto.mono_left
      (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
  apply le_of_tendsto_of_tendsto hleft hright
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact he ε hε

/-- Actual operator domination on the whole physical cyclic sector. -/
theorem tensorOperator_diagonal_norm_le_on_cyclicSector
    (Ω : TensorRegister n (Fin d)) (mu : Fin d → ℕ)
    (hweight : ∀ a, collectiveGenerator n a a Ω = (mu a : ℂ) • Ω)
    (p : Fin d → ℝ) (hp : ∀ a, 0 ≤ p a) (horder : Antitone p)
    {x : TensorRegister n (Fin d)} (hx : x ∈ cyclicSector Ω) :
    ‖tensorOperator n (Matrix.diagonal (fun a => (p a : ℂ))) x‖ ≤
      (∏ a, p a ^ mu a) * ‖x‖ := by
  apply register_norm_le_of_pointwise _ x _
    (Finset.prod_nonneg (fun a _ => pow_nonneg (hp a) _))
  intro v
  rw [tensorOperator_diagonal_apply, norm_mul]
  by_cases hv : x v = 0
  · simp [hv]
  · have hb := cyclicSector_coefficient_highest_bound Ω mu hweight p hp horder hx v hv
    have hn : ‖∏ t, (p (v t) : ℂ)‖ = tensorWordMultiplier p v := by
      rw [← Complex.ofReal_prod, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Finset.prod_nonneg (fun t _ => hp (v t)))]
      rfl
    rw [hn]
    exact mul_le_mul_of_nonneg_right hb (norm_nonneg _)

/-- The physical character is bounded by its actual dimension times the
highest eigenvalue, with no character or spectral inequality premise. -/
theorem sectorPartitionFunction_le_finrank_highest
    (Ω : TensorRegister n (Fin d)) (mu : Fin d → ℕ)
    (hweight : ∀ a, collectiveGenerator n a a Ω = (mu a : ℂ) • Ω)
    (hraise : ∀ a b, a < b → collectiveGenerator n a b Ω = 0)
    (p : Fin d → ℝ) (hp : ∀ a, 0 ≤ p a) (horder : Antitone p) :
    sectorPartitionFunction Ω mu hweight hraise p ≤
      (Module.finrank ℂ (cyclicSector Ω) : ℝ) * ∏ a, p a ^ mu a := by
  let b := stdOrthonormalBasis ℂ (cyclicSector Ω)
  rw [sectorPartitionFunction_eq_linearMapTrace Ω mu hweight hraise p hp,
    LinearMap.trace_eq_sum_inner _ b, Complex.re_sum]
  calc
    _ ≤ ∑ i : Fin (Module.finrank ℂ (cyclicSector Ω)), ∏ a, p a ^ mu a := by
      apply Finset.sum_le_sum
      intro i _
      have hb := tensorOperator_diagonal_norm_le_on_cyclicSector Ω mu hweight p hp horder (b i).property
      change ‖sectorGibbsOperator Ω mu hweight hraise p (b i)‖ ≤
        (∏ a, p a ^ mu a) * ‖b i‖ at hb
      rw [b.norm_eq_one, mul_one] at hb
      exact (Complex.re_le_norm _).trans ((norm_inner_le_norm _ _).trans (by
        simpa only [b.norm_eq_one, one_mul] using hb))
    _ = _ := by simp

/-- A uniform polynomial bound for the physical partition trace. -/
theorem sectorPartitionFunction_le_polynomial_highest
    (Ω : TensorRegister n (Fin d)) (mu : Fin d → ℕ)
    (hweight : ∀ a, collectiveGenerator n a a Ω = (mu a : ℂ) • Ω)
    (hraise : ∀ a b, a < b → collectiveGenerator n a b Ω = 0)
    (p : Fin d → ℝ) (hp : ∀ a, 0 ≤ p a) (horder : Antitone p) :
    sectorPartitionFunction Ω mu hweight hraise p ≤
      ((n * d + 1 : ℕ) : ℝ) ^ Fintype.card (PositiveRoot d) * ∏ a, p a ^ mu a := by
  apply (sectorPartitionFunction_le_finrank_highest Ω mu hweight hraise p hp horder).trans
  apply mul_le_mul_of_nonneg_right
  · exact_mod_cast finrank_cyclicSector_le_polynomial Ω mu hweight
  · exact Finset.prod_nonneg (fun a _ => pow_nonneg (hp a) _)

theorem physicalSectorCharacter_le_polynomial_highest
    (mu : Fin d → ℕ) (p : Fin d → ℝ) (hp : ∀ a, 0 ≤ p a) (horder : Antitone p) :
    physicalSectorCharacter mu p ≤
      (((∑ a, mu a) * d + 1 : ℕ) : ℝ) ^ Fintype.card (PositiveRoot d) * ∏ a, p a ^ mu a := by
  unfold physicalSectorCharacter
  split_ifs with hmu
  · exact sectorPartitionFunction_le_polynomial_highest _ _
      (partitionHighestTensor_cartan mu hmu) (partitionHighestTensor_raising_zero mu hmu) p hp horder
  · exact mul_nonneg (by positivity) (Finset.prod_nonneg (fun a _ => pow_nonneg (hp a) _))

end Cloning.TensorLie
