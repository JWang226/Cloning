import Cloning.TensorCyclicSectorCovariance
import Cloning.InfiniteTraceClassSeries
import Cloning.InfiniteTraceClassPositive

/-! The actual diagonal tensor density restricted to a physical cyclic sector.
Positivity, nonzero partition function and normalization are derived from the
literal tensor action; no spectral or tail conclusion is assumed. -/
noncomputable section
open scoped BigOperators InnerProductSpace Matrix ComplexOrder
namespace Cloning.TensorLie
open Cloning.PCT Cloning.InfiniteTraceClass
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
variable {n d : ℕ}

local instance : FiniteDimensional ℂ (TensorRegister n (Fin d)) :=
  (registerBasis (Fin n → Fin d)).toOrthonormalBasis.toBasis.finiteDimensional_of_finite

/-- A simultaneous physical Cartan eigenvector has the expected literal
diagonal tensor eigenvalue, including negative formal weights of zero vectors. -/
theorem tensorOperator_diagonal_weight
    (D : Fin d → ℂ) (x : TensorRegister n (Fin d)) (κ : Fin d → ℤ)
    (hx : ∀ a, collectiveGenerator n a a x = (κ a : ℂ) • x) :
    tensorOperator n (Matrix.diagonal D) x = (∏ a, D a ^ κ a) • x := by
  ext w
  rw [tensorOperator_diagonal_apply]
  simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  by_cases hw : x w = 0
  · simp [hw]
  · have hc (a : Fin d) : (occupancy w a : ℤ) = κ a := by
      have he := congrArg (fun y : TensorRegister n (Fin d) => y w) (hx a)
      simp only [collectiveGenerator_diagonal, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul] at he
      have hh := mul_right_cancel₀ hw he
      apply Int.cast_injective (α := ℂ)
      simpa only [Int.cast_natCast] using hh
    rw [word_product_eq_occupancy]
    congr 1
    apply Finset.prod_congr rfl
    intro a _
    rw [← hc a, zpow_natCast]

variable (Ω : TensorRegister n (Fin d)) (mu : Fin d → ℕ)
    (hweight : ∀ a, collectiveGenerator n a a Ω = (mu a : ℂ) • Ω)
    (hraise : ∀ a b, a < b → collectiveGenerator n a b Ω = 0)

theorem cyclicTensorOperator_star (X : Matrix (Fin d) (Fin d) ℂ) :
    cyclicTensorOperator Ω (fun a => (mu a : ℂ)) hweight hraise Xᴴ =
      (cyclicTensorOperator Ω (fun a => (mu a : ℂ)) hweight hraise X).adjoint := by
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro x y
  change ⟪tensorOperator n Xᴴ (x : TensorRegister n (Fin d)),
      (y : TensorRegister n (Fin d))⟫_ℂ =
    ⟪(x : TensorRegister n (Fin d)), tensorOperator n X y⟫_ℂ
  rw [tensorOperator_star, ContinuousLinearMap.adjoint_inner_left]

/-- The literal diagonal tensor operator on its physical cyclic Hilbert space. -/
def sectorGibbsOperator (p : Fin d → ℝ) : cyclicSector Ω →L[ℂ] cyclicSector Ω :=
  cyclicTensorOperator Ω (fun a => (mu a : ℂ)) hweight hraise
    (Matrix.diagonal (fun a => (p a : ℂ)))

theorem sectorGibbsOperator_nonneg (p : Fin d → ℝ) (hp : ∀ a, 0 ≤ p a) :
    0 ≤ sectorGibbsOperator Ω mu hweight hraise p := by
  let S : Matrix (Fin d) (Fin d) ℂ := Matrix.diagonal (fun a => (Real.sqrt (p a) : ℂ))
  have hS : Sᴴ * S = Matrix.diagonal (fun a => (p a : ℂ)) := by
    simp only [S, Matrix.diagonal_conjTranspose, Complex.conj_ofReal,
      Matrix.diagonal_mul_diagonal]
    congr 1
    funext a
    simp [Complex.star_def, ← Complex.ofReal_mul, Real.mul_self_sqrt (hp a)]
  unfold sectorGibbsOperator
  rw [← hS, cyclicTensorOperator_mul, cyclicTensorOperator_star]
  simpa only [ContinuousLinearMap.star_eq_adjoint] using
    (star_mul_self_nonneg (cyclicTensorOperator Ω (fun a => (mu a : ℂ)) hweight hraise S))

/-- The highest tensor is an exact positive eigenvector of this operator. -/
theorem sectorGibbsOperator_highest (p : Fin d → ℝ) :
    sectorGibbsOperator Ω mu hweight hraise p
      ⟨Ω, highest_mem_cyclicSector Ω⟩ =
      ((∏ a, p a ^ mu a : ℝ) : ℂ) • (⟨Ω, highest_mem_cyclicSector Ω⟩ : cyclicSector Ω) := by
  apply Subtype.ext
  have h := tensorOperator_diagonal_weight (fun a => (p a : ℂ)) Ω
    (fun a => (mu a : ℤ)) (by simpa using hweight)
  simpa only [sectorGibbsOperator, cyclicTensorOperator_coe_apply, Submodule.coe_smul,
    zpow_natCast, Complex.ofReal_prod, Complex.ofReal_pow] using h

/-- Finite dimensionality makes the actual sector operator trace class. -/
def sectorGibbsWeight (p : Fin d → ℝ) : TraceClass (cyclicSector Ω) :=
  TraceClass.ofOperator (sectorGibbsOperator Ω mu hweight hraise p)
    (isTraceClass_of_finiteDimensional _)

theorem sectorGibbsWeight_nonneg (p : Fin d → ℝ) (hp : ∀ a, 0 ≤ p a) :
    0 ≤ (sectorGibbsWeight Ω mu hweight hraise p).1 :=
  sectorGibbsOperator_nonneg Ω mu hweight hraise p hp

theorem sectorGibbsWeight_ne_zero (hΩ : ‖Ω‖ = 1)
    (p : Fin d → ℝ) (hp : ∀ a, 0 < p a) :
    sectorGibbsWeight Ω mu hweight hraise p ≠ 0 := by
  intro he
  have hop : sectorGibbsOperator Ω mu hweight hraise p = 0 := congrArg Subtype.val he
  have h := sectorGibbsOperator_highest Ω mu hweight hraise p
  rw [hop, ContinuousLinearMap.zero_apply] at h
  have hc : ((∏ a, p a ^ mu a : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Finset.prod_pos (fun a _ => pow_pos (hp a) _)).ne'
  have hz : (⟨Ω, highest_mem_cyclicSector Ω⟩ : cyclicSector Ω) = 0 :=
    (smul_eq_zero.mp h.symm).resolve_left hc
  have hz' : Ω = 0 := congrArg Subtype.val hz
  simp [hz'] at hΩ

/-- The partition function is the actual analytic trace of the positive
restricted tensor power, expressed as its equal trace norm. -/
def sectorPartitionFunction (p : Fin d → ℝ) : ℝ :=
  ‖sectorGibbsWeight Ω mu hweight hraise p‖

theorem sectorPartitionFunction_pos (hΩ : ‖Ω‖ = 1)
    (p : Fin d → ℝ) (hp : ∀ a, 0 < p a) :
    0 < sectorPartitionFunction Ω mu hweight hraise p :=
  norm_pos_iff.mpr (sectorGibbsWeight_ne_zero Ω mu hweight hraise hΩ p hp)

theorem trace_sectorGibbsWeight (p : Fin d → ℝ) (hp : ∀ a, 0 ≤ p a) :
    traceCLM (sectorGibbsWeight Ω mu hweight hraise p) =
      (sectorPartitionFunction Ω mu hweight hraise p : ℂ) :=
  trace_eq_traceNorm_of_nonneg (sectorGibbsWeight_nonneg Ω mu hweight hraise p hp) _

theorem sectorPartitionFunction_eq_linearMapTrace (p : Fin d → ℝ) (hp : ∀ a, 0 ≤ p a) :
    sectorPartitionFunction Ω mu hweight hraise p =
      (LinearMap.trace ℂ (cyclicSector Ω)
        (sectorGibbsOperator Ω mu hweight hraise p).toLinearMap).re := by
  have h := trace_sectorGibbsWeight Ω mu hweight hraise p hp
  change trace (sectorGibbsOperator Ω mu hweight hraise p) _ = _ at h
  rw [trace_eq_linearMap_trace_of_finiteDimensional] at h
  exact (congrArg Complex.re h).symm

/-- The real sector density used in mixed-state LAN. -/
def sectorGibbsState (hΩ : ‖Ω‖ = 1) (p : Fin d → ℝ) (hp : ∀ a, 0 < p a) :
    DensityState (cyclicSector Ω) where
  op := (((sectorPartitionFunction Ω mu hweight hraise p)⁻¹ : ℝ) : ℂ) •
    sectorGibbsOperator Ω mu hweight hraise p
  positive := by
    apply (ContinuousLinearMap.nonneg_iff_isPositive _).mpr
    apply ((ContinuousLinearMap.nonneg_iff_isPositive _).mp
      (sectorGibbsOperator_nonneg Ω mu hweight hraise p (fun a => (hp a).le))).smul_of_nonneg
    exact_mod_cast inv_nonneg.mpr (sectorPartitionFunction_pos Ω mu hweight hraise hΩ p hp).le
  traceClass := isTraceClass_of_finiteDimensional _
  trace_one := by
    rw [trace_smul]
    change (((sectorPartitionFunction Ω mu hweight hraise p)⁻¹ : ℝ) : ℂ) *
      traceCLM (sectorGibbsWeight Ω mu hweight hraise p) = 1
    rw [trace_sectorGibbsWeight Ω mu hweight hraise p (fun a => (hp a).le)]
    exact_mod_cast inv_mul_cancel₀ (sectorPartitionFunction_pos Ω mu hweight hraise hΩ p hp).ne'

end Cloning.TensorLie
