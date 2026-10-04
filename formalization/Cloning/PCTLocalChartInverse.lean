import Cloning.PCTLocalChartAlgebra

/-! The actual exponential chart has identity derivative and therefore an
exact local inverse. This concerns finite-dimensional matrix geometry only;
it does not construct mixed-state LAN channels. -/
noncomputable section
open scoped Matrix ComplexOrder Matrix.Norms.L2Operator Topology BigOperators RightActions
open Matrix NormedSpace Filter
namespace Cloning.PCTLocalChart
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
variable {A : Type*} [Fintype A] [DecidableEq A]

local instance : NormedAlgebra ℝ (Matrix A A ℂ) :=
  NormedAlgebra.restrictScalars ℝ ℂ (Matrix A A ℂ)

local instance : FiniteDimensional ℝ (Hermitian A) :=
  FiniteDimensional.of_injective (selfAdjoint.submodule ℝ (Matrix A A ℂ)).subtype
    Subtype.val_injective

local instance : CompleteSpace (Hermitian A) := FiniteDimensional.complete ℝ (Hermitian A)

def inclusion : Hermitian A →L[ℝ] Matrix A A ℂ :=
  (selfAdjoint.submodule ℝ (Matrix A A ℂ)).subtypeL

def diagonalCLM : Hermitian A →L[ℝ] Matrix A A ℂ :=
  (diagonalPart (A := A)).toContinuousLinearMap.comp inclusion

def generatorCLM (p : A → ℝ) : Hermitian A →L[ℝ] Matrix A A ℂ :=
  (generator p).toContinuousLinearMap.comp inclusion

def hermitianPart : Matrix A A ℂ →L[ℝ] Hermitian A :=
  (selfAdjointPart ℝ (A := Matrix A A ℂ)).toContinuousLinearMap

@[simp] lemma inclusion_apply (H : Hermitian A) : inclusion H = (H : Matrix A A ℂ) := rfl
@[simp] lemma diagonalCLM_apply (H : Hermitian A) :
    diagonalCLM H = diagonalPart (H : Matrix A A ℂ) := rfl
@[simp] lemma generatorCLM_apply (p : A → ℝ) (H : Hermitian A) :
    generatorCLM p H = generator p H := rfl

lemma chart_eq_hermitianPart (p : A → ℝ) (H : Hermitian A) :
    chart p H = hermitianPart (rawChart p H) := by
  apply Subtype.ext
  exact ((rawChart_hermitian p H).isSelfAdjoint.coe_selfAdjointPart_apply ℝ).symm

/-- The explicit commutator identity makes the differential exactly the
inclusion of the Hermitian tangent space. -/
theorem rawChart_hasStrictFDerivAt_zero (p : A → ℝ) (hp : Function.Injective p) :
    HasStrictFDerivAt (rawChart p) inclusion (0 : Hermitian A) := by
  have hg : HasStrictFDerivAt (fun H : Hermitian A => NormedSpace.exp (generator p H))
      (generatorCLM p) 0 := by
    have he : HasStrictFDerivAt NormedSpace.exp (1 : Matrix A A ℂ →L[ℝ] Matrix A A ℂ)
        ((generatorCLM p) 0) := by simpa using (hasStrictFDerivAt_exp_zero (𝕂 := ℝ)
          (𝔸 := Matrix A A ℂ))
    have h := he.comp (0 : Hermitian A) (generatorCLM p).hasStrictFDerivAt
    simpa using h
  have hgn : HasStrictFDerivAt (fun H : Hermitian A => NormedSpace.exp (-generator p H))
      (-generatorCLM p) 0 := by
    have he : HasStrictFDerivAt NormedSpace.exp (1 : Matrix A A ℂ →L[ℝ] Matrix A A ℂ)
        ((-generatorCLM p) 0) := by simpa using (hasStrictFDerivAt_exp_zero (𝕂 := ℝ)
          (𝔸 := Matrix A A ℂ))
    have h := he.comp (0 : Hermitian A) (-generatorCLM p).hasStrictFDerivAt
    simpa using h
  have hd : HasStrictFDerivAt (fun H : Hermitian A => base p + diagonalPart H)
      diagonalCLM 0 := (diagonalCLM (A := A)).hasStrictFDerivAt.const_add (base p)
  have h := ((hg.mul' hd).mul' hgn).sub_const (base p)
  convert h using 1
  ext H : 1
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.neg_apply, Pi.mul_apply, ZeroMemClass.coe_zero, map_zero, exp_zero, add_zero, one_mul, mul_one,
      generatorCLM_apply, diagonalCLM_apply, inclusion_apply, neg_zero, exp_zero,
      smul_eq_mul, op_smul_eq_mul, one_mul, mul_one, mul_neg]
  change (H : Matrix A A ℂ) =
      -(base p * generator p H) + (diagonalPart H + generator p H * base p)
  have he := generator_commutator p hp (H : Matrix A A ℂ)
  calc
    (H : Matrix A A ℂ) = diagonalPart H + generator p H * base p -
      base p * generator p H := he.symm
    _ = _ := by abel

/-- In the actual Hermitian chart, the derivative is a continuous linear
equivalence: the identity. -/
theorem chart_hasStrictFDerivAt_zero (p : A → ℝ) (hp : Function.Injective p) :
    HasStrictFDerivAt (chart p) ((ContinuousLinearEquiv.refl ℝ (Hermitian A)).toContinuousLinearMap) 0 := by
  have h := (hermitianPart (A := A)).hasStrictFDerivAt.comp 0
    (rawChart_hasStrictFDerivAt_zero p hp)
  convert h using 1
  · funext H
    exact chart_eq_hermitianPart p H
  · ext H : 1
    apply Subtype.ext
    exact (H.2.coe_selfAdjointPart_apply ℝ).symm

/-- A chosen local inverse supplied by the inverse function theorem. -/
def localInverse (p : A → ℝ) (hp : Function.Injective p) : Hermitian A → Hermitian A :=
  (chart_hasStrictFDerivAt_zero p hp).localInverse (chart p)
    (ContinuousLinearEquiv.refl ℝ (Hermitian A)) 0

@[simp] theorem localInverse_zero (p : A → ℝ) (hp : Function.Injective p) :
    localInverse p hp 0 = 0 := by
  simpa [localInverse] using (chart_hasStrictFDerivAt_zero p hp).localInverse_apply_image

theorem eventually_chart_localInverse (p : A → ℝ) (hp : Function.Injective p) :
    ∀ᶠ X in 𝓝 (0 : Hermitian A), chart p (localInverse p hp X) = X := by
  simpa [localInverse] using (chart_hasStrictFDerivAt_zero p hp).eventually_right_inverse

theorem localInverse_hasStrictFDerivAt_zero (p : A → ℝ) (hp : Function.Injective p) :
    HasStrictFDerivAt (localInverse p hp) ((ContinuousLinearEquiv.refl ℝ (Hermitian A)).toContinuousLinearMap) 0 := by
  simpa [localInverse] using (chart_hasStrictFDerivAt_zero p hp).to_localInverse

end Cloning.PCTLocalChart
