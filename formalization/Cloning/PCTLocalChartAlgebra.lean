import Cloning.PCTTangentNormalization
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! A literal exponential chart around a simple-spectrum state. Hermitian
tangent matrices are used as coordinates, making the derivative the identity.
The usual diagonal and orbital coordinates are recovered by linear extraction. -/
noncomputable section
open scoped Matrix ComplexOrder Matrix.Norms.L2Operator InnerProductSpace Topology BigOperators
open Matrix NormedSpace
namespace Cloning.PCTLocalChart
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {A : Type*} [Fintype A] [DecidableEq A]

abbrev Hermitian (A : Type*) [Fintype A] [DecidableEq A] := selfAdjoint (Matrix A A ℂ)

def base (p : A → ℝ) : Matrix A A ℂ := Matrix.diagonal (fun a => (p a : ℂ))

def diagonalPart : Matrix A A ℂ →ₗ[ℝ] Matrix A A ℂ where
  toFun H := Matrix.diagonal (fun a => H a a)
  map_add' H K := by ext a b; by_cases hab : a = b <;> simp [Matrix.diagonal_apply, hab]
  map_smul' r H := by ext a b; by_cases hab : a = b <;> simp [Matrix.diagonal_apply, hab]

/-- The skew generator dividing every off-diagonal tangent entry by its
fixed spectral gap. -/
def generator (p : A → ℝ) : Matrix A A ℂ →ₗ[ℝ] Matrix A A ℂ where
  toFun H := fun a b => if a = b then 0 else H a b / ((p b - p a : ℝ) : ℂ)
  map_add' H K := by
    ext a b
    by_cases h : a = b <;> simp [h, add_div]
  map_smul' r H := by
    ext a b
    by_cases h : a = b <;> simp [h, Complex.real_smul, mul_div_assoc]

@[simp] lemma generator_apply (p : A → ℝ) (H : Matrix A A ℂ) (a b : A) :
    generator p H a b = if a = b then 0 else H a b / ((p b - p a : ℝ) : ℂ) := rfl

@[simp] lemma generator_diagonal (p : A → ℝ) (H : Matrix A A ℂ) (a : A) :
    generator p H a a = 0 := by simp

lemma generator_skew (p : A → ℝ) (H : Hermitian A) :
    (generator p H)ᴴ = -generator p H := by
  have hh : (H : Matrix A A ℂ)ᴴ = H := H.2
  ext a b
  have hh' := congrArg (fun M : Matrix A A ℂ => M a b) hh
  simp only [Matrix.conjTranspose_apply] at hh'
  by_cases hab : a = b
  · subst b
    simp
  · have hba := Ne.symm hab
    simp only [Matrix.conjTranspose_apply, generator_apply, if_neg hab, if_neg hba,
      Matrix.neg_apply, star_div₀, Complex.star_def, Complex.conj_ofReal, hh']
    rw [show ((p a - p b : ℝ) : ℂ) = -((p b - p a : ℝ) : ℂ) by push_cast; ring]
    rw [div_neg]

/-- The commutator is exactly the off-diagonal part of the input tangent. -/
theorem generator_commutator (p : A → ℝ) (hp : Function.Injective p) (H : Matrix A A ℂ) :
    diagonalPart H + generator p H * base p - base p * generator p H = H := by
  ext a b
  simp only [Matrix.add_apply, Matrix.sub_apply, base, Matrix.mul_diagonal,
    Matrix.diagonal_mul, diagonalPart, LinearMap.coe_mk, AddHom.coe_mk]
  by_cases hab : a = b
  · subst b
    simp
  · have hgap : ((p b - p a : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast sub_ne_zero.mpr (fun h => hab (hp h).symm)
    simp only [Matrix.diagonal_apply_ne _ hab, generator_apply, if_neg hab]
    push_cast at hgap ⊢
    field_simp [hgap]
    <;> ring

lemma base_hermitian (p : A → ℝ) : (base p).IsHermitian := by
  rw [base, Matrix.isHermitian_diagonal_iff]
  intro a
  change star (p a : ℂ) = (p a : ℂ)
  simp

lemma diagonalPart_hermitian (H : Hermitian A) : (diagonalPart (H : Matrix A A ℂ)).IsHermitian := by
  have hh : (H : Matrix A A ℂ)ᴴ = H := H.2
  change (Matrix.diagonal (fun a => (H : Matrix A A ℂ) a a)).IsHermitian
  rw [Matrix.isHermitian_diagonal_iff]
  intro a
  have ha := congrArg (fun M : Matrix A A ℂ => M a a) hh
  exact ha

/-- The actual raw matrix chart, formed by matrix exponentials. -/
def rawChart (p : A → ℝ) (H : Hermitian A) : Matrix A A ℂ :=
  NormedSpace.exp (generator p H) * (base p + diagonalPart H) *
    NormedSpace.exp (-generator p H) - base p

lemma rawChart_hermitian (p : A → ℝ) (H : Hermitian A) : (rawChart p H).IsHermitian := by
  change (rawChart p H)ᴴ = rawChart p H
  have he : (NormedSpace.exp (generator p H))ᴴ = NormedSpace.exp (-generator p H) := by
    rw [← Matrix.exp_conjTranspose, generator_skew]
  have he' : (NormedSpace.exp (-generator p H))ᴴ = NormedSpace.exp (generator p H) := by
    rw [← Matrix.exp_conjTranspose, Matrix.conjTranspose_neg, generator_skew, neg_neg]
  simp only [rawChart, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_add, he, he', (base_hermitian p).eq,
    (diagonalPart_hermitian H).eq, mul_assoc]

/-- The chart as a map of real Hermitian Banach spaces. -/
def chart (p : A → ℝ) (H : Hermitian A) : Hermitian A :=
  ⟨rawChart p H, rawChart_hermitian p H⟩

@[simp] lemma chart_coe (p : A → ℝ) (H : Hermitian A) :
    (chart p H : Matrix A A ℂ) = rawChart p H := rfl

@[simp] lemma chart_zero (p : A → ℝ) : chart p 0 = 0 := by
  apply Subtype.ext
  simp [rawChart, chart, map_zero]

/-- The true chart eigenvalues are the base spectrum plus the tangent diagonal. -/
theorem chart_trace (p : A → ℝ) (H : Hermitian A) :
    Matrix.trace (chart p H : Matrix A A ℂ) = Matrix.trace (H : Matrix A A ℂ) := by
  change Matrix.trace (_ - base p) = _
  rw [Matrix.trace_sub, Matrix.trace_mul_cycle]
  rw [← Matrix.exp_add_of_commute _ _ (Commute.refl (generator p H)).neg_left, neg_add_cancel,
    exp_zero, one_mul, Matrix.trace_add]
  simp [diagonalPart, Matrix.trace]

end Cloning.PCTLocalChart
