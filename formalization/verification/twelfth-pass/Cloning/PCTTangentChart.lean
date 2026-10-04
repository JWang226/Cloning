import Cloning.PCTLocalChartInverse
import Cloning.PCTGaussianCovarianceOrbital
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow

/-! Exact inverse-chart coordinates of the normalized physical purification
tangent. Their scaled limit is its literal reduced-state differential. -/
noncomputable section
open scoped Matrix ComplexOrder Matrix.Norms.L2Operator InnerProductSpace Topology BigOperators
open Matrix NormedSpace Filter
namespace Cloning.PCTLocalChart
open Cloning.PCT Cloning.PCTReducedGaussian Cloning.PCTGaussianCovariance
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
variable {A : Type*} [Fintype A] [DecidableEq A]

/-- The Hermitian tangent furnished by the actual partial trace differential. -/
def tangentDifferential (p : A → ℝ) (Z : Matrix A A ℂ) : Hermitian A :=
  ⟨partialTraceDifferential p Z, partialTraceDifferential_hermitian p Z⟩

/-- The exact rational curve determined by normalized purification, centered
at the base state. The projection only packages its Hermitian codomain. -/
def tangentCurve (p : A → ℝ) (Z : Matrix A A ℂ) (t : ℝ) : Hermitian A :=
  hermitianPart ((1 + t ^ 2 * ‖coefficientVector Z‖ ^ 2)⁻¹ •
    (base p + t • partialTraceDifferential p Z + t ^ 2 • (Z * Zᴴ)) - base p)

@[simp] lemma tangentCurve_zero (p : A → ℝ) (Z : Matrix A A ℂ) : tangentCurve p Z 0 = 0 := by
  simp [tangentCurve]

lemma reducedDensityMatrix_hermitian (ψ : Register (A × A)) :
    (reducedDensityMatrix ψ).IsHermitian := by
  let M : Matrix A A ℂ := fun a b => ψ (a,b)
  change (M * Mᴴ)ᴴ = M * Mᴴ
  simp

/-- The curve is exactly the actual reduced normalized purification, with no
change caused by the Hermitian packaging projection. -/
theorem tangentCurve_coe (p : A → ℝ) (hp : ∀ a, 0 ≤ p a)
    (Z : Matrix A A ℂ) (t : ℝ) :
    (tangentCurve p Z t : Matrix A A ℂ) =
      reducedDensityMatrix (normalizedTangentVector p Z (‖coefficientVector Z‖ ^ 2) t) - base p := by
  have hh := (reducedDensityMatrix_hermitian
    (normalizedTangentVector p Z (‖coefficientVector Z‖ ^ 2) t)).sub (base_hermitian p)
  have he := hh.isSelfAdjoint.coe_selfAdjointPart_apply ℝ
  rw [normalizedTangent_reduced_exact p hp Z _ (sq_nonneg _) t] at he
  rw [normalizedTangent_reduced_exact p hp Z _ (sq_nonneg _) t]
  exact he

/-- The exact normalized physical curve has the stated first derivative. -/
theorem tangentCurve_hasDerivAt_zero (p : A → ℝ) (Z : Matrix A A ℂ) :
    HasDerivAt (tangentCurve p Z) (tangentDifferential p Z) 0 := by
  have ht2 : HasDerivAt (fun t : ℝ => t ^ 2) 0 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).pow 2
  have hn : HasDerivAt (fun t : ℝ => base p + t • partialTraceDifferential p Z +
      t ^ 2 • (Z * Zᴴ)) (partialTraceDifferential p Z) 0 := by
    simpa using (((hasDerivAt_id (0 : ℝ)).smul_const (partialTraceDifferential p Z)).const_add
      (base p)).add (ht2.smul_const (Z * Zᴴ))
  have hi : HasDerivAt (fun t : ℝ => (1 + t ^ 2 * ‖coefficientVector Z‖ ^ 2)⁻¹) 0 0 := by
    simpa using ((ht2.mul_const (‖coefficientVector Z‖ ^ 2)).const_add 1).inv (by norm_num)
  have hr := (hi.smul hn).sub_const (base p)
  have hr' : HasDerivAt (fun t : ℝ => (1 + t ^ 2 * ‖coefficientVector Z‖ ^ 2)⁻¹ •
      (base p + t • partialTraceDifferential p Z + t ^ 2 • (Z * Zᴴ)) - base p)
      (partialTraceDifferential p Z) 0 := by simpa using hr
  have h := (hermitianPart (A := A)).hasFDerivAt.comp_hasDerivAt 0 hr'
  have he : hermitianPart (partialTraceDifferential p Z) = tangentDifferential p Z := by
    apply Subtype.ext
    exact (partialTraceDifferential_hermitian p Z).isSelfAdjoint.coe_selfAdjointPart_apply ℝ
  simpa only [he, tangentCurve] using h

/-- The actual (unscaled) local inverse coordinates of the tangent curve. -/
def tangentCoordinates (p : A → ℝ) (hp : Function.Injective p)
    (Z : Matrix A A ℂ) (t : ℝ) : Hermitian A := localInverse p hp (tangentCurve p Z t)

@[simp] lemma tangentCoordinates_zero (p : A → ℝ) (hp : Function.Injective p)
    (Z : Matrix A A ℂ) : tangentCoordinates p hp Z 0 = 0 := by simp [tangentCoordinates]

theorem tangentCoordinates_hasDerivAt_zero (p : A → ℝ) (hp : Function.Injective p)
    (Z : Matrix A A ℂ) :
    HasDerivAt (tangentCoordinates p hp Z) (tangentDifferential p Z) 0 := by
  have hi : HasFDerivAt (localInverse p hp)
      (ContinuousLinearMap.id ℝ (Hermitian A)) (tangentCurve p Z 0) := by
    simpa using (localInverse_hasStrictFDerivAt_zero p hp).hasFDerivAt
  simpa [tangentCoordinates] using hi.comp_hasDerivAt 0 (tangentCurve_hasDerivAt_zero p Z)

/-- The scaled exact coordinates converge. No quadratic bound on the inverse,
or uniform control over unbounded tangents, is needed. -/
theorem scaledTangentCoordinates_tendsto (p : A → ℝ) (hp : Function.Injective p)
    (Z : Matrix A A ℂ) :
    Tendsto (fun t : ℝ => t⁻¹ • tangentCoordinates p hp Z t) (𝓝[≠] 0)
      (𝓝 (tangentDifferential p Z)) := by
  simpa only [zero_add, tangentCoordinates_zero, sub_zero] using
    (tangentCoordinates_hasDerivAt_zero p hp Z).tendsto_slope_zero

/-- For every fixed tangent, inverse-chart equality holds at all sufficiently
small scales. The matrices here are the physical normalized reduced states. -/
theorem eventually_tangent_exact_chart (p : A → ℝ) (hp : Function.Injective p)
    (hp0 : ∀ a, 0 ≤ p a) (Z : Matrix A A ℂ) :
    ∀ᶠ t : ℝ in 𝓝 0,
      NormedSpace.exp (generator p (tangentCoordinates p hp Z t)) *
        (base p + diagonalPart (tangentCoordinates p hp Z t : Matrix A A ℂ)) *
          NormedSpace.exp (-generator p (tangentCoordinates p hp Z t)) =
        reducedDensityMatrix (normalizedTangentVector p Z (‖coefficientVector Z‖ ^ 2) t) := by
  have hc : Tendsto (tangentCurve p Z) (𝓝 0) (𝓝 0) := by
    simpa only [tangentCurve_zero] using (tangentCurve_hasDerivAt_zero p Z).continuousAt.tendsto
  filter_upwards [hc.eventually (eventually_chart_localInverse p hp)] with t ht
  have h := congrArg (fun H : Hermitian A => (H : Matrix A A ℂ)) ht
  dsimp only at h
  rw [chart_coe, tangentCurve_coe p hp0] at h
  change _ - base p = _ - base p at h
  exact sub_left_injective h

end Cloning.PCTLocalChart
