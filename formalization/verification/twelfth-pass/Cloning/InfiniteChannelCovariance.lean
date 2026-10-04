import Cloning.InfiniteTraceClassCutoff

/-!
# Covariance of weak limits from vanishing trace-norm defects

Approximate intertwining identities pass to a common weak operator limit on
the actual trace-class spaces. The argument applies separately to every
parameter after extraction, with no countability assumption on that parameter
space. Unitarity is unnecessary for this closure argument.
-/

namespace Cloning.InfiniteTraceClass

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped InnerProductSpace Topology
open Filter

variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Matrix coefficients are continuous linear functionals for the genuine
trace norm, via the bounded inclusion into bounded operators. -/
def traceClassMatrixCoefficient (x y : H) : TraceClass H →L[ℂ] ℂ :=
  (innerSL ℂ x).comp ((ContinuousLinearMap.apply ℂ H y).comp inclusionCLM)

@[simp] theorem traceClassMatrixCoefficient_apply (x y : H) (A : TraceClass H) :
    traceClassMatrixCoefficient x y A = ⟪x, A.1 y⟫_ℂ := rfl

/-- Multiplication by fixed bounded operators is weak-operator continuous. -/
theorem inner_sandwichCLM (P Q : H →L[ℂ] H) (A : TraceClass H) (x y : H) :
    ⟪x, (sandwichCLM P Q A).1 y⟫_ℂ = ⟪star P x, A.1 (Q y)⟫_ℂ := by
  change ⟪x, P (A.1 (Q y))⟫_ℂ = _
  rw [ContinuousLinearMap.star_eq_adjoint]
  exact (ContinuousLinearMap.adjoint_inner_left P (A.1 (Q y)) x).symm

theorem sandwichCLM_weakOperator_tendsto {α : Type*} (l : Filter α)
    (A : α → TraceClass H) (T : TraceClass H)
    (hlim : ∀ x y, Tendsto (fun a => ⟪x, (A a).1 y⟫_ℂ) l (𝓝 ⟪x, T.1 y⟫_ℂ))
    (P Q : H →L[ℂ] H) (x y : H) :
    Tendsto (fun a => ⟪x, (sandwichCLM P Q (A a)).1 y⟫_ℂ) l
      (𝓝 ⟪x, (sandwichCLM P Q T).1 y⟫_ℂ) := by
  simpa only [inner_sandwichCLM] using hlim (star P x) (Q y)

/-- Exact intertwining follows from a vanishing actual trace-norm defect and
convergence of all matrix coefficients of the maps on every input. -/
theorem intertwining_of_weakLimit {α : Type*} (l : Filter α) [l.NeBot]
    (Φ : α → TraceClass H →ₗ[ℂ] TraceClass K)
    (Ψ : TraceClass H →ₗ[ℂ] TraceClass K)
    (hlim : ∀ A x y, Tendsto (fun a => ⟪x, (Φ a A).1 y⟫_ℂ) l
      (𝓝 ⟪x, (Ψ A).1 y⟫_ℂ))
    (U : H →L[ℂ] H) (V : K →L[ℂ] K)
    (hdefect : ∀ A, Tendsto (fun a =>
      ‖Φ a (sandwichCLM U (star U) A) - sandwichCLM V (star V) (Φ a A)‖)
        l (𝓝 (0 : ℝ))) (A : TraceClass H) :
    Ψ (sandwichCLM U (star U) A) = sandwichCLM V (star V) (Ψ A) := by
  apply Subtype.ext
  ext y
  apply ext_inner_left ℂ
  intro x
  have hd : Tendsto (fun a =>
      Φ a (sandwichCLM U (star U) A) - sandwichCLM V (star V) (Φ a A))
      l (𝓝 (0 : TraceClass K)) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr (hdefect A)
  have hz := (traceClassMatrixCoefficient x y).continuous.tendsto 0 |>.comp hd
  have hz' : Tendsto (fun a =>
      ⟪x, (Φ a (sandwichCLM U (star U) A)).1 y⟫_ℂ -
        ⟪x, (sandwichCLM V (star V) (Φ a A)).1 y⟫_ℂ) l (𝓝 (0 : ℂ)) := by
    simpa only [Function.comp_def, map_sub, map_zero, traceClassMatrixCoefficient_apply] using hz
  have hconv := (hlim (sandwichCLM U (star U) A) x y).sub
    (sandwichCLM_weakOperator_tendsto l (fun a => Φ a A) (Ψ A)
      (hlim A) V (star V) x y)
  exact sub_eq_zero.mp (tendsto_nhds_unique hconv hz')

/-- All parameters share the already chosen limit. In particular the group
index may be uncountable; no diagonal extraction over group elements is used. -/
theorem covariance_of_weakLimit {α G : Type*} (l : Filter α) [l.NeBot]
    (Φ : α → TraceClass H →ₗ[ℂ] TraceClass K)
    (Ψ : TraceClass H →ₗ[ℂ] TraceClass K)
    (hlim : ∀ A x y, Tendsto (fun a => ⟪x, (Φ a A).1 y⟫_ℂ) l
      (𝓝 ⟪x, (Ψ A).1 y⟫_ℂ))
    (U : G → H →L[ℂ] H) (V : G → K →L[ℂ] K)
    (hdefect : ∀ g A, Tendsto (fun a =>
      ‖Φ a (sandwichCLM (U g) (star (U g)) A) -
        sandwichCLM (V g) (star (V g)) (Φ a A)‖) l (𝓝 (0 : ℝ))) :
    ∀ g A, Ψ (sandwichCLM (U g) (star (U g)) A) =
      sandwichCLM (V g) (star (V g)) (Ψ A) := by
  intro g A
  exact intertwining_of_weakLimit l Φ Ψ hlim (U g) (V g) (hdefect g) A

/-- The approximate identities along the original sequence automatically pass
to any extracted subsequence with a common weak limit. -/
theorem covariance_of_subsequence_weakLimit {G : Type*}
    (Φ : ℕ → TraceClass H →ₗ[ℂ] TraceClass K)
    (Ψ : TraceClass H →ₗ[ℂ] TraceClass K) (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (hlim : ∀ A x y, Tendsto (fun n => ⟪x, (Φ (φ n) A).1 y⟫_ℂ) atTop
      (𝓝 ⟪x, (Ψ A).1 y⟫_ℂ))
    (U : G → H →L[ℂ] H) (V : G → K →L[ℂ] K)
    (hdefect : ∀ g A, Tendsto (fun n =>
      ‖Φ n (sandwichCLM (U g) (star (U g)) A) -
        sandwichCLM (V g) (star (V g)) (Φ n A)‖) atTop (𝓝 (0 : ℝ))) :
    ∀ g A, Ψ (sandwichCLM (U g) (star (U g)) A) =
      sandwichCLM (V g) (star (V g)) (Ψ A) := by
  apply covariance_of_weakLimit atTop (fun n => Φ (φ n)) Ψ hlim U V
  intro g A
  exact (hdefect g A).comp hφ.tendsto_atTop

end
end Cloning.InfiniteTraceClass
