import Cloning.WeylQuantumPositiveBounds
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.MeasureTheory.Function.L2Space

/-! A normalized continuous positive kernel has a genuine Hilbert-space feature
map. Its Bochner integrals obey Cauchy--Schwarz. This turns the finite quantum
positivity tests into integral inequalities without an idler representation. -/

noncomputable section
open scoped ComplexOrder InnerProductSpace Topology BigOperators
open MeasureTheory Filter

namespace Cloning.PositiveKernel
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

variable {X : Type*}

structure IsNormalizedPositive (K : X → X → ℂ) : Prop where
  hermitian : ∀ x y, star (K y x) = K x y
  diagonal : ∀ x, K x x = 1
  positive : ∀ (s : Finset X) (c : X → ℂ),
    0 ≤ (∑ x ∈ s, ∑ y ∈ s, star (c x) * c y * K x y).re

set_option linter.unusedVariables false in
/-- Finitely supported formal linear combinations of kernel vectors. -/
def PreSpace (K : X → X → ℂ) := X →₀ ℂ

instance (K : X → X → ℂ) : AddCommGroup (PreSpace K) :=
  inferInstanceAs (AddCommGroup (X →₀ ℂ))
instance (K : X → X → ℂ) : Module ℂ (PreSpace K) :=
  inferInstanceAs (Module ℂ (X →₀ ℂ))

variable (K : X → X → ℂ) [hK : Fact (IsNormalizedPositive K)]

instance : PreInnerProductSpace.Core ℂ (PreSpace K) where
  inner f g := (f : X →₀ ℂ).sum fun x a => (g : X →₀ ℂ).sum fun y b => star a * b * K x y
  conj_inner_symm f g := by
    simp only [map_finsuppSum, map_mul]
    rw [Finsupp.sum_comm]
    apply Finsupp.sum_congr
    intro x a
    apply Finsupp.sum_congr
    intro y b
    change star (star ((show X →₀ ℂ from g) y)) * star ((show X →₀ ℂ from f) x) * star (K y x) = _
    rw [star_star, hK.out.hermitian]
    ring
  re_inner_nonneg f := by
    exact hK.out.positive (f : X →₀ ℂ).support (fun x => (show X →₀ ℂ from f) x)
  add_left f g h := by
    rw [Finsupp.sum_add_index'] <;>
      simp [← Finsupp.sum_add, add_mul]
  smul_left f g c := by
    rw [Finsupp.sum_smul_index] <;>
      simp [Finsupp.mul_sum, ← mul_assoc]

instance : SeminormedAddCommGroup (PreSpace K) :=
  InnerProductSpace.Core.toSeminormedAddCommGroup (𝕜 := ℂ)
instance : InnerProductSpace ℂ (PreSpace K) := .ofCore _

abbrev Space := UniformSpace.Completion (PreSpace K)

def feature (x : X) : Space K :=
  UniformSpace.Completion.coe' (show PreSpace K from Finsupp.single x 1)

lemma inner_feature (x y : X) : ⟪feature K x, feature K y⟫_ℂ = K x y := by
  unfold feature
  rw [UniformSpace.Completion.inner_coe]
  change ((Finsupp.single x 1 : X →₀ ℂ).sum fun a u =>
    (Finsupp.single y 1 : X →₀ ℂ).sum fun b v => star u * v * K a b) = _
  simp

lemma norm_feature (x : X) : ‖feature K x‖ = 1 := by
  have h := congrArg Complex.re (inner_feature K x x)
  rw [hK.out.diagonal, inner_self_eq_norm_sq_to_K] at h
  norm_cast at h
  change ‖feature K x‖ ^ 2 = 1 at h
  nlinarith [norm_nonneg (feature K x)]

lemma norm_feature_sub (x y : X) :
    ‖feature K x - feature K y‖ = Real.sqrt (2 - 2 * (K x y).re) := by
  rw [← Real.sqrt_sq (norm_nonneg _), @norm_sub_sq ℂ,
    norm_feature, norm_feature, inner_feature]
  change Real.sqrt (1 ^ 2 - 2 * (K x y).re + 1 ^ 2) = _
  congr 1
  ring

lemma continuous_feature [TopologicalSpace X]
    (hc : Continuous (fun p : X × X => K p.1 p.2)) : Continuous (feature K) := by
  rw [continuous_iff_continuousAt]
  intro x
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  simp_rw [norm_feature_sub]
  have hc' : Continuous (fun y => Real.sqrt (2 - 2 * (K y x).re)) := by
    exact Real.continuous_sqrt.comp
      (continuous_const.sub (continuous_const.mul
        (Complex.continuous_re.comp (hc.comp (continuous_id.prodMk continuous_const)))))
  have h := hc'.continuousAt (x := x)
  simpa only [hK.out.diagonal, Complex.one_re, mul_one, sub_self, Real.sqrt_zero] using h.tendsto

section Integral
variable [TopologicalSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X] {μ : Measure X}

lemma integrable_weighted_feature (hc : Continuous (fun p : X × X => K p.1 p.2))
    {w : X → ℝ} (hw : Integrable w μ) :
    Integrable (fun x => (w x : ℂ) • feature K x) μ := by
  apply hw.norm.mono'
    ((Complex.continuous_ofReal.comp_aestronglyMeasurable hw.aestronglyMeasurable).smul
      (continuous_feature K hc).aestronglyMeasurable)
  exact Eventually.of_forall (fun x => by
    simp only [norm_smul, norm_feature, mul_one, Complex.norm_real]
    exact le_rfl)

/-- Finite positivity has become positivity and Cauchy--Schwarz for actual
Bochner integrals. The weight may be signed and the measure need not be finite. -/
theorem integral_cauchySchwarz
    (hc : Continuous (fun p : X × X => K p.1 p.2))
    {w : X → ℝ} (hw : Integrable w μ) (x₀ : X) :
    ‖∫ x, (w x : ℂ) * K x₀ x ∂μ‖ ^ 2 ≤
      (∫ x, ∫ y, (w x : ℂ) * (w y : ℂ) * K x y ∂μ ∂μ).re := by
  let v : X → Space K := fun x => (w x : ℂ) • feature K x
  have hv : Integrable v μ := integrable_weighted_feature K hc hw
  have hfirst : (∫ x, (w x : ℂ) * K x₀ x ∂μ) =
      ⟪feature K x₀, ∫ x, v x ∂μ⟫_ℂ := by
    convert integral_inner hv (feature K x₀) using 1
    congr 1
    funext x
    simp only [v, inner_smul_right, inner_feature]
  have hdouble : (∫ x, ∫ y, (w x : ℂ) * (w y : ℂ) * K x y ∂μ ∂μ) =
      ⟪∫ x, v x ∂μ, ∫ x, v x ∂μ⟫_ℂ := by
    calc
      _ = ∫ x, ∫ y, ⟪v x, v y⟫_ℂ ∂μ ∂μ := by
        congr 1
        funext x
        congr 1
        funext y
        simp only [v, inner_smul_left, inner_smul_right, inner_feature,
          Complex.conj_ofReal]
        ring
      _ = ∫ x, ⟪v x, ∫ y, v y ∂μ⟫_ℂ ∂μ := by
        congr 1
        funext x
        exact integral_inner hv (v x)
      _ = star (∫ x, ⟪∫ y, v y ∂μ, v x⟫_ℂ ∂μ) := by
        simp_rw [← inner_conj_symm (v _) (∫ y, v y ∂μ)]
        exact integral_conj
      _ = _ := by rw [integral_inner hv]; exact inner_conj_symm _ _
  rw [hfirst, hdouble]
  have h := norm_inner_le_norm (𝕜 := ℂ) (feature K x₀) (∫ x, v x ∂μ)
  rw [norm_feature, one_mul] at h
  have hs := pow_le_pow_left₀ (norm_nonneg _) h 2
  rw [inner_self_eq_norm_sq_to_K]
  change _ ≤ ((‖∫ x, v x ∂μ‖ : ℂ) ^ 2).re
  rw [← Complex.ofReal_pow, Complex.ofReal_re]
  exact hs

end Integral

end Cloning.PositiveKernel
