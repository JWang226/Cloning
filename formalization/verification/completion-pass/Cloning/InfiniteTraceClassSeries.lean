import Cloning.InfiniteTraceClassAlgebra
import Cloning.InfiniteDensityState
import Cloning.CountableScheffe
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-!
# Infinite mixtures in the actual trace-class Banach space

The analytic trace and inclusion into bounded operators are continuous linear
maps. Summable mixtures of unit-vector projectors therefore define genuine
trace-class operators. Their trace-norm variation is bounded by the ℓ¹ variation
of the coefficients, linking countable occupation laws to quantum states.
-/

namespace Cloning.InfiniteTraceClass

set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped ComplexOrder InnerProductSpace Topology BigOperators
open Filter

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem norm_trace_le_traceNorm {T : H →L[ℂ] H} (hT : IsTraceClass T) :
    ‖trace T hT‖ ≤ traceNorm T hT := by
  obtain ⟨w, b, _⟩ := exists_hilbertBasis ℂ H
  rw [trace_eq_of_hilbertBasis hT b]
  have hs := summable_trace_diagonal_of_isTraceClass hT b
  calc
    ‖∑' i : w, ⟪b i, T (b i)⟫_ℂ‖ ≤ ∑' i : w, ‖⟪b i, T (b i)⟫_ℂ‖ :=
      norm_tsum_le_tsum_norm hs.norm
    _ ≤ traceNorm T hT := by
      simpa using tsum_norm_inner_contraction_le_traceNorm hT
        (W := (1 : H →L[ℂ] H)) (ContinuousLinearMap.opNorm_le_bound _ zero_le_one (by intro x; simp)) b

/-- The analytic trace as a continuous complex-linear functional. -/
def traceCLM : TraceClass H →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun T => trace T.1 T.2
      map_add' := fun S T => trace_add S.2 T.2
      map_smul' := fun c T => trace_smul c T.2 }
    1 (fun T => by simpa using norm_trace_le_traceNorm T.2)

theorem traceCLM_apply (T : TraceClass H) : traceCLM T = trace T.1 T.2 := rfl

/-- The trace norm continuously dominates the bounded-operator norm. -/
def inclusionCLM : TraceClass H →L[ℂ] (H →L[ℂ] H) :=
  LinearMap.mkContinuous
    { toFun := fun T => T.1
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    1 (fun T => by simpa using opNorm_le_traceNorm T.2)

theorem inclusionCLM_apply (T : TraceClass H) : inclusionCLM T = T.1 := rfl

/-- A rank-one projector as an element of the trace-class Banach space. -/
def vectorProjector (x : H) : TraceClass H :=
  TraceClass.ofOperator (InnerProductSpace.rankOne ℂ x x) (isTraceClass_rankOne_self x)

theorem norm_vectorProjector (x : H) : ‖vectorProjector x‖ = ‖x‖ ^ 2 :=
  traceNorm_rankOne_self x

theorem traceCLM_vectorProjector (x : H) :
    traceCLM (vectorProjector x) = (‖x‖ ^ 2 : ℝ) := trace_rankOne_self x

variable {ι : Type*}

theorem norm_weighted_projector (x : H) (hx : ‖x‖ = 1) (a : ℝ) :
    ‖(a : ℂ) • vectorProjector x‖ = |a| := by
  rw [norm_smul, norm_vectorProjector, hx]
  simp

theorem summable_weighted_projectors (x : ι → H) (hx : ∀ i, ‖x i‖ = 1)
    (p : ι → ℝ) (hp : Summable p) :
    Summable (fun i => (p i : ℂ) • vectorProjector (x i)) := by
  apply Summable.of_norm
  simpa only [norm_weighted_projector _ (hx _) _, Real.norm_eq_abs] using hp.norm

/-- The mixture is a series in the trace norm, not just a formal diagonal. -/
def vectorMixture (x : ι → H) (p : ι → ℝ) : TraceClass H :=
  ∑' i, (p i : ℂ) • vectorProjector (x i)

theorem traceCLM_vectorMixture (x : ι → H) (hx : ∀ i, ‖x i‖ = 1)
    (p : ι → ℝ) (hp : Summable p) :
    traceCLM (vectorMixture x p) = ((∑' i, p i : ℝ) : ℂ) := by
  rw [vectorMixture, ContinuousLinearMap.map_tsum _ (summable_weighted_projectors x hx p hp)]
  simp only [map_smul, traceCLM_vectorProjector, hx, one_pow, Complex.ofReal_one,
    smul_eq_mul, mul_one]
  exact (Complex.hasSum_ofReal.mpr hp.hasSum).tsum_eq

theorem vectorMixture_nonneg (x : ι → H) (hx : ∀ i, ‖x i‖ = 1)
    (p : ι → ℝ) (hp : Summable p) (hp0 : ∀ i, 0 ≤ p i) :
    0 ≤ (vectorMixture x p).1 := by
  change 0 ≤ inclusionCLM (vectorMixture x p)
  rw [vectorMixture, ContinuousLinearMap.map_tsum _ (summable_weighted_projectors x hx p hp)]
  apply tsum_nonneg
  intro i
  change 0 ≤ (p i : ℂ) • InnerProductSpace.rankOne ℂ (x i) (x i)
  have hcast : (p i : ℂ) • InnerProductSpace.rankOne ℂ (x i) (x i) =
      p i • InnerProductSpace.rankOne ℂ (x i) (x i) := by
    ext y
    simp only [ContinuousLinearMap.smul_apply, RCLike.real_smul_eq_coe_smul (K := ℂ)]
    rfl
  rw [hcast]
  exact smul_nonneg (hp0 i)
    ((InnerProductSpace.rankOne ℂ (x i) (x i)).nonneg_iff_isPositive.mpr
      (InnerProductSpace.isPositive_rankOne_self (x i)))

/-- A normalized nonnegative law gives an actual analytic density operator. -/
def DensityState.vectorMixture (x : ι → H) (hx : ∀ i, ‖x i‖ = 1)
    (p : ι → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp : HasSum p 1) : DensityState H where
  op := (Cloning.InfiniteTraceClass.vectorMixture x p).1
  positive := vectorMixture_nonneg x hx p hp.summable hp0
  traceClass := (Cloning.InfiniteTraceClass.vectorMixture x p).2
  trace_one := by
    change traceCLM (Cloning.InfiniteTraceClass.vectorMixture x p) = 1
    rw [traceCLM_vectorMixture x hx p hp.summable, hp.tsum_eq]
    simp

theorem vectorMixture_sub (x : ι → H) (hx : ∀ i, ‖x i‖ = 1)
    (p q : ι → ℝ) (hp : Summable p) (hq : Summable q) :
    vectorMixture x p - vectorMixture x q = vectorMixture x (p - q) := by
  rw [vectorMixture, vectorMixture, ← (summable_weighted_projectors x hx p hp).tsum_sub
    (summable_weighted_projectors x hx q hq)]
  apply tsum_congr
  intro i
  simp [sub_smul]

theorem norm_vectorMixture_le (x : ι → H) (hx : ∀ i, ‖x i‖ = 1)
    (p : ι → ℝ) (hp : Summable p) :
    ‖vectorMixture x p‖ ≤ ∑' i, |p i| := by
  have hs : Summable (fun i => ‖(p i : ℂ) • vectorProjector (x i)‖) := by
    simpa only [norm_weighted_projector _ (hx _) _, Real.norm_eq_abs] using hp.norm
  simpa only [vectorMixture, norm_weighted_projector _ (hx _) _] using
    norm_tsum_le_tsum_norm hs

theorem norm_vectorMixture_sub_le_l1 (x : ι → H) (hx : ∀ i, ‖x i‖ = 1)
    (p q : ι → ℝ) (hp : Summable p) (hq : Summable q) :
    ‖vectorMixture x p - vectorMixture x q‖ ≤ CountableScheffe.l1Distance p q := by
  rw [vectorMixture_sub x hx p q hp hq]
  exact norm_vectorMixture_le x hx (p - q) (hp.sub hq)

theorem vectorMixture_tendsto_of_pointwise (x : ι → H) (hx : ∀ i, ‖x i‖ = 1)
    (p : ℕ → ι → ℝ) (q : ι → ℝ)
    (hp : ∀ n i, 0 ≤ p n i) (hq : ∀ i, 0 ≤ q i)
    (hp_sum : ∀ n, HasSum (p n) 1) (hq_sum : HasSum q 1)
    (hlim : ∀ i, Tendsto (fun n => p n i) atTop (𝓝 (q i))) :
    Tendsto (fun n => vectorMixture x (p n)) atTop (𝓝 (vectorMixture x q)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  exact squeeze_zero (fun _ => norm_nonneg _)
    (fun n => norm_vectorMixture_sub_le_l1 x hx (p n) q
      (hp_sum n).summable hq_sum.summable)
    (CountableScheffe.discrete_scheffe p q hp hq hp_sum hq_sum hlim)

end
end Cloning.InfiniteTraceClass
