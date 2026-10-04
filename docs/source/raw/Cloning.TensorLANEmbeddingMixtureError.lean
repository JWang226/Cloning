import Cloning.TensorLANEmbeddingSchur
import Cloning.MixedChannelsBounded

/-! Trace-norm error algebra for the actual finite classical/quantum mixtures. -/
noncomputable section
open scoped BigOperators Topology Classical InnerProductSpace
open MeasureTheory Filter
namespace Cloning.Hybrid
open Cloning.InfiniteTraceClass
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {ι X H : Type*} [Fintype ι] [MeasurableSpace X] {ν : Measure X}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem prepareL1_density_difference_norm (f g : X → ℝ)
    (hf : Integrable f ν) (hg : Integrable g ν) (A : TraceClass H) :
    ‖prepareL1 f hf A-prepareL1 g hg A‖ = (∫ x, |f x-g x| ∂ν)*‖A‖ := by
  rw [L1.norm_eq_integral_norm]
  calc
    _ = ∫ x, |f x-g x| * ‖A‖ ∂ν := by
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_sub (prepareL1 f hf A) (prepareL1 g hg A),
        prepareL1_ae f hf A, prepareL1_ae g hg A] with x hx hf hg
      rw [hx, Pi.sub_apply, hf, hg, ← sub_smul, ← Complex.ofReal_sub,
        norm_smul, Complex.norm_real, Real.norm_eq_abs]
    _ = _ := integral_mul_const _ _

theorem prepareL1_weighted_density_sum (w : ι → ℝ) (g : ι → X → ℝ)
    (hg : ∀ i, Integrable (g i) ν) (A : TraceClass H) :
    (∑ i, prepareL1 (g i) (hg i) ((w i : ℂ) • A)) =
      prepareL1 (fun x => ∑ i, w i*g i x)
        (integrable_finset_sum _ (fun i _ => (hg i).const_mul (w i))) A := by
  apply Lp.ext
  have hall : ∀ᵐ x ∂ν, ∀ i, prepareL1 (g i) (hg i) ((w i : ℂ) • A) x =
      (g i x : ℂ) • ((w i : ℂ) • A) :=
    ae_all_iff.mpr fun i => prepareL1_ae _ _ _
  filter_upwards [Lp_finset_sum_ae Finset.univ
    (fun i => prepareL1 (g i) (hg i) ((w i : ℂ) • A)), hall,
    prepareL1_ae (fun x => ∑ i, w i*g i x)
      (integrable_finset_sum _ (fun i _ => (hg i).const_mul (w i))) A] with x hs hall hf
  rw [hs,hf,Complex.ofReal_sum,Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro i _
  rw [hall i, smul_smul, Complex.ofReal_mul, mul_comm]

/-- Quantum mixture errors add with their actual copy probabilities; the
remaining classical error is exactly scalar L1 distance. -/
theorem finite_prepared_mixture_error (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (g : ι → X → ℝ) (hg : ∀ i, Integrable (g i) ν)
    (hg0 : ∀ i x, 0 ≤ g i x) (hgi : ∀ i, ∫ x, g i x ∂ν = 1)
    (A : ι → TraceClass H) (B : TraceClass H) (f : X → ℝ) (hf : Integrable f ν) :
    ‖(∑ i, prepareL1 (g i) (hg i) ((w i : ℂ) • A i))-prepareL1 f hf B‖ ≤
      (∑ i, w i*‖A i-B‖) +
        (∫ x, |(∑ i, w i*g i x)-f x| ∂ν)*‖B‖ := by
  let C := ∑ i, prepareL1 (g i) (hg i) ((w i : ℂ) • B)
  have he := norm_sub_le_norm_sub_add_norm_sub
    (∑ i, prepareL1 (g i) (hg i) ((w i : ℂ) • A i)) C (prepareL1 f hf B)
  have hq : ‖(∑ i, prepareL1 (g i) (hg i) ((w i : ℂ) • A i))-C‖ ≤
      ∑ i, w i*‖A i-B‖ := by
    dsimp only [C]
    rw [← Finset.sum_sub_distrib]
    simp_rw [← map_sub, ← smul_sub]
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro i _
    rw [norm_prepareL1 _ _ (hg0 i) (hgi i), norm_smul, Complex.norm_real,
      Real.norm_of_nonneg (hw i)]
  have hc : ‖C-prepareL1 f hf B‖ =
      (∫ x, |(∑ i, w i*g i x)-f x| ∂ν)*‖B‖ := by
    dsimp only [C]
    rw [prepareL1_weighted_density_sum]
    exact prepareL1_density_difference_norm _ _ _ _ _
  rw [hc] at he
  exact he.trans (add_le_add hq le_rfl)

theorem weightedL1Integral_prepare (χ f : X → ℝ)
    (hχ : AEStronglyMeasurable χ ν) {C : ℝ} (hb : ∀ x, ‖χ x‖ ≤ C)
    (hf : Integrable f ν) (hχf : Integrable (fun x => χ x*f x) ν) (A : TraceClass H) :
    weightedL1Integral χ hχ hb (prepareL1 f hf A) =
      ((∫ x, χ x*f x ∂ν : ℝ) : ℂ) • A := by
  change (∫ x, (χ x : ℂ) • (prepareL1 f hf A) x ∂ν) = _
  calc
    _ = ∫ x, ((χ x*f x : ℝ) : ℂ) • A ∂ν := by
      apply integral_congr_ae
      filter_upwards [prepareL1_ae f hf A] with x hx
      rw [hx, smul_smul, Complex.ofReal_mul]
    _ = _ := by
      rw [integral_smul_const]
      congr 1
      exact Complex.ofRealCLM.integral_comp_comm hχf

/-- Split any finite probabilistic error average into uniformly good terms
and a residual controlled only by the true exceptional probability. -/
theorem weighted_error_good_bad (w E : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hs : ∑ i, w i = 1) (good : ι → Prop) [DecidablePred good]
    (ε C : ℝ) (hε : 0 ≤ ε) (hC : 0 ≤ C)
    (hgood : ∀ i, good i → E i ≤ ε) (hall : ∀ i, E i ≤ C) :
    (∑ i, w i*E i) ≤ ε+C*(∑ i, if good i then 0 else w i) := by
  calc
    _ ≤ ∑ i, (w i*ε + C*(if good i then 0 else w i)) := by
      apply Finset.sum_le_sum
      intro i _
      by_cases hi : good i
      · simp only [if_pos hi,mul_zero,add_zero]
        exact mul_le_mul_of_nonneg_left (hgood i hi) (hw i)
      · simp only [if_neg hi]
        have hh := mul_le_mul_of_nonneg_left (hall i) (hw i)
        have hp := mul_nonneg (hw i) hε
        nlinarith
    _ = _ := by rw [Finset.sum_add_distrib, ← Finset.sum_mul, hs, one_mul, ← Finset.mul_sum]

end Cloning.Hybrid
