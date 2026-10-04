import Cloning.TensorWeightFrameOrthogonal
import Mathlib.Analysis.SpecificLimits.Basic

/-! Gram convergence to the identity produces nearby common orthonormal
frames, even when the physical Hilbert spaces vary with the sample size.
The orthogonalization is literal Gram--Schmidt, so the exact weight labels
proved in `TensorWeightFrameOrthogonal` are retained. -/
noncomputable section
open scoped BigOperators InnerProductSpace Topology Classical
open Filter InnerProductSpace
namespace Cloning.TensorLie

variable {H : ℕ → Type*} [∀ N, NormedAddCommGroup (H N)]
    [∀ N, InnerProductSpace ℂ (H N)]

theorem varying_norm_tendsto_of_close (x y : ∀ N, H N) (a : ℝ)
    (hy : Tendsto (fun N ↦ ‖y N‖) atTop (𝓝 a))
    (hxy : Tendsto (fun N ↦ ‖x N - y N‖) atTop (𝓝 0)) :
    Tendsto (fun N ↦ ‖x N‖) atTop (𝓝 a) := by
  have hl := hy.sub hxy
  have hu := hy.add hxy
  simp only [sub_zero, add_zero] at hl hu
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hl hu
  · intro N
    have h := norm_sub_norm_le (y N) (x N)
    rw [norm_sub_rev] at h
    linarith
  · intro N
    have h := norm_sub_norm_le (x N) (y N)
    linarith

theorem varying_inner_tendsto_zero_of_close (x y z : ∀ N, H N) (a : ℝ)
    (hxy : Tendsto (fun N ↦ ‖x N - y N‖) atTop (𝓝 0))
    (hz : Tendsto (fun N ↦ ‖z N‖) atTop (𝓝 a))
    (hyz : Tendsto (fun N ↦ ⟪y N, z N⟫_ℂ) atTop (𝓝 0)) :
    Tendsto (fun N ↦ ⟪x N, z N⟫_ℂ) atTop (𝓝 0) := by
  have hb := hxy.mul hz
  simp only [zero_mul] at hb
  have hd : Tendsto (fun N ↦ ‖⟪x N - y N, z N⟫_ℂ‖) atTop (𝓝 0) :=
    squeeze_zero (fun _ ↦ norm_nonneg _) (fun N ↦ norm_inner_le_norm _ _) hb
  have hd' := (tendsto_zero_iff_norm_tendsto_zero).mpr hd
  have hsum := hd'.add hyz
  simpa only [inner_sub_left, sub_add_cancel, add_zero] using hsum

variable {ι : Type*} [LinearOrder ι] [LocallyFiniteOrderBot ι] [WellFoundedLT ι]
    (v : ∀ N, ι → H N)
    (hgram : ∀ i j, Tendsto (fun N ↦ ⟪v N i, v N j⟫_ℂ) atTop
      (𝓝 (if i = j then 1 else 0)))

include hgram

theorem varying_vector_norm_tendsto (i : ι) :
    Tendsto (fun N ↦ ‖v N i‖) atTop (𝓝 1) := by
  have hself : Tendsto (fun N ↦ ⟪v N i, v N i⟫_ℂ) atTop (𝓝 1) := by
    simpa only [if_pos rfl] using hgram i i
  have hs := (Complex.continuous_re.tendsto 1).comp hself
  have h := Real.continuous_sqrt.continuousAt.tendsto.comp hs
  simpa only [Function.comp_def, norm_eq_sqrt_re_inner (𝕜 := ℂ),
    Complex.one_re, Real.sqrt_one] using h

/-- Every unnormalized Gram--Schmidt vector approaches its original vector
when the original Gram matrices approach the identity. -/
theorem gramSchmidt_sub_tendsto_zero (i : ι) :
    Tendsto (fun N ↦ ‖gramSchmidt ℂ (v N) i - v N i‖) atTop (𝓝 0) := by
  induction i using (wellFounded_lt (α := ι)).induction with
  | h i ih =>
    have hp (j : ι) (hj : j ∈ Finset.Iio i) :
        Tendsto (fun N ↦ ‖(ℂ ∙ gramSchmidt ℂ (v N) j).starProjection (v N i)‖)
          atTop (𝓝 0) := by
      have hji : j < i := Finset.mem_Iio.mp hj
      have hjnorm := varying_norm_tendsto_of_close
        (fun N ↦ gramSchmidt ℂ (v N) j) (fun N ↦ v N j) 1
        (varying_vector_norm_tendsto v hgram j) (ih j hji)
      have hij := varying_inner_tendsto_zero_of_close
        (fun N ↦ gramSchmidt ℂ (v N) j) (fun N ↦ v N j) (fun N ↦ v N i) 1
        (ih j hji) (varying_vector_norm_tendsto v hgram i)
        (by simpa only [if_neg (ne_of_lt hji)] using hgram j i)
      have hc := Complex.continuous_ofReal.continuousAt.tendsto.comp hjnorm
      have hcoef := hij.div (hc.pow 2) (by norm_num : (1 : ℂ)^2 ≠ 0)
      have hnorm := hcoef.norm.mul hjnorm
      simpa only [Submodule.starProjection_singleton, norm_smul, Complex.ofReal_one,
        one_pow, zero_div, norm_zero, zero_mul, Pi.div_apply, Function.comp_def,
        RCLike.ofReal_eq_complex_ofReal, Complex.ofReal_pow] using hnorm
    have hsum := tendsto_finset_sum (Finset.Iio i) hp
    simp only [Finset.sum_const_zero] at hsum
    apply squeeze_zero (fun _ ↦ norm_nonneg _) _ hsum
    intro N
    rw [gramSchmidt_def]
    have heq : v N i - (∑ j ∈ Finset.Iio i,
        (ℂ ∙ gramSchmidt ℂ (v N) j).starProjection (v N i)) - v N i =
        -(∑ j ∈ Finset.Iio i,
          (ℂ ∙ gramSchmidt ℂ (v N) j).starProjection (v N i)) := by abel
    rw [heq, norm_neg]
    exact norm_sum_le _ _

theorem gramSchmidt_norm_tendsto_one (i : ι) :
    Tendsto (fun N ↦ ‖gramSchmidt ℂ (v N) i‖) atTop (𝓝 1) :=
  varying_norm_tendsto_of_close _ _ 1 (varying_vector_norm_tendsto v hgram i)
    (gramSchmidt_sub_tendsto_zero v hgram i)

/-- The literal normalized frame approaches the PBW vectors in Hilbert norm.
Together with exact eigenvalue preservation, this is a common frame in every
weight block, including blocks with repeated weights. -/
theorem gramSchmidtNormed_sub_tendsto_zero (i : ι) :
    Tendsto (fun N ↦ ‖gramSchmidtNormed ℂ (v N) i - v N i‖) atTop (𝓝 0) := by
  have hnorm := gramSchmidt_norm_tendsto_one v hgram i
  have hcast := Complex.continuous_ofReal.continuousAt.tendsto.comp
    (hnorm.inv₀ (by norm_num : (1 : ℝ) ≠ 0))
  have hc := (hcast.sub_const 1).norm.mul hnorm
  simp only [inv_one, Complex.ofReal_one, sub_self, norm_zero, zero_mul] at hc
  have hgs : Tendsto (fun N ↦
      ‖gramSchmidtNormed ℂ (v N) i - gramSchmidt ℂ (v N) i‖) atTop (𝓝 0) := by
    convert hc using 1
    ext N
    rw [gramSchmidtNormed]
    calc
      _ = ‖(((‖gramSchmidt ℂ (v N) i‖ : ℂ)⁻¹ - 1) •
          gramSchmidt ℂ (v N) i)‖ := by
        rw [sub_smul, one_smul]
        rfl
      _ = _ := by rw [norm_smul]; simp only [Function.comp_apply, Complex.ofReal_inv]
  have hs := hgs.add (gramSchmidt_sub_tendsto_zero v hgram i)
  simp only [add_zero] at hs
  exact squeeze_zero (fun _ ↦ norm_nonneg _)
    (fun N ↦ norm_sub_le_norm_sub_add_norm_sub _ (gramSchmidt ℂ (v N) i) _) hs

end Cloning.TensorLie
