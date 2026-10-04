import Cloning.PCTProjectorPurityParticle
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

/-! The literal finite-sample scaled-purity kernel converges pointwise to
the exponential of the full Hermitian tangent cross term. -/
noncomputable section
open scoped BigOperators Topology Matrix ComplexOrder InnerProductSpace
open Filter MeasureTheory
namespace Cloning.PCTProjectorPurity
open Cloning.PCT Cloning.PCTReducedGaussian Cloning.PCTPhysicalState
open Cloning.PCTLocalChart Cloning.PCTGaussianCovariance Cloning.YoungGeneral
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 200000
variable {r s : ℕ}

lemma flatBase_eq_smul_one (r : ℕ) :
    flatBase r=((r : ℂ)⁻¹) • (1 : Matrix (Fin r) (Fin r) ℂ) := by
  ext i j
  simp [flatBase,Matrix.one_apply,Matrix.diagonal_apply]

lemma trace_particle (hr : 0<r)
    (u : OrthonormalBasis (Fin (s+1)) ℂ (Register (Fin r × Fin r)))
    (z : Fin s → ℂ) (L : ℕ) : Matrix.trace (particle u z L)=1 := by
  letI : Nonempty (Fin r) := ⟨⟨0,hr⟩⟩
  rw [particle,trace_reducedDensityMatrix_complex,frameParticle_norm u.orthonormal]
  norm_num

lemma rank_trace_centered_mul (hr : 0<r) (P Q : Matrix (Fin r) (Fin r) ℂ)
    (hP : Matrix.trace P=1) (hQ : Matrix.trace Q=1) :
    (r : ℂ)*Matrix.trace ((P-flatBase r)*(Q-flatBase r))=
      (r : ℂ)*Matrix.trace (P*Q)-1 := by
  have hR : (r : ℂ)≠0 := by exact_mod_cast Nat.ne_of_gt hr
  rw [flatBase_eq_smul_one]
  simp only [Matrix.sub_mul,Matrix.mul_sub,Matrix.mul_smul,Matrix.smul_mul,
    Matrix.mul_one,Matrix.one_mul,Matrix.trace_sub,Matrix.trace_smul,hP,hQ,smul_eq_mul,
    Matrix.trace_one,Fintype.card_fin]
  field_simp
  <;> ring

lemma particle_scaled_trace_tendsto (hr : 0<r)
    (u : OrthonormalBasis (Fin (s+1)) ℂ (Register (Fin r × Fin r)))
    (hu : u 0=coefficientVector (schmidtCoefficients (flatSpectrum r)))
    (z w : Fin s → ℂ) :
    Tendsto (fun L : ℕ => (L : ℂ)*((r : ℂ)*Matrix.trace (particle u z L*particle u w L)-1))
      atTop (𝓝 ((r : ℂ)*Matrix.trace (tangent u z*tangent u w))) := by
  have hh : Tendsto (fun L : ℕ => ∑i : Fin r,∑j : Fin r,
      ((Real.sqrt (L : ℝ) : ℂ)*(particle u z L i j-flatBase r i j))*
      ((Real.sqrt (L : ℝ) : ℂ)*(particle u w L j i-flatBase r j i)))
      atTop (𝓝 (∑i : Fin r,∑j : Fin r,tangent u z i j*tangent u w j i)) := by
    apply tendsto_finset_sum
    intro i _
    apply tendsto_finset_sum
    intro j _
    exact (particle_scaled_entry_tendsto u hu z i j).mul
      (particle_scaled_entry_tendsto u hu w j i)
  have ht := hh.const_mul (r : ℂ)
  change Tendsto _ atTop (𝓝 ((r : ℂ)*Matrix.trace (tangent u z*tangent u w))) at ht
  apply ht.congr
  intro L
  rw [←rank_trace_centered_mul hr _ _ (trace_particle hr u z L) (trace_particle hr u w L)]
  simp only [Matrix.trace,Matrix.diag_apply,Matrix.mul_apply,Matrix.sub_apply,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have hsq : (Real.sqrt (L : ℝ) : ℂ)^2=(L : ℂ) := by
    exact_mod_cast Real.sq_sqrt (Nat.cast_nonneg L : 0≤(L : ℝ))
  calc
    _ = (r : ℂ)*(Real.sqrt (L : ℝ) : ℂ)^2*
        ((particle u z L i j-flatBase r i j)*(particle u w L j i-flatBase r j i)) := by ring
    _ = _ := by rw [hsq]; ring

/-- Pointwise asymptotic of the actual normalized one-particle overlap. -/
theorem particle_purity_kernel_tendsto (hr : 0<r)
    (u : OrthonormalBasis (Fin (s+1)) ℂ (Register (Fin r × Fin r)))
    (hu : u 0=coefficientVector (schmidtCoefficients (flatSpectrum r)))
    (z w : Fin s → ℂ) :
    Tendsto (fun L : ℕ => ((r : ℝ)*(Matrix.trace (particle u z L*particle u w L)).re)^L)
      atTop (𝓝 (Real.exp ((r : ℝ)*(Matrix.trace (tangent u z*tangent u w)).re))) := by
  have hh := Complex.continuous_re.tendsto _ |>.comp (particle_scaled_trace_tendsto hr u hu z w)
  simp only [Function.comp_def,Complex.mul_re,Complex.natCast_re,Complex.natCast_im,zero_mul,mul_zero,
    sub_zero,Complex.sub_re,Complex.one_re] at hh
  have ht := Real.tendsto_one_add_pow_exp_of_tendsto hh
  simpa only [add_sub_cancel] using ht

end Cloning.PCTProjectorPurity
