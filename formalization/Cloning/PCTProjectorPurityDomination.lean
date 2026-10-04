import Cloning.PCTProjectorPurityKernel
import Cloning.PCTPurityFidelityBound
import Cloning.PCTFlatGaussianCrossKernel
import Cloning.MatrixTraceOrder
import Cloning.GeneralCoherentMixture

/-! An actual two-energy integrable envelope for the finite PCT purity
kernel. The bound uses the normalized physical particle, not a truncation. -/
noncomputable section
open scoped BigOperators Topology Matrix ComplexOrder InnerProductSpace Matrix.Norms.Frobenius
open Filter MeasureTheory
namespace Cloning.PCTProjectorPurity
open Cloning.PCT Cloning.PCTReducedGaussian Cloning.PCTPhysicalState
open Cloning.PCTLocalChart Cloning.PCTGaussianCovariance Cloning.YoungGeneral
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 180000
variable {r s : ℕ}

lemma continuous_particle_entry
    (u : OrthonormalBasis (Fin (s+1)) ℂ (Register (Fin r×Fin r)))
    (L : ℕ) (i j : Fin r) : Continuous (fun z => particle u z L i j) := by
  have hc (a b : Fin r) : Continuous (fun z => frameParticle u z L (a,b)) := by
    simp only [frameParticle_apply]
    exact continuous_finset_sum _ (fun k _ =>
      (GeneralCoherent.continuous_oneParticle s L k).mul_const _)
  unfold particle reducedDensityMatrix
  exact continuous_finset_sum _ (fun k _ => (hc i k).mul (hc j k).star)

lemma continuous_particle_purity_kernel
    (u : OrthonormalBasis (Fin (s+1)) ℂ (Register (Fin r×Fin r))) (L : ℕ) :
    Continuous (fun zw : (Fin s→ℂ)×(Fin s→ℂ) =>
      ((r:ℝ)*(Matrix.trace (particle u zw.1 L*particle u zw.2 L)).re)^L) := by
  apply Continuous.pow
  apply Continuous.const_mul
  apply Complex.continuous_re.comp
  simp only [Matrix.trace,Matrix.diag_apply,Matrix.mul_apply]
  apply continuous_finset_sum
  intro i _
  apply continuous_finset_sum
  intro j _
  exact ((continuous_particle_entry u L i j).comp continuous_fst).mul
    ((continuous_particle_entry u L j i).comp continuous_snd)

lemma particle_overlap_nonneg (hr : 0<r)
    (u : OrthonormalBasis (Fin (s+1)) ℂ (Register (Fin r×Fin r)))
    (z w : Fin s→ℂ) (L : ℕ) :
    0≤(r:ℝ)*(Matrix.trace (particle u z L*particle u w L)).re := by
  letI : Nonempty (Fin r) := ⟨⟨0,hr⟩⟩
  exact mul_nonneg (Nat.cast_nonneg _) (Cloning.MatrixFidelity.trace_mul_re_nonneg
    (reducedDensityMatrix_posSemidef _) (reducedDensityMatrix_posSemidef _))

lemma trace_mul_re_le_frobenius (P Q : Matrix (Fin r) (Fin r) ℂ) (hP : P.IsHermitian) :
    (Matrix.trace (P*Q)).re≤‖P‖*‖Q‖ := by
  rw [←Cloning.PCTFlatGaussianCross.coefficientVector_inner_trace P Q hP,
    Cloning.PCTPurity.frobenius_norm_eq_coefficientVector,
    Cloning.PCTPurity.frobenius_norm_eq_coefficientVector]
  exact (Complex.re_le_norm _).trans (norm_inner_le_norm _ _)

lemma particle_overlap_scaled_bound (hr : 2≤r)
    (u : OrthonormalBasis (Fin (s+1)) ℂ (Register (Fin r×Fin r)))
    (hu : u 0=coefficientVector (schmidtCoefficients (flatSpectrum r)))
    (z w : Fin s→ℂ) (L : ℕ) (hL : 0<L) :
    (L:ℝ)*((r:ℝ)*(Matrix.trace (particle u z L*particle u w L)).re-1)≤
      2*(r:ℝ)*(GeneralCoherent.energy z+GeneralCoherent.energy w) := by
  have hr0 : 0<r := by omega
  letI : Nonempty (Fin r) := ⟨⟨0,hr0⟩⟩
  have hF : (flatBase r).IsHermitian := by
    apply Matrix.isHermitian_diagonal_iff.mpr
    intro i
    simp [isSelfAdjoint_iff]
  have hP : (particle u z L-flatBase r).IsHermitian :=
    (reducedDensityMatrix_posSemidef _).isHermitian.sub hF
  have ht := trace_mul_re_le_frobenius (particle u z L-flatBase r)
    (particle u w L-flatBase r) hP
  have hnorm := mul_le_mul
    (Cloning.PCTPurity.particle_frobenius_deviation_le hr u hu z L)
    (Cloning.PCTPurity.particle_frobenius_deviation_le hr u hu w L)
    (norm_nonneg _) (by positivity)
  have hz : 0≤GeneralCoherent.energy z/(L:ℝ) := div_nonneg (GeneralCoherent.energy_nonneg z) (Nat.cast_nonneg _)
  have hw : 0≤GeneralCoherent.energy w/(L:ℝ) := div_nonneg (GeneralCoherent.energy_nonneg w) (Nat.cast_nonneg _)
  have hab : 2*Real.sqrt (GeneralCoherent.energy z/L)*
      (2*Real.sqrt (GeneralCoherent.energy w/L))≤
      2*(GeneralCoherent.energy z/L+GeneralCoherent.energy w/L) := by
    nlinarith [sq_nonneg (Real.sqrt (GeneralCoherent.energy z/L)-
      Real.sqrt (GeneralCoherent.energy w/L)),Real.sq_sqrt hz,Real.sq_sqrt hw]
  have hc := congrArg Complex.re (rank_trace_centered_mul hr0 (particle u z L)
    (particle u w L) (trace_particle hr0 u z L) (trace_particle hr0 u w L))
  simp only [Complex.mul_re,Complex.natCast_re,Complex.natCast_im,zero_mul,sub_zero,
    Complex.sub_re,Complex.one_re] at hc
  rw [←hc]
  calc
    _ ≤ (L:ℝ)*((r:ℝ)*(2*(GeneralCoherent.energy z/L+GeneralCoherent.energy w/L))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
        (ht.trans (hnorm.trans hab)) (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
    _ = _ := by field_simp <;> ring

/-- The exact manuscript domination, valid at every sample size. -/
theorem particle_purity_kernel_le_energy (hr : 2≤r)
    (u : OrthonormalBasis (Fin (s+1)) ℂ (Register (Fin r×Fin r)))
    (hu : u 0=coefficientVector (schmidtCoefficients (flatSpectrum r)))
    (z w : Fin s→ℂ) (L : ℕ) :
    ((r:ℝ)*(Matrix.trace (particle u z L*particle u w L)).re)^L≤
      Real.exp (2*(r:ℝ)*(GeneralCoherent.energy z+GeneralCoherent.energy w)) := by
  rcases Nat.eq_zero_or_pos L with rfl|hL
  · simp only [pow_zero]
    apply Real.one_le_exp
    exact mul_nonneg (by positivity) (add_nonneg (GeneralCoherent.energy_nonneg z) (GeneralCoherent.energy_nonneg w))
  let a := (r:ℝ)*(Matrix.trace (particle u z L*particle u w L)).re
  have ha : 0≤a := particle_overlap_nonneg (by omega) u z w L
  calc
    a^L ≤ (Real.exp (a-1))^L := by
      apply pow_le_pow_left₀ ha
      linarith [Real.add_one_le_exp (a-1)]
    _ = Real.exp ((L:ℝ)*(a-1)) := by rw [←Real.exp_nat_mul]
    _ ≤ _ := Real.exp_le_exp.mpr (particle_overlap_scaled_bound hr u hu z w L hL)

end Cloning.PCTProjectorPurity
