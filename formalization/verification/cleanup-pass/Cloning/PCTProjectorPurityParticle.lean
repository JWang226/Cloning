import Cloning.PCTTangentChartFrame
import Cloning.PCTPhysicalState
import Cloning.YoungGeneralMoments
import Mathlib.Analysis.Matrix.Normed

/-! Exact reduced particles in the flat PCT Gaussian mixture and their
scaled matrix-entry limit. No simple-spectrum assumption is used. -/
noncomputable section
open scoped BigOperators Topology Matrix ComplexOrder InnerProductSpace
open Filter MeasureTheory
namespace Cloning.PCTProjectorPurity
open Cloning.PCT Cloning.PCTReducedGaussian Cloning.PCTPhysicalState
open Cloning.PCTLocalChart Cloning.PCTGaussianCovariance Cloning.YoungGeneral
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 400000
variable {r s : ℕ}

def flatBase (r : ℕ) : Matrix (Fin r) (Fin r) ℂ :=
  Matrix.diagonal (fun _ => ((r : ℝ)⁻¹ : ℂ))

def particle (u : OrthonormalBasis (Fin (s+1)) ℂ (Register (Fin r × Fin r)))
    (z : Fin s → ℂ) (L : ℕ) : Matrix (Fin r) (Fin r) ℂ :=
  reducedDensityMatrix (frameParticle u z L)

def tangent (u : OrthonormalBasis (Fin (s+1)) ℂ (Register (Fin r × Fin r)))
    (z : Fin s → ℂ) : Matrix (Fin r) (Fin r) ℂ :=
  partialTraceDifferential (flatSpectrum r) (frameTangentMatrix u z)

theorem particle_exact
    (u : OrthonormalBasis (Fin (s+1)) ℂ (Register (Fin r × Fin r)))
    (hu : u 0=coefficientVector (schmidtCoefficients (flatSpectrum r)))
    (z : Fin s → ℂ) (L : ℕ) :
    particle u z L=(1+sampleScale L^2*‖coefficientVector (frameTangentMatrix u z)‖^2)⁻¹ •
      (flatBase r+sampleScale L • tangent u z+
        sampleScale L^2 • (frameTangentMatrix u z*(frameTangentMatrix u z)ᴴ)) := by
  rw [particle,←normalizedTangentVector_eq_frameParticle u (flatSpectrum r) hu z L,
    normalizedTangent_reduced_exact (flatSpectrum r) (fun _ => by unfold flatSpectrum; positivity)
      (frameTangentMatrix u z) _ (sq_nonneg _) (sampleScale L)]
  simp only [flatBase,flatSpectrum,one_div,tangent,Complex.ofReal_inv]

private theorem scaled_rational_difference (t a e : ℝ) (p b v : ℂ)
    (ht : a*t=1) (hd : 1+t^2*e≠0) :
    (a : ℂ)*((1+(t : ℂ)^2*e)⁻¹*(p+(t : ℂ)*v+(t : ℂ)^2*b)-p)=
      (v+(t : ℂ)*(b-(e : ℂ)*p))/(1+(t : ℂ)^2*e) := by
  have htC : (a : ℂ)*t=1 := by exact_mod_cast ht
  have hdC : (1 : ℂ)+(t : ℂ)^2*e≠0 := by exact_mod_cast hd
  calc
    _ = ((a : ℂ)*t)*(v+(t : ℂ)*(b-(e : ℂ)*p))/(1+(t : ℂ)^2*e) := by
      field_simp
      ring
    _ = _ := by rw [htC,one_mul]

/-- The true physical matrix perturbation has the full Hermitian tangent as
its root-sample limit, including every off-diagonal entry. -/
theorem particle_scaled_entry_tendsto
    (u : OrthonormalBasis (Fin (s+1)) ℂ (Register (Fin r × Fin r)))
    (hu : u 0=coefficientVector (schmidtCoefficients (flatSpectrum r)))
    (z : Fin s → ℂ) (i j : Fin r) :
    Tendsto (fun L : ℕ => (Real.sqrt (L : ℝ) : ℂ)*(particle u z L i j-flatBase r i j))
      atTop (𝓝 (tangent u z i j)) := by
  let e := ‖coefficientVector (frameTangentMatrix u z)‖^2
  let b := (frameTangentMatrix u z*(frameTangentMatrix u z)ᴴ) i j
  have ht : Tendsto (fun L => (sampleScale L : ℂ)) atTop (𝓝 0) := by
    simpa only [Complex.ofReal_zero] using
      (Complex.continuous_ofReal.tendsto 0).comp sampleScale_tendsto
  have hh := ((tendsto_const_nhds (x := tangent u z i j)).add
      (ht.mul_const (b-(e : ℂ)*flatBase r i j))).div
        ((tendsto_const_nhds (x := (1 : ℂ))).add ((ht.pow 2).mul_const (e : ℂ))) (by norm_num)
  simp only [zero_mul,zero_pow (by omega : 2≠0),add_zero,div_one] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop 0] with L hL
  rw [particle_exact u hu z L]
  simp only [Matrix.smul_apply,Matrix.add_apply,Complex.real_smul,Complex.ofReal_inv,
    Complex.ofReal_add,Complex.ofReal_mul,Complex.ofReal_pow,Complex.ofReal_one]
  have he : 0≤e := sq_nonneg _
  have hd : 1+sampleScale L^2*e≠0 := by positivity
  have hs : Real.sqrt (L : ℝ)*sampleScale L=1 := by
    rw [sampleScale,mul_inv_cancel₀ (by positivity : Real.sqrt (L : ℝ)≠0)]
  simpa only [Pi.div_apply,e,b,Complex.ofReal_pow] using
    (scaled_rational_difference (sampleScale L) (Real.sqrt (L : ℝ)) e
      (flatBase r i j) b (tangent u z i j) hs hd).symm

end Cloning.PCTProjectorPurity
