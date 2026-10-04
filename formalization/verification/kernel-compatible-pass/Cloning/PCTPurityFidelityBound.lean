import Cloning.PCTPurityFidelityBoundAlgebra
import Cloning.PCTProjectorPurityParticle

/-! A uniform Frobenius bound for the actual normalized reduced particle.
The constant gives the integrable two-energy envelope at the appendix's
variance threshold. -/
noncomputable section
open scoped BigOperators Matrix InnerProductSpace ComplexOrder Matrix.Norms.Frobenius
namespace Cloning.PCTPurity
open Cloning.PCT Cloning.PCTReducedGaussian Cloning.PCTGaussianCovariance
open Cloning.PCTLocalChart Cloning.PCTProjectorPurity Cloning.YoungGeneral
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
variable {r s : ℕ}

lemma flatBase_eq_smul_one (r : ℕ) :
    flatBase r=(r:ℝ)⁻¹ • (1 : Matrix (Fin r) (Fin r) ℂ) := by
  ext i j
  simp [flatBase,Matrix.one_apply,Matrix.diagonal_apply]

lemma flat_tangent_eq (Z : Matrix (Fin r) (Fin r) ℂ) :
    partialTraceDifferential (flatSpectrum r) Z=(Real.sqrt r)⁻¹ • (Z+Zᴴ) := by
  ext i j
  simp only [partialTraceDifferential_apply,flatSpectrum,one_div,Real.sqrt_inv,
    Matrix.smul_apply,Matrix.add_apply,Matrix.conjTranspose_apply,Complex.real_smul,
    Complex.ofReal_inv]
  ring

/-- The exact physical particle, for all sample sizes (including the harmless
zero convention), has Frobenius deviation at most twice its tangent scale. -/
theorem particle_frobenius_deviation_le (hr : 2≤r)
    (u : OrthonormalBasis (Fin (s+1)) ℂ (Register (Fin r×Fin r)))
    (hu : u 0=coefficientVector (schmidtCoefficients (flatSpectrum r)))
    (z : Fin s→ℂ) (L : ℕ) :
    ‖particle u z L-flatBase r‖≤2*Real.sqrt (GeneralCoherent.energy z/L) := by
  let Z := frameTangentMatrix u z
  have hn : ‖Z‖=Real.sqrt (GeneralCoherent.energy z) := by
    rw [frobenius_norm_eq_coefficientVector]
    have he := frameTangentMatrix_energy u u.orthonormal z
    rw [←he,Real.sqrt_sq (norm_nonneg _)]
  have ht : 0≤sampleScale L := by unfold sampleScale; positivity
  have hf := flat_rational_frobenius_le hr Z (sampleScale L) ht
  rw [particle_exact u hu,flatBase_eq_smul_one]
  have hz : ‖coefficientVector Z‖=‖Z‖ := (frobenius_norm_eq_coefficientVector Z).symm
  change ‖(1+sampleScale L^2*‖coefficientVector Z‖^2)⁻¹ •
      ((r:ℝ)⁻¹ • (1 : Matrix (Fin r) (Fin r) ℂ)+sampleScale L •
        partialTraceDifferential (flatSpectrum r) Z+sampleScale L^2 • (Z*Zᴴ))-
      (r:ℝ)⁻¹ • (1 : Matrix (Fin r) (Fin r) ℂ)‖≤_
  rw [hz,flat_tangent_eq]
  calc
    _ ≤ 2*sampleScale L*‖Z‖ := hf
    _ = _ := by
      rw [hn,Real.sqrt_div (GeneralCoherent.energy_nonneg z),sampleScale]
      ring

end Cloning.PCTPurity
