import Cloning.PCTPhysicalState
import Cloning.FiniteKrausLift
import Cloning.MatrixFidelityEmbedding

/-! Literal unitary transport of coefficient purifications, complete physical
frames, reduced matrices and tensor-power trace-class operators. -/
noncomputable section
open scoped BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace ComplexOrder Topology
open Cloning.InfiniteTraceClass
namespace Cloning.PCTUnitaryTransport
open Cloning.PCT Cloning.PCTReducedGaussian Cloning.PCTPurificationChannel
open Cloning.PCTPhysicalState Cloning.FiniteKrausLift
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]

def coefficients (ψ : Register (A × A)) : Matrix A A ℂ := fun a b => ψ (a,b)

@[simp] theorem coefficientVector_coefficients (ψ : Register (A × A)) :
    coefficientVector (coefficients ψ) = ψ := by ext ⟨a,b⟩; rfl

@[simp] theorem coefficients_coefficientVector (M : Matrix A A ℂ) :
    coefficients (coefficientVector M) = M := rfl

@[simp] theorem coefficients_add (ψ φ : Register (A × A)) :
    coefficients (ψ+φ) = coefficients ψ + coefficients φ := rfl

@[simp] theorem coefficients_smul (c : ℂ) (ψ : Register (A × A)) :
    coefficients (c • ψ) = c • coefficients ψ := rfl

theorem reduced_eq_coefficients (ψ : Register (A × A)) :
    reducedDensityMatrix ψ = coefficients ψ * (coefficients ψ)ᴴ := rfl

def conjugatePurification (U : unitary (Matrix A A ℂ)) (ψ : Register (A × A)) :
    Register (A × A) := coefficientVector ((U : Matrix A A ℂ) * coefficients ψ * (U : Matrix A A ℂ)ᴴ)

theorem reduced_conjugatePurification (U : unitary (Matrix A A ℂ)) (ψ : Register (A × A)) :
    reducedDensityMatrix (conjugatePurification U ψ) =
      (U : Matrix A A ℂ) * reducedDensityMatrix ψ * (U : Matrix A A ℂ)ᴴ := by
  have hU : (U : Matrix A A ℂ)ᴴ * U = 1 := Unitary.star_mul_self_of_mem U.property
  rw [conjugatePurification, reducedDensityMatrix_coefficientVector, reduced_eq_coefficients]
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (U : Matrix A A ℂ)ᴴ, hU, Matrix.one_mul]

theorem conjugatePurification_norm (U : unitary (Matrix A A ℂ)) (ψ : Register (A × A)) :
    ‖conjugatePurification U ψ‖ = ‖ψ‖ := by
  have hU : (U : Matrix A A ℂ)ᴴ * U = 1 := Unitary.star_mul_self_of_mem U.property
  have h : Matrix.trace (reducedDensityMatrix (conjugatePurification U ψ)) =
      Matrix.trace (reducedDensityMatrix ψ) := by
    rw [reduced_conjugatePurification, Matrix.trace_mul_comm,
      ← Matrix.mul_assoc, hU, Matrix.one_mul]
  rw [trace_reducedDensityMatrix_complex, trace_reducedDensityMatrix_complex] at h
  have hr := congrArg Complex.re h
  simp only [Complex.ofReal_re] at hr
  nlinarith [norm_nonneg (conjugatePurification U ψ), norm_nonneg ψ]

theorem conjugatePurification_star (U : unitary (Matrix A A ℂ)) (ψ : Register (A × A)) :
    conjugatePurification (star U) (conjugatePurification U ψ) = ψ := by
  have hU : (U : Matrix A A ℂ)ᴴ * U = 1 := Unitary.star_mul_self_of_mem U.property
  have hV : (U : Matrix A A ℂ) * (U : Matrix A A ℂ)ᴴ = 1 := Unitary.mul_star_self_of_mem U.property
  simp only [conjugatePurification, coefficients_coefficientVector, Unitary.coe_star,
    Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose]
  change coefficientVector ((U : Matrix A A ℂ)ᴴ *
    ((U : Matrix A A ℂ) * coefficients ψ * (U : Matrix A A ℂ)ᴴ) * (U : Matrix A A ℂ)) = ψ
  simp only [← Matrix.mul_assoc]
  rw [hU, Matrix.one_mul, Matrix.mul_assoc, hU, Matrix.mul_one, coefficientVector_coefficients]

def purificationEquiv (U : unitary (Matrix A A ℂ)) : Register (A × A) ≃ₗᵢ[ℂ] Register (A × A) where
  toFun := conjugatePurification U
  invFun := conjugatePurification (star U)
  left_inv := conjugatePurification_star U
  right_inv := by simpa only [star_star] using conjugatePurification_star (star U)
  map_add' ψ φ := by
    ext ⟨a,b⟩
    simp only [conjugatePurification, coefficients_add, Matrix.mul_add, Matrix.add_mul,
      coefficientVector_apply, Matrix.add_apply, lp.coeFn_add, Pi.add_apply]
  map_smul' c ψ := by
    ext ⟨a,b⟩
    simp only [conjugatePurification, coefficients_smul, Matrix.mul_smul, Matrix.smul_mul,
      coefficientVector_apply, Matrix.smul_apply, lp.coeFn_smul, Pi.smul_apply, RingHom.id_apply]
  norm_map' := conjugatePurification_norm U

@[simp] theorem purificationEquiv_apply (U : unitary (Matrix A A ℂ)) (ψ : Register (A × A)) :
    purificationEquiv U ψ = conjugatePurification U ψ := rfl

theorem canonicalPurification_conjugate (U : unitary (Matrix A A ℂ))
    (ρ : Matrix A A ℂ) (hρ : ρ.PosSemidef) :
    canonicalPurification ((U : Matrix A A ℂ) * ρ * (U : Matrix A A ℂ)ᴴ) =
      purificationEquiv U (canonicalPurification ρ) := by
  rw [canonicalPurification, Cloning.MatrixFidelity.sqrt_isometric_embedding
    (U : Matrix A A ℂ) (Unitary.star_mul_self_of_mem U.property) hρ]
  rfl

def transportFrame {s : ℕ}
    (u : OrthonormalBasis (Fin (s+1)) ℂ (Register (A × A)))
    (U : unitary (Matrix A A ℂ)) : OrthonormalBasis (Fin (s+1)) ℂ (Register (A × A)) :=
  u.map (purificationEquiv U)

theorem frameParticle_transport {s : ℕ}
    (u : OrthonormalBasis (Fin (s+1)) ℂ (Register (A × A)))
    (U : unitary (Matrix A A ℂ)) (z : Fin s → ℂ) (L : ℕ) :
    frameParticle (transportFrame u U) z L = purificationEquiv U (frameParticle u z L) := by
  simp only [frameParticle, map_sum, map_smul, transportFrame, OrthonormalBasis.map_apply]

theorem reduced_frameParticle_transport {s : ℕ}
    (u : OrthonormalBasis (Fin (s+1)) ℂ (Register (A × A)))
    (U : unitary (Matrix A A ℂ)) (z : Fin s → ℂ) (L : ℕ) :
    reducedDensityMatrix (frameParticle (transportFrame u U) z L) =
      (U : Matrix A A ℂ) * reducedDensityMatrix (frameParticle u z L) * (U : Matrix A A ℂ)ᴴ := by
  rw [frameParticle_transport, purificationEquiv_apply, reduced_conjugatePurification]

theorem unitaryRegister_eq_matrixRegister (U : unitary (Matrix A A ℂ)) :
    (unitaryRegister U).toContinuousLinearMap = matrixRegister (U : Matrix A A ℂ) := by
  ext x a
  exact unitaryRegister_apply U x a

def unitaryChannel (U : unitary (Matrix A A ℂ)) : QuantumChannel (Register A) (Register A) :=
  QuantumChannel.ofIsometry (unitaryRegister U)

theorem unitaryChannel_registerLift (U : unitary (Matrix A A ℂ)) (X : Matrix A A ℂ) :
    (unitaryChannel U).toLinearMap (registerLiftCLM X) =
      registerLiftCLM ((U : Matrix A A ℂ) * X * (U : Matrix A A ℂ)ᴴ) := by
  change conjugationLinearMap (unitaryRegister U).toContinuousLinearMap (registerLiftCLM X) = _
  rw [unitaryRegister_eq_matrixRegister, conjugation_matrixRegister]

def tensorUnitary (U : unitary (Matrix A A ℂ)) (L : ℕ) :
    unitary (Matrix (Fin L → A) (Fin L → A) ℂ) :=
  ⟨tensorPower L (U : Matrix A A ℂ), by
    apply Matrix.mem_unitaryGroup_iff'.mpr
    change (tensorPower L (U : Matrix A A ℂ))ᴴ * tensorPower L (U : Matrix A A ℂ) = 1
    have hU : (U : Matrix A A ℂ)ᴴ * U = 1 := Unitary.star_mul_self_of_mem U.property
    rw [← tensorPower_star, ← tensorPower_mul, hU, tensorPower_one]⟩

theorem tensor_unitaryChannel_matrixTensorPower (U : unitary (Matrix A A ℂ))
    (X : Matrix A A ℂ) (L : ℕ) :
    (unitaryChannel (tensorUnitary U L)).toLinearMap (matrixTensorPower X L) =
      matrixTensorPower ((U : Matrix A A ℂ) * X * (U : Matrix A A ℂ)ᴴ) L := by
  simp only [matrixTensorPower_eq_registerLift, unitaryChannel_registerLift, tensorUnitary,
    tensorPower_mul, tensorPower_star]

end Cloning.PCTUnitaryTransport
