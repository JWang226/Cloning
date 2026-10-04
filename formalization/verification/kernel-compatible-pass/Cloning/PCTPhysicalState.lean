import Cloning.PCTGlobalPhysical
import Cloning.PCTTangentChartFrame
import Cloning.PCTMixedMixtureTransfer
import Cloning.MatrixFidelityScaling

/-! Concrete normalized positive tensor states used in the physical PCT
comparison. No positivity, normalization, or integrability premise is hidden
in the statistical-model packaging. -/
noncomputable section
open scoped BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace ComplexOrder Topology
open MeasureTheory Filter Cloning.InfiniteTraceClass Cloning.Hybrid
namespace Cloning.PCTPhysicalState
open Cloning.PCT Cloning.PCTReducedGaussian Cloning.PCTPurificationChannel
open Cloning.InfiniteFiniteCorner
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]

def diagonalState (p : A → ℝ) (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) :
    Cloning.MatrixFidelity.State A where
  matrix := Matrix.diagonal (fun i => (p i : ℂ))
  positive := Matrix.PosSemidef.diagonal (fun i => Complex.nonneg_iff.mpr ⟨hp i, rfl⟩)
  trace_one := by rw [Matrix.trace_diagonal, ← Complex.ofReal_sum, hs, Complex.ofReal_one]

theorem canonicalPurification_diagonal (p : A → ℝ) (hp : ∀ i, 0 ≤ p i) :
    canonicalPurification (Matrix.diagonal (fun i => (p i : ℂ))) =
      coefficientVector (schmidtCoefficients p) := by
  rw [canonicalPurification, Cloning.MatrixFidelity.sqrt_diagonal_real p hp]
  rfl

theorem tensorPower_posSemidef (ρ : Matrix A A ℂ) (hρ : ρ.PosSemidef) (L : ℕ) :
    (tensorPower L ρ).PosSemidef := by
  have h : ρ = CFC.sqrt ρ * (CFC.sqrt ρ)ᴴ := by
    rw [Cloning.MatrixFidelity.sqrt_conjTranspose, Cloning.MatrixFidelity.sqrt_mul_self hρ]
  rw [h, tensorPower_mul, tensorPower_star]
  exact Matrix.posSemidef_self_mul_conjTranspose _

@[simp] theorem matrixTensorPower_eq_registerLift (ρ : Matrix A A ℂ) (L : ℕ) :
    matrixTensorPower ρ L = registerLiftCLM (tensorPower L ρ) := rfl

def tensorState (ρ : Cloning.MatrixFidelity.State A) (L : ℕ) :
    PositiveTraceClass (Register (Fin L → A)) :=
  ⟨matrixTensorPower ρ.matrix L,
    ofMatrix_nonneg (registerBasis _).orthonormal (tensorPower_posSemidef _ ρ.positive L)⟩

@[simp] theorem norm_tensorState (ρ : Cloning.MatrixFidelity.State A) (L : ℕ) :
    ‖(tensorState ρ L).1‖ = 1 := by
  rw [TraceClass.norm_eq_trace_re_of_nonneg _ (tensorState ρ L).2]
  change (trace (ofMatrix (registerBasis _) (tensorPower L ρ.matrix)) _).re = 1
  rw [trace_ofMatrix (registerBasis _).orthonormal, trace_tensorPower, ρ.trace_one, one_pow]
  rfl

theorem reducedDensityMatrix_posSemidef (ψ : Register (A × A)) :
    (reducedDensityMatrix ψ).PosSemidef := by
  let M : Matrix A A ℂ := fun a b => ψ (a,b)
  have he : reducedDensityMatrix ψ = M * Mᴴ := by
    ext a b
    simp only [M, reducedDensityMatrix, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [he]
  exact Matrix.posSemidef_self_mul_conjTranspose _

theorem trace_reducedDensityMatrix_complex (ψ : Register (A × A)) :
    Matrix.trace (reducedDensityMatrix ψ) = ((‖ψ‖ ^ 2 : ℝ) : ℂ) := by
  calc
    _ = ⟪ψ,ψ⟫_ℂ := by
      simp only [reducedDensityMatrix, Matrix.trace, Matrix.diag, lp.inner_eq_tsum,
        tsum_fintype, Fintype.sum_prod_type, RCLike.inner_apply, Complex.star_def]
    _ = _ := by rw [inner_self_eq_norm_sq_to_K]; push_cast; rfl

def reducedState (ψ : Register (A × A)) (hψ : ‖ψ‖ = 1) : Cloning.MatrixFidelity.State A where
  matrix := reducedDensityMatrix ψ
  positive := reducedDensityMatrix_posSemidef ψ
  trace_one := by rw [trace_reducedDensityMatrix_complex, hψ]; norm_num

def frameState {s : ℕ} (u : OrthonormalBasis (Fin (s+1)) ℂ (Register (A × A)))
    (z : Fin s → ℂ) (L : ℕ) : PositiveTraceClass (Register (Fin L → A)) :=
  tensorState (reducedState (frameParticle u z L) (frameParticle_norm u.orthonormal z L)) L

@[simp] theorem frameState_val {s : ℕ}
    (u : OrthonormalBasis (Fin (s+1)) ℂ (Register (A × A))) (z : Fin s → ℂ) (L : ℕ) :
    (frameState u z L).1 = matrixTensorPower (reducedDensityMatrix (frameParticle u z L)) L := rfl

@[simp] theorem norm_frameState {s : ℕ}
    (u : OrthonormalBasis (Fin (s+1)) ℂ (Register (A × A))) (z : Fin s → ℂ) (L : ℕ) :
    ‖(frameState u z L).1‖ = 1 := norm_tensorState _ _

theorem integrable_frameState {s : ℕ}
    (u : OrthonormalBasis (Fin (s+1)) ℂ (Register (A × A))) (L : ℕ)
    (ν : Measure (Fin s → ℂ)) [IsFiniteMeasure ν] :
    Integrable (fun z => (frameState u z L).1) ν :=
  integrable_reduced_product_mixture u.orthonormal L ν

def outputState {s : ℕ} (hcard : Fintype.card (A × A) = s+1)
    (ρ : Cloning.MatrixFidelity.State A) (n r : ℕ) :
    PositiveTraceClass (Register (Fin (n+r) → A)) :=
  (tensorState ρ n).map (Cloning.PCTGlobal.channel hcard n r).toPositiveTracePreservingMap

@[simp] theorem norm_outputState {s : ℕ} (hcard : Fintype.card (A × A) = s+1)
    (ρ : Cloning.MatrixFidelity.State A) (n r : ℕ) : ‖(outputState hcard ρ n r).1‖ = 1 := by
  rw [outputState, PositiveTraceClass.norm_map, norm_tensorState]

end Cloning.PCTPhysicalState
