import Cloning.PCTPhysicalFidelityLAN
import Cloning.PCTJointGaussianChart
import Cloning.TensorCloningPayoff
import Cloning.TensorGibbsLocalUnitary

/-! Literal local physical states and the exact change of sample size needed
by the cloning converse. No LAN approximation is asserted here. -/
noncomputable section
open scoped BigOperators Topology Matrix Matrix.Norms.L2Operator
open Filter NormedSpace
namespace Cloning.PhysicalCloningConverse
open Cloning.PCT Cloning.PCTLocalChart Cloning.PCTPhysicalFidelity
open Cloning.PCTPhysicalState Cloning.PCTUnitaryTransport Cloning.PCTJointGaussianWhitening
open Cloning.TensorLie Cloning.Hybrid
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
variable {k s : ℕ}
local instance : NormedAlgebra ℚ (Matrix (Fin (k+1)) (Fin (k+1)) ℂ) :=
  NormedAlgebra.restrictScalars ℚ ℂ _

def phaseParameters (p : SimpleSpectrum (k+1))
    (b : Fin (k+1) → EuclideanSpace ℝ (Fin (k+1))) (e : Fin s ≃ PairIndex (k+1))
    (ξ : PhaseSpace k s) : Parameters k :=
  (unwhiten p.eigenvalue b ξ.1, fun a => ξ.2 (e.symm a))

theorem continuous_phaseParameters (p : SimpleSpectrum (k+1))
    (b : Fin (k+1) → EuclideanSpace ℝ (Fin (k+1))) (e : Fin s ≃ PairIndex (k+1)) :
    Continuous (phaseParameters p b e) :=
  ((continuous_unwhiten p.eigenvalue b).comp continuous_fst).prodMk (by fun_prop)

theorem phaseParameters_sum_zero (p : SimpleSpectrum (k+1))
    (b : OrthonormalBasis (Fin (k+1)) ℝ (EuclideanSpace ℝ (Fin (k+1))))
    (hb : b 0 = sqrtSpectrum p.eigenvalue) (e : Fin s ≃ PairIndex (k+1))
    (ξ : PhaseSpace k s) : ∑ i, (phaseParameters p b e ξ).1 i = 0 :=
  unwhiten_sum_zero p.eigenvalue b hb ξ.1

theorem parameterTranslation_phaseParameters (p : SimpleSpectrum (k+1))
    (b : OrthonormalBasis (Fin (k+1)) ℝ (EuclideanSpace ℝ (Fin (k+1))))
    (e : Fin s ≃ PairIndex (k+1)) (ξ : PhaseSpace k s) :
    parameterTranslation p b e (phaseParameters p b e ξ) = ξ := by
  apply Prod.ext
  · exact whiten_unwhiten p.eigenvalue p.positive b ξ.1
  · funext i
    exact congrArg ξ.2 (e.symm_apply_apply i)

theorem compact_phaseParameters (p : SimpleSpectrum (k+1))
    (b : Fin (k+1) → EuclideanSpace ℝ (Fin (k+1))) (e : Fin s ≃ PairIndex (k+1))
    (K : Set (PhaseSpace k s)) (hK : IsCompact K) :
    IsCompact (phaseParameters p b e '' K) := hK.image (continuous_phaseParameters p b e)

def localEigenvalues (p : SimpleSpectrum (k+1)) (θ : Parameters k) (n : ℕ) : Fin (k+1) → ℝ :=
  fun i => p.eigenvalue i + sampleScale n * θ.1 i

theorem localEigenvalues_sum (p : SimpleSpectrum (k+1)) (θ : Parameters k) (n : ℕ)
    (hθ : ∑ i, θ.1 i = 0) : ∑ i, localEigenvalues p θ n i = 1 := by
  simp only [localEigenvalues, Finset.sum_add_distrib, ← Finset.mul_sum, hθ,
    mul_zero, add_zero, p.normalized]

def localUnitary (p : SimpleSpectrum (k+1)) (θ : Parameters k) (n : ℕ) :
    unitary (Matrix (Fin (k+1)) (Fin (k+1)) ℂ) :=
  ⟨exp (sampleScale n • orbitalGenerator p.eigenvalue θ.2), by
    apply exp_mem_unitary_of_mem_skewAdjoint
    change star (sampleScale n • orbitalGenerator p.eigenvalue θ.2) = _
    rw [star_smul, star_trivial]
    change sampleScale n • (orbitalGenerator p.eigenvalue θ.2)ᴴ = _
    rw [orbitalGenerator_star, smul_neg]⟩

theorem localUnitary_star (p : SimpleSpectrum (k+1)) (θ : Parameters k) (n : ℕ) :
    ((localUnitary p θ n : Matrix (Fin (k+1)) (Fin (k+1)) ℂ))ᴴ =
      exp (-(sampleScale n • orbitalGenerator p.eigenvalue θ.2)) := by
  change star (exp (sampleScale n • orbitalGenerator p.eigenvalue θ.2)) = _
  rw [star_exp, star_smul, star_trivial]
  change exp (sampleScale n • (orbitalGenerator p.eigenvalue θ.2)ᴴ) = _
  rw [orbitalGenerator_star, smul_neg]

def localState (p : SimpleSpectrum (k+1)) (θ : Parameters k) (n : ℕ)
    (hθ : ∑ i, θ.1 i = 0) (hp : ∀ i, 0 ≤ localEigenvalues p θ n i) :
    Cloning.MatrixFidelity.State (Fin (k+1)) :=
  conjugatedState (diagonalState (localEigenvalues p θ n) hp (localEigenvalues_sum p θ n hθ))
    (localUnitary p θ n)

@[simp] theorem localState_matrix (p : SimpleSpectrum (k+1)) (θ : Parameters k) (n : ℕ)
    (hθ : ∑ i, θ.1 i = 0) (hp : ∀ i, 0 ≤ localEigenvalues p θ n i) :
    (localState p θ n hθ hp).matrix = chartMatrix p θ n := by
  change _ * _ * ((localUnitary p θ n : Matrix (Fin (k+1)) (Fin (k+1)) ℂ))ᴴ = _
  rw [localUnitary_star]
  rfl

@[simp] theorem tensorState_localState (p : SimpleSpectrum (k+1)) (θ : Parameters k) (n : ℕ)
    (hθ : ∑ i, θ.1 i = 0) (hp : ∀ i, 0 ≤ localEigenvalues p θ n i) :
    (tensorState (localState p θ n hθ hp) n).1 = chartTensor p θ n := by
  change matrixTensorPower (localState p θ n hθ hp).matrix n = _
  rw [localState_matrix]
  rfl

theorem orbitalGenerator_smul (p : Fin (k+1) → ℝ) (c : ℝ) (z : PairIndex (k+1) → ℂ) :
    orbitalGenerator p (c • z) = c • orbitalGenerator p z := by
  ext i j
  simp only [orbitalGenerator, Pi.smul_apply, star_smul, star_trivial,
    Matrix.smul_apply, smul_neg, smul_div_assoc, smul_ite, smul_zero]
  split_ifs <;> simp <;> ring

/-- The finite-sample output displacement factor, before its asymptotic limit. -/
def sampleRatio (n m : ℕ) : ℝ := Real.sqrt (m : ℝ) / Real.sqrt (n : ℝ)

theorem sampleScale_mul_sampleRatio (n m : ℕ) (hm : 0 < m) :
    sampleScale m * sampleRatio n m = sampleScale n := by
  unfold sampleScale sampleRatio
  have hm' : Real.sqrt (m : ℝ) ≠ 0 := (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hm)).ne'
  field_simp

/-- The same physical one-site state has exactly the rescaled output LAN parameter. -/
theorem chartMatrix_rescale (p : SimpleSpectrum (k+1)) (θ : Parameters k)
    (n m : ℕ) (hm : 0 < m) :
    chartMatrix p (sampleRatio n m • θ) m = chartMatrix p θ n := by
  unfold chartMatrix
  simp only [Prod.smul_fst, Prod.smul_snd, orbitalGenerator_smul, smul_smul,
    sampleScale_mul_sampleRatio n m hm, Pi.smul_apply, smul_eq_mul, ← mul_assoc]

theorem tensorState_localState_output (p : SimpleSpectrum (k+1)) (θ : Parameters k)
    (n m : ℕ) (hm : 0 < m) (hθ : ∑ i, θ.1 i = 0)
    (hp : ∀ i, 0 ≤ localEigenvalues p θ n i) :
    (tensorState (localState p θ n hθ hp) m).1 =
      chartTensor p (sampleRatio n m • θ) m := by
  change matrixTensorPower (localState p θ n hθ hp).matrix m =
    matrixTensorPower (chartMatrix p (sampleRatio n m • θ) m) m
  rw [localState_matrix, chartMatrix_rescale p θ n m hm]

theorem sampleRatio_tendsto (m : ℕ → ℕ) (g : ℝ)
    (hg : Tendsto (fun n => (m n : ℝ)/(n : ℝ)) atTop (𝓝 g)) :
    Tendsto (fun n => sampleRatio n (m n)) atTop (𝓝 (Real.sqrt g)) := by
  have he : (fun n => sampleRatio n (m n)) = (fun n => Real.sqrt ((m n : ℝ)/(n : ℝ))) := by
    funext n
    exact (Real.sqrt_div (Nat.cast_nonneg (m n)) (n : ℝ)).symm
  rw [he]
  exact Real.continuous_sqrt.continuousAt.tendsto.comp hg

end Cloning.PhysicalCloningConverse
