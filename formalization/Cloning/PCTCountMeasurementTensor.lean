import Cloning.PCTCountMeasurementFidelity
import Cloning.CountMultinomialPMF
import Cloning.PCTPhysicalState

/-! The literal computational count measurement of tensor-product states is
the actual multinomial count PMF, with diagonal particle probabilities. -/
noncomputable section
open scoped BigOperators InnerProductSpace Matrix Classical ComplexOrder
namespace Cloning.PCTCountMeasurement
open Cloning.PCT Cloning.PCTReducedGaussian Cloning.InfiniteTraceClass Cloning.InfiniteFiniteCorner
open TensorLie Cloning.GeneralSymmetricOccupation
open Cloning.Hybrid Cloning.YoungGeneral Cloning.CountMultinomial Cloning.YoungMultinomial
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

def countWeight (d N : ℕ) (A : TraceClass (TensorRegister N (Fin d))) (s : Shape d N) : ℝ :=
  weightCLM (registerBasis (Word N d)) countShape s A

theorem countWeight_nonneg (d N : ℕ) (A : TraceClass (TensorRegister N (Fin d))) (hA : 0≤A.1)
    (s : Shape d N) : 0≤countWeight d N A s := weightCLM_nonneg _ _ _ A hA

theorem countWeight_l1_contraction (d N : ℕ) (A B : TraceClass (TensorRegister N (Fin d)))
    (hA : 0≤A.1) (hB : 0≤B.1) :
    (∑ s, |countWeight d N A s-countWeight d N B s|) ≤ ‖A-B‖ := by
  simpa only [countWeight, HilbertBasis.coe_toOrthonormalBasis] using
    weightCLM_l1_contraction (registerBasis (Word N d)).toOrthonormalBasis countShape A B hA hB

theorem count_rootFidelity_le (d N : ℕ) (A B : PositiveTraceClass (TensorRegister N (Fin d))) :
    A.rootFidelity B ≤ ∑ s, Real.sqrt (countWeight d N A.1 s * countWeight d N B.1 s) :=
  rootFidelity_le_measurement_affinity countShape A B

theorem countWeight_matrixTensorPower (d N : ℕ) (ρ : Matrix (Fin d) (Fin d) ℂ)
    (hρ : ρ.PosSemidef) (s : Shape d N) :
    countWeight d N (matrixTensorPower ρ N) s =
      ∑ w : Word N d, if countShape w=s then wordWeight (fun a => (ρ a a).re) w else 0 := by
  have hdiag (w : Word N d) :
      ⟪registerBasis (Word N d) w, (matrixTensorPower ρ N).1 (registerBasis (Word N d) w)⟫_ℂ =
        ∏ i, ρ (w i) (w i) := by
    change matrixOf (registerBasis (Word N d))
      (ofMatrix (registerBasis (Word N d)) (fun a c => ∏ i, ρ (a i) (c i))) w w = _
    rw [matrixOf_ofMatrix (registerBasis (Word N d)).orthonormal]
  have hr a : ρ a a = ((ρ a a).re : ℂ) := by
    have hp := Complex.nonneg_iff.mp (hρ.diag_nonneg (i := a))
    apply Complex.ext <;> simp [hp.2]
  unfold countWeight
  rw [weightCLM_apply]
  apply Finset.sum_congr rfl
  intro w _
  by_cases hw : countShape w=s
  · simp only [if_pos hw, hdiag]
    have he : (∏ i, ρ (w i) (w i)) = ∏ i, (((ρ (w i) (w i)).re : ℂ)) :=
      Finset.prod_congr rfl (fun i _ => hr (w i))
    rw [he, ← Complex.ofReal_prod, Complex.ofReal_re]
    rfl
  · simp only [if_neg hw]

def stateProbability {d : ℕ} (ρ : Cloning.MatrixFidelity.State (Fin d)) (i : Fin d) : ℝ :=
  (ρ.matrix i i).re

theorem stateProbability_nonneg {d : ℕ} (ρ : Cloning.MatrixFidelity.State (Fin d)) (i : Fin d) :
    0≤stateProbability ρ i := (Complex.nonneg_iff.mp (ρ.positive.diag_nonneg (i := i))).1

theorem stateProbability_sum {d : ℕ} (ρ : Cloning.MatrixFidelity.State (Fin d)) :
    ∑ i, stateProbability ρ i = 1 := by
  simpa only [Matrix.trace, Matrix.diag, Complex.re_sum, Complex.one_re, stateProbability] using
    congrArg Complex.re ρ.trace_one

/-- Exact product-state count law, before any central limit approximation. -/
theorem countWeight_tensorState {d : ℕ} (ρ : Cloning.MatrixFidelity.State (Fin (d+1)))
    (N : ℕ) (s : Shape (d+1) N) :
    countWeight (d+1) N (Cloning.PCTPhysicalState.tensorState ρ N).1 s =
      (countPMF (d+1) N (stateProbability ρ) (stateProbability_nonneg ρ) (stateProbability_sum ρ) s).toReal := by
  rw [countPMF_eq_sum]
  exact countWeight_matrixTensorPower (d+1) N ρ.matrix ρ.positive s

end Cloning.PCTCountMeasurement
