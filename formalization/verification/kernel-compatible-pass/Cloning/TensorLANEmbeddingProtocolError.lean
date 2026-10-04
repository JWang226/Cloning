import Cloning.TensorLANEmbeddingCellError
import Cloning.TensorLANEmbeddingAverageUniform
import Cloning.TensorLANEmbeddingFockProtocol
import Cloning.TensorLANEmbeddingClassicalUniform

/-! The exact physical chart protocol is controlled by the already proved
classical L1 error and actual weighted sector errors. -/
noncomputable section
open scoped BigOperators Topology Classical InnerProductSpace Matrix Matrix.Norms.L2Operator
open Filter MeasureTheory NormedSpace
namespace Cloning.TensorLAN
open Cloning.PCT Cloning.TensorLie Cloning.InfiniteTraceClass Cloning.Hybrid
open Cloning.PCTPhysicalFidelity Cloning.PhysicalCloningConverse Cloning.PCTLocalChart
open Cloning.PCTJointGaussianWhitening
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
variable {k s : ℕ}
local instance (n d : ℕ) : FiniteDimensional ℂ (TensorRegister n (Fin d)) :=
  (registerBasis (Fin n → Fin d)).toOrthonormalBasis.toBasis.finiteDimensional_of_finite
variable (p : SimpleSpectrum (k+1))
    (b : OrthonormalBasis (Fin (k+1)) ℝ (EuclideanSpace ℝ (Fin (k+1))))
    (hb : b 0 = sqrtSpectrum p.eigenvalue) (e : Fin s ≃ PairIndex (k+1))

def classicalLocalError (N : ℕ) (h : Fin (k+1) → ℝ) : ℝ :=
  ∫ y, |physicalLabelDensity p.eigenvalue p.positive b hb N (localSpectrum p.eigenvalue h N) y-
    translatedStandardDensity (whiten p.eigenvalue b h) y|

theorem rotated_local_tensor (N : ℕ) (θ : Parameters k) :
    matrixTensorPower
      (exp (sampleScale N • orbitalGenerator p.eigenvalue θ.2)*
        Matrix.diagonal (fun a => (localSpectrum p.eigenvalue θ.1 N a : ℂ))*
          (exp (sampleScale N • orbitalGenerator p.eigenvalue θ.2))ᴴ) N = chartTensor p θ N := by
  have hs := localUnitary_star p θ N
  change (exp (sampleScale N • orbitalGenerator p.eigenvalue θ.2))ᴴ = _ at hs
  rw [hs]
  rfl

theorem physicalCoordinate_errors_le (N Q : ℕ) (hN : 0 < N) (θ : Parameters k)
    (hzero : ∑ a, θ.1 a = 0) (hr : ∀ a, 0 < localSpectrum p.eigenvalue θ.1 N a) :
    ‖(physicalCoordinateForward p b hb e N Q).map (chartTensor p θ N)-(model p b e θ).1‖ ≤
      2*physicalForwardAverage N Q (localSpectrum p.eigenvalue θ.1 N) p.eigenvalue θ.2 +
        2*classicalLocalError p b hb N θ.1 ∧
    ‖(physicalCoordinateReverse p b hb e N Q).map (model p b e θ).1-chartTensor p θ N‖ ≤
      2*physicalReverseAverage N Q (localSpectrum p.eigenvalue θ.1 N) p.eigenvalue θ.2 +
        2*classicalLocalError p b hb N θ.1 := by
  let r := localSpectrum p.eigenvalue θ.1 N
  let U := exp (sampleScale N • orbitalGenerator p.eigenvalue θ.2)
  let σ := rootDisplacedThermal p.eigenvalue θ.2
  let f := translatedStandardDensity (whiten p.eigenvalue b θ.1)
  let hf := integrable_translatedStandardDensity (whiten p.eigenvalue b θ.1)
  have hσ : ‖σ‖ = 1 := rootDisplacedThermal_norm p.eigenvalue p.positive p.strictAnti θ.2
  have hsf := physicalCellForward_rotated_error p.eigenvalue p.positive b hb N Q U r hr σ f hf
  have hsr := physicalCellReverse_rotated_error p.eigenvalue p.positive b hb N Q hN U r hr
    (localSpectrum_sum p.eigenvalue θ.1 p.normalized hzero N) σ f hf
  have hfsum : (∑ i : SchurCopy N (k+1), ((recursivePhysicalDecomposition N (k+1)).get i).character r *
      ‖(copyToFock N (k+1) Q i).toLinearMap
        (canonicalRotatedGibbs ((recursivePhysicalDecomposition N (k+1)).get i) U r)-σ‖) =
      physicalForwardAverage N Q r p.eigenvalue θ.2 := by
    unfold physicalForwardAverage
    apply Finset.sum_congr rfl
    intro i _
    have he := canonicalRotatedGibbs_eq_partitionPhysicalGibbs
      ((recursivePhysicalDecomposition N (k+1)).get i) r p.eigenvalue θ.2
    exact congrArg (fun A : TraceClass ((recursivePhysicalDecomposition N (k+1)).get i).CanonicalSector => ((recursivePhysicalDecomposition N (k+1)).get i).character r *
      ‖(copyToFock N (k+1) Q i).toLinearMap A-σ‖) he
  have hrsum : (∑ i : SchurCopy N (k+1), ((recursivePhysicalDecomposition N (k+1)).get i).character r *
      ‖(fockToSectorTotal (partitionHighestTensor ((recursivePhysicalDecomposition N (k+1)).get i).weight
          ((recursivePhysicalDecomposition N (k+1)).get i).weight_antitone)
        ((recursivePhysicalDecomposition N (k+1)).get i).weight Q (partitionHighestTensor_norm ((recursivePhysicalDecomposition N (k+1)).get i).weight
          ((recursivePhysicalDecomposition N (k+1)).get i).weight_antitone)).toLinearMap σ-
        canonicalRotatedGibbs ((recursivePhysicalDecomposition N (k+1)).get i) U r‖) =
      physicalReverseAverage N Q r p.eigenvalue θ.2 := by
    unfold physicalReverseAverage
    apply Finset.sum_congr rfl
    intro i _
    have he := canonicalRotatedGibbs_eq_partitionPhysicalGibbs
      ((recursivePhysicalDecomposition N (k+1)).get i) r p.eigenvalue θ.2
    exact congrArg (fun A : TraceClass ((recursivePhysicalDecomposition N (k+1)).get i).CanonicalSector => ((recursivePhysicalDecomposition N (k+1)).get i).character r *
      ‖(fockToSectorTotal (partitionHighestTensor ((recursivePhysicalDecomposition N (k+1)).get i).weight
          ((recursivePhysicalDecomposition N (k+1)).get i).weight_antitone)
        ((recursivePhysicalDecomposition N (k+1)).get i).weight Q (partitionHighestTensor_norm ((recursivePhysicalDecomposition N (k+1)).get i).weight
          ((recursivePhysicalDecomposition N (k+1)).get i).weight_antitone)).toLinearMap σ-A‖) he
  have hT : matrixTensorPower (U*Matrix.diagonal (fun a => (r a : ℂ))*Uᴴ) N = chartTensor p θ N :=
    rotated_local_tensor p N θ
  have hf' : ‖(physicalCellForward p.eigenvalue p.positive b hb N Q).map
      (chartTensor p θ N)-prepareL1 f hf σ‖ ≤
      physicalForwardAverage N Q r p.eigenvalue θ.2 + classicalLocalError p b hb N θ.1 := by
    calc
      _ = ‖(physicalCellForward p.eigenvalue p.positive b hb N Q).map
          (matrixTensorPower (U*Matrix.diagonal (fun a => (r a : ℂ))*Uᴴ) N)-prepareL1 f hf σ‖ :=
        congrArg (fun A => ‖(physicalCellForward p.eigenvalue p.positive b hb N Q).map A-prepareL1 f hf σ‖) hT.symm
      _ ≤ _ := hsf
      _ = _ := congrArg₂ (fun x y : ℝ => x+y) hfsum
        ((congrArg (fun x : ℝ => classicalLocalError p b hb N θ.1*x) hσ).trans (mul_one _))
  have hr' : ‖(physicalCellReverse p.eigenvalue p.positive b hb N Q).map
      (prepareL1 f hf σ)-chartTensor p θ N‖ ≤
      2*physicalReverseAverage N Q r p.eigenvalue θ.2 + 2*classicalLocalError p b hb N θ.1 := by
    calc
      _ = ‖(physicalCellReverse p.eigenvalue p.positive b hb N Q).map (prepareL1 f hf σ)-
          matrixTensorPower (U*Matrix.diagonal (fun a => (r a : ℂ))*Uᴴ) N‖ :=
        congrArg (fun A => ‖(physicalCellReverse p.eigenvalue p.positive b hb N Q).map (prepareL1 f hf σ)-A‖) hT.symm
      _ ≤ _ := hsr
      _ = _ := congrArg₂ (fun x y : ℝ => x+y)
        (congrArg (fun x : ℝ => 2*x) hrsum)
        ((congrArg (fun x : ℝ => 2*classicalLocalError p b hb N θ.1*x) hσ).trans (mul_one _))
  constructor
  · have hh := physicalCoordinateForward_error_le p b hb e N Q θ (chartTensor p θ N)
    exact hh.trans ((mul_le_mul_of_nonneg_left hf' (by norm_num)).trans_eq (by ring))
  · have he := physicalCoordinateReverse_model p b hb e N Q θ
    exact (congrArg (fun A => ‖A-chartTensor p θ N‖) he).le.trans hr'

end Cloning.TensorLAN
