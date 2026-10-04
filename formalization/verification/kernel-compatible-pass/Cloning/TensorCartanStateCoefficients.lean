import Cloning.TensorCartanStateProduct
import Cloning.TensorGibbsStateLimit
import Cloning.TensorFlatProjectorDimensionLimit

/-! Exact finite-corner formula for the actual Cartan output of a sector Gibbs state. -/
noncomputable section
open scoped BigOperators InnerProductSpace Matrix Kronecker ComplexOrder Topology
open Filter
namespace Cloning.TensorLie
open Cloning.PCT Cloning.InfiniteTraceClass
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
variable {d : ℕ}
local instance (n d : ℕ) : FiniteDimensional ℂ (TensorRegister n (Fin d)) :=
  (registerBasis (Fin n → Fin d)).toOrthonormalBasis.toBasis.finiteDimensional_of_finite

section Generic
variable {K I J : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [Fintype I] [Fintype J]

theorem inner_operator_of_finite_expansion (B : K →L[ℂ] K) (x y : K)
    (v : I → J → K) (a c : I → J → ℂ) (lam : I → ℂ)
    (hy : y = ∑ i, ∑ j, c i j • v i j)
    (ha : ∀ i j, ⟪v i j,x⟫_ℂ = a i j)
    (hB : ∀ i j, B (v i j) = lam i • v i j) :
    ⟪x,B y⟫_ℂ = ∑ i, ∑ j, starRingEnd ℂ (a i j) * lam i * c i j := by
  rw [hy]
  simp only [map_sum, map_smul, hB, inner_sum, inner_smul_right]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have hi : ⟪x,v i j⟫_ℂ = starRingEnd ℂ (a i j) := by
    rw [← ha i j]
    exact (inner_conj_symm _ _).symm
  rw [hi]
  ring
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [CompleteSpace K]

theorem inner_scaled_adjoint_compression (V : H →L[ℂ] K) (B : K →L[ℂ] K)
    (c : ℂ) (x y : H) :
    ⟪x,(c • V.adjoint.comp (B.comp V)) y⟫_ℂ = c * ⟪V x,B (V y)⟫_ℂ := by
  simp only [ContinuousLinearMap.smul_apply, inner_smul_right,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right]

theorem traceCLM_quantumChannel (Φ : QuantumChannel H K) (A : TraceClass H) :
    traceCLM (Φ.toLinearMap A) = traceCLM A := Φ.trace_preserving A

end Generic

theorem physicalCartanChannel_cutoff_coefficient
    (mu nu : Fin d → ℕ) (hmu : Antitone mu) (hnu : Antitone nu) (R : ℕ)
    (hmuGap : ∀ a : PositiveRoot d, 0 < rootGap mu a)
    (hnuGap : ∀ a : PositiveRoot d, 0 < rootGap nu a)
    (hmuLI : LinearIndependent ℂ (cutoffRawFrame (partitionHighestTensor mu hmu) mu R))
    (hnuLI : LinearIndependent ℂ (cutoffRawFrame (partitionHighestTensor nu hnu) nu R))
    (A : TraceClass (cyclicSector (partitionHighestTensor mu hmu))) (lam : CutoffIndex d R → ℂ)
    (hA : ∀ j, A.1 (cutoffSectorFrame (partitionHighestTensor mu hmu) mu R j) =
      lam j • cutoffSectorFrame (partitionHighestTensor mu hmu) mu R j)
    (i l : CutoffIndex d R) :
    ⟪cutoffSectorFrame (partitionHighestTensor _ (sumPartition_antitone mu nu hmu hnu))
        (fun a => mu a + nu a) R i,
      ((physicalCartanChannel mu nu hmu hnu).toLinearMap A).1
        (cutoffSectorFrame (partitionHighestTensor _ (sumPartition_antitone mu nu hmu hnu))
          (fun a => mu a + nu a) R l)⟫_ℂ =
      ((((partitionDimension mu hmu : ℝ) /
        (partitionDimension _ (sumPartition_antitone mu nu hmu hnu) : ℝ)) : ℂ)) *
      ∑ j : CutoffIndex d R, ∑ k : CutoffIndex d R,
        starRingEnd ℂ (cartanCutoffFrameMatrixElement mu nu hmu hnu R i j k) *
          lam j * cartanCutoffFrameMatrixElement mu nu hmu hnu R l j k := by
  let H := cyclicSector (partitionHighestTensor _ (sumPartition_antitone mu nu hmu hnu))
  let x : H := cutoffSectorFrame _ (fun a => mu a + nu a) R i
  let y : H := cutoffSectorFrame _ (fun a => mu a + nu a) R l
  let V := (cartanInclusion mu nu hmu hnu).toContinuousLinearMap
  let B := cartanProductOperator mu nu hmu hnu A.1
  let c : ℂ := ((partitionDimension mu hmu : ℝ) /
    (partitionDimension _ (sumPartition_antitone mu nu hmu hnu) : ℝ))
  have he := congrArg (fun (T : H →L[ℂ] H) => ⟪x,T y⟫_ℂ)
    (physicalCartanChannel_operator mu nu hmu hnu A)
  have he' := inner_scaled_adjoint_compression V B c x y
  have hexp : ⟪V x,B (V y)⟫_ℂ =
      ∑ j : CutoffIndex d R, ∑ k : CutoffIndex d R,
        starRingEnd ℂ (cartanCutoffFrameMatrixElement mu nu hmu hnu R i j k) *
          lam j * cartanCutoffFrameMatrixElement mu nu hmu hnu R l j k := by
    apply inner_operator_of_finite_expansion B (V x) (V y)
      (fun j k => cartanProductVector mu nu hmu hnu
        (cutoffSectorFrame (partitionHighestTensor mu hmu) mu R j)
        (cutoffSectorFrame (partitionHighestTensor nu hnu) nu R k))
      (fun j k => cartanCutoffFrameMatrixElement mu nu hmu hnu R i j k)
      (fun j k => cartanCutoffFrameMatrixElement mu nu hmu hnu R l j k) lam
    · exact cartanInclusion_cutoff_product_expansion mu nu hmu hnu R hmuGap hnuGap hmuLI hnuLI l
    · intro j k
      rfl
    · intro j k
      exact (cartanProductOperator_productVector mu nu hmu hnu A.1 _ _).trans
        ((congrArg (fun z => cartanProductVector mu nu hmu hnu z
          (cutoffSectorFrame (partitionHighestTensor nu hnu) nu R k)) (hA j)).trans
          (cartanProductVector_smul_left mu nu hmu hnu (lam j) _ _))
  exact he.trans (he'.trans (congrArg (fun z : ℂ => c * z) hexp))

def cartanGibbsOutput (mu nu : Fin d → ℕ) (hmu : Antitone mu) (hnu : Antitone nu)
    (p : Fin d → ℝ) :
    TraceClass (cyclicSector (partitionHighestTensor _ (sumPartition_antitone mu nu hmu hnu))) :=
  (physicalCartanChannel mu nu hmu hnu).toLinearMap
    (sectorGibbsDensity (partitionHighestTensor mu hmu) mu
      (partitionHighestTensor_cartan mu hmu) (partitionHighestTensor_raising_zero mu hmu) p)

theorem cartanGibbsOutput_nonneg (mu nu : Fin d → ℕ) (hmu : Antitone mu) (hnu : Antitone nu)
    (p : Fin d → ℝ) (hp : ∀ a, 0 < p a) : 0 ≤ (cartanGibbsOutput mu nu hmu hnu p).1 :=
  (physicalCartanChannel mu nu hmu hnu).map_nonneg _
    (sectorGibbsDensity_nonneg _ _ _ _ (partitionHighestTensor_norm mu hmu) p hp)

theorem cartanGibbsOutput_trace (mu nu : Fin d → ℕ) (hmu : Antitone mu) (hnu : Antitone nu)
    (p : Fin d → ℝ) (hp : ∀ a, 0 < p a) : traceCLM (cartanGibbsOutput mu nu hmu hnu p) = 1 := by
  exact (traceCLM_quantumChannel (physicalCartanChannel mu nu hmu hnu)
    (sectorGibbsDensity (partitionHighestTensor mu hmu) mu
      (partitionHighestTensor_cartan mu hmu) (partitionHighestTensor_raising_zero mu hmu) p)).trans
    (sectorGibbsDensity_trace _ _ _ _ (partitionHighestTensor_norm mu hmu) p hp)

theorem cartanGibbsOutput_cutoff_coefficient
    (mu nu : Fin d → ℕ) (hmu : Antitone mu) (hnu : Antitone nu)
    (p : Fin d → ℝ) (hp : ∀ a, 0 < p a) (R : ℕ)
    (hmuGap : ∀ a : PositiveRoot d, 0 < rootGap mu a)
    (hnuGap : ∀ a : PositiveRoot d, 0 < rootGap nu a)
    (hmuLI : LinearIndependent ℂ (cutoffRawFrame (partitionHighestTensor mu hmu) mu R))
    (hnuLI : LinearIndependent ℂ (cutoffRawFrame (partitionHighestTensor nu hnu) nu R))
    (i l : CutoffIndex d R) :
    ⟪cutoffSectorFrame (partitionHighestTensor _ (sumPartition_antitone mu nu hmu hnu))
        (fun a => mu a + nu a) R i,
      (cartanGibbsOutput mu nu hmu hnu p).1
        (cutoffSectorFrame (partitionHighestTensor _ (sumPartition_antitone mu nu hmu hnu))
          (fun a => mu a + nu a) R l)⟫_ℂ =
      ((((partitionDimension mu hmu : ℝ) /
        (partitionDimension _ (sumPartition_antitone mu nu hmu hnu) : ℝ)) : ℂ)) *
      ∑ j : CutoffIndex d R, ∑ k : CutoffIndex d R,
        starRingEnd ℂ (cartanCutoffFrameMatrixElement mu nu hmu hnu R i j k) *
          (sectorOccupationWeight (partitionHighestTensor mu hmu) mu
            (partitionHighestTensor_cartan mu hmu) (partitionHighestTensor_raising_zero mu hmu)
            p (cutoffOccupation d R j).val : ℂ) *
          cartanCutoffFrameMatrixElement mu nu hmu hnu R l j k := by
  exact physicalCartanChannel_cutoff_coefficient mu nu hmu hnu R hmuGap hnuGap hmuLI hnuLI
    (sectorGibbsDensity (partitionHighestTensor mu hmu) mu
      (partitionHighestTensor_cartan mu hmu) (partitionHighestTensor_raising_zero mu hmu) p)
    (fun j => (sectorOccupationWeight (partitionHighestTensor mu hmu) mu
      (partitionHighestTensor_cartan mu hmu) (partitionHighestTensor_raising_zero mu hmu)
      p (cutoffOccupation d R j).val : ℂ))
    (sectorGibbsDensity_cutoffFrame (partitionHighestTensor mu hmu) mu
      (partitionHighestTensor_cartan mu hmu) (partitionHighestTensor_raising_zero mu hmu) p hp R) i l

end Cloning.TensorLie
