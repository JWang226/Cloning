import Cloning.TensorCartanStateCovariance

/-! Unitary covariance of the full all-input Cartan CPTP map, derived from
literal physical tensor actions and the exact compression formula. -/
noncomputable section
open scoped BigOperators InnerProductSpace Matrix
namespace Cloning.TensorLie
open Cloning.PCT Cloning.InfiniteTraceClass
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
private theorem compression_covariance_algebra {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (V : H →L[ℂ] K) (S : H →L[ℂ] H) (W T : K →L[ℂ] K)
    (hleft : V.adjoint.comp W = S.comp V.adjoint)
    (hright : W.adjoint.comp V = V.comp S.adjoint) :
    V.adjoint.comp ((W.comp (T.comp W.adjoint)).comp V) =
      S.comp ((V.adjoint.comp (T.comp V)).comp S.adjoint) := by
  calc
    _ = (V.adjoint.comp W).comp (T.comp (W.adjoint.comp V)) := by
      simp only [ContinuousLinearMap.comp_assoc]
    _ = (S.comp V.adjoint).comp (T.comp (V.comp S.adjoint)) :=
      congrArg₂ (fun (L : K →L[ℂ] H) (R : H →L[ℂ] K) ↦ L.comp (T.comp R)) hleft hright
    _ = _ := by simp only [ContinuousLinearMap.comp_assoc]

variable {d : ℕ}
local instance (n d : ℕ) : FiniteDimensional ℂ (TensorRegister n (Fin d)) :=
  (registerBasis (Fin n → Fin d)).toOrthonormalBasis.toBasis.finiteDimensional_of_finite

theorem cartanInclusion_adjoint_tensorAction
    (mu nu : Fin d → ℕ) (hmu : Antitone mu) (hnu : Antitone nu)
    (X : Matrix (Fin d) (Fin d) ℂ) :
    (cartanInclusion mu nu hmu hnu).toContinuousLinearMap.adjoint.comp
      (cartanProductAction mu nu hmu hnu X) =
      (partitionTensorAction (fun i ↦ mu i + nu i) (sumPartition_antitone mu nu hmu hnu) X).comp
        (cartanInclusion mu nu hmu hnu).toContinuousLinearMap.adjoint := by
  have h := congrArg ContinuousLinearMap.adjoint (cartanInclusion_tensorAction mu nu hmu hnu Xᴴ)
  simpa only [ContinuousLinearMap.adjoint_comp, partitionTensorAction,
    cyclicTensorOperator_star, cartanProductAction_star, ContinuousLinearMap.adjoint_adjoint] using h.symm

/-- Exact covariance, on every complex trace-class input, under the actual
restricted physical unitary tensor powers. -/
theorem physicalCartanChannel_covariant
    (mu nu : Fin d → ℕ) (hmu : Antitone mu) (hnu : Antitone nu)
    (U : Matrix (Fin d) (Fin d) ℂ) (hU : Uᴴ * U = 1)
    (A : TraceClass (cyclicSector (partitionHighestTensor mu hmu))) :
    (physicalCartanChannel mu nu hmu hnu).toLinearMap
      (conjugationLinearMap (partitionTensorAction mu hmu U) A) =
    conjugationLinearMap
      (partitionTensorAction (fun i ↦ mu i + nu i) (sumPartition_antitone mu nu hmu hnu) U)
      ((physicalCartanChannel mu nu hmu hnu).toLinearMap A) := by
  let V := (cartanInclusion mu nu hmu hnu).toContinuousLinearMap
  let W := cartanProductAction mu nu hmu hnu U
  let S := partitionTensorAction (fun i ↦ mu i + nu i) (sumPartition_antitone mu nu hmu hnu) U
  let T := cartanProductOperator mu nu hmu hnu A.1
  have hleft : V.adjoint.comp W = S.comp V.adjoint :=
    cartanInclusion_adjoint_tensorAction mu nu hmu hnu U
  have hright : W.adjoint.comp V = V.comp S.adjoint := by
    have h := cartanInclusion_tensorAction mu nu hmu hnu Uᴴ
    simpa only [partitionTensorAction, cyclicTensorOperator_star, cartanProductAction_star] using h.symm
  have hprod : cartanProductOperator mu nu hmu hnu
      (operatorConjugation (partitionTensorAction mu hmu U) A.1) = W.comp (T.comp W.adjoint) := by
    have h := cartanProductOperator_conjugate mu nu hmu hnu U hU A.1
    rw [show partitionTensorAction mu hmu Uᴴ = (partitionTensorAction mu hmu U).adjoint from
      cyclicTensorOperator_star _ _ _ _ U, cartanProductAction_star] at h
    exact h
  have hcomp := compression_covariance_algebra V S W T hleft hright
  let r : ℂ := (((partitionDimension mu hmu : ℝ) /
    (partitionDimension _ (sumPartition_antitone mu nu hmu hnu) : ℝ)) : ℂ)
  have hcin := physicalCartanChannel_operator mu nu hmu hnu
    (conjugationLinearMap (partitionTensorAction mu hmu U) A)
  have hcout := physicalCartanChannel_operator mu nu hmu hnu A
  apply Subtype.ext
  calc
    _ = r • V.adjoint.comp ((cartanProductOperator mu nu hmu hnu
        (operatorConjugation (partitionTensorAction mu hmu U) A.1)).comp V) := hcin
    _ = r • V.adjoint.comp ((W.comp (T.comp W.adjoint)).comp V) :=
      congrArg (fun (Z : tensorProductSector (cyclicSector (partitionHighestTensor mu hmu))
          (cyclicSector (partitionHighestTensor nu hnu)) →L[ℂ]
          tensorProductSector (cyclicSector (partitionHighestTensor mu hmu))
            (cyclicSector (partitionHighestTensor nu hnu))) ↦ r • V.adjoint.comp (Z.comp V)) hprod
    _ = r • S.comp ((V.adjoint.comp (T.comp V)).comp S.adjoint) :=
      congrArg (fun (Z : cyclicSector (partitionHighestTensor _ (sumPartition_antitone mu nu hmu hnu)) →L[ℂ]
        cyclicSector (partitionHighestTensor _ (sumPartition_antitone mu nu hmu hnu))) ↦ r • Z) hcomp
    _ = operatorConjugation S (r • V.adjoint.comp (T.comp V)) :=
      ((operatorConjugation S).map_smul r (V.adjoint.comp (T.comp V))).symm
    _ = _ := congrArg (operatorConjugation S) hcout.symm

end Cloning.TensorLie
