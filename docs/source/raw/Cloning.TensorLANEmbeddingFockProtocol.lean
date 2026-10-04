import Cloning.TensorLANEmbeddingFockStateCoordinates
import Cloning.TensorLANEmbeddingCellProtocol
import Cloning.HybridGaussianAttainmentChannel
import Cloning.IsometricRecovery

/-! Genuine physical LAN channels with arbitrary allowed Fock mode coordinates.
Both maps act on all complex inputs and use inverse unitary mode transports. -/
noncomputable section
open scoped BigOperators Topology Classical InnerProductSpace
open MeasureTheory Filter
namespace Cloning.Hybrid
open Cloning.InfiniteTraceClass
set_option backward.isDefEq.respectTransparency false
variable {X H K J : Type*} [MeasurableSpace X] {ν : Measure X}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup J] [InnerProductSpace ℂ J] [CompleteSpace J]

def QuantumToHybrid.postHybrid (Λ : Channel K J ν) (T : QuantumToHybrid H K ν) :
    QuantumToHybrid H J ν where
  map := Λ.map.comp T.map
  completelyPositive := fun n A hA => Λ.completelyPositive n _ (T.completelyPositive n A hA)
  tracePreserving := by
    intro A
    change integratedTrace (Λ.map (T.map A)) = traceCLM A
    exact (integratedTrace_apply (Λ.map (T.map A))).trans
      ((Λ.tracePreserving (T.map A)).trans
        ((integratedTrace_apply (T.map A)).symm.trans (T.tracePreserving A)))

def HybridToQuantum.preHybrid (S : HybridToQuantum K J ν) (Λ : Channel H K ν) :
    HybridToQuantum H J ν where
  map := S.map.comp Λ.map
  completelyPositive := fun n A hA => S.completelyPositive n _ (Λ.completelyPositive n A hA)
  tracePreserving := by
    intro A
    apply (S.tracePreserving (Λ.map A)).trans
    simpa only [integratedTrace_apply] using Λ.tracePreserving A

theorem fibreChannel_prepare (Φ : QuantumChannel H K) (f : X → ℝ) (hf : Integrable f ν)
    (A : TraceClass H) :
    (fibreChannel ν Φ).map (prepareL1 f hf A) = prepareL1 f hf (Φ.toLinearMap A) :=
  (prepareL1_compLp Φ.toPositiveTracePreservingMap.toContinuousLinearMap f hf A).symm

theorem isometryEquiv_conjugation_cancel (U : H ≃ₗᵢ[ℂ] K) (A : TraceClass H) :
    conjugationLinearMap U.symm.toLinearIsometry.toContinuousLinearMap
      (conjugationLinearMap U.toLinearIsometry.toContinuousLinearMap A) = A := by
  have h := conjugation_adjoint_isometry_cancel U.toLinearIsometry A
  have hadj : U.toLinearIsometry.toContinuousLinearMap.adjoint =
      U.symm.toLinearIsometry.toContinuousLinearMap := U.adjoint_eq_symm
  rw [hadj] at h
  exact h

end Cloning.Hybrid
namespace Cloning.TensorLAN
open Cloning.PCT Cloning.PCTJointGaussianWhitening Cloning.PCTPhysicalFidelity
open Cloning.Hybrid Cloning.InfiniteTraceClass Cloning.MultimodeCoherent Cloning.TensorLie
open Cloning.PhysicalCloningConverse
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {k s : ℕ}
local instance (n d : ℕ) : FiniteDimensional ℂ (TensorRegister n (Fin d)) :=
  (registerBasis (Fin n → Fin d)).toOrthonormalBasis.toBasis.finiteDimensional_of_finite
variable (p : SimpleSpectrum (k+1))
    (b : OrthonormalBasis (Fin (k+1)) ℝ (EuclideanSpace ℝ (Fin (k+1))))
    (hb : b 0 = sqrtSpectrum p.eigenvalue) (e : Fin s ≃ PairIndex (k+1))

def physicalCoordinateForward (N Q : ℕ) :
    QuantumToHybrid (TensorRegister N (Fin (k+1))) (Fock s) (volume : Measure (Fin k → ℝ)) :=
  QuantumToHybrid.postHybrid
    (fibreChannel volume (QuantumChannel.ofIsometry (rootFockReindex e).toLinearIsometry))
    (physicalCellForward p.eigenvalue p.positive b hb N Q)

def physicalCoordinateReverse (N Q : ℕ) :
    HybridToQuantum (Fock s) (TensorRegister N (Fin (k+1))) (volume : Measure (Fin k → ℝ)) :=
  HybridToQuantum.preHybrid (physicalCellReverse p.eigenvalue p.positive b hb N Q)
    (fibreChannel volume (QuantumChannel.ofIsometry (rootFockReindex e).symm.toLinearIsometry))

theorem physical_model_root_coordinates (θ : Parameters k) :
    (model p b e θ).1 =
      (fibreChannel volume (QuantumChannel.ofIsometry (rootFockReindex e).toLinearIsometry)).map
        (prepareL1 (translatedStandardDensity (whiten p.eigenvalue b θ.1))
          (integrable_translatedStandardDensity _) (rootDisplacedThermal p.eigenvalue θ.2)) := by
  rw [model_eq_prepare_translated, fibreChannel_prepare]
  exact congrArg (prepareL1 _ (integrable_translatedStandardDensity _))
    (rootFockReindex_displacedProductThermal p e θ.2).symm

theorem physicalCoordinateReverse_model (N Q : ℕ) (θ : Parameters k) :
    (physicalCoordinateReverse p b hb e N Q).map (model p b e θ).1 =
      (physicalCellReverse p.eigenvalue p.positive b hb N Q).map
        (prepareL1 (translatedStandardDensity (whiten p.eigenvalue b θ.1))
          (integrable_translatedStandardDensity _) (rootDisplacedThermal p.eigenvalue θ.2)) := by
  rw [physical_model_root_coordinates p b e θ]
  change (physicalCellReverse p.eigenvalue p.positive b hb N Q).map
    ((fibreChannel volume (QuantumChannel.ofIsometry (rootFockReindex e).symm.toLinearIsometry)).map
      ((fibreChannel volume (QuantumChannel.ofIsometry (rootFockReindex e).toLinearIsometry)).map _)) = _
  let f := translatedStandardDensity (whiten p.eigenvalue b θ.1)
  let hf := integrable_translatedStandardDensity (whiten p.eigenvalue b θ.1)
  let U := QuantumChannel.ofIsometry (rootFockReindex e).toLinearIsometry
  let V := QuantumChannel.ofIsometry (rootFockReindex e).symm.toLinearIsometry
  let σ := rootDisplacedThermal p.eigenvalue θ.2
  have h₁ := fibreChannel_prepare (ν := (volume : Measure (Fin k → ℝ))) U f hf σ
  have h₂ := fibreChannel_prepare (ν := (volume : Measure (Fin k → ℝ))) V f hf (U.toLinearMap σ)
  have h₃ := congrArg (prepareL1 f hf)
    (isometryEquiv_conjugation_cancel (rootFockReindex e) σ)
  exact congrArg ((physicalCellReverse p.eigenvalue p.positive b hb N Q).map)
    (((congrArg ((fibreChannel volume V).map) h₁).trans h₂).trans h₃)

theorem physicalCoordinateForward_error_le (N Q : ℕ) (θ : Parameters k)
    (A : TraceClass (TensorRegister N (Fin (k+1)))) :
    ‖(physicalCoordinateForward p b hb e N Q).map A-(model p b e θ).1‖ ≤
      2*‖(physicalCellForward p.eigenvalue p.positive b hb N Q).map A-
        prepareL1 (translatedStandardDensity (whiten p.eigenvalue b θ.1))
          (integrable_translatedStandardDensity _) (rootDisplacedThermal p.eigenvalue θ.2)‖ := by
  rw [physical_model_root_coordinates p b e θ]
  let Λ := fibreChannel (volume : Measure (Fin k → ℝ))
    (QuantumChannel.ofIsometry (rootFockReindex e).toLinearIsometry)
  change ‖Λ.map _-Λ.map _‖ ≤ _
  have hh := Λ.norm_le_two ((physicalCellForward p.eigenvalue p.positive b hb N Q).map A-
    prepareL1 (translatedStandardDensity (whiten p.eigenvalue b θ.1))
      (integrable_translatedStandardDensity _) (rootDisplacedThermal p.eigenvalue θ.2))
  simpa only [map_sub] using hh

end Cloning.TensorLAN
