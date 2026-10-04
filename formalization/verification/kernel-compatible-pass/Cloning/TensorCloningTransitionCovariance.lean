import Cloning.TensorCartanChannelCovariance
import Cloning.TensorCloningAchievabilityMixture

/-! Dependent-target transport and covariance of the concrete partition
transition channel on every compatible pair. -/
noncomputable section
open scoped BigOperators InnerProductSpace Matrix Classical
namespace Cloning.TensorCloning
open Cloning.PCT Cloning.TensorLie Cloning.InfiniteTraceClass Cloning.Hybrid
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
variable {d : ℕ}

local instance (n d : ℕ) : FiniteDimensional ℂ (TensorRegister n (Fin d)) :=
  (registerBasis (Fin n → Fin d)).toOrthonormalBasis.toBasis.finiteDimensional_of_finite

private theorem dependent_map_cast {α : Type} (β : α → Type) (f : (a : α) → β a)
    {a b : α} (h : a = b) : Eq.mp (congrArg β h) (f a) = f b := by
  cases h
  rfl

theorem partitionTransitionChannel_add (mu tau : Fin d → ℕ)
    (hmu : Antitone mu) (htau : Antitone tau) :
    partitionTransitionChannel mu (fun i ↦ mu i + tau i) hmu (sumPartition_antitone mu tau hmu htau) =
      physicalCartanChannel mu tau hmu htau := by
  have hc : PartitionCompatible mu (fun i ↦ mu i + tau i) :=
    ⟨fun i ↦ Nat.le_add_right _ _, by simpa only [Nat.add_sub_cancel_left] using htau⟩
  unfold partitionTransitionChannel
  rw [dif_pos hc]
  have hd : (fun i ↦ mu i + tau i - mu i) = tau := funext (fun i ↦ Nat.add_sub_cancel_left _ _)
  let F (v : {v : Fin d → ℕ // Antitone v}) : Type :=
    QuantumChannel (cyclicSector (partitionHighestTensor mu hmu))
      (cyclicSector (partitionHighestTensor (fun i ↦ mu i + v.val i)
        (sumPartition_antitone mu v.val hmu v.property)))
  let f (v : {v : Fin d → ℕ // Antitone v}) : F v :=
    physicalCartanChannel mu v.val hmu v.property
  have hh : (⟨fun i ↦ mu i + tau i - mu i, hc.2⟩ : {v : Fin d → ℕ // Antitone v}) =
      ⟨tau, htau⟩ := Subtype.ext hd
  exact dependent_map_cast F f hh

theorem partitionTransitionChannel_covariant (mu nu : Fin d → ℕ)
    (hmu : Antitone mu) (hnu : Antitone nu) (hc : PartitionCompatible mu nu)
    (U : Matrix (Fin d) (Fin d) ℂ) (hU : Uᴴ * U = 1)
    (A : TraceClass (cyclicSector (partitionHighestTensor mu hmu))) :
    (partitionTransitionChannel mu nu hmu hnu).toLinearMap
      (conjugationLinearMap (partitionTensorAction mu hmu U) A) =
      conjugationLinearMap (partitionTensorAction nu hnu U)
        ((partitionTransitionChannel mu nu hmu hnu).toLinearMap A) := by
  have he : (fun i ↦ mu i + (nu i - mu i)) = nu := funext (fun i ↦ Nat.add_sub_of_le (hc.1 i))
  have hh := physicalCartanChannel_covariant mu (fun i ↦ nu i - mu i) hmu hc.2 U hU A
  rw [← partitionTransitionChannel_add] at hh
  let P (v : {v : Fin d → ℕ // Antitone v}) : Prop :=
    (partitionTransitionChannel mu v.val hmu v.property).toLinearMap
      (conjugationLinearMap (partitionTensorAction mu hmu U) A) =
      conjugationLinearMap (partitionTensorAction v.val v.property U)
        ((partitionTransitionChannel mu v.val hmu v.property).toLinearMap A)
  have hab : (⟨fun i ↦ mu i + (nu i - mu i), sumPartition_antitone mu _ hmu hc.2⟩ :
    {v : Fin d → ℕ // Antitone v}) = ⟨nu, hnu⟩ := Subtype.ext he
  exact Eq.mp (congrArg P hab) hh

section Isometry
variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem rootFidelity_map_isometryEquiv (e : H ≃ₗᵢ[ℂ] K) (A B : PositiveTraceClass H) :
    (A.map (QuantumChannel.ofIsometry e.toLinearIsometry).toPositiveTracePreservingMap).rootFidelity
      (B.map (QuantumChannel.ofIsometry e.toLinearIsometry).toPositiveTracePreservingMap) =
      A.rootFidelity B := by
  let C := QuantumChannel.ofIsometry e.toLinearIsometry
  let D := QuantumChannel.ofIsometry e.symm.toLinearIsometry
  have hback (X : PositiveTraceClass H) :
      (X.map C.toPositiveTracePreservingMap).map D.toPositiveTracePreservingMap = X :=
    Subtype.ext (isometryEquiv_channel_roundtrip e.symm X.1)
  apply le_antisymm
  · have h := Cloning.InfiniteFidelity.fidelity_data_processing D
      (A.map C.toPositiveTracePreservingMap).1 (B.map C.toPositiveTracePreservingMap).1
      (A.map C.toPositiveTracePreservingMap).2 (B.map C.toPositiveTracePreservingMap).2
    change (A.map C.toPositiveTracePreservingMap).rootFidelity (B.map C.toPositiveTracePreservingMap) ≤
      ((A.map C.toPositiveTracePreservingMap).map D.toPositiveTracePreservingMap).rootFidelity
        ((B.map C.toPositiveTracePreservingMap).map D.toPositiveTracePreservingMap) at h
    simpa only [hback] using h
  · exact Cloning.InfiniteFidelity.fidelity_data_processing C A.1 B.1 A.2 B.2

end Isometry
end Cloning.TensorCloning
