import Cloning.TensorFlatProjectorGibbsState
import Cloning.TensorCloningTransitionCovariance

/-! Exact flat-state fidelity for the actual compatible physical transition channel. -/
noncomputable section
open scoped BigOperators InnerProductSpace ComplexOrder Matrix
namespace Cloning.TensorLie
open Cloning.PCT Cloning.InfiniteTraceClass Cloning.InfiniteFiniteCorner Cloning.Hybrid
open Cloning.TensorCloning Cloning.YoungDimensionRatio
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
variable {d r : ℕ}
local instance (n d : ℕ) : FiniteDimensional ℂ (TensorRegister n (Fin d)) :=
  (registerBasis (Fin n → Fin d)).toOrthonormalBasis.toBasis.finiteDimensional_of_finite

theorem nonnegativePartitionGibbsPositive_support_transport {k : ℕ}
    (mu nu : Fin (r+k) → ℕ) (hmu : Antitone mu) (hnu : Antitone nu) (he : mu=nu)
    (c : ℝ) (hc : 0 ≤ c)
    (hm : nonnegativePartitionGibbsPositive mu hmu (rankFlatSpectrum r k) (rankFlatSpectrum_nonneg r k) =
      partitionMatrixState mu hmu (c • partitionCoordinateProjection mu hmu)
        ((partitionCoordinateProjection_posSemidef mu hmu).smul hc)) :
    nonnegativePartitionGibbsPositive nu hnu (rankFlatSpectrum r k) (rankFlatSpectrum_nonneg r k) =
      partitionMatrixState nu hnu (c • partitionCoordinateProjection nu hnu)
        ((partitionCoordinateProjection_posSemidef nu hnu).smul hc) := by
  subst nu
  exact hm

/-- The general Gibbs family at a sum of padded partitions has the exact
normalized support matrix in the physical output Hilbert space. -/
theorem nonnegativePartitionGibbsPositive_pad_sum (mu nu : Fin r → ℕ) (hmu : Antitone mu) (hnu : Antitone nu)
    (k : ℕ) (hr : 0 < r) :
    nonnegativePartitionGibbsPositive (fun a => padPartition mu k a + padPartition nu k a)
      (sumPartition_antitone _ _ (padPartition_antitone mu hmu k) (padPartition_antitone nu hnu k))
      (rankFlatSpectrum r k) (rankFlatSpectrum_nonneg r k) =
      partitionMatrixState _ (sumPartition_antitone _ _ (padPartition_antitone mu hmu k) (padPartition_antitone nu hnu k))
        ((1/(partitionDimension (fun a => mu a+nu a) (sumPartition_antitone mu nu hmu hnu) : ℝ)) •
          partitionCoordinateProjection _ (sumPartition_antitone _ _ (padPartition_antitone mu hmu k) (padPartition_antitone nu hnu k)))
        ((partitionCoordinateProjection_posSemidef _ _).smul (by positivity)) := by
  exact nonnegativePartitionGibbsPositive_support_transport _ _
    (padPartition_antitone _ (sumPartition_antitone mu nu hmu hnu) k)
    (sumPartition_antitone _ _ (padPartition_antitone mu hmu k) (padPartition_antitone nu hnu k))
    (padPartition_add mu nu k) _ (by positivity)
    (nonnegativePartitionGibbsPositive_pad_rankFlat _ (sumPartition_antitone mu nu hmu hnu) k hr)

/-- Exact physical fidelity for the all-input compatible transition, with
all normalizations and representation data constructed internally. -/
theorem partitionTransition_rankFlat_fidelity (mu lam : Fin r → ℕ)
    (hmu : Antitone mu) (hlam : Antitone lam) (hc : PartitionCompatible mu lam)
    (k : ℕ) (hr : 0 < r) :
    ((nonnegativePartitionGibbsPositive (padPartition mu k) (padPartition_antitone mu hmu k)
        (rankFlatSpectrum r k) (rankFlatSpectrum_nonneg r k)).map
      (partitionTransitionChannel (padPartition mu k) (padPartition lam k)
        (padPartition_antitone mu hmu k) (padPartition_antitone lam hlam k)).toPositiveTracePreservingMap).rootFidelity
      (nonnegativePartitionGibbsPositive (padPartition lam k) (padPartition_antitone lam hlam k)
        (rankFlatSpectrum r k) (rankFlatSpectrum_nonneg r k)) =
      Real.sqrt (dimensionRatio r k (fun a => (mu a : ℝ)) / dimensionRatio r k (fun a => (lam a : ℝ))) := by
  have hsum : (fun a => mu a+(lam a-mu a)) = lam := funext (fun a => Nat.add_sub_of_le (hc.1 a))
  have hadd (nu : Fin r → ℕ) (hnu : Antitone nu) :
      ((nonnegativePartitionGibbsPositive (padPartition mu k) (padPartition_antitone mu hmu k)
          (rankFlatSpectrum r k) (rankFlatSpectrum_nonneg r k)).map
        (partitionTransitionChannel (padPartition mu k) (padPartition (fun a => mu a+nu a) k)
          (padPartition_antitone mu hmu k) (padPartition_antitone _ (sumPartition_antitone mu nu hmu hnu) k)).toPositiveTracePreservingMap).rootFidelity
        (nonnegativePartitionGibbsPositive (padPartition (fun a => mu a+nu a) k)
          (padPartition_antitone _ (sumPartition_antitone mu nu hmu hnu) k)
          (rankFlatSpectrum r k) (rankFlatSpectrum_nonneg r k)) =
        Real.sqrt (dimensionRatio r k (fun a => (mu a : ℝ)) /
          dimensionRatio r k (fun a => ((mu a+nu a : ℕ) : ℝ))) := by
    let P (v : {v : Fin (r+k) → ℕ // Antitone v}) : Prop :=
      ((nonnegativePartitionGibbsPositive (padPartition mu k) (padPartition_antitone mu hmu k)
          (rankFlatSpectrum r k) (rankFlatSpectrum_nonneg r k)).map
        (partitionTransitionChannel (padPartition mu k) v.val (padPartition_antitone mu hmu k) v.property).toPositiveTracePreservingMap).rootFidelity
        (nonnegativePartitionGibbsPositive v.val v.property (rankFlatSpectrum r k) (rankFlatSpectrum_nonneg r k)) =
        Real.sqrt (dimensionRatio r k (fun a => (mu a : ℝ)) /
          dimensionRatio r k (fun a => ((mu a+nu a : ℕ) : ℝ)))
    have hh : P ⟨(fun a => padPartition mu k a + padPartition nu k a),
        sumPartition_antitone _ _ (padPartition_antitone mu hmu k) (padPartition_antitone nu hnu k)⟩ := by
      dsimp only [P]
      rw [partitionTransitionChannel_add, nonnegativePartitionGibbsPositive_pad_sum mu nu hmu hnu k hr,
        nonnegativePartitionGibbsPositive_pad_rankFlat mu hmu k hr]
      change ((partitionMatrixState _ _ _ _).map _).rootFidelity _ = _
      rw [physicalCartanChannel_partitionMatrix_fidelity]
      exact physicalCartanMatrixChannel_rankFlat_fidelity mu nu hmu hnu k
    have he : (⟨(fun a => padPartition mu k a + padPartition nu k a),
        sumPartition_antitone _ _ (padPartition_antitone mu hmu k) (padPartition_antitone nu hnu k)⟩ :
        {v : Fin (r+k) → ℕ // Antitone v}) =
        ⟨padPartition (fun a => mu a+nu a) k,padPartition_antitone _ (sumPartition_antitone mu nu hmu hnu) k⟩ :=
      Subtype.ext (padPartition_add mu nu k).symm
    exact Eq.mp (congrArg P he) hh
  let P (v : {v : Fin r → ℕ // Antitone v}) : Prop :=
    ((nonnegativePartitionGibbsPositive (padPartition mu k) (padPartition_antitone mu hmu k)
        (rankFlatSpectrum r k) (rankFlatSpectrum_nonneg r k)).map
      (partitionTransitionChannel (padPartition mu k) (padPartition v.val k)
        (padPartition_antitone mu hmu k) (padPartition_antitone v.val v.property k)).toPositiveTracePreservingMap).rootFidelity
      (nonnegativePartitionGibbsPositive (padPartition v.val k) (padPartition_antitone v.val v.property k)
        (rankFlatSpectrum r k) (rankFlatSpectrum_nonneg r k)) =
      Real.sqrt (dimensionRatio r k (fun a => (mu a : ℝ)) / dimensionRatio r k (fun a => (v.val a : ℝ)))
  have he : (⟨(fun a => mu a+(lam a-mu a)),sumPartition_antitone mu _ hmu hc.2⟩ :
      {v : Fin r → ℕ // Antitone v}) = ⟨lam,hlam⟩ := Subtype.ext hsum
  exact Eq.mp (congrArg P he) (hadd _ hc.2)

end Cloning.TensorLie
