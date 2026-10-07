import Cloning.PCTWernerLowerBasis
import Cloning.PCTRankAdaptedProduct
import Cloning.InfiniteFidelityTransition
import Cloning.HybridGaussianAttainmentFidelity

/-! Finite PCT lower bounds for the actual reduced Werner output, obtained
by retaining its pure-product component in the operator order. -/
noncomputable section
open scoped BigOperators InnerProductSpace ComplexOrder
namespace Cloning.PCTRankAdapted
open Cloning.PCT Cloning.PCTPurificationChannel Cloning.InfiniteTraceClass
open Cloning.GeneralSymmetricOccupation Cloning.Hybrid Cloning.PCTPhysicalState
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

theorem map_operator_le {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (Φ : QuantumChannel H K) (X Y : TraceClass H) (h : X.1≤Y.1) :
    (Φ.toLinearMap X).1 ≤ (Φ.toLinearMap Y).1 := by
  have hp : 0≤(Y-X).1 := sub_nonneg.mpr h
  have hh := Φ.map_nonneg (Y-X) hp
  change 0 ≤ inclusionCLM (Φ.toLinearMap (Y-X)) at hh
  rw [map_sub,map_sub] at hh
  exact sub_nonneg.mp hh

set_option backward.isDefEq.respectTransparency true in
theorem pureWernerOutput_product_lower {A : Type*} [Fintype A] [DecidableEq A]
    {L s : ℕ} (hA : Fintype.card A=s+1)
    (ψ : Register A) (hψ : ‖ψ‖=1) (S : Finset (Fin L)) :
    (wernerScale S.card L s : ℂ) •
      (vectorProjector (tensorVector (fun _ : Fin L => ψ))).1 ≤
      (pureWernerOutput hA ψ hψ S).1 := by
  obtain ⟨u,hu⟩ := exists_purification_frame hA ψ hψ
  subst ψ
  rw [pureWernerOutput_eq_frame hA u.orthonormal]
  have h := map_operator_le (QuantumChannel.ofIsometry (tensorFrame u.orthonormal L))
    ((wernerScale S.card L s : ℂ) •
      vectorProjector (lp.single 2 (fun _ : Fin L => (0:Fin (s+1))) 1))
    (wernerOutput (s:=s) S) (wernerOutput_vacuum_lower S)
  simpa only [map_smul,QuantumChannel.ofIsometry_vectorProjector,tensorFrame_single] using h

theorem reducedWernerOutput_product_lower {A E : Type*}
    [Fintype A] [Fintype E] [DecidableEq A] [DecidableEq E]
    {L s : ℕ} (hA : Fintype.card (A×E)=s+1)
    (ψ : Register (A×E)) (hψ : ‖ψ‖=1) (S : Finset (Fin L)) :
    (wernerScale S.card L s : ℂ) • (matrixTensorPower (reducedDensityMatrix ψ) L).1 ≤
      (reducedWernerOutput hA ψ hψ S).1 := by
  have h := map_operator_le
    (partialTraceChannel.comp (QuantumChannel.ofIsometry (regroup L)))
    ((wernerScale S.card L s : ℂ) • vectorProjector (tensorVector (fun _ => ψ)))
    (pureWernerOutput hA ψ hψ S) (pureWernerOutput_product_lower hA ψ hψ S)
  change (partialTraceChannel.toLinearMap
    ((QuantumChannel.ofIsometry (regroup L)).toLinearMap
      ((wernerScale S.card L s : ℂ) • vectorProjector (tensorVector (fun _ => ψ))))).1 ≤
      (reducedWernerOutput hA ψ hψ S).1 at h
  simpa only [map_smul,QuantumChannel.ofIsometry_vectorProjector,
    partialTrace_product_eq_matrixTensorPower] using h

theorem rootFidelity_lower_of_operator_lower {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (X Y : PositiveTraceClass H) (hY : ‖Y.1‖=1)
    (c : ℝ) (hc : 0≤c) (hle : (c:ℂ) • Y.1.1 ≤ X.1.1) :
    Real.sqrt c ≤ X.rootFidelity Y := by
  let a : NNReal := ⟨c,hc⟩
  have h1 : PositiveTraceClass.scale 1 Y=Y := by
    apply Subtype.ext
    simp [PositiveTraceClass.scale]
  have he := PositiveTraceClass.rootFidelity_scale a 1 Y Y
  rw [h1,PositiveTraceClass.rootFidelity_self,hY] at he
  simp only [NNReal.coe_one,Real.sqrt_one,mul_one] at he
  exact he.symm.le.trans (PositiveTraceClass.rootFidelity_mono_left _ X Y hle)

theorem outputState_fidelity_lower {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]
    {s : ℕ} (hA : Fintype.card (A×A)=s+1) (ρ : Cloning.MatrixFidelity.State A)
    (n t : ℕ) :
    Real.sqrt (wernerScale n (n+t) s) ≤
      (outputState hA ρ n t).rootFidelity (tensorState ρ (n+t)) := by
  apply rootFidelity_lower_of_operator_lower _ _ (norm_tensorState ρ (n+t)) _
    (wernerScale_pos n (n+t) s).le
  rw [outputState_eq_reducedWernerPositive]
  have h := reducedWernerOutput_product_lower hA (canonicalPurification ρ.matrix)
    (canonicalPurification_norm ρ) (inputSlots n (n+t) (Nat.le_add_right n t))
  simpa only [inputSlots_card,canonicalPurification_reduced _ ρ.positive] using h

end Cloning.PCTRankAdapted
