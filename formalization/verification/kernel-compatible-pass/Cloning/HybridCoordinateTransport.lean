import Cloning.MixedChannels
import Cloning.HybridGaussianAttainmentFidelity

/-! Genuine transport of hybrid channels along a measure-preserving coordinate
equivalence. Both the full complex L1 space and every finite positive block are
transported; fidelity and all competitors are preserved. -/
noncomputable section
open scoped ComplexOrder InnerProductSpace Topology
open MeasureTheory Filter Cloning.InfiniteTraceClass
namespace Cloning.Hybrid
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {Ω Ξ H K : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
  {μ : Measure Ω} {ν : Measure Ξ}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Pull back the classical coordinate with its actual reference measure. -/
def coordinatePull (e : Ω ≃ᵐ Ξ) (he : MeasurePreserving e μ ν) :
    Lp (TraceClass H) 1 ν →ₗᵢ[ℂ] Lp (TraceClass H) 1 μ :=
  Lp.compMeasurePreservingₗᵢ ℂ e he

theorem coordinatePull_ae (e : Ω ≃ᵐ Ξ) (he : MeasurePreserving e μ ν)
    (A : Lp (TraceClass H) 1 ν) : coordinatePull e he A =ᵐ[μ] fun y => A (e y) :=
  Lp.coeFn_compMeasurePreserving A he

theorem coordinatePull_blockPositive (e : Ω ≃ᵐ Ξ) (he : MeasurePreserving e μ ν)
    (n : ℕ) (A : Fin n → Fin n → Lp (TraceClass H) 1 ν) (hA : L1BlockPositive A) :
    L1BlockPositive (fun i j => coordinatePull e he (A i j)) := by
  have hp := he.quasiMeasurePreserving.ae hA
  have heq : ∀ᵐ y ∂μ, ∀ i j : Fin n, coordinatePull e he (A i j) y = A i j (e y) :=
    ae_all_iff.mpr fun i => ae_all_iff.mpr fun j => coordinatePull_ae e he (A i j)
  filter_upwards [hp, heq] with y hy heq
  simpa only [heq] using hy

theorem coordinatePull_nonneg (e : Ω ≃ᵐ Ξ) (he : MeasurePreserving e μ ν)
    (A : PositiveL1 H ν) : ∀ᵐ y ∂μ, 0 ≤ (coordinatePull e he A.1 y).1 := by
  filter_upwards [he.quasiMeasurePreserving.ae A.2, coordinatePull_ae e he A.1] with y hy heq
  simpa only [heq] using hy

def coordinatePullPositive (e : Ω ≃ᵐ Ξ) (he : MeasurePreserving e μ ν)
    (A : PositiveL1 H ν) : PositiveL1 H μ :=
  ⟨coordinatePull e he A.1, coordinatePull_nonneg e he A⟩

theorem coordinatePull_trace (e : Ω ≃ᵐ Ξ) (he : MeasurePreserving e μ ν)
    (A : Lp (TraceClass H) 1 ν) :
    (∫ y, traceCLM (coordinatePull e he A y) ∂μ) = ∫ y, traceCLM (A y) ∂ν := by
  calc
    _ = ∫ y, traceCLM (A (e y)) ∂μ :=
      integral_congr_ae ((coordinatePull_ae e he A).fun_comp traceCLM)
    _ = _ := he.integral_comp e.measurableEmbedding (fun y => traceCLM (A y))

@[simp] theorem coordinatePull_symm_apply (e : Ω ≃ᵐ Ξ) (he : MeasurePreserving e μ ν)
    (A : Lp (TraceClass H) 1 ν) :
    coordinatePull e.symm (he.symm e) (coordinatePull e he A) = A := by
  apply Lp.ext
  have hh := (he.symm e).quasiMeasurePreserving.ae (coordinatePull_ae e he A)
  filter_upwards [hh, coordinatePull_ae e.symm (he.symm e) (coordinatePull e he A)] with y hy heq
  simp only [heq, hy, e.apply_symm_apply]

@[simp] theorem coordinatePull_apply_symm (e : Ω ≃ᵐ Ξ) (he : MeasurePreserving e μ ν)
    (A : Lp (TraceClass H) 1 μ) :
    coordinatePull e he (coordinatePull e.symm (he.symm e) A) = A := by
  exact coordinatePull_symm_apply e.symm (he.symm e) A

/-- Actual root fidelity is invariant under the coordinate equivalence. -/
theorem coordinatePullPositive_rootFidelity (e : Ω ≃ᵐ Ξ) (he : MeasurePreserving e μ ν)
    (A B : PositiveL1 H ν) :
    (coordinatePullPositive e he A).rootFidelity (coordinatePullPositive e he B) =
      A.rootFidelity B := by
  rw [PositiveL1.rootFidelity_eq_integral, PositiveL1.rootFidelity_eq_integral]
  calc
    _ = ∫ y, extendedRootFidelity (A.1 (e y), B.1 (e y)) ∂μ := by
      apply integral_congr_ae
      filter_upwards [coordinatePull_ae e he A.1, coordinatePull_ae e he B.1] with y hA hB
      change extendedRootFidelity (coordinatePull e he A.1 y, coordinatePull e he B.1 y) = _
      rw [hA, hB]
    _ = _ := he.integral_comp e.measurableEmbedding
      (fun y => extendedRootFidelity (A.1 y, B.1 y))

/-- Conjugate an arbitrary actual hybrid competitor into new classical
coordinates, retaining global CP and TP on all inputs. -/
def Channel.transportCoordinates (e : Ω ≃ᵐ Ξ) (he : MeasurePreserving e μ ν)
    (Λ : Channel H K μ) : Channel H K ν where
  map := (coordinatePull (H := K) e.symm (he.symm e)).toContinuousLinearMap.comp
    (Λ.map.comp (coordinatePull (H := H) e he).toContinuousLinearMap)
  completelyPositive := by
    intro n A hA
    exact coordinatePull_blockPositive e.symm (he.symm e) n _
      (Λ.completelyPositive n _ (coordinatePull_blockPositive e he n A hA))
  tracePreserving := by
    intro A
    change (∫ y, traceCLM
      (coordinatePull e.symm (he.symm e) (Λ.map (coordinatePull e he A)) y) ∂ν) = _
    rw [coordinatePull_trace]
    exact (Λ.tracePreserving (coordinatePull e he A)).trans (coordinatePull_trace e he A)

@[simp] theorem Channel.transportCoordinates_apply
    (e : Ω ≃ᵐ Ξ) (he : MeasurePreserving e μ ν) (Λ : Channel H K μ)
    (A : Lp (TraceClass H) 1 ν) :
    (Λ.transportCoordinates e he).map A =
      coordinatePull e.symm (he.symm e) (Λ.map (coordinatePull e he A)) := rfl

/-- Coordinate transport preserves the payoff for every competitor, not just
for product or covariant channels. -/
theorem Channel.transportCoordinates_rootFidelity
    (e : Ω ≃ᵐ Ξ) (he : MeasurePreserving e μ ν) (Λ : Channel H K μ)
    (A : PositiveL1 H ν) (B : PositiveL1 K ν) :
    (A.map (Λ.transportCoordinates e he)).rootFidelity B =
      ((coordinatePullPositive e he A).map Λ).rootFidelity (coordinatePullPositive e he B) := by
  rw [← coordinatePullPositive_rootFidelity e he]
  congr 1
  apply Subtype.ext
  exact coordinatePull_apply_symm e he _

theorem Channel.eq_of_map_eq {Λ Γ : Channel H K μ} (h : Λ.map = Γ.map) : Λ = Γ := by
  cases Λ
  cases Γ
  cases h
  rfl

/-- Pullback of the new measure returns every original competitor exactly. -/
theorem Channel.transportCoordinates_symm
    (e : Ω ≃ᵐ Ξ) (he : MeasurePreserving e μ ν) (Λ : Channel H K μ) :
    (Λ.transportCoordinates e he).transportCoordinates e.symm (he.symm e) = Λ := by
  apply Channel.eq_of_map_eq
  apply ContinuousLinearMap.ext
  intro A
  simp only [Channel.transportCoordinates_apply, coordinatePull_symm_apply,
    coordinatePull_apply_symm]

/-- A bijection of all actual competitors under the coordinate change. -/
def Channel.coordinateEquiv (e : Ω ≃ᵐ Ξ) (he : MeasurePreserving e μ ν) :
    Channel H K μ ≃ Channel H K ν where
  toFun := Channel.transportCoordinates e he
  invFun := Channel.transportCoordinates e.symm (he.symm e)
  left_inv := Channel.transportCoordinates_symm e he
  right_inv := Channel.transportCoordinates_symm e.symm (he.symm e)

end Cloning.Hybrid
