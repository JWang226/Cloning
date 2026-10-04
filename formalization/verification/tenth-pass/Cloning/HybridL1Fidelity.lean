import Cloning.HybridL1Cone
import Cloning.HybridJensen
import Cloning.HybridChannel

/-! Root fidelity on the positive cone of the genuine operator-valued L1
Banach space. A positive representative is repaired on a null set, so all
definitions and continuity statements concern actual L1 equivalence classes. -/

noncomputable section
open scoped ComplexOrder InnerProductSpace Topology BigOperators
open MeasureTheory Filter Cloning.InfiniteTraceClass Cloning.InfiniteFidelity
namespace Cloning.Hybrid
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

variable {Ω H K : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

namespace PositiveField

/-- Repair an almost-everywhere positive L1 representative only on its null
exceptional set. -/
def ofL1 (A : Lp (TraceClass H) 1 μ) (hA : ∀ᵐ y ∂μ, 0 ≤ (A y).1) :
    PositiveField (H := H) μ := by
  classical
  let f : Ω → TraceClass H := fun y => if 0 ≤ (A y).1 then A y else 0
  have he : f =ᵐ[μ] A := hA.mono fun y hy => if_pos hy
  exact ofIntegrable f ((L1.integrable_coeFn A).congr he.symm) (fun y => by
    dsimp only [f]
    split_ifs with hy
    · exact hy
    · exact le_rfl)

theorem ofL1_ae (A : Lp (TraceClass H) 1 μ) (hA : ∀ᵐ y ∂μ, 0 ≤ (A y).1) :
    (fun y => ((ofL1 A hA).value y).1) =ᵐ[μ] A := by
  classical
  filter_upwards [hA] with y hy
  change (if 0 ≤ (A y).1 then A y else 0) = A y
  exact if_pos hy

@[simp] theorem toL1_ofL1 (A : Lp (TraceClass H) 1 μ) (hA : ∀ᵐ y ∂μ, 0 ≤ (A y).1) :
    (ofL1 A hA).toL1 = A :=
  Lp.ext (((ofL1 A hA).coe_toL1).trans (ofL1_ae A hA))

theorem rootFidelity_ofL1_eq_integral (A B : Lp (TraceClass H) 1 μ)
    (hA : ∀ᵐ y ∂μ, 0 ≤ (A y).1) (hB : ∀ᵐ y ∂μ, 0 ≤ (B y).1) :
    (ofL1 A hA).rootFidelity (ofL1 B hB) =
      ∫ y, extendedRootFidelity (A y, B y) ∂μ := by
  apply integral_congr_ae
  filter_upwards [ofL1_ae A hA, ofL1_ae B hB, hA, hB] with y hAy hBy hpA hpB
  rw [extendedRootFidelity_eq _ _ hpA hpB]
  unfold PositiveTraceClass.rootFidelity
  congr 1 <;> simp only [hAy, hBy]

end PositiveField

/-- The closed positive cone in operator-valued L1. -/
def PositiveL1 (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (μ : Measure Ω) :=
  {A : Lp (TraceClass H) 1 μ // ∀ᵐ y ∂μ, 0 ≤ (A y).1}

namespace PositiveL1

instance : TopologicalSpace (PositiveL1 H μ) := inferInstanceAs
  (TopologicalSpace {A : Lp (TraceClass H) 1 μ // ∀ᵐ y ∂μ, 0 ≤ (A y).1})
instance : MetricSpace (PositiveL1 H μ) := inferInstanceAs
  (MetricSpace {A : Lp (TraceClass H) 1 μ // ∀ᵐ y ∂μ, 0 ≤ (A y).1})

def field (A : PositiveL1 H μ) : PositiveField (H := H) μ := PositiveField.ofL1 A.1 A.2

@[simp] theorem field_toL1 (A : PositiveL1 H μ) : A.field.toL1 = A.1 :=
  PositiveField.toL1_ofL1 A.1 A.2

@[simp] theorem field_mass (A : PositiveL1 H μ) : A.field.mass = ‖A.1‖ := by
  rw [← PositiveField.norm_toL1, field_toL1]

theorem field_traceDistance (A B : PositiveL1 H μ) :
    A.field.traceDistance B.field = ‖A.1 - B.1‖ := by
  rw [PositiveField.traceDistance_eq_norm, field_toL1, field_toL1]

/-- The actual integrated root fidelity of two positive L1 classes. -/
def rootFidelity (A B : PositiveL1 H μ) : ℝ := A.field.rootFidelity B.field

theorem rootFidelity_eq_integral (A B : PositiveL1 H μ) :
    A.rootFidelity B = ∫ y, extendedRootFidelity (A.1 y, B.1 y) ∂μ :=
  PositiveField.rootFidelity_ofL1_eq_integral A.1 B.1 A.2 B.2

theorem integrable_rootFidelity (A B : PositiveL1 H μ) :
    Integrable (fun y => extendedRootFidelity (A.1 y, B.1 y)) μ := by
  apply (A.field.integrable_rootFidelity B.field).congr
  filter_upwards [PositiveField.ofL1_ae A.1 A.2, PositiveField.ofL1_ae B.1 B.2,
    A.2, B.2] with y hAy hBy hpA hpB
  rw [extendedRootFidelity_eq _ _ hpA hpB]
  unfold PositiveTraceClass.rootFidelity field
  congr 1 <;> simp only [hAy, hBy]

theorem rootFidelity_nonneg (A B : PositiveL1 H μ) : 0 ≤ A.rootFidelity B :=
  A.field.rootFidelity_nonneg B.field

theorem rootFidelity_comm (A B : PositiveL1 H μ) : A.rootFidelity B = B.rootFidelity A :=
  A.field.rootFidelity_comm B.field

@[simp] theorem rootFidelity_self (A : PositiveL1 H μ) : A.rootFidelity A = ‖A.1‖ := by
  rw [rootFidelity, PositiveField.rootFidelity_self, field_mass]

theorem rootFidelity_le_sqrt (A B : PositiveL1 H μ) :
    A.rootFidelity B ≤ Real.sqrt ‖A.1‖ * Real.sqrt ‖B.1‖ := by
  simpa only [field_mass] using A.field.rootFidelity_le_sqrt_mass B.field

theorem rootFidelity_continuity (A B C D : PositiveL1 H μ) :
    |A.rootFidelity B - C.rootFidelity D| ≤
      Real.sqrt ‖A.1 - C.1‖ * Real.sqrt ‖B.1‖ +
      Real.sqrt ‖B.1 - D.1‖ * Real.sqrt ‖C.1‖ := by
  simpa only [field_traceDistance, field_mass] using
    A.field.rootFidelity_continuity B.field C.field D.field

theorem continuous_rootFidelity :
    Continuous (fun p : PositiveL1 H μ × PositiveL1 H μ => p.1.rootFidelity p.2) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  rw [ContinuousAt, ← tendsto_sub_nhds_zero_iff, tendsto_zero_iff_norm_tendsto_zero]
  have hA : Tendsto (fun q : PositiveL1 H μ × PositiveL1 H μ => q.1.1)
      (𝓝 p) (𝓝 p.1.1) := continuous_subtype_val.continuousAt.comp continuous_fst.continuousAt
  have hB : Tendsto (fun q : PositiveL1 H μ × PositiveL1 H μ => q.2.1)
      (𝓝 p) (𝓝 p.2.1) := continuous_subtype_val.continuousAt.comp continuous_snd.continuousAt
  have hlim : Tendsto
      (fun q : PositiveL1 H μ × PositiveL1 H μ =>
        Real.sqrt ‖q.1.1 - p.1.1‖ * Real.sqrt ‖q.2.1‖ +
        Real.sqrt ‖q.2.1 - p.2.1‖ * Real.sqrt ‖p.1.1‖) (𝓝 p) (𝓝 0) := by
    convert (((hA.sub tendsto_const_nhds).norm.sqrt).mul hB.norm.sqrt).add
      (((hB.sub tendsto_const_nhds).norm.sqrt).mul tendsto_const_nhds) using 1 <;> simp
  exact squeeze_zero (fun _ => norm_nonneg _) (fun q => by
    simpa only [Real.norm_eq_abs] using rootFidelity_continuity q.1 q.2 p.1 p.2) hlim

/-- Actual hybrid channels act continuously on the positive L1 cone. -/
def map (Λ : Channel H K μ) (A : PositiveL1 H μ) : PositiveL1 K μ :=
  ⟨Λ.map A.1, Λ.completelyPositive.map_nonneg A.1 A.2⟩

theorem continuous_map (Λ : Channel H K μ) : Continuous (map Λ) :=
  (Λ.map.continuous.comp continuous_subtype_val).subtype_mk _

@[simp] theorem norm_map (Λ : Channel H K μ) (A : PositiveL1 H μ) :
    ‖(map Λ A).1‖ = ‖A.1‖ :=
  norm_L1_map_nonneg Λ.map.toLinearMap Λ.completelyPositive Λ.tracePreserving A.1 A.2

end PositiveL1

namespace PositiveField

def toPositiveL1 (R : PositiveField (H := H) μ) : PositiveL1 H μ :=
  ⟨R.toL1, by
    filter_upwards [R.coe_toL1] with y hy
    rw [hy]
    exact (R.value y).2⟩

theorem toPositiveL1_rootFidelity (R S : PositiveField (H := H) μ) :
    R.toPositiveL1.rootFidelity S.toPositiveL1 = R.rootFidelity S :=
  rootFidelity_eq_of_toL1_eq (PositiveL1.field_toL1 _) (PositiveL1.field_toL1 _)

end PositiveField
end Cloning.Hybrid
