import Cloning.HybridFlatBox
import Mathlib.Analysis.Convex.Basic

/-! Normalized flat priors on arbitrary compact convex phase-space bodies.
Their exact dilation Jacobian and nesting apply in particular to the image
of the manuscript's score-hyperplane boxes under whitening. -/
noncomputable section
open scoped Topology
open Filter MeasureTheory
namespace Cloning.Hybrid
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {k s : ℕ}

structure PhaseBody (k s : ℕ) where
  carrier : Set (PhaseSpace k s)
  compact : IsCompact carrier
  convex : Convex ℝ carrier
  zero_interior : (0 : PhaseSpace k s) ∈ interior carrier

namespace PhaseBody
variable (B : PhaseBody k s)

theorem volume_real_pos : 0 < volume.real B.carrier :=
  ENNReal.toReal_pos
    (Measure.measure_pos_of_nonempty_interior volume ⟨0,B.zero_interior⟩).ne'
    B.compact.measure_ne_top

def dilate (L : ℝ) : Set (PhaseSpace k s) := (fun ξ => L • ξ) '' B.carrier

theorem dilate_compact (L : ℝ) : IsCompact (B.dilate L) :=
  B.compact.image (by fun_prop)

theorem smul_mem_dilate_iff {L : ℝ} (hL : L ≠ 0) (ξ : PhaseSpace k s) :
    L • ξ ∈ B.dilate L ↔ ξ ∈ B.carrier := by
  constructor
  · rintro ⟨x,hx,he⟩
    have hxξ : x=ξ := (smul_right_injective _ hL) he
    simpa only [hxξ] using hx
  · intro h
    exact ⟨ξ,h,rfl⟩

theorem dilate_mono {L M : ℝ} (hL : 0 ≤ L) (hM : 0 < M) (hLM : L ≤ M) :
    B.dilate L ⊆ B.dilate M := by
  rintro ξ ⟨x,hx,rfl⟩
  refine ⟨(L/M) • x,B.convex.smul_mem_of_zero_mem
    (interior_subset B.zero_interior) hx ⟨div_nonneg hL hM.le,(div_le_one hM).mpr hLM⟩,?_⟩
  change M • ((L/M) • x)=L • x
  rw [smul_smul,mul_div_cancel₀ _ hM.ne']

def density : PhaseDensity k s where
  value := B.carrier.indicator (fun _ => (volume.real B.carrier)⁻¹)
  measurable := measurable_const.indicator B.compact.isClosed.measurableSet
  nonneg := fun ξ => Set.indicator_nonneg (fun _ _ => inv_nonneg.mpr measureReal_nonneg) ξ
  integral_one := by
    rw [integral_indicator B.compact.isClosed.measurableSet,integral_const]
    simp only [measureReal_restrict_apply_univ,smul_eq_mul]
    exact mul_inv_cancel₀ B.volume_real_pos.ne'

theorem integral_expandingPrior {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (n : ℕ) (f : PhaseSpace k s → E) (hf : Continuous f) :
    (∫ ξ,f ξ ∂B.density.expandingPrior n)=
      (volume.real B.carrier)⁻¹ • ∫ z in B.carrier,f (((n : ℝ)+1) • z) := by
  rw [B.density.integral_expandingPrior n f hf]
  change (∫ z,(B.carrier.indicator (fun _ => (volume.real B.carrier)⁻¹) z) •
    f (((n : ℝ)+1) • z))=_
  rw [← integral_smul,← integral_indicator B.compact.isClosed.measurableSet]
  congr 1
  funext z
  by_cases hz : z∈B.carrier <;> simp [hz]

theorem integral_dilate {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {L : ℝ} (hL : 0<L) (f : PhaseSpace k s → E) :
    (∫ z in B.carrier,f (L • z))=
      (L^Module.finrank ℝ (PhaseSpace k s))⁻¹ • ∫ z in B.dilate L,f z := by
  classical
  have he : (fun z => (B.dilate L).indicator f (L • z))=
      B.carrier.indicator (fun z => f (L • z)) := by
    funext z
    by_cases hz : z∈B.carrier
    · simp only [Set.indicator_of_mem hz,
        Set.indicator_of_mem ((B.smul_mem_dilate_iff hL.ne' z).mpr hz)]
    · simp only [Set.indicator_of_notMem hz,
        Set.indicator_of_notMem (mt (B.smul_mem_dilate_iff hL.ne' z).mp hz)]
  calc
    _ = ∫ z,B.carrier.indicator (fun z => f (L • z)) z :=
      (integral_indicator B.compact.isClosed.measurableSet).symm
    _ = ∫ z,(B.dilate L).indicator f (L • z) :=
      (congrArg (fun g : PhaseSpace k s → E => ∫ z,g z) he).symm
    _ = _ := Measure.integral_comp_smul_of_nonneg volume ((B.dilate L).indicator f) L
      (hR:=hL.le)
    _ = _ := congrArg (fun v : E => (L^Module.finrank ℝ (PhaseSpace k s))⁻¹ • v)
      (integral_indicator (B.dilate_compact L).isClosed.measurableSet)

theorem dilate_volume_real {L : ℝ} (hL : 0<L) :
    volume.real (B.dilate L)=L^Module.finrank ℝ (PhaseSpace k s)*volume.real B.carrier := by
  have hv := B.integral_dilate hL (fun _ : PhaseSpace k s => (1:ℝ))
  simp only [integral_const,Measure.restrict_apply_univ,measureReal_def,smul_eq_mul,mul_one] at hv
  change volume.real B.carrier=(L^Module.finrank ℝ (PhaseSpace k s))⁻¹*volume.real (B.dilate L) at hv
  rw [hv,← mul_assoc,mul_inv_cancel₀ (pow_ne_zero _ hL.ne'),one_mul]

theorem normalized_dilate {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {L : ℝ} (hL : 0<L) (f : PhaseSpace k s → E) :
    (volume.real B.carrier)⁻¹ • (∫ z in B.carrier,f (L • z))=
      (volume.real (B.dilate L))⁻¹ • ∫ z in B.dilate L,f z := by
  rw [B.integral_dilate hL f,smul_smul,B.dilate_volume_real hL,mul_inv_rev]

end PhaseBody
end Cloning.Hybrid
