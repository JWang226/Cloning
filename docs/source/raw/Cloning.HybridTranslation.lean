import Cloning.HybridWeightedTrace
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
import Mathlib.MeasureTheory.Group.Integral

/-!
# Classical translations of operator-valued L¹

Translation acts on actual L¹ equivalence classes by `A(y-h)`.  It is a
strongly continuous complex linear isometry, preserves positivity at every
finite quantum ancilla, and preserves the integrated trace.
-/

noncomputable section
open scoped ComplexOrder InnerProductSpace Topology BigOperators
open MeasureTheory Filter Cloning.InfiniteTraceClass
namespace Cloning.Hybrid
set_option backward.isDefEq.respectTransparency false

variable {k : ℕ} {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Translation of the classical register, with the density convention
`(T h A)(y) = A(y-h)`. -/
def classicalTranslation (h : Fin k → ℝ) :
    Lp (TraceClass H) 1 (volume : Measure (Fin k → ℝ)) →ₗᵢ[ℂ]
      Lp (TraceClass H) 1 (volume : Measure (Fin k → ℝ)) :=
  Lp.compMeasurePreservingₗᵢ ℂ (fun y => y - h)
    (measurePreserving_sub_right volume h)

theorem classicalTranslation_ae (h : Fin k → ℝ)
    (A : Lp (TraceClass H) 1 (volume : Measure (Fin k → ℝ))) :
    classicalTranslation h A =ᵐ[volume] fun y => A (y - h) :=
  Lp.coeFn_compMeasurePreserving A (measurePreserving_sub_right volume h)

@[simp] theorem norm_classicalTranslation (h : Fin k → ℝ)
    (A : Lp (TraceClass H) 1 (volume : Measure (Fin k → ℝ))) :
    ‖classicalTranslation h A‖ = ‖A‖ :=
  (classicalTranslation h).norm_map A

@[simp] theorem classicalTranslation_zero
    (A : Lp (TraceClass H) 1 (volume : Measure (Fin k → ℝ))) :
    classicalTranslation 0 A = A := by
  apply Lp.ext
  simpa only [sub_zero] using classicalTranslation_ae 0 A

theorem classicalTranslation_add (h g : Fin k → ℝ)
    (A : Lp (TraceClass H) 1 (volume : Measure (Fin k → ℝ))) :
    classicalTranslation (h + g) A = classicalTranslation h (classicalTranslation g A) := by
  apply Lp.ext
  have he := (measurePreserving_sub_right volume h).quasiMeasurePreserving.ae
    (classicalTranslation_ae g A)
  filter_upwards [classicalTranslation_ae (h + g) A,
    classicalTranslation_ae h (classicalTranslation g A), he] with y hsum hh hg
  rw [hsum, hh, hg, sub_sub]

theorem classicalTranslation_nonneg (h : Fin k → ℝ)
    (A : Lp (TraceClass H) 1 (volume : Measure (Fin k → ℝ)))
    (hA : ∀ᵐ y ∂volume, 0 ≤ (A y).1) :
    ∀ᵐ y ∂volume, 0 ≤ (classicalTranslation h A y).1 := by
  have hp := (measurePreserving_sub_right volume h).quasiMeasurePreserving.ae hA
  filter_upwards [classicalTranslation_ae h A, hp] with y hy hp
  rwa [hy]

theorem classicalTranslation_completelyPositive (h : Fin k → ℝ) :
    L1CompletelyPositive (classicalTranslation (H := H) h).toLinearMap := by
  intro n A hA
  have hp := (measurePreserving_sub_right volume h).quasiMeasurePreserving.ae hA
  have he : ∀ᵐ y ∂volume, ∀ i j : Fin n,
      classicalTranslation h (A i j) y = A i j (y - h) :=
    ae_all_iff.mpr fun i => ae_all_iff.mpr fun j => classicalTranslation_ae h (A i j)
  filter_upwards [he, hp] with y hy hp
  change BlockPositive (fun i j => classicalTranslation h (A i j) y)
  simpa only [hy] using hp

theorem integral_classicalTranslation (h : Fin k → ℝ)
    (A : Lp (TraceClass H) 1 (volume : Measure (Fin k → ℝ))) :
    (∫ y, classicalTranslation h A y) = ∫ y, A y := by
  calc
    _ = ∫ y, A (y - h) := integral_congr_ae (classicalTranslation_ae h A)
    _ = _ := integral_sub_right_eq_self A h

theorem classicalTranslation_tracePreserving (h : Fin k → ℝ) :
    L1TracePreserving (classicalTranslation (H := H) h).toLinearMap := by
  intro A
  calc
    _ = ∫ y, traceCLM (A (y - h)) :=
      integral_congr_ae ((classicalTranslation_ae h A).fun_comp traceCLM)
    _ = _ := integral_sub_right_eq_self (fun y => traceCLM (A y)) h

/-- The classical action is jointly continuous in the displacement and L¹
input, in particular strongly continuous in the displacement. -/
theorem continuous_classicalTranslation_joint :
    Continuous (fun p : (Fin k → ℝ) ×
      Lp (TraceClass H) 1 (volume : Measure (Fin k → ℝ)) =>
        classicalTranslation p.1 p.2) := by
  let g : C((Fin k → ℝ), C((Fin k → ℝ), (Fin k → ℝ))) :=
    (⟨fun p : (Fin k → ℝ) × (Fin k → ℝ) => p.2 - p.1,
      continuous_snd.sub continuous_fst⟩ : C(_, _)).curry
  exact continuous_snd.compMeasurePreservingLp (g.continuous.comp continuous_fst)
    (fun p => measurePreserving_sub_right volume p.1) (by simp)

theorem continuous_classicalTranslation
    (A : Lp (TraceClass H) 1 (volume : Measure (Fin k → ℝ))) :
    Continuous (fun h => classicalTranslation h A) :=
  continuous_classicalTranslation_joint.comp (continuous_id.prodMk continuous_const)

end Cloning.Hybrid
