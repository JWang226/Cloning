import Cloning.YoungCompatibilityFallback
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
# The root hyperplane and its actual coordinate transport

The affine lattice and the real sum-zero hyperplane are constructed as
subtypes, with explicit coordinate equivalences.  Probability distributions,
cells and densities are transported along those equivalences.  This exposes
the dependent last coordinate rather than dropping it from the state space.
-/

set_option maxHeartbeats 800000
noncomputable section
open scoped BigOperators Topology Classical
open MeasureTheory

namespace Cloning.YoungHyperplane

/-- The actual root hyperplane, with the metric and inner product induced
from the ambient Euclidean space of `d+1` coordinates. -/
abbrev rootSpace (d : ℕ) : Submodule ℝ (EuclideanSpace ℝ (Fin (d + 1))) where
  carrier := {x | ∑ i, x i = 0}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    change (∑ i, (x + y) i) = 0
    change (∑ i, x i) = 0 at hx
    change (∑ i, y i) = 0 at hy
    simp only [PiLp.add_apply, Finset.sum_add_distrib, hx, hy, add_zero]
  smul_mem' := by
    intro c x hx
    change (∑ i, (c • x) i) = 0
    change (∑ i, x i) = 0 at hx
    simp only [PiLp.smul_apply, smul_eq_mul, ← Finset.mul_sum, hx, mul_zero]

/-- Coordinates along `e_i-e_last` as an explicit linear equivalence. -/
def coordinates (d : ℕ) : (Fin d → ℝ) ≃ₗ[ℝ] rootSpace d where
  toFun x := ⟨WithLp.toLp 2 (Fin.snoc (α := fun _ : Fin (d + 1) ↦ ℝ) x (-∑ i, x i)), by
    change (∑ i, Fin.snoc (α := fun _ : Fin (d + 1) ↦ ℝ) x (-∑ j, x j) i) = 0
    rw [Fin.sum_univ_castSucc]
    simp⟩
  invFun x i := x.1 i.castSucc
  left_inv x := by ext i; simp
  right_inv x := by
    apply Subtype.ext
    ext i
    change Fin.snoc (α := fun _ : Fin (d + 1) ↦ ℝ) (fun j : Fin d ↦ x.1 j.castSucc) (-∑ j : Fin d, x.1 j.castSucc) i = x.1 i
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · rw [Fin.snoc_last]
      have hx := x.2
      change (∑ i, x.1 i) = 0 at hx
      rw [Fin.sum_univ_castSucc] at hx
      linarith
    · simp
  map_add' x y := by
    apply Subtype.ext
    ext i
    change Fin.snoc (α := fun _ : Fin (d + 1) ↦ ℝ) (x + y) (-∑ j, (x + y) j) i =
      Fin.snoc (α := fun _ : Fin (d + 1) ↦ ℝ) x (-∑ j, x j) i + Fin.snoc (α := fun _ : Fin (d + 1) ↦ ℝ) y (-∑ j, y j) i
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · simp [Finset.sum_add_distrib, add_comm]
    · simp
  map_smul' c x := by
    apply Subtype.ext
    ext i
    change Fin.snoc (α := fun _ : Fin (d + 1) ↦ ℝ) (c • x) (-∑ j, (c • x) j) i = c * Fin.snoc (α := fun _ : Fin (d + 1) ↦ ℝ) x (-∑ j, x j) i
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · simp [← Finset.mul_sum]
    · simp

@[simp] theorem coordinates_head (d : ℕ) (x : Fin d → ℝ) (i : Fin d) :
    (coordinates d x).1 i.castSucc = x i := by simp [coordinates]

@[simp] theorem coordinates_last (d : ℕ) (x : Fin d → ℝ) :
    (coordinates d x).1 (Fin.last d) = -∑ i, x i := by simp [coordinates]

@[simp] theorem coordinates_symm_apply (d : ℕ) (x : rootSpace d) (i : Fin d) :
    (coordinates d).symm x i = x.1 i.castSucc := rfl

def coordinatesContinuous (d : ℕ) : (Fin d → ℝ) ≃L[ℝ] rootSpace d :=
  (coordinates d).toContinuousLinearEquiv

/-- The induced coordinate volume.  Its relation to canonical Euclidean
hyperplane volume is a separate normalization identity. -/
def coordinateMeasure (d : ℕ) : Measure (rootSpace d) :=
  Measure.map (coordinatesContinuous d) volume

theorem coordinates_measurePreserving (d : ℕ) :
    MeasurePreserving (coordinatesContinuous d) volume (coordinateMeasure d) :=
  ⟨(coordinatesContinuous d).continuous.measurable, rfl⟩

/-- The affine integer lattice with the exact required total mass. -/
def Lattice (d : ℕ) (n : ℤ) := {μ : Fin (d + 1) → ℤ // ∑ i, μ i = n}

/-- Every affine label is uniquely determined by its first `d` coordinates. -/
def latticeCoordinates (d : ℕ) (n : ℤ) : (Fin d → ℤ) ≃ Lattice d n where
  toFun z := ⟨YoungCompatibility.complete n z, YoungCompatibility.complete_sum n z⟩
  invFun μ i := μ.1 i.castSucc
  left_inv z := by ext i; simp
  right_inv μ := by
    apply Subtype.ext
    ext i
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · change YoungCompatibility.complete n (fun j ↦ μ.1 j.castSucc) (Fin.last d) = μ.1 (Fin.last d)
      rw [YoungCompatibility.complete_last]
      unfold Rounding.completeLast
      have hμ := μ.2
      rw [Fin.sum_univ_castSucc] at hμ
      change n - (∑ j : Fin d, μ.1 j.castSucc) = μ.1 (Fin.last d)
      omega
    · simp

@[simp] theorem latticeCoordinates_head (d : ℕ) (n : ℤ) (z : Fin d → ℤ) (i : Fin d) :
    (latticeCoordinates d n z).1 i.castSucc = z i := by simp [latticeCoordinates]

@[simp] theorem latticeCoordinates_sum (d : ℕ) (n : ℤ) (μ : Lattice d n) :
    ∑ i, μ.1 i = n := μ.2

/-- A literal fundamental cell in the Euclidean root hyperplane. -/
def cell (d : ℕ) (z : Fin d → ℤ) : Set (rootSpace d) :=
  (coordinates d).symm ⁻¹' YoungRounding.cell z

theorem measurableSet_cell (d : ℕ) (z : Fin d → ℤ) : MeasurableSet (cell d z) :=
  (coordinatesContinuous d).symm.continuous.measurable (YoungRounding.measurableSet_cell z)

theorem cells_cover (d : ℕ) : (⋃ z : Fin d → ℤ, cell d z) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  refine Set.mem_iUnion.mpr ⟨YoungRounding.round ((coordinates d).symm x), ?_⟩
  exact (YoungRounding.round_eq_iff _ _).mp rfl

theorem cells_disjoint (d : ℕ) : Pairwise fun z w : Fin d → ℤ ↦ Disjoint (cell d z) (cell d w) := by
  intro z w hzw
  exact (YoungRounding.cells_disjoint hzw).preimage _

theorem coordinateMeasure_cell (d : ℕ) (z : Fin d → ℤ) :
    coordinateMeasure d (cell d z) = 1 := by
  rw [coordinateMeasure, Measure.map_apply (coordinatesContinuous d).continuous.measurable
    (measurableSet_cell d z)]
  have heq : (coordinatesContinuous d) ⁻¹' cell d z = YoungRounding.cell z := by
    ext x
    change (coordinates d).symm (coordinates d x) ∈ YoungRounding.cell z ↔ _
    rw [LinearEquiv.symm_apply_apply]
  rw [heq, YoungRounding.volume_cell]

/-- Integration is transported to the actual hyperplane, rather than merely
asserting an unspecified Jacobian cancellation. -/
theorem integral_coordinates (d : ℕ) (f : (Fin d → ℝ) → ℝ) :
    (∫ x : rootSpace d, f ((coordinates d).symm x) ∂coordinateMeasure d) = ∫ x, f x := by
  have h := (coordinates_measurePreserving d).integral_comp
    (coordinatesContinuous d).toHomeomorph.measurableEmbedding
    (fun x ↦ f ((coordinates d).symm x))
  have heq (x : Fin d → ℝ) : (coordinates d).symm (coordinatesContinuous d x) = x :=
    (coordinates d).symm_apply_apply x
  simpa only [heq] using h.symm

/-- The actual affine-label PMF, constructed by pushing forward a head law. -/
def latticePMF (d : ℕ) (n : ℤ) (P : PMF (Fin d → ℤ)) : PMF (Lattice d n) :=
  P.map (latticeCoordinates d n)

theorem latticePMF_apply (d : ℕ) (n : ℤ) (P : PMF (Fin d → ℤ)) (z : Fin d → ℤ) :
    latticePMF d n P (latticeCoordinates d n z) = P z := by
  unfold latticePMF
  rw [PMF.map_apply]
  simp only [(latticeCoordinates d n).injective.eq_iff]
  exact tsum_eq_single z (fun b hb ↦ if_neg (Ne.symm hb)) |>.trans (if_pos rfl)

/-- Transport the actual dither kernel to the full affine lattice. -/
def latticeRoundingPMF (d : ℕ) (n m : ℤ) (γ : ℝ) (μ : Lattice d n) : PMF (Lattice d m) :=
  latticePMF d m (YoungRounding.roundingPMF γ (fun i : Fin d ↦ (μ.1 i.castSucc : ℝ)))

theorem latticeRoundingPMF_apply (d : ℕ) (n m : ℤ) (γ : ℝ) (μ : Lattice d n) (z : Fin d → ℤ) :
    latticeRoundingPMF d n m γ μ (latticeCoordinates d m z) =
      YoungRounding.roundingPMF γ (fun i : Fin d ↦ (μ.1 i.castSucc : ℝ)) z :=
  latticePMF_apply d m _ z

/-- Scaled and translated interpolation on the full root hyperplane. The law
is indexed by the actual affine lattice; `a` is the recentering displacement
in the hyperplane and `h>0` is the cell scale. -/
def interpolate (d : ℕ) (n : ℤ) (h : ℝ) (a : rootSpace d)
    (P : Lattice d n → ℝ) (x : rootSpace d) : ℝ :=
  YoungRounding.affineDensity h ((coordinates d).symm a)
    (YoungRounding.interpolate (fun z ↦ P (latticeCoordinates d n z))) ((coordinates d).symm x)

theorem interpolate_integral (d : ℕ) (n : ℤ) (h : ℝ) (hh : 0 < h) (a : rootSpace d)
    (P : Lattice d n → ℝ) (hP : Summable P) :
    (∫ x, interpolate d n h a P x ∂coordinateMeasure d) = ∑' μ, P μ := by
  have hp : Summable (fun z ↦ P (latticeCoordinates d n z)) :=
    (latticeCoordinates d n).summable_iff.mpr hP
  unfold interpolate
  rw [integral_coordinates, YoungRounding.integral_affineDensity h hh,
    YoungRounding.integral_interpolate hp]
  exact (latticeCoordinates d n).tsum_eq P

/-- Exact `ℓ¹` preservation on the full affine lattice and root hyperplane. -/
theorem interpolate_l1_isometry (d : ℕ) (n : ℤ) (h : ℝ) (hh : 0 < h) (a : rootSpace d)
    (P Q : Lattice d n → ℝ) (hP : Summable P) (hQ : Summable Q) :
    (∫ x, |interpolate d n h a P x - interpolate d n h a Q x| ∂coordinateMeasure d) =
      ∑' μ, |P μ - Q μ| := by
  have hp : Summable (fun z ↦ P (latticeCoordinates d n z)) :=
    (latticeCoordinates d n).summable_iff.mpr hP
  have hq : Summable (fun z ↦ Q (latticeCoordinates d n z)) :=
    (latticeCoordinates d n).summable_iff.mpr hQ
  unfold interpolate
  rw [integral_coordinates d (fun y ↦
    |YoungRounding.affineDensity h ((coordinates d).symm a)
        (YoungRounding.interpolate (fun z ↦ P (latticeCoordinates d n z))) y -
      YoungRounding.affineDensity h ((coordinates d).symm a)
        (YoungRounding.interpolate (fun z ↦ Q (latticeCoordinates d n z))) y|),
    YoungRounding.affineDensity_l1_isometry h hh,
    YoungRounding.interpolate_l1_isometry hp hq]
  exact (latticeCoordinates d n).tsum_eq (fun μ ↦ |P μ - Q μ|)

/-- Positive affine density transport preserves Hellinger affinity exactly,
including its Jacobian on the density, at every positive scale. -/
theorem affineDensity_affinity (d : ℕ) (h : ℝ) (hh : 0 < h) (a : Fin d → ℝ)
    (f g : (Fin d → ℝ) → ℝ) :
    (∫ x, Real.sqrt (YoungRounding.affineDensity h a f x) *
      Real.sqrt (YoungRounding.affineDensity h a g x)) = ∫ x, Real.sqrt (f x) * Real.sqrt (g x) := by
  have hscale : 0 ≤ (h ^ Fintype.card (Fin d))⁻¹ := inv_nonneg.mpr (pow_nonneg hh.le _)
  have heq : (fun x ↦ Real.sqrt (YoungRounding.affineDensity h a f x) *
      Real.sqrt (YoungRounding.affineDensity h a g x)) =
      YoungRounding.affineDensity h a (fun x ↦ Real.sqrt (f x) * Real.sqrt (g x)) := by
    funext x
    simp only [YoungRounding.affineDensity, Real.sqrt_mul hscale]
    rw [show Real.sqrt (h ^ Fintype.card (Fin d))⁻¹ * Real.sqrt (f (h⁻¹ • (x - a))) *
          (Real.sqrt (h ^ Fintype.card (Fin d))⁻¹ * Real.sqrt (g (h⁻¹ • (x - a)))) =
        (Real.sqrt (h ^ Fintype.card (Fin d))⁻¹) ^ 2 *
          (Real.sqrt (f (h⁻¹ • (x - a))) * Real.sqrt (g (h⁻¹ • (x - a)))) by ring]
    rw [Real.sq_sqrt hscale]
  rw [heq, YoungRounding.integral_affineDensity h hh]

/-- Exact Hellinger-affinity preservation on the actual affine lattice. -/
theorem interpolate_affinity (d : ℕ) (n : ℤ) (h : ℝ) (hh : 0 < h) (a : rootSpace d)
    (P Q : Lattice d n → ℝ) (hP0 : ∀ μ, 0 ≤ P μ) (hQ0 : ∀ μ, 0 ≤ Q μ)
    (hP : Summable P) (hQ : Summable Q) :
    (∫ x, Real.sqrt (interpolate d n h a P x) * Real.sqrt (interpolate d n h a Q x)
      ∂coordinateMeasure d) = ∑' μ, Real.sqrt (P μ) * Real.sqrt (Q μ) := by
  have hp : Summable (fun z ↦ P (latticeCoordinates d n z)) :=
    (latticeCoordinates d n).summable_iff.mpr hP
  have hq : Summable (fun z ↦ Q (latticeCoordinates d n z)) :=
    (latticeCoordinates d n).summable_iff.mpr hQ
  unfold interpolate
  rw [integral_coordinates d (fun y ↦
    Real.sqrt (YoungRounding.affineDensity h ((coordinates d).symm a)
        (YoungRounding.interpolate (fun z ↦ P (latticeCoordinates d n z))) y) *
      Real.sqrt (YoungRounding.affineDensity h ((coordinates d).symm a)
        (YoungRounding.interpolate (fun z ↦ Q (latticeCoordinates d n z))) y)),
    affineDensity_affinity d h hh,
    YoungRounding.interpolate_affinity (fun z ↦ hP0 _) (fun z ↦ hQ0 _) hp hq]
  exact (latticeCoordinates d n).tsum_eq (fun μ ↦ Real.sqrt (P μ) * Real.sqrt (Q μ))

end Cloning.YoungHyperplane
