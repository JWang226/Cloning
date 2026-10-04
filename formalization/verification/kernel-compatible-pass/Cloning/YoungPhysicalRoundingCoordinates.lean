import Cloning.YoungUniformLocalPhysicalL1

/-! The actual physical Young law in the head coordinates used by the dither kernel. -/
noncomputable section
open scoped BigOperators Topology Classical
open MeasureTheory Filter
namespace Cloning.YoungHyperplane
open Cloning.TensorLie Cloning.YoungGeneral
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- The fixed coordinate Jacobian turns any root-space density into a head density. -/
def coordinateDensity (d : ℕ) (f : rootSpace d → ℝ) (x : Fin d → ℝ) : ℝ :=
  Real.sqrt ((d : ℝ) + 1) * f (coordinates d x)

theorem integral_coordinateDensity (d : ℕ) (f : rootSpace d → ℝ) :
    (∫ x, coordinateDensity d f x) = ∫ x, f x := by
  rw [volume_eq_sqrt_smul_coordinateMeasure, integral_smul_measure,
    ENNReal.toReal_ofReal (Real.sqrt_nonneg _), smul_eq_mul]
  unfold coordinateDensity
  rw [integral_const_mul]
  congr 1
  exact (coordinates_measurePreserving d).integral_comp
    (coordinatesContinuous d).toHomeomorph.measurableEmbedding f

theorem coordinateDensity_l1_isometry (d : ℕ) (f g : rootSpace d → ℝ) :
    (∫ x, |coordinateDensity d f x - coordinateDensity d g x|) = ∫ x, |f x-g x| := by
  have he : (fun x ↦ |coordinateDensity d f x - coordinateDensity d g x|) =
      coordinateDensity d (fun x ↦ |f x-g x|) := by
    funext x
    simp only [coordinateDensity, ← mul_sub, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
  rw [he, integral_coordinateDensity]

def tensorYoungHeadPMF (d N : ℕ) (p : Fin (d + 1) → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) : PMF (Fin d → ℤ) :=
  (tensorYoungLatticePMF d N p hp hs).map (latticeCoordinates d N).symm

theorem tensorYoungHeadPMF_apply (d N : ℕ) (p : Fin (d + 1) → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) (z : Fin d → ℤ) :
    tensorYoungHeadPMF d N p hp hs z =
      tensorYoungLatticePMF d N p hp hs (latticeCoordinates d N z) := by
  rw [tensorYoungHeadPMF, PMF.map_apply]
  rw [tsum_eq_single (latticeCoordinates d N z)]
  · simp
  · intro b hb
    have hne : z ≠ (latticeCoordinates d N).symm b := by
      intro h
      apply hb
      exact ((latticeCoordinates d N).apply_eq_iff_eq_symm_apply.mpr h).symm
    simp [hne]

/-- The head law is the literal pushforward of the actual finite Young measurement. -/
theorem tensorYoungHeadPMF_eq_map (d N : ℕ) (p : Fin (d + 1) → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) :
    tensorYoungHeadPMF d N p hp hs =
      (tensorYoungPMF N (d+1) p hp hs).map
        (fun μ i ↦ ((μ i.castSucc).val : ℤ)) := by
  rw [tensorYoungHeadPMF, tensorYoungLatticePMF, PMF.map_comp]
  congr 1
  funext μ
  exact (latticeCoordinates d N).symm_apply_apply _

def headAnchor (d N : ℕ) (p : Fin (d+1) → ℝ) : Fin d → ℝ :=
  fun i ↦ -Real.sqrt (N : ℝ) * p i.castSucc

def headDensity (d N : ℕ) (p : Fin (d+1) → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) : (Fin d → ℝ) → ℝ :=
  YoungRounding.affineDensity (Real.sqrt (N : ℝ))⁻¹ (headAnchor d N p)
    (YoungRounding.interpolate (fun z ↦ (tensorYoungHeadPMF d N p hp hs z).toReal))

theorem coordinateDensity_tensorYoungDensity (d N : ℕ) (p : Fin (d+1) → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) :
    coordinateDensity d (tensorYoungDensity d N p hp hs) = headDensity d N p hp hs := by
  funext x
  simp only [coordinateDensity, tensorYoungDensity, sampleInterpolate, euclideanInterpolate,
    interpolate, tensorYoungHeadPMF_apply, headDensity, headAnchor, sampleAnchor,
    LinearEquiv.symm_apply_apply, Int.cast_natCast]
  rw [← mul_assoc, mul_inv_cancel₀ (Real.sqrt_ne_zero'.mpr (by positivity)), one_mul]
  rfl

/-- The actual physical global L¹ limit in the precise dither coordinate system. -/
theorem headDensity_l1_tendsto (d : ℕ) (n : ℕ → ℕ)
    (hn : Tendsto n atTop atTop) (hn0 : ∀ k, 0 < n k)
    (p : ℕ → Fin (d + 1) → ℝ) (hp : ∀ k, ∑ i, p k i = 1)
    (hp0 : ∀ k i, 0 < p k i) (p₀ : Fin (d + 1) → ℝ) (hs₀ : ∑ i, p₀ i = 1)
    (hp₀ : ∀ i, 0 < p₀ i) (hord : StrictAnti p₀)
    (hlim : ∀ i, Tendsto (fun k ↦ p k i) atTop (𝓝 (p₀ i))) :
    Tendsto (fun k ↦ ∫ x, |headDensity d (n k) (p k) (fun i ↦ (hp0 k i).le) (hp k) x -
      coordinateDensity d (covarianceGaussian d p₀ hs₀) x|) atTop (𝓝 0) := by
  have h := tensorYoungDensity_l1_tendsto d n hn hn0 p hp hp0 p₀ hs₀ hp₀ hord hlim
  simpa only [← coordinateDensity_l1_isometry, coordinateDensity_tensorYoungDensity] using h

end Cloning.YoungHyperplane
