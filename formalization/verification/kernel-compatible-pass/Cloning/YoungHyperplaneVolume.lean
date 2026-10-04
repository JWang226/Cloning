import Cloning.YoungHyperplane

/-!
# The Euclidean volume normalization of the root hyperplane

The coordinate basis has Gram matrix `I + 11ᵀ`, determinant `d+1`.  Its
Euclidean fundamental volume is therefore `sqrt (d+1)`.  The measure identity
below relates the actual induced hyperplane volume to coordinate transport.
-/

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators Topology Classical
open MeasureTheory

namespace Cloning.YoungHyperplane


instance rootSpace_borelSpace (d : ℕ) : BorelSpace (rootSpace d) := by
  change BorelSpace {x : EuclideanSpace ℝ (Fin (d + 1)) // ∑ i, x i = 0}
  infer_instance

def rootBasis (d : ℕ) : Module.Basis (Fin d) ℝ (rootSpace d) :=
  (Pi.basisFun ℝ (Fin d)).map (coordinates d)

theorem rootSpace_finrank (d : ℕ) : Module.finrank ℝ (rootSpace d) = d := by
  simpa only [Fintype.card_fin] using Module.finrank_eq_card_basis (rootBasis d)

theorem rootBasis_inner (d : ℕ) (i j : Fin d) :
    inner ℝ (rootBasis d i) (rootBasis d j) = (if i = j then 1 else 0) + 1 := by
  change inner ℝ (rootBasis d i).1 (rootBasis d j).1 = _
  erw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [dotProduct, Pi.star_apply, star_trivial]
  rw [Fin.sum_univ_castSucc]
  simp only [rootBasis, Module.Basis.map_apply, Pi.basisFun_apply, coordinates_head,
    coordinates_last]
  by_cases hij : i = j
  · subst j
    simp [Pi.single_apply]
  · simp [Pi.single_apply, hij]

theorem rootBasis_gram_det (d : ℕ) :
    Matrix.det (fun i j : Fin d ↦ inner ℝ (rootBasis d i) (rootBasis d j)) = (d : ℝ) + 1 := by
  have heq : (fun i j : Fin d ↦ inner ℝ (rootBasis d i) (rootBasis d j)) =
      (1 : Matrix (Fin d) (Fin d) ℝ) +
        Matrix.replicateCol Unit (fun _ : Fin d ↦ (1 : ℝ)) *
        Matrix.replicateRow Unit (fun _ : Fin d ↦ (1 : ℝ)) := by
    ext i j
    rw [rootBasis_inner]
    simp [Matrix.mul_apply, Matrix.one_apply]
  rw [heq, Matrix.det_one_add_replicateCol_mul_replicateRow]
  simp [dotProduct, add_comm]

/-- The exact basis change from an orthonormal basis. -/
def rootOrthonormalBasis (d : ℕ) : OrthonormalBasis (Fin d) ℝ (rootSpace d) :=
  (stdOrthonormalBasis ℝ (rootSpace d)).reindex (finCongr (rootSpace_finrank d))

/-- Its determinant squared is the determinant of the explicit Gram matrix. -/
theorem rootBasis_det_sq (d : ℕ) :
    ((rootOrthonormalBasis d).toBasis.det (rootBasis d)) ^ 2 = (d : ℝ) + 1 := by
  let o := rootOrthonormalBasis d
  let M := o.toBasis.toMatrix (rootBasis d)
  have hgram : M.transpose * M = fun i j : Fin d ↦ inner ℝ (rootBasis d i) (rootBasis d j) := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.transpose_apply, M, Module.Basis.toMatrix_apply]
    have hrepr (x : rootSpace d) (k : Fin d) : o.toBasis.repr x k = inner ℝ (o k) x :=
      o.repr_apply_apply x k
    simp only [hrepr]
    simpa only [real_inner_comm] using o.sum_inner_mul_inner (rootBasis d i) (rootBasis d j)
  have hdet := congrArg Matrix.det hgram
  rw [Matrix.det_mul, Matrix.det_transpose, rootBasis_gram_det] at hdet
  simpa only [o, M, Module.Basis.det_apply, pow_two] using hdet

theorem rootBasis_abs_det (d : ℕ) :
    |(rootOrthonormalBasis d).toBasis.det (rootBasis d)| = Real.sqrt ((d : ℝ) + 1) := by
  rw [← rootBasis_det_sq d, Real.sqrt_sq_eq_abs]

theorem volume_rootBasis_parallelepiped (d : ℕ) :
    volume (parallelepiped (rootBasis d)) = ENNReal.ofReal (Real.sqrt ((d : ℝ) + 1)) := by
  rw [← (rootOrthonormalBasis d).addHaar_eq_volume,
    Measure.addHaar_parallelepiped, rootBasis_abs_det]

/-- The coordinate pushforward is the Haar measure normalized on the explicit
root basis. -/
theorem coordinateMeasure_eq_basis (d : ℕ) : coordinateMeasure d = (rootBasis d).addHaar := by
  have hpi : (Pi.basisFun ℝ (Fin d)).addHaar = volume := by
    rw [Module.Basis.addHaar_def, Module.Basis.parallelepiped_basisFun,
      addHaarMeasure_eq_volume_pi]
  rw [coordinateMeasure, ← hpi, Module.Basis.map_addHaar]
  rfl

/-- Canonical induced Euclidean hyperplane volume has the manuscript's
`sqrt(number of rows)` Jacobian relative to the explicit coordinate map. -/
theorem volume_eq_sqrt_smul_coordinateMeasure (d : ℕ) :
    (volume : Measure (rootSpace d)) =
      ENNReal.ofReal (Real.sqrt ((d : ℝ) + 1)) • coordinateMeasure d := by
  have h := Measure.addHaarMeasure_unique (volume : Measure (rootSpace d))
    (rootBasis d).parallelepiped
  rw [Module.Basis.coe_parallelepiped, volume_rootBasis_parallelepiped,
    ← Module.Basis.addHaar_def, ← coordinateMeasure_eq_basis] at h
  exact h

/-- The actual half-open fundamental cell has Euclidean volume `sqrt(d+1)`. -/
theorem volume_cell (d : ℕ) (z : Fin d → ℤ) :
    volume (cell d z) = ENNReal.ofReal (Real.sqrt ((d : ℝ) + 1)) := by
  rw [volume_eq_sqrt_smul_coordinateMeasure, Measure.smul_apply, coordinateMeasure_cell]
  simp

/-- A density with respect to Euclidean volume has the extra reciprocal
fundamental-cell volume appearing in the manuscript. -/
def euclideanInterpolate (d : ℕ) (n : ℤ) (h : ℝ) (a : rootSpace d)
    (P : Lattice d n → ℝ) (x : rootSpace d) : ℝ :=
  (Real.sqrt ((d : ℝ) + 1))⁻¹ * interpolate d n h a P x

/-- Exact integration formula for the Jacobian-normalized density. -/
theorem integral_volume_normalize (d : ℕ) (f : rootSpace d → ℝ) :
    (∫ x, (Real.sqrt ((d : ℝ) + 1))⁻¹ * f x) = ∫ x, f x ∂coordinateMeasure d := by
  have hj : 0 < Real.sqrt ((d : ℝ) + 1) := Real.sqrt_pos.2 (by positivity)
  rw [volume_eq_sqrt_smul_coordinateMeasure, integral_smul_measure,
    integral_const_mul, ENNReal.toReal_ofReal hj.le, smul_eq_mul,
    ← mul_assoc, mul_inv_cancel₀ hj.ne', one_mul]

/-- Exact normalization of the manuscript's interpolated full-label law with
respect to the canonical induced Euclidean hyperplane volume. -/
theorem euclideanInterpolate_integral (d : ℕ) (n : ℤ) (h : ℝ) (hh : 0 < h)
    (a : rootSpace d) (P : Lattice d n → ℝ) (hP : Summable P) :
    (∫ x, euclideanInterpolate d n h a P x) = ∑' μ, P μ := by
  unfold euclideanInterpolate
  rw [integral_volume_normalize, interpolate_integral d n h hh a P hP]

/-- The `sqrt(d+1)` factors cancel in the actual Euclidean `L¹` integral. -/
theorem euclideanInterpolate_l1_isometry (d : ℕ) (n : ℤ) (h : ℝ) (hh : 0 < h)
    (a : rootSpace d) (P Q : Lattice d n → ℝ) (hP : Summable P) (hQ : Summable Q) :
    (∫ x, |euclideanInterpolate d n h a P x - euclideanInterpolate d n h a Q x|) =
      ∑' μ, |P μ - Q μ| := by
  have hj : 0 ≤ (Real.sqrt ((d : ℝ) + 1))⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
  simp only [euclideanInterpolate, ← mul_sub, abs_mul, abs_of_nonneg hj]
  rw [integral_volume_normalize, interpolate_l1_isometry d n h hh a P Q hP hQ]

private theorem sqrt_scale_product (c : ℝ) (hc : 0 ≤ c) (x y : ℝ) :
    Real.sqrt (c * x) * Real.sqrt (c * y) = c * (Real.sqrt x * Real.sqrt y) := by
  rw [Real.sqrt_mul hc, Real.sqrt_mul hc]
  calc
    _ = (Real.sqrt c)^2 * (Real.sqrt x * Real.sqrt y) := by ring
    _ = _ := by rw [Real.sq_sqrt hc]

/-- Exact Hellinger preservation for the canonical Euclidean volume; the
hyperplane Jacobian is now proved and included, not left as a premise. -/
theorem euclideanInterpolate_affinity (d : ℕ) (n : ℤ) (h : ℝ) (hh : 0 < h)
    (a : rootSpace d) (P Q : Lattice d n → ℝ)
    (hP0 : ∀ μ, 0 ≤ P μ) (hQ0 : ∀ μ, 0 ≤ Q μ) (hP : Summable P) (hQ : Summable Q) :
    (∫ x, Real.sqrt (euclideanInterpolate d n h a P x) *
      Real.sqrt (euclideanInterpolate d n h a Q x)) =
        ∑' μ, Real.sqrt (P μ) * Real.sqrt (Q μ) := by
  have hj : 0 ≤ (Real.sqrt ((d : ℝ) + 1))⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
  simp only [euclideanInterpolate, sqrt_scale_product _ hj]
  rw [integral_volume_normalize, interpolate_affinity d n h hh a P Q hP0 hQ0 hP hQ]

end Cloning.YoungHyperplane
