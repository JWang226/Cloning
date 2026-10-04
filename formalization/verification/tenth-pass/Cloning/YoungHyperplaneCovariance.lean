import Cloning.YoungHyperplaneSampling
import Mathlib.Analysis.InnerProductSpace.Symmetric

/-!
# The simplex covariance on the actual root hyperplane

These are the exact covariance determinant and inverse quadratic identities
used in the Young local limit. They are finite-dimensional algebraic identities,
not local-limit or Stirling asymptotics.
-/

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators Topology Classical Matrix
open MeasureTheory

namespace Cloning.YoungHyperplane

/-- The covariance of the first `d` coordinates of a multinomial fluctuation. -/
def headCovariance (d : ℕ) (p : Fin (d + 1) → ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  fun i j ↦ (if i = j then p i.castSucc else 0) - p i.castSucc * p j.castSucc

/-- The principal minor has the exact product normalization. -/
theorem headCovariance_det (d : ℕ) (p : Fin (d + 1) → ℝ) (hp : ∑ i, p i = 1) :
    Matrix.det (headCovariance d p) = ∏ i, p i := by
  have heq : headCovariance d p =
      Matrix.diagonal (fun i : Fin d ↦ p i.castSucc) *
        (1 + Matrix.replicateCol Unit (fun _ : Fin d ↦ (1 : ℝ)) *
          Matrix.replicateRow Unit (fun i : Fin d ↦ -p i.castSucc)) := by
    ext i j
    rw [Matrix.diagonal_mul]
    simp only [headCovariance, Matrix.add_apply, Matrix.mul_apply, Matrix.one_apply]
    simp only [Matrix.replicateCol_apply, Matrix.replicateRow_apply, one_mul,
      Fintype.sum_unique]
    by_cases hij : i = j
    · simp [hij]; ring
    · simp [hij]
  rw [heq, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_one_add_replicateCol_mul_replicateRow]
  rw [Fin.sum_univ_castSucc] at hp
  simp only [dotProduct, mul_one, Finset.sum_neg_distrib]
  rw [Fin.prod_univ_castSucc]
  congr 1
  linarith

/-- The induced covariance endomorphism in the nonorthonormal root basis has
matrix `C G`, where `G=I+11ᵀ` is the root-basis Gram matrix. -/
def rootCovarianceMatrix (d : ℕ) (p : Fin (d + 1) → ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  headCovariance d p * (show Matrix (Fin d) (Fin d) ℝ from
    fun i j ↦ inner ℝ (rootBasis d i) (rootBasis d j))

theorem rootCovarianceMatrix_det (d : ℕ) (p : Fin (d + 1) → ℝ) (hp : ∑ i, p i = 1) :
    Matrix.det (rootCovarianceMatrix d p) = ((d : ℝ) + 1) * ∏ i, p i := by
  rw [rootCovarianceMatrix, Matrix.det_mul, headCovariance_det d p hp, rootBasis_gram_det]
  ring

/-- The covariance is a genuine endomorphism of the Euclidean root hyperplane. -/
def rootCovariance (d : ℕ) (p : Fin (d + 1) → ℝ) : rootSpace d →ₗ[ℝ] rootSpace d :=
  (coordinates d).toLinearMap ∘ₗ (rootCovarianceMatrix d p).toLin' ∘ₗ
    (coordinates d).symm.toLinearMap

theorem rootCovariance_det (d : ℕ) (p : Fin (d + 1) → ℝ) (hp : ∑ i, p i = 1) :
    LinearMap.det (rootCovariance d p) = ((d : ℝ) + 1) * ∏ i, p i := by
  rw [rootCovariance, LinearMap.det_conj, LinearMap.det_toLin']
  exact rootCovarianceMatrix_det d p hp

/-- The root Gram action adds the sum of the coordinates to each component. -/
theorem rootGram_mulVec (d : ℕ) (x : Fin d → ℝ) (i : Fin d) :
    ((fun i j ↦ inner ℝ (rootBasis d i) (rootBasis d j)) *ᵥ x) i = x i + ∑ j, x j := by
  simp only [Matrix.mulVec, dotProduct, rootBasis_inner, add_mul, Finset.sum_add_distrib]
  simp

/-- Ordinary coordinate action of the principal covariance minor. -/
theorem headCovariance_mulVec (d : ℕ) (p : Fin (d + 1) → ℝ) (x : Fin d → ℝ) (i : Fin d) :
    (headCovariance d p *ᵥ x) i =
      p i.castSucc * x i - p i.castSucc * ∑ j, p j.castSucc * x j := by
  simp only [Matrix.mulVec, dotProduct, headCovariance, sub_mul, Finset.sum_sub_distrib]
  rw [show (∑ j : Fin d, (if i = j then p i.castSucc else 0) * x j) = p i.castSucc * x i by simp]
  rw [Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The constructed endomorphism is exactly the ambient covariance
`diag(p) - p pᵀ`, restricted to the true Euclidean sum-zero hyperplane. -/
theorem rootCovariance_apply (d : ℕ) (p : Fin (d + 1) → ℝ) (hp : ∑ i, p i = 1)
    (x : rootSpace d) (i : Fin (d + 1)) :
    (rootCovariance d p x).1 i = p i * x.1 i - p i * ∑ j, p j * x.1 j := by
  have hhead (k : Fin d) : (rootCovariance d p x).1 k.castSucc =
      p k.castSucc * x.1 k.castSucc - p k.castSucc * ∑ j, p j * x.1 j := by
    change (coordinates d (((rootCovarianceMatrix d p).toLin') ((coordinates d).symm x))).1 k.castSucc = _
    rw [coordinates_head, Matrix.toLin'_apply, rootCovarianceMatrix, ← Matrix.mulVec_mulVec]
    rw [headCovariance_mulVec]
    simp only [rootGram_mulVec, coordinates_symm_apply]
    have hx : (∑ j : Fin d, x.1 j.castSucc) + x.1 (Fin.last d) = 0 := by
      have hx0 : (∑ j, x.1 j) = 0 := x.2
      simpa only [Fin.sum_univ_castSucc] using hx0
    have hp' : (∑ j : Fin d, p j.castSucc) + p (Fin.last d) = 1 := by
      simpa only [Fin.sum_univ_castSucc] using hp
    rw [Fin.sum_univ_castSucc]
    simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul]
    have hpx := congrArg (fun t : ℝ ↦ t * (∑ j : Fin d, x.1 j.castSucc)) hp'
    have hsum : (∑ j : Fin d, p j.castSucc) * (∑ j : Fin d, x.1 j.castSucc) =
        (∑ j : Fin d, x.1 j.castSucc) + p (Fin.last d) * x.1 (Fin.last d) := by
      have hlast := congrArg (fun t : ℝ ↦ p (Fin.last d) * t) hx
      nlinarith only [hpx, hlast]
    rw [hsum]
    ring
  refine Fin.lastCases ?_ (fun k ↦ hhead k) i
  have hout : (∑ j : Fin d, (rootCovariance d p x).1 j.castSucc) +
      (rootCovariance d p x).1 (Fin.last d) = 0 := by
    have h0 : (∑ j, (rootCovariance d p x).1 j) = 0 := (rootCovariance d p x).2
    simpa only [Fin.sum_univ_castSucc] using h0
  have htar : (∑ j, (p j * x.1 j - p j * ∑ k, p k * x.1 k)) = 0 := by
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hp, one_mul, sub_self]
  rw [Fin.sum_univ_castSucc] at htar
  simp only [hhead] at hout
  linarith only [hout, htar]

/-- Explicit inverse vector, subtracting the mean to restore zero total. -/
def inverseCovarianceVector (d : ℕ) (p : Fin (d + 1) → ℝ) (x : rootSpace d) : rootSpace d :=
  ⟨WithLp.toLp 2 (fun i ↦ x.1 i / p i - (∑ j, x.1 j / p j) / ((d : ℝ) + 1)), by
    change (∑ i, (x.1 i / p i - (∑ j, x.1 j / p j) / ((d : ℝ) + 1))) = 0
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      Nat.cast_add, Nat.cast_one]
    field_simp
    ring⟩

@[simp] theorem inverseCovarianceVector_apply (d : ℕ) (p : Fin (d + 1) → ℝ)
    (x : rootSpace d) (i : Fin (d + 1)) :
    (inverseCovarianceVector d p x).1 i =
      x.1 i / p i - (∑ j, x.1 j / p j) / ((d : ℝ) + 1) := rfl

/-- The candidate inverse solves the covariance equation for every root-space
vector; it is not merely a formula for a quadratic form. -/
theorem rootCovariance_inverseVector (d : ℕ) (p : Fin (d + 1) → ℝ)
    (hp : ∑ i, p i = 1) (hp0 : ∀ i, p i ≠ 0) (x : rootSpace d) :
    rootCovariance d p (inverseCovarianceVector d p x) = x := by
  have hsum : (∑ j, p j * (inverseCovarianceVector d p x).1 j) =
      -(∑ j, x.1 j / p j) / ((d : ℝ) + 1) := by
    simp only [inverseCovarianceVector_apply, mul_sub, mul_div_cancel₀ _ (hp0 _),
      Finset.sum_sub_distrib, ← Finset.sum_mul, hp, one_mul]
    have hx : (∑ j, x.1 j) = 0 := x.2
    rw [hx]
    ring
  apply Subtype.ext
  ext i
  rw [rootCovariance_apply d p hp, hsum, inverseCovarianceVector_apply]
  rw [mul_sub, mul_div_cancel₀ _ (hp0 i)]
  ring

/-- The inverse quadratic form is the manuscript's exact weighted sum. -/
theorem inverseCovariance_quadratic (d : ℕ) (p : Fin (d + 1) → ℝ) (x : rootSpace d) :
    inner ℝ x (inverseCovarianceVector d p x) = ∑ i, (x.1 i)^2 / p i := by
  change inner ℝ x.1 (inverseCovarianceVector d p x).1 = _
  erw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [dotProduct, Pi.star_apply, star_trivial, inverseCovarianceVector_apply,
    sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum]
  have hx : (∑ j, x.1 j) = 0 := x.2
  rw [hx, mul_zero, sub_zero]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The covariance determinant is nonzero whenever all spectral coordinates
are nonzero. -/
theorem rootCovariance_det_ne_zero (d : ℕ) (p : Fin (d + 1) → ℝ)
    (hp : ∑ i, p i = 1) (hp0 : ∀ i, p i ≠ 0) :
    LinearMap.det (rootCovariance d p) ≠ 0 := by
  rw [rootCovariance_det d p hp]
  exact mul_ne_zero (by positivity) (Finset.prod_ne_zero_iff.mpr (fun i _ ↦ hp0 i))

/-- The inverse used in the Gaussian density is an actual linear equivalence. -/
def rootCovarianceEquiv (d : ℕ) (p : Fin (d + 1) → ℝ)
    (hp : ∑ i, p i = 1) (hp0 : ∀ i, p i ≠ 0) : rootSpace d ≃ₗ[ℝ] rootSpace d :=
  LinearMap.equivOfIsUnitDet (isUnit_iff_ne_zero.mpr (rootCovariance_det_ne_zero d p hp hp0))

@[simp] theorem rootCovarianceEquiv_apply (d : ℕ) (p : Fin (d + 1) → ℝ)
    (hp : ∑ i, p i = 1) (hp0 : ∀ i, p i ≠ 0) (x : rootSpace d) :
    rootCovarianceEquiv d p hp hp0 x = rootCovariance d p x := by
  simp [rootCovarianceEquiv]

/-- The explicit vector formula is exactly the inverse of the constructed
covariance equivalence. -/
theorem rootCovarianceEquiv_symm_apply (d : ℕ) (p : Fin (d + 1) → ℝ)
    (hp : ∑ i, p i = 1) (hp0 : ∀ i, p i ≠ 0) (x : rootSpace d) :
    (rootCovarianceEquiv d p hp hp0).symm x = inverseCovarianceVector d p x := by
  apply (rootCovarianceEquiv d p hp hp0).injective
  rw [LinearEquiv.apply_symm_apply, rootCovarianceEquiv_apply, rootCovariance_inverseVector d p hp hp0]

/-- Exact Gaussian inverse quadratic form for the actual root-space operator. -/
theorem rootCovarianceEquiv_inverse_quadratic (d : ℕ) (p : Fin (d + 1) → ℝ)
    (hp : ∑ i, p i = 1) (hp0 : ∀ i, p i ≠ 0) (x : rootSpace d) :
    inner ℝ x ((rootCovarianceEquiv d p hp hp0).symm x) = ∑ i, (x.1 i)^2 / p i := by
  rw [rootCovarianceEquiv_symm_apply, inverseCovariance_quadratic]

/-- Strict positivity of the inverse quadratic form follows from a strictly
positive spectrum. -/
theorem inverseCovariance_quadratic_pos (d : ℕ) (p : Fin (d + 1) → ℝ)
    (hp : ∀ i, 0 < p i) (x : rootSpace d) (hx : x ≠ 0) :
    0 < inner ℝ x (inverseCovarianceVector d p x) := by
  rw [inverseCovariance_quadratic]
  have hi : ∃ i, x.1 i ≠ 0 := by
    by_contra h
    push_neg at h
    apply hx
    apply Subtype.ext
    ext i
    simpa using h i
  obtain ⟨i, hi⟩ := hi
  exact Finset.sum_pos' (fun j _ ↦ div_nonneg (sq_nonneg _) (hp j).le)
    ⟨i, Finset.mem_univ i, div_pos (sq_pos_of_ne_zero hi) (hp i)⟩

/-- The root covariance is positive definite on the actual Euclidean
hyperplane whenever `p` is a positive normalized spectrum. -/
theorem rootCovariance_quadratic_pos (d : ℕ) (p : Fin (d + 1) → ℝ)
    (hp : ∑ i, p i = 1) (hp0 : ∀ i, 0 < p i) (x : rootSpace d) (hx : x ≠ 0) :
    0 < inner ℝ x (rootCovariance d p x) := by
  let e := rootCovarianceEquiv d p hp (fun i ↦ (hp0 i).ne')
  have hy : e x ≠ 0 := by
    intro h
    apply hx
    exact e.injective (by simpa using h)
  have h := inverseCovariance_quadratic_pos d p hp0 (e x) hy
  rw [← rootCovarianceEquiv_symm_apply d p hp (fun i ↦ (hp0 i).ne')] at h
  change 0 < inner ℝ (e x) (e.symm (e x)) at h
  rw [LinearEquiv.symm_apply_apply, real_inner_comm] at h
  simpa only [e, rootCovarianceEquiv_apply] using h

/-- Bilinear form of the actual covariance restriction. -/
theorem rootCovariance_inner (d : ℕ) (p : Fin (d + 1) → ℝ) (hp : ∑ i, p i = 1)
    (x y : rootSpace d) :
    inner ℝ x (rootCovariance d p y) =
      (∑ i, p i * x.1 i * y.1 i) - (∑ i, p i * x.1 i) * (∑ i, p i * y.1 i) := by
  change inner ℝ x.1 (rootCovariance d p y).1 = _
  erw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [dotProduct, Pi.star_apply, star_trivial, rootCovariance_apply d p hp]
  calc
    (∑ i, (p i * y.1 i - p i * ∑ j, p j * y.1 j) * x.1 i) =
        ∑ i, (p i * x.1 i * y.1 i - (p i * x.1 i) * ∑ j, p j * y.1 j) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by rw [Finset.sum_sub_distrib, ← Finset.sum_mul]

/-- Symmetry, together with the preceding strict positivity theorem, verifies
that the constructed operator is a nondegenerate Euclidean covariance. -/
theorem rootCovariance_isSymmetric (d : ℕ) (p : Fin (d + 1) → ℝ) (hp : ∑ i, p i = 1) :
    (rootCovariance d p).IsSymmetric := by
  intro x y
  rw [real_inner_comm y (rootCovariance d p x),
    rootCovariance_inner d p hp y x, rootCovariance_inner d p hp x y]
  rw [mul_comm (∑ i, p i * y.1 i) (∑ i, p i * x.1 i)]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

end Cloning.YoungHyperplane
