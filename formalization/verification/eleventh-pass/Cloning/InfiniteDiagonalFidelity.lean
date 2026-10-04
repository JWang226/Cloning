import Cloning.InfiniteFidelityBlockBound
import Cloning.InfiniteOccupationStates
import Cloning.MatrixFidelityScaling

/-!
# Fidelity of actual diagonal and thermal density operators

Finite Hilbert-basis compressions identify diagonal operator fidelity with
finite Hellinger sums. Trace-norm convergence of the compressions and fidelity
continuity then give the countable identity. Geometric thermal density
operators, including multimode ones, consequently have the previously proved
scalar thermal fidelity formula.
-/

namespace Cloning.InfiniteDiagonalFidelity

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped ComplexOrder InnerProductSpace Topology BigOperators MatrixOrder
open Filter InfiniteTraceClass InfiniteFidelity

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type*}

theorem matrixOf_vectorMixture_basis [DecidableEq ι] (b : HilbertBasis ι ℂ H)
    (p : ι → ℝ) (hp : Summable p) (s : Finset ι) :
    InfiniteFiniteCorner.matrixOf (fun i : s ↦ b i) (vectorMixture b p).1 =
      Matrix.diagonal (fun i : s ↦ (p i : ℂ)) := by
  classical
  ext i j
  change ⟪b i, (vectorMixture b p).1 (b j)⟫_ℂ = _
  rw [InfiniteOccupationStates.vectorMixture_apply_basis b p hp j, inner_smul_right,
    orthonormal_iff_ite.mp b.orthonormal]
  by_cases hij : i = j
  · subst j
    simp
  · have hval : (i : ι) ≠ j := fun h ↦ hij (Subtype.ext h)
    simp [hij, hval]

/-- Actual infinite-dimensional fidelity of arbitrary nonnegative summable
diagonal operators equals their countable Hellinger affinity. -/
theorem fidelity_vectorMixture (b : HilbertBasis ι ℂ H) (p q : ι → ℝ)
    (hp0 : ∀ i, 0 ≤ p i) (hq0 : ∀ i, 0 ≤ q i)
    (hp : Summable p) (hq : Summable q) :
    fidelity (vectorMixture b p).1 (vectorMixture b q).1
      (vectorMixture_nonneg b b.orthonormal.norm_eq_one p hp hp0)
      (vectorMixture_nonneg b b.orthonormal.norm_eq_one q hq hq0)
      (vectorMixture b p).2 (vectorMixture b q).2 = CountableScheffe.affinity p q := by
  classical
  let A := vectorMixture b p
  let B := vectorMixture b q
  have hA : 0 ≤ A.1 := vectorMixture_nonneg b b.orthonormal.norm_eq_one p hp hp0
  have hB : 0 ≤ B.1 := vectorMixture_nonneg b b.orthonormal.norm_eq_one q hq hq0
  let compress := fun (s : Finset ι) (T : TraceClass H) ↦
    sandwichCLM (basisProjection b s) (basisProjection b s) T
  have hpos (s : Finset ι) (T : TraceClass H) (hT : 0 ≤ T.1) :
      0 ≤ (compress s T).1 :=
    sandwichCLM_nonneg (basisProjection_isStarProjection b s).isSelfAdjoint T hT
  have hfid := tendsto_fidelity_traceClass (fun s ↦ compress s A) (fun s ↦ compress s B)
    A B (fun s ↦ hpos s A hA) (fun s ↦ hpos s B hB) hA hB
    (basis_sandwich_tendsto b A) (basis_sandwich_tendsto b B)
  have hfinite (s : Finset ι) :
      fidelity (compress s A).1 (compress s B).1 (hpos s A hA) (hpos s B hB)
        (compress s A).2 (compress s B).2 =
      ∑ i ∈ s, Real.sqrt (p i) * Real.sqrt (q i) := by
    let v : s → H := fun i ↦ b i
    have hv : Orthonormal ℂ v := InfiniteFiniteCorner.basisFamily_orthonormal b s
    have eF : fidelity (compress s A).1 (compress s B).1 (hpos s A hA) (hpos s B hB)
        (compress s A).2 (compress s B).2 =
        MatrixFidelity.fidelity (InfiniteFiniteCorner.matrixOf v A.1)
          (InfiniteFiniteCorner.matrixOf v B.1) := by
      simpa only [v, compress, InfiniteFiniteCorner.ofMatrix_matrixOf_basis, sandwichCLM_coe] using
        InfiniteFiniteCorner.fidelity_ofMatrix hv
          (InfiniteFiniteCorner.matrixOf_posSemidef v hA)
          (InfiniteFiniteCorner.matrixOf_posSemidef v hB)
    rw [eF]
    change MatrixFidelity.fidelity
      (InfiniteFiniteCorner.matrixOf (fun i : s ↦ b i) (vectorMixture b p).1)
      (InfiniteFiniteCorner.matrixOf (fun i : s ↦ b i) (vectorMixture b q).1) = _
    rw [matrixOf_vectorMixture_basis b p hp s, matrixOf_vectorMixture_basis b q hq s,
      MatrixFidelity.fidelity_diagonal_real _ _ (fun i : s ↦ hp0 i) (fun i : s ↦ hq0 i)]
    exact Finset.sum_coe_sort s (fun i ↦ Real.sqrt (p i) * Real.sqrt (q i))
  simp_rw [hfinite] at hfid
  exact tendsto_nhds_unique hfid (CountableScheffe.affinity_summable p q hp0 hq0 hp hq).hasSum

theorem stateFidelity_vectorMixture (b : HilbertBasis ι ℂ H) (p q : ι → ℝ)
    (hp0 : ∀ i, 0 ≤ p i) (hq0 : ∀ i, 0 ≤ q i) (hp : HasSum p 1) (hq : HasSum q 1) :
    stateFidelity (DensityState.vectorMixture b b.orthonormal.norm_eq_one p hp0 hp)
      (DensityState.vectorMixture b b.orthonormal.norm_eq_one q hq0 hq) =
      CountableScheffe.affinity p q :=
  fidelity_vectorMixture b p q hp0 hq0 hp.summable hq.summable

/-- A one-mode geometric thermal density operator in an actual occupation basis. -/
def geometricState (b : HilbertBasis ℕ ℂ H) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) :
    DensityState H :=
  DensityState.vectorMixture b b.orthonormal.norm_eq_one (Thermal.geometric q)
    (Thermal.geometric_nonneg hq0 hq1.le) (Thermal.geometric_hasSum hq0 hq1)

/-- The scalar thermal formula is the fidelity of the actual normalized
infinite-dimensional thermal density operators. -/
theorem stateFidelity_geometric (b : HilbertBasis ℕ ℂ H) (q x : ℝ)
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hx0 : 0 ≤ x) (hx1 : x < 1) :
    stateFidelity (geometricState b q hq0 hq1) (geometricState b x hx0 hx1) =
      Thermal.fidelity q x := by
  rw [geometricState, geometricState, stateFidelity_vectorMixture]
  unfold CountableScheffe.affinity
  simp_rw [← Real.sqrt_mul (Thermal.geometric_nonneg hq0 hq1.le _)]
  exact Thermal.affinity_tsum hq0 hq1 hx0 hx1

/-- The actual multimode product-geometric occupation density operator. -/
def productGeometricState {s : ℕ} (b : HilbertBasis (Fin s → ℕ) ℂ H)
    (q : Fin s → ℝ) (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i < 1) : DensityState H :=
  DensityState.vectorMixture b b.orthonormal.norm_eq_one
    (fun k ↦ ∏ i, Thermal.geometric (q i) (k i))
    (fun k ↦ Finset.prod_nonneg (fun i _ ↦ Thermal.geometric_nonneg (hq0 i) (hq1 i).le (k i)))
    (Thermal.multimode_geometric_hasSum hq0 hq1)

/-- Thermal fidelity is multiplicative on actual multimode density operators. -/
theorem stateFidelity_productGeometric {s : ℕ} (b : HilbertBasis (Fin s → ℕ) ℂ H)
    (q x : Fin s → ℝ) (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i < 1)
    (hx0 : ∀ i, 0 ≤ x i) (hx1 : ∀ i, x i < 1) :
    stateFidelity (productGeometricState b q hq0 hq1)
      (productGeometricState b x hx0 hx1) = ∏ i, Thermal.fidelity (q i) (x i) := by
  rw [productGeometricState, productGeometricState, stateFidelity_vectorMixture]
  unfold CountableScheffe.affinity
  have hp (k : Fin s → ℕ) : 0 ≤ ∏ i, Thermal.geometric (q i) (k i) :=
    Finset.prod_nonneg (fun i _ ↦ Thermal.geometric_nonneg (hq0 i) (hq1 i).le (k i))
  simp_rw [← Real.sqrt_mul (hp _)]
  exact (Thermal.multimode_affinity_of_product_laws hq0 hq1 hx0 hx1).tsum_eq

end
end Cloning.InfiniteDiagonalFidelity
