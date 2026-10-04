import Cloning.ThermalWitness

/-!
# Thermal witnesses are scaled geometric states

The actual bounded multimode fidelity witness is a strictly positive scalar
multiple of a normalized product-geometric trace-class state. This identifies
its operator, not just its diagonal moments, with the thermal Gaussian object
used by the Fourier argument.
-/

noncomputable section
open scoped BigOperators
namespace Cloning.ThermalWitness
open Cloning.InfiniteTraceClass Cloning.InfiniteOccupationStates
set_option backward.isDefEq.respectTransparency false

/-- Geometric parameter of each thermal-witness factor. -/
def witnessGeometricParameter {s : ℕ} (q x : Fin s → ℝ) (i : Fin s) : ℝ :=
  Real.sqrt (q i / x i)

/-- Exact positive scalar multiplying the normalized geometric state. -/
def witnessGeometricScale {s : ℕ} (q x : Fin s → ℝ) : ℝ :=
  ∏ i, Real.sqrt ((1 - q i) / (1 - x i)) / (1 - witnessGeometricParameter q x i)

lemma witnessGeometricParameter_pos {s : ℕ} {q x : Fin s → ℝ}
    (hq0 : ∀ i, 0 < q i) (hqx : ∀ i, q i < x i) (i : Fin s) :
    0 < witnessGeometricParameter q x i :=
  Real.sqrt_pos.mpr (div_pos (hq0 i) ((hq0 i).trans (hqx i)))

lemma witnessGeometricParameter_lt_one {s : ℕ} {q x : Fin s → ℝ}
    (hq0 : ∀ i, 0 < q i) (hqx : ∀ i, q i < x i) (i : Fin s) :
    witnessGeometricParameter q x i < 1 := by
  unfold witnessGeometricParameter
  rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 1)]
  simpa using (div_lt_one ((hq0 i).trans (hqx i))).mpr (hqx i)

lemma witnessGeometricScale_pos {s : ℕ} {q x : Fin s → ℝ}
    (hq0 : ∀ i, 0 < q i) (hqx : ∀ i, q i < x i) (hx1 : ∀ i, x i < 1) :
    0 < witnessGeometricScale q x := by
  apply Finset.prod_pos
  intro i _
  apply div_pos
  · exact Real.sqrt_pos.mpr (div_pos (sub_pos.mpr ((hqx i).trans (hx1 i)))
      (sub_pos.mpr (hx1 i)))
  · exact sub_pos.mpr (witnessGeometricParameter_lt_one hq0 hqx i)

/-- Exact coefficient identity, valid for every occupation vector. -/
lemma productWitness_eq_scale_geometric {s : ℕ} {q x : Fin s → ℝ}
    (hq0 : ∀ i, 0 < q i) (hqx : ∀ i, q i < x i) (hx1 : ∀ i, x i < 1)
    (k : Fin s → ℕ) :
    productWitness q x k = witnessGeometricScale q x *
      productGeometric (witnessGeometricParameter q x) k := by
  unfold productWitness witnessGeometricScale productGeometric
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  rw [Thermal.witness_closed (hq0 i).le ((hqx i).trans (hx1 i))
    ((hq0 i).trans (hqx i)).le (hx1 i)]
  have hy : 1 - witnessGeometricParameter q x i ≠ 0 :=
    (sub_pos.mpr (witnessGeometricParameter_lt_one hq0 hqx i)).ne'
  unfold Thermal.geometric
  rw [← mul_assoc, div_mul_cancel₀ _ hy]
  rfl

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Equality of the actual bounded witness operator with a positive scalar
multiple of a product-geometric state. It holds on the entire Hilbert space. -/
lemma productWitnessOperator_eq_scale_geometric {s : ℕ}
    (b : HilbertBasis (Fin s → ℕ) ℂ H) {q x : Fin s → ℝ}
    (hq0 : ∀ i, 0 < q i) (hqx : ∀ i, q i < x i) (hx1 : ∀ i, x i < 1) :
    productWitnessOperator b q x = (witnessGeometricScale q x : ℂ) •
      (vectorMixture b (productGeometric (witnessGeometricParameter q x))).1 := by
  apply ContinuousLinearMap.ext_on
    (Submodule.dense_iff_topologicalClosure_eq_top.mpr b.dense_span)
  rintro _ ⟨k, rfl⟩
  rw [productWitnessOperator_apply_basis b hq0 hqx hx1,
    ContinuousLinearMap.smul_apply, vectorMixture_apply_basis b _
      (productGeometric_hasSum (fun i => (witnessGeometricParameter_pos hq0 hqx i).le)
        (witnessGeometricParameter_lt_one hq0 hqx)).summable,
    productWitness_eq_scale_geometric hq0 hqx hx1, Complex.ofReal_mul, smul_smul]

/-- Trace-class version of the same exact identification. -/
lemma productWitnessTraceClass_eq_scale_geometric {s : ℕ}
    (b : HilbertBasis (Fin s → ℕ) ℂ H) {q x : Fin s → ℝ}
    (hq0 : ∀ i, 0 < q i) (hqx : ∀ i, q i < x i) (hx1 : ∀ i, x i < 1) :
    vectorMixture b (productWitness q x) = (witnessGeometricScale q x : ℂ) •
      vectorMixture b (productGeometric (witnessGeometricParameter q x)) := by
  apply Subtype.ext
  exact productWitnessOperator_eq_scale_geometric b hq0 hqx hx1

end Cloning.ThermalWitness
