import Cloning.TensorLANEmbeddingSchurWeights
import Cloning.TensorLANEmbeddingClassicalLimit

/-! Exact classical density of the physical copy instrument. -/
noncomputable section
open scoped BigOperators Topology Classical InnerProductSpace NNReal ENNReal
open MeasureTheory Filter
namespace Cloning.TensorLAN
open Cloning.YoungHyperplane Cloning.PCTJointGaussianWhitening Cloning.TensorLie
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

/-- The actual mixture of uniform cells is the physical Young density,
including repeated sector labels and all dependent affine coordinates. -/
theorem sum_copy_rootCellDensity (N d : ℕ) (hN : 0 < N)
    (p₀ p : Fin (d+1) → ℝ) (hp : ∀ a, 0 ≤ p a) (hs : ∑ a, p a = 1)
    (x : rootSpace d) :
    (∑ i : SchurCopy N (d+1), ((recursivePhysicalDecomposition N (d+1)).get i).character p *
      rootCellDensity d N p₀ (schurCopyLattice N d i) x) =
      fixedBaseYoungDensity d N p₀ p hp hs x := by
  let mu := sampleLabel d N p₀ x
  have hx := mem_sampleCell_sampleLabel d N p₀ x
  have hi (i : SchurCopy N (d+1)) : rootCellDensity d N p₀ (schurCopyLattice N d i) x =
      (Real.sqrt (N : ℝ)^d / Real.sqrt ((d : ℝ)+1)) *
        (if schurCopyLattice N d i = mu then (1 : ℝ) else 0) := by
    rw [rootCellDensity, sampleInterpolate_eq_on_cell d N (by exact_mod_cast hN) p₀ _ mu x hx]
    simp only [PMF.pure_apply]
    split_ifs <;> simp_all [mu, eq_comm]
  rw [fixedBaseYoungDensity, sampleInterpolate_eq_on_cell d N (by exact_mod_cast hN) p₀ _ mu x hx,
    tensorYoungLatticePMF_toReal_eq_sum_copies, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [hi]
  split_ifs <;> simp only [Int.cast_natCast] <;> ring

/-- In the final Lebesgue coordinates the literal instrument emits exactly the
Jacobian-correct fixed-base physical Young density. -/
theorem sum_copy_physicalCellDensity (N d : ℕ) (hN : 0 < N)
    (p₀ : Fin (d+1) → ℝ) (hp₀ : ∀ a, 0 < p₀ a)
    (b : OrthonormalBasis (Fin (d+1)) ℝ (EuclideanSpace ℝ (Fin (d+1))))
    (hb : b 0 = sqrtSpectrum p₀)
    (p : Fin (d+1) → ℝ) (hp : ∀ a, 0 ≤ p a) (hs : ∑ a, p a = 1)
    (y : Fin d → ℝ) :
    (∑ i : SchurCopy N (d+1), ((recursivePhysicalDecomposition N (d+1)).get i).character p *
      physicalCellDensity p₀ hp₀ b hb N i y) =
      whiteningDensity (rootWhitening p₀ hp₀ b hb)
        (fixedBaseYoungDensity d N p₀ p hp hs) y := by
  simp only [physicalCellDensity, if_pos hN, whiteningDensity]
  rw [← sum_copy_rootCellDensity N d hN p₀ p hp hs, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Integrating any bounded or unbounded measurable label fibre commutes
exactly with the actual whitening change of variables. -/
theorem binMass_whiteningDensity {d : ℕ} {Λ : Type*} [MeasurableSpace Λ]
    [MeasurableSingletonClass Λ]
    (W : rootSpace d ≃L[ℝ] (Fin d → ℝ)) (q : rootSpace d → Λ) (hq : Measurable q)
    (f : rootSpace d → ℝ) (a : Λ) :
    YoungRounding.binMass volume (fun y => q (W.symm y)) (whiteningDensity W f) a =
      YoungRounding.binMass volume q f a := by
  have hm : Measurable (fun y => q (W.symm y)) := hq.comp W.symm.continuous.measurable
  rw [YoungRounding.binMass, YoungRounding.binMass,
    ← integral_indicator (hm (measurableSet_singleton a)),
    ← integral_indicator (hq (measurableSet_singleton a))]
  have he (y : Fin d → ℝ) :
      ((fun y => q (W.symm y)) ⁻¹' {a}).indicator (whiteningDensity W f) y =
        whiteningDensity W ((q ⁻¹' {a}).indicator f) y := by
    unfold whiteningDensity
    by_cases h : q (W.symm y) = a <;> simp [Set.indicator, h]
  simp_rw [he]
  exact whiteningDensity_integral W _

/-- Exact quantization recovery remains true after the physical whitening
chart, with the quantizer fixed at the base spectrum. -/
theorem binMass_physicalCellQuantizer (N d : ℕ) (hN : 0 < N)
    (p₀ : Fin (d+1) → ℝ) (hp₀ : ∀ a, 0 < p₀ a)
    (b : OrthonormalBasis (Fin (d+1)) ℝ (EuclideanSpace ℝ (Fin (d+1))))
    (hb : b 0 = sqrtSpectrum p₀)
    (p : Fin (d+1) → ℝ) (hp : ∀ a, 0 ≤ p a) (hs : ∑ a, p a = 1)
    (mu : Lattice d (N : ℤ)) :
    YoungRounding.binMass volume (physicalCellQuantizer p₀ hp₀ b hb N)
      (whiteningDensity (rootWhitening p₀ hp₀ b hb) (fixedBaseYoungDensity d N p₀ p hp hs)) mu =
        (tensorYoungLatticePMF d N p hp hs mu).toReal := by
  change YoungRounding.binMass volume
    (fun y => sampleLabel d N p₀ ((rootWhitening p₀ hp₀ b hb).symm y)) _ mu = _
  rw [binMass_whiteningDensity _ _ (measurable_sampleLabel d N p₀),
    binMass_fixedBaseYoungDensity d N hN]

end Cloning.TensorLAN
