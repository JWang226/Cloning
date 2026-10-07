import Cloning.InfinitePureStateContinuity
import Mathlib.Data.Finset.Powerset

/-!
# Symmetric occupation vectors in the computational tensor basis

A subset of `Fin L` labels the tensor-basis vector whose excited slots are
exactly that subset. The `j`-excitation symmetric vector is the normalized
uniform sum of those basis vectors. Its normalization and orthogonality are
proved from the cardinality of `powersetCard`, rather than supplied as data.
-/
noncomputable section
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000
open scoped BigOperators InnerProductSpace Topology
open Filter

namespace Cloning.SymmetricOccupation

abbrev TensorSpace (L : ℕ) := lp (fun _ : Finset (Fin L) => ℂ) 2
abbrev OccupationSpace (L : ℕ) := lp (fun _ : Fin (L + 1) => ℂ) 2

private theorem count_card (L j : ℕ) :
    (Finset.univ.filter (fun S : Finset (Fin L) => S.card = j)).card = L.choose j := by
  have h : Finset.univ.filter (fun S : Finset (Fin L) => S.card = j) =
      Finset.powersetCard j (Finset.univ : Finset (Fin L)) := by
    ext S
    simp
  rw [h, Finset.card_powersetCard]
  simp

/-- Squared coefficients of the symmetric occupation vector. -/
def weight (L : ℕ) (j : Fin (L + 1)) (S : Finset (Fin L)) : ℝ :=
  if S.card = j.val then (L.choose j.val : ℝ)⁻¹ else 0

theorem weight_nonneg (L : ℕ) (j : Fin (L + 1)) (S : Finset (Fin L)) :
    0 ≤ weight L j S := by
  unfold weight
  split_ifs <;> positivity

theorem weight_hasSum (L : ℕ) (j : Fin (L + 1)) : HasSum (weight L j) 1 := by
  classical
  have hj : j.val ≤ L := by omega
  have hc : (L.choose j.val : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hj).ne'
  have hs : ∑ S : Finset (Fin L), weight L j S = 1 := by
    simp only [weight, ← Finset.sum_filter]
    rw [Finset.sum_const, nsmul_eq_mul, count_card, mul_inv_cancel₀ hc]
  exact hs ▸ hasSum_fintype (weight L j)

/-- Normalized symmetric sum of the computational tensors with `j` excitations. -/
def column (L : ℕ) (j : Fin (L + 1)) : TensorSpace L :=
  Cloning.CoherentCoefficients.amplitudeVector (weight L j)
    (weight_nonneg L j) (weight_hasSum L j)

theorem column_apply (L : ℕ) (j : Fin (L + 1)) (S : Finset (Fin L)) :
    column L j S = if S.card = j.val then
      ((Real.sqrt (L.choose j.val : ℝ))⁻¹ : ℂ) else 0 := by
  simp only [column, Cloning.CoherentCoefficients.amplitudeVector_apply, weight]
  split_ifs <;> simp [Real.sqrt_inv]

theorem column_norm (L : ℕ) (j : Fin (L + 1)) : ‖column L j‖ = 1 :=
  Cloning.CoherentCoefficients.amplitudeVector_norm _ _ _

theorem column_orthonormal (L : ℕ) : Orthonormal ℂ (column L) := by
  refine ⟨column_norm L, ?_⟩
  intro i j hij
  rw [lp.inner_eq_tsum]
  have hzero : ∀ S : Finset (Fin L), ⟪column L i S, column L j S⟫_ℂ = 0 := by
    intro S
    rw [column_apply, column_apply]
    split_ifs with hi hj
    · exact False.elim (hij (Fin.ext (hi.symm.trans hj)))
    all_goals simp
  simp only [hzero, tsum_zero]

/-- The occupation isometry into the actual finite computational tensor space. -/
def isometry (L : ℕ) : OccupationSpace L →ₗᵢ[ℂ] TensorSpace L :=
  (column_orthonormal L).orthogonalFamily.linearIsometry

theorem isometry_single (L : ℕ) (j : Fin (L + 1)) :
    isometry L (lp.single 2 j 1) = column L j := by
  rw [isometry, OrthogonalFamily.linearIsometry_apply_single]
  exact one_smul ℂ _

/-- Each computational tensor has exactly the occupation coefficient divided
by the square root of its multiplicity. -/
theorem isometry_apply (L : ℕ) (v : OccupationSpace L) (S : Finset (Fin L)) :
    isometry L v S = v ⟨S.card, by have := Finset.card_le_univ S; simp at this; omega⟩ /
      (Real.sqrt (L.choose S.card : ℝ) : ℂ) := by
  classical
  let j : Fin (L + 1) := ⟨S.card, by have := Finset.card_le_univ S; simp at this; omega⟩
  have hsum : isometry L v = ∑ i : Fin (L + 1), v i • column L i := by
    rw [isometry, OrthogonalFamily.linearIsometry_apply, tsum_fintype]
    rfl
  rw [hsum]
  simp only [lp.coeFn_sum, Finset.sum_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single j]
  · simp [column_apply, j, div_eq_mul_inv]
  · intro i hi hij
    have hne : S.card ≠ i.val := by
      intro h
      apply hij
      apply Fin.ext
      exact h.symm
    simp [column_apply, hne]
  · simp


open Cloning.PoissonApproximation Cloning.CoherentCoefficients

private theorem finite_binomial_hasSum (t : ℝ) (ht : 0 ≤ t) (L : ℕ) :
    HasSum (fun j : Fin (L + 1) => binomialWeight t L j) 1 := by
  have hs : ∑ j : Fin (L + 1), binomialWeight t L j = 1 := by
    rw [Fin.sum_univ_eq_sum_range]
    exact binomialWeight_sum ht L
  exact hs ▸ hasSum_fintype _

/-- The product-state coefficients in the finite occupation basis. -/
def finiteProductVector (t : ℝ) (ht : 0 ≤ t) (L : ℕ) : OccupationSpace L :=
  amplitudeVector (fun j => binomialWeight t L j)
    (fun j => binomialWeight_nonneg ht L j) (finite_binomial_hasSum t ht L)

/-- The symmetric product vector in the finite computational tensor space. -/
def productTensor (t : ℝ) (ht : 0 ≤ t) (L : ℕ) : TensorSpace L :=
  isometry L (finiteProductVector t ht L)

theorem productTensor_norm (t : ℝ) (ht : 0 ≤ t) (L : ℕ) :
    ‖productTensor t ht L‖ = 1 := by
  rw [productTensor, LinearIsometry.norm_map]
  exact amplitudeVector_norm _ _ _

/-- The occupation construction has exactly the coefficients of the normalized
product `( |0⟩ + sqrt(t/L) |1⟩ )^⊗L`. -/
theorem productTensor_apply (t : ℝ) (ht : 0 ≤ t) (L : ℕ) (S : Finset (Fin L)) :
    productTensor t ht L S =
      ((Real.sqrt (t / L) ^ S.card / Real.sqrt (1 + t / L) ^ L : ℝ) : ℂ) := by
  have hj : S.card ≤ L := by simpa using Finset.card_le_univ S
  have hc : Real.sqrt (L.choose S.card : ℝ) ≠ 0 :=
    (Real.sqrt_pos.mpr (by exact_mod_cast Nat.choose_pos hj)).ne'
  have hx : 0 ≤ t / L := by positivity
  have hy : 0 ≤ 1 + t / L := by positivity
  rw [productTensor, isometry_apply]
  change (Real.sqrt (binomialWeight t L S.card) : ℂ) /
    (Real.sqrt (L.choose S.card : ℝ) : ℂ) = _
  rw [← Complex.ofReal_div]
  congr 1
  rw [binomialWeight, Real.sqrt_div (by positivity), Real.sqrt_mul (by positivity),
    Cloning.Thermal.sqrt_nat_pow hx, Cloning.Thermal.sqrt_nat_pow hy]
  field_simp


/-- Restriction to the occupations retained by the finite tensor space. -/
def restrict (L : ℕ) (v : lp (fun _ : ℕ => ℂ) 2) : OccupationSpace L :=
  ⟨fun j => v j, memℓp_gen (by simp only [ENNReal.toReal_ofNat]; exact (hasSum_fintype _).summable)⟩

@[simp] theorem restrict_apply (L : ℕ) (v : lp (fun _ : ℕ => ℂ) 2)
    (j : Fin (L + 1)) : restrict L v j = v j := rfl

theorem restrict_norm_le (L : ℕ) (v : lp (fun _ : ℕ => ℂ) 2) :
    ‖restrict L v‖ ≤ ‖v‖ := by
  have hs : HasSum (fun j : ℕ => ‖v j‖ ^ 2) (‖v‖ ^ 2) := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      lp.hasSum_norm (show 0 < (2 : ENNReal).toReal by norm_num) v
  have heq : ‖restrict L v‖ ^ 2 = ∑ j : Fin (L + 1), ‖v j‖ ^ 2 := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two, tsum_fintype, restrict_apply] using
      lp.norm_rpow_eq_tsum (p := 2) (by norm_num) (restrict L v)
  have hle := hs.summable.sum_le_tsum (Finset.range (L + 1)) (fun j hj => sq_nonneg ‖v j‖)
  rw [hs.tsum_eq, ← Fin.sum_univ_eq_sum_range, ← heq] at hle
  nlinarith [norm_nonneg (restrict L v), norm_nonneg v]

theorem restrict_sub (L : ℕ) (v w : lp (fun _ : ℕ => ℂ) 2) :
    restrict L (v - w) = restrict L v - restrict L w := by ext j; rfl

theorem restrict_productVector (t : ℝ) (ht : 0 ≤ t) (L : ℕ) :
    restrict L (productVector t ht L) = finiteProductVector t ht L := by
  ext j
  rfl

/-- The truncated coherent vector embedded into the finite symmetric space. -/
def embeddedCoherent (t : ℝ) (ht : 0 ≤ t) (L : ℕ) : TensorSpace L :=
  isometry L (restrict L (coherentVector t ht))

theorem embeddedCoherent_norm_le (t : ℝ) (ht : 0 ≤ t) (L : ℕ) :
    ‖embeddedCoherent t ht L‖ ≤ 1 := by
  rw [embeddedCoherent, LinearIsometry.norm_map]
  simpa only [coherentVector_norm] using restrict_norm_le L (coherentVector t ht)

/-- A dimension-independent estimate transfers the coefficient limit to the
actual finite tensor vectors. Both vectors now live in the physical output space. -/
theorem embeddedCoherent_sub_productTensor_le (t : ℝ) (ht : 0 ≤ t) (L : ℕ) :
    ‖embeddedCoherent t ht L - productTensor t ht L‖ ≤
      ‖coherentVector t ht - productVector t ht L‖ := by
  rw [embeddedCoherent, productTensor, ← restrict_productVector, ← map_sub,
    LinearIsometry.norm_map, ← restrict_sub]
  exact restrict_norm_le _ _

theorem embeddedCoherent_sub_productTensor_tendsto (t : ℝ) (ht : 0 ≤ t) :
    Tendsto (fun L => ‖embeddedCoherent t ht L - productTensor t ht L‖) atTop (𝓝 0) := by
  apply squeeze_zero (fun L => norm_nonneg _) (embeddedCoherent_sub_productTensor_le t ht)
  simpa using ((productVector_tendsto_coherentVector t ht).const_sub (coherentVector t ht)).norm

/-- The physical finite tensor projector and truncated coherent projector
converge in genuine trace norm. -/
theorem coherent_product_traceNorm_tendsto (t : ℝ) (ht : 0 ≤ t) :
    Tendsto (fun L => ‖Cloning.InfiniteTraceClass.vectorProjector (embeddedCoherent t ht L) -
      Cloning.InfiniteTraceClass.vectorProjector (productTensor t ht L)‖) atTop (𝓝 0) := by
  apply squeeze_zero (fun L => norm_nonneg _)
    (fun L => (Cloning.InfiniteTraceClass.norm_vectorProjector_sub_le _ _).trans
      (mul_le_mul_of_nonneg_right
        (show ‖embeddedCoherent t ht L‖ + ‖productTensor t ht L‖ ≤ (2 : ℝ) by
          linarith [embeddedCoherent_norm_le t ht L, productTensor_norm t ht L])
        (norm_nonneg _)))
  simpa using (embeddedCoherent_sub_productTensor_tendsto t ht).const_mul 2


open Cloning.InfiniteTraceClass
open scoped ComplexOrder

/-- Lost Fock-tail mass of the truncated coherent vector. -/
def tailMass (t : ℝ) (ht : 0 ≤ t) (L : ℕ) : ℝ :=
  1 - ‖embeddedCoherent t ht L‖ ^ 2

theorem tailMass_nonneg (t : ℝ) (ht : 0 ≤ t) (L : ℕ) : 0 ≤ tailMass t ht L := by
  have h := embeddedCoherent_norm_le t ht L
  have h0 := norm_nonneg (embeddedCoherent t ht L)
  unfold tailMass
  nlinarith

theorem tailMass_le (t : ℝ) (ht : 0 ≤ t) (L : ℕ) :
    tailMass t ht L ≤ 2 * ‖embeddedCoherent t ht L - productTensor t ht L‖ := by
  have h := norm_sub_norm_le (productTensor t ht L) (embeddedCoherent t ht L)
  rw [productTensor_norm, norm_sub_rev] at h
  unfold tailMass
  nlinarith [sq_nonneg (1 - ‖embeddedCoherent t ht L‖)]

/-- The output of occupation compression with the discarded mass put in vacuum.
This is the trace-preserving output, including the tail term in the manuscript. -/
def occupationCoherentOutput (t : ℝ) (ht : 0 ≤ t) (L : ℕ) : TraceClass (TensorSpace L) :=
  vectorProjector (embeddedCoherent t ht L) +
    (tailMass t ht L : ℂ) • vectorProjector (column L 0)

theorem occupationCoherentOutput_trace (t : ℝ) (ht : 0 ≤ t) (L : ℕ) :
    traceCLM (occupationCoherentOutput t ht L) = 1 := by
  simp only [occupationCoherentOutput, map_add, map_smul, traceCLM_vectorProjector,
    column_norm, one_pow, Complex.ofReal_one, smul_eq_mul, mul_one]
  simp [tailMass]

theorem occupationCoherentOutput_nonneg (t : ℝ) (ht : 0 ≤ t) (L : ℕ) :
    0 ≤ (occupationCoherentOutput t ht L).1 := by
  change 0 ≤ InnerProductSpace.rankOne ℂ (embeddedCoherent t ht L) (embeddedCoherent t ht L) +
    (tailMass t ht L : ℂ) • InnerProductSpace.rankOne ℂ (column L 0) (column L 0)
  apply add_nonneg
  · exact (InnerProductSpace.rankOne ℂ _ _).nonneg_iff_isPositive.mpr
      (InnerProductSpace.isPositive_rankOne_self _)
  · have hcast : (tailMass t ht L : ℂ) • InnerProductSpace.rankOne ℂ (column L 0) (column L 0) =
        tailMass t ht L • InnerProductSpace.rankOne ℂ (column L 0) (column L 0) := by
      ext y
      simp only [ContinuousLinearMap.smul_apply]
      rfl
    rw [hcast]
    exact smul_nonneg (tailMass_nonneg t ht L)
      ((InnerProductSpace.rankOne ℂ _ _).nonneg_iff_isPositive.mpr
        (InnerProductSpace.isPositive_rankOne_self _))

/-- The full occupation output, with its vacuum tail replacement, converges to
the normalized physical product projector in trace norm. -/
theorem occupation_coherent_product_traceNorm_tendsto (t : ℝ) (ht : 0 ≤ t) :
    Tendsto (fun L => ‖occupationCoherentOutput t ht L -
      vectorProjector (productTensor t ht L)‖) atTop (𝓝 0) := by
  have hbound : ∀ L, ‖occupationCoherentOutput t ht L -
      vectorProjector (productTensor t ht L)‖ ≤
        4 * ‖embeddedCoherent t ht L - productTensor t ht L‖ := by
    intro L
    rw [occupationCoherentOutput, add_sub_right_comm]
    have h1 := norm_vectorProjector_sub_le (embeddedCoherent t ht L) (productTensor t ht L)
    have h2 := norm_add_le
      (vectorProjector (embeddedCoherent t ht L) - vectorProjector (productTensor t ht L))
      ((tailMass t ht L : ℂ) • vectorProjector (column L 0))
    rw [norm_weighted_projector _ (column_norm L 0), abs_of_nonneg (tailMass_nonneg t ht L)] at h2
    have h3 : ‖embeddedCoherent t ht L‖ + ‖productTensor t ht L‖ ≤ 2 := by
      linarith [embeddedCoherent_norm_le t ht L, productTensor_norm t ht L]
    have h4 := mul_le_mul_of_nonneg_right h3
      (norm_nonneg (embeddedCoherent t ht L - productTensor t ht L))
    linarith [tailMass_le t ht L]
  apply squeeze_zero (fun L => norm_nonneg _) hbound
  simpa using (embeddedCoherent_sub_productTensor_tendsto t ht).const_mul 4


/-- Literal tensor-product factorization in the computational basis: every
slot has the same normalized one-particle amplitudes. -/
theorem productTensor_apply_eq_tensorPower (t : ℝ) (ht : 0 ≤ t) (L : ℕ)
    (S : Finset (Fin L)) :
    productTensor t ht L S = ∏ i : Fin L,
      (((if i ∈ S then Real.sqrt (t / L) else 1) / Real.sqrt (1 + t / L) : ℝ) : ℂ) := by
  rw [productTensor_apply, ← Complex.ofReal_prod]
  congr 1
  rw [Finset.prod_div_distrib]
  have hprod : (∏ i : Fin L, if i ∈ S then Real.sqrt (t / L) else 1) =
      Real.sqrt (t / L) ^ S.card := by
    rw [Finset.prod_ite]
    simp [div_pow]
  rw [hprod]
  simp

/-- The explicit occupation output is an analytic density operator. -/
def occupationCoherentState (t : ℝ) (ht : 0 ≤ t) (L : ℕ) : DensityState (TensorSpace L) where
  op := (occupationCoherentOutput t ht L).1
  traceClass := (occupationCoherentOutput t ht L).2
  positive := occupationCoherentOutput_nonneg t ht L
  trace_one := occupationCoherentOutput_trace t ht L

end Cloning.SymmetricOccupation
