import Cloning.OccupationChannel

/-! Arbitrary complex coherent amplitudes via genuine phase isometries on ℓ².
Normalization and binomial approximation are derived from the proved radial
probability laws, including zero amplitude. -/

noncomputable section
open scoped BigOperators InnerProductSpace Topology
open Filter

namespace Cloning.ComplexCoherent
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

abbrev Fock := lp (fun _ : ℕ => ℂ) 2

variable {ι : Type*}

/-- Multiplication by coordinate phases as an actual ℓ² vector. -/
def phaseVector (u : ι → ℂ) (hu : ∀ i, ‖u i‖ = 1)
    (x : lp (fun _ : ι => ℂ) 2) : lp (fun _ : ι => ℂ) 2 := by
  refine ⟨fun i => u i * x i, memℓp_gen ?_⟩
  simpa only [norm_mul, hu, one_mul] using (lp.memℓp x).summable (by norm_num)

@[simp] theorem phaseVector_apply (u : ι → ℂ) (hu : ∀ i, ‖u i‖ = 1)
    (x : lp (fun _ : ι => ℂ) 2) (i : ι) : phaseVector u hu x i = u i * x i := rfl

theorem phaseVector_norm (u : ι → ℂ) (hu : ∀ i, ‖u i‖ = 1)
    (x : lp (fun _ : ι => ℂ) 2) : ‖phaseVector u hu x‖ = ‖x‖ := by
  rw [lp.norm_eq_tsum_rpow (by norm_num), lp.norm_eq_tsum_rpow (by norm_num)]
  simp only [phaseVector_apply, norm_mul, hu, one_mul]

/-- Coordinate phases define a complex-linear isometry, rather than merely a
coefficient transformation preserving a formally assigned norm. -/
def phaseIsometry (u : ι → ℂ) (hu : ∀ i, ‖u i‖ = 1) :
    lp (fun _ : ι => ℂ) 2 →ₗᵢ[ℂ] lp (fun _ : ι => ℂ) 2 where
  toLinearMap :=
    { toFun := phaseVector u hu
      map_add' := by intro x y; ext i; simp [mul_add]
      map_smul' := by intro c x; ext i; simp [mul_left_comm] }
  norm_map' := phaseVector_norm u hu

@[simp] theorem phaseIsometry_apply (u : ι → ℂ) (hu : ∀ i, ‖u i‖ = 1)
    (x : lp (fun _ : ι => ℂ) 2) (i : ι) : phaseIsometry u hu x i = u i * x i := rfl

/-- The phase of zero is chosen to be one, making all coefficients total. -/
def phase (z : ℂ) : ℂ := if z = 0 then 1 else z / (‖z‖ : ℂ)

theorem phase_norm (z : ℂ) : ‖phase z‖ = 1 := by
  by_cases hz : z = 0
  · simp [phase, hz]
  · simp [phase, hz, Complex.norm_real, norm_ne_zero_iff.mpr hz]

theorem phase_mul_norm (z : ℂ) : phase z * (‖z‖ : ℂ) = z := by
  by_cases hz : z = 0
  · simp [phase, hz]
  · simp only [phase, if_neg hz]
    exact div_mul_cancel₀ z (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hz))

theorem phase_pow_norm (z : ℂ) (n : ℕ) : phase z ^ n * (‖z‖ : ℂ) ^ n = z ^ n := by
  rw [← mul_pow, phase_mul_norm]

def numberPhase (z : ℂ) : Fock →ₗᵢ[ℂ] Fock :=
  phaseIsometry (fun n => phase z ^ n) (fun n => by rw [norm_pow, phase_norm, one_pow])

@[simp] theorem numberPhase_apply (z : ℂ) (x : Fock) (n : ℕ) :
    numberPhase z x n = phase z ^ n * x n := rfl

open Cloning.CoherentCoefficients

/-- The normalized coherent vector for an arbitrary complex amplitude. -/
def coherentVector (z : ℂ) : Fock :=
  numberPhase z (Cloning.CoherentCoefficients.coherentVector (‖z‖ ^ 2) (sq_nonneg _))

/-- The familiar exponential/power/factorial coefficients, valid also at zero. -/
theorem coherentVector_apply (z : ℂ) (n : ℕ) :
    coherentVector z n = (Real.exp (-‖z‖ ^ 2 / 2) : ℂ) * z ^ n /
      (Real.sqrt (n.factorial : ℝ) : ℂ) := by
  rw [coherentVector, numberPhase_apply, Cloning.CoherentCoefficients.coherentVector_apply,
    Real.sqrt_sq (norm_nonneg z)]
  simp only [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_pow]
  calc
    _ = (Real.exp (-‖z‖ ^ 2 / 2) : ℂ) * (phase z ^ n * (‖z‖ : ℂ) ^ n) /
        (Real.sqrt (n.factorial : ℝ) : ℂ) := by ring
    _ = _ := by rw [phase_pow_norm]

theorem coherentVector_norm (z : ℂ) : ‖coherentVector z‖ = 1 := by
  rw [coherentVector, LinearIsometry.norm_map]
  exact Cloning.CoherentCoefficients.coherentVector_norm _ _

/-- The normalized padded binomial approximation with its full complex phase. -/
def productVector (z : ℂ) (L : ℕ) : Fock :=
  numberPhase z (Cloning.CoherentCoefficients.productVector (‖z‖ ^ 2) (sq_nonneg _) L)

theorem productVector_norm (z : ℂ) (L : ℕ) : ‖productVector z L‖ = 1 := by
  rw [productVector, LinearIsometry.norm_map]
  exact Cloning.CoherentCoefficients.productVector_norm _ _ _

theorem productVector_tendsto_coherentVector (z : ℂ) :
    Tendsto (productVector z) atTop (𝓝 (coherentVector z)) :=
  (numberPhase z).continuous.tendsto _ |>.comp
    (Cloning.CoherentCoefficients.productVector_tendsto_coherentVector (‖z‖ ^ 2) (sq_nonneg _))

theorem product_projector_tendsto (z : ℂ) :
    Tendsto (fun L => Cloning.InfiniteTraceClass.vectorProjector (productVector z L)) atTop
      (𝓝 (Cloning.InfiniteTraceClass.vectorProjector (coherentVector z))) :=
  Cloning.InfiniteTraceClass.vectorProjector_tendsto (productVector_tendsto_coherentVector z)

open SymmetricOccupation

/-- The finite occupation vector with the same complex binomial amplitudes. -/
def finiteProductVector (z : ℂ) (L : ℕ) : OccupationSpace L :=
  phaseIsometry (fun j : Fin (L + 1) => phase z ^ j.val)
    (fun j => by rw [norm_pow, phase_norm, one_pow])
    (SymmetricOccupation.finiteProductVector (‖z‖ ^ 2) (sq_nonneg _) L)

theorem restrict_productVector (z : ℂ) (L : ℕ) :
    restrict L (productVector z L) = finiteProductVector z L := by
  ext j
  rfl

/-- An actual normalized vector in the finite computational tensor space. -/
def productTensor (z : ℂ) (L : ℕ) : TensorSpace L :=
  SymmetricOccupation.isometry L (finiteProductVector z L)

theorem productTensor_norm (z : ℂ) (L : ℕ) : ‖productTensor z L‖ = 1 := by
  rw [productTensor, LinearIsometry.norm_map, finiteProductVector, LinearIsometry.norm_map]
  exact Cloning.CoherentCoefficients.amplitudeVector_norm _ _ _

theorem productTensor_phase (z : ℂ) (L : ℕ) (S : Finset (Fin L)) :
    productTensor z L S = phase z ^ S.card *
      SymmetricOccupation.productTensor (‖z‖ ^ 2) (sq_nonneg _) L S := by
  rw [productTensor, SymmetricOccupation.productTensor, SymmetricOccupation.isometry_apply,
    SymmetricOccupation.isometry_apply]
  simp only [finiteProductVector, phaseIsometry_apply]
  ring

lemma phase_mul_scaled_radius (z : ℂ) (L : ℕ) :
    phase z * (Real.sqrt (‖z‖ ^ 2 / L) : ℂ) = z / (Real.sqrt (L : ℝ) : ℂ) := by
  rw [Real.sqrt_div (sq_nonneg _), Real.sqrt_sq (norm_nonneg z)]
  push_cast
  rw [← mul_div_assoc, phase_mul_norm]

/-- Literal coefficients of the normalized product
`(|0⟩ + z/√L |1⟩)^⊗L`, including the zero-length convention. -/
theorem productTensor_apply (z : ℂ) (L : ℕ) (S : Finset (Fin L)) :
    productTensor z L S = (z / (Real.sqrt (L : ℝ) : ℂ)) ^ S.card /
      (Real.sqrt (1 + ‖z‖ ^ 2 / L) : ℂ) ^ L := by
  rw [productTensor_phase, SymmetricOccupation.productTensor_apply]
  push_cast
  rw [← mul_div_assoc, ← mul_pow, phase_mul_scaled_radius]

/-- The actual occupation embedding of the truncated complex coherent vector. -/
def embeddedCoherent (z : ℂ) (L : ℕ) : TensorSpace L :=
  SymmetricOccupation.isometry L (restrict L (coherentVector z))

theorem embeddedCoherent_sub_productTensor_le (z : ℂ) (L : ℕ) :
    ‖embeddedCoherent z L - productTensor z L‖ ≤ ‖coherentVector z - productVector z L‖ := by
  rw [embeddedCoherent, productTensor, ← restrict_productVector, ← map_sub,
    LinearIsometry.norm_map, ← restrict_sub]
  exact restrict_norm_le _ _

theorem embeddedCoherent_sub_productTensor_tendsto (z : ℂ) :
    Tendsto (fun L => ‖embeddedCoherent z L - productTensor z L‖) atTop (𝓝 0) := by
  apply squeeze_zero (fun L => norm_nonneg _) (embeddedCoherent_sub_productTensor_le z)
  simpa using ((productVector_tendsto_coherentVector z).const_sub (coherentVector z)).norm

/-- The binomial vector is supported in exactly the retained occupations. -/
theorem productVector_eq_zero_of_lt (z : ℂ) (L j : ℕ) (hLj : L < j) :
    productVector z L j = 0 := by
  simp only [productVector, numberPhase_apply, Cloning.CoherentCoefficients.productVector,
    amplitudeVector_apply, Cloning.PoissonApproximation.binomialWeight_eq_zero_of_lt _ hLj,
    Real.sqrt_zero, Complex.ofReal_zero, mul_zero]

/-- The actual occupation channel sends any complex coherent vector to its
normalized finite computational product approximation in genuine trace norm. -/
theorem occupationChannel_coherent_product_tendsto (z : ℂ) :
    Tendsto (fun L => ‖(SymmetricOccupation.occupationChannel L).toLinearMap
      (Cloning.InfiniteTraceClass.vectorProjector (coherentVector z)) -
        Cloning.InfiniteTraceClass.vectorProjector (productTensor z L)‖) atTop (𝓝 0) := by
  have hb (L : ℕ) : ‖(SymmetricOccupation.occupationChannel L).toLinearMap
      (Cloning.InfiniteTraceClass.vectorProjector (coherentVector z)) -
        Cloning.InfiniteTraceClass.vectorProjector (productTensor z L)‖ ≤
      2 * ‖coherentVector z - productVector z L‖ := by
    have h := SymmetricOccupation.occupationChannel_pure_distance_le L
      (coherentVector z) (productVector z L)
      (SymmetricOccupation.restrict_norm_eq_of_support L (productVector z L)
        (fun j hj => productVector_eq_zero_of_lt z L j hj))
    simpa only [coherentVector_norm, productVector_norm, show (1 : ℝ) + 1 = 2 by norm_num,
      SymmetricOccupation.compression_apply, restrict_productVector, productTensor] using h
  apply squeeze_zero (fun L => norm_nonneg _) hb
  simpa using (((productVector_tendsto_coherentVector z).const_sub (coherentVector z)).norm).const_mul 2

end Cloning.ComplexCoherent
