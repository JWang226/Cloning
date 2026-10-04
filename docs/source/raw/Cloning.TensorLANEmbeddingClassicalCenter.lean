import Cloning.YoungUniformLocalQuantization

/-! Exact recentering at a fixed reference spectrum. The classical cell
protocol consequently does not depend on the unknown local parameter. -/
noncomputable section
open scoped BigOperators Topology Classical
open Filter MeasureTheory
namespace Cloning.YoungHyperplane
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- The displacement of two spectral centers in physical root coordinates. -/
def spectralCenterShift (d N : ℕ) (p q : Fin (d + 1) → ℝ) : rootSpace d :=
  coordinates d (fun i => Real.sqrt (N : ℝ) * (q i.castSucc - p i.castSucc))

theorem sampleLabel_recenter (d N : ℕ) (p q : Fin (d + 1) → ℝ)
    (x : rootSpace d) :
    sampleLabel d N p x =
      sampleLabel d N q (x - spectralCenterShift d N p q) := by
  unfold sampleLabel
  congr 2
  funext i
  simp only [Submodule.coe_sub, PiLp.sub_apply, spectralCenterShift, coordinates_head]
  have hs := Real.sq_sqrt (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
  nlinarith [congrArg (fun t : ℝ => t * (q i.castSucc - p i.castSucc)) hs]

theorem sampleInterpolate_recenter (d N : ℕ) (hN : 0 < N)
    (p q : Fin (d + 1) → ℝ) (P : Lattice d (N : ℤ) → ℝ) (x : rootSpace d) :
    sampleInterpolate d N p P x =
      sampleInterpolate d N q P (x - spectralCenterShift d N p q) := by
  rw [sampleInterpolate_eq_on_cell d N (by exact_mod_cast hN) p P
    (sampleLabel d N p x) x (mem_sampleCell_sampleLabel d N p x),
    sampleInterpolate_eq_on_cell d N (by exact_mod_cast hN) q P
      (sampleLabel d N q (x - spectralCenterShift d N p q))
      (x - spectralCenterShift d N p q)
      (mem_sampleCell_sampleLabel d N q (x - spectralCenterShift d N p q)),
    sampleLabel_recenter d N p q x]

/-- Translation leaves the full L1 error exactly unchanged. -/
theorem sampleInterpolate_recenter_l1 (d N : ℕ) (hN : 0 < N)
    (p q : Fin (d + 1) → ℝ) (P : Lattice d (N : ℤ) → ℝ)
    (g : rootSpace d → ℝ) :
    (∫ x, |sampleInterpolate d N p P x - g (x - spectralCenterShift d N p q)|) =
      ∫ x, |sampleInterpolate d N q P x - g x| := by
  simp_rw [sampleInterpolate_recenter d N hN p q P]
  exact integral_sub_right_eq_self (μ := (volume : Measure (rootSpace d)))
    (fun x : rootSpace d => |sampleInterpolate d N q P x - g x|)
    (spectralCenterShift d N p q)

/-- The true physical Young law, emitted into cells centered at the fixed
reference `p₀`, even when the input spectrum is `p`. -/
def fixedBaseYoungDensity (d N : ℕ) (p₀ p : Fin (d + 1) → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) : rootSpace d → ℝ :=
  sampleInterpolate d N p₀ (fun μ => (tensorYoungLatticePMF d N p hp hs μ).toReal)

theorem fixedBaseYoungDensity_eq_translate (d N : ℕ) (hN : 0 < N)
    (p₀ p : Fin (d + 1) → ℝ) (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1)
    (x : rootSpace d) :
    fixedBaseYoungDensity d N p₀ p hp hs x =
      tensorYoungDensity d N p hp hs (x - spectralCenterShift d N p₀ p) :=
  sampleInterpolate_recenter d N hN p₀ p _ x

theorem fixedBaseYoungDensity_l1_tendsto (d : ℕ) (n : ℕ → ℕ)
    (hn : Tendsto n atTop atTop) (hn0 : ∀ k, 0 < n k)
    (p : ℕ → Fin (d + 1) → ℝ) (hp : ∀ k, ∑ i, p k i = 1)
    (hp0 : ∀ k i, 0 < p k i) (p₀ : Fin (d + 1) → ℝ) (hs₀ : ∑ i, p₀ i = 1)
    (hp₀ : ∀ i, 0 < p₀ i) (hord : StrictAnti p₀)
    (hlim : ∀ i, Tendsto (fun k => p k i) atTop (𝓝 (p₀ i))) :
    Tendsto (fun k => ∫ x,
      |fixedBaseYoungDensity d (n k) p₀ (p k) (fun i => (hp0 k i).le) (hp k) x -
        covarianceGaussian d p₀ hs₀ (x - spectralCenterShift d (n k) p₀ (p k))|)
      atTop (𝓝 0) := by
  have h := tensorYoungDensity_l1_tendsto d n hn hn0 p hp hp0 p₀ hs₀ hp₀ hord hlim
  simpa only [fixedBaseYoungDensity, sampleInterpolate_recenter_l1 d _ (hn0 _) p₀,
    tensorYoungDensity] using h

/-- The fixed quantizer recovers the exact physical law, including all affine
lattice outcomes, rather than only labels in a typical set. -/
theorem binMass_fixedBaseYoungDensity (d N : ℕ) (hN : 0 < N)
    (p₀ p : Fin (d + 1) → ℝ) (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1)
    (μ : Lattice d (N : ℤ)) :
    YoungRounding.binMass volume (sampleLabel d N p₀)
      (fixedBaseYoungDensity d N p₀ p hp hs) μ =
        (tensorYoungLatticePMF d N p hp hs μ).toReal := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hnz : Real.sqrt (N : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hn).ne'
  have hdz : Real.sqrt ((d : ℝ) + 1) ≠ 0 := by positivity
  rw [YoungRounding.binMass, sampleLabel_fiber, fixedBaseYoungDensity]
  rw [setIntegral_congr_fun (measurableSet_sampleCell d N p₀ μ)
    (fun x hx => sampleInterpolate_eq_on_cell d N (by exact_mod_cast hN) p₀
      (fun μ => (tensorYoungLatticePMF d N p hp hs μ).toReal) μ x hx), setIntegral_const]
  simp only [Measure.real, volume_sampleCell d N (by exact_mod_cast hN),
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity : 0 ≤ Real.sqrt ((d : ℝ) + 1)),
    ENNReal.toReal_ofReal (by positivity : 0 ≤ ((Real.sqrt (N : ℝ)) ^ d)⁻¹),
    smul_eq_mul, Int.cast_natCast]
  field_simp

end Cloning.YoungHyperplane
