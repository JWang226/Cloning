import Cloning.Rounding
import Cloning.CountableScheffe
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Probability.ProbabilityMassFunction.Monad

/-!
# Actual lattice cells and randomized rounding

The coordinate space here is `ι → ℝ`, where `ι` indexes the first `d-1`
coordinates of the manuscript's affine lattice.  The last coordinate is
recovered by `Cloning.Rounding.completeLast`.  Lebesgue measure in these
coordinates gives the unit cell volume one; the common Jacobian `√d` for
the induced hyperplane volume cancels from all probabilities.

The rounding distribution is constructed by pushing forward restricted
Lebesgue measure, rather than by supplying a row-sum assumption.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal Topology

namespace Cloning.YoungRounding

variable {ι : Type*} [Fintype ι]

def cell (z : ι → ℤ) : Set (ι → ℝ) :=
  Set.pi Set.univ fun i ↦ Set.Ico ((z i : ℝ) - 1 / 2) ((z i : ℝ) + 1 / 2)

def round (x : ι → ℝ) : ι → ℤ := fun i ↦ Rounding.nearest (x i)

omit [Fintype ι] in
theorem measurable_round : Measurable (round (ι := ι)) := by
  apply measurable_pi_lambda
  intro i
  exact Int.measurable_floor.comp ((measurable_pi_apply i).add_const (1 / 2))

omit [Fintype ι] in
theorem round_eq_iff (x : ι → ℝ) (z : ι → ℤ) : round x = z ↔ x ∈ cell z := by
  simp only [funext_iff, round, cell, Set.mem_pi, Set.mem_univ, true_implies,
    Set.mem_Ico, Rounding.nearest_eq_iff]

omit [Fintype ι] in
theorem cell_eq_fiber (z : ι → ℤ) : cell z = round ⁻¹' {z} := by
  ext x
  exact (round_eq_iff x z).symm

theorem measurableSet_cell (z : ι → ℤ) : MeasurableSet (cell z) := by
  rw [cell_eq_fiber]
  exact measurable_round (measurableSet_singleton z)

omit [Fintype ι] in
theorem cells_disjoint : Pairwise fun z w : ι → ℤ ↦ Disjoint (cell z) (cell w) := by
  intro z w hzw
  rw [Set.disjoint_left]
  intro x hx hw
  exact hzw ((round_eq_iff x z).mpr hx |>.symm.trans ((round_eq_iff x w).mpr hw))

omit [Fintype ι] in
theorem cells_cover : (⋃ z : ι → ℤ, cell z) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  exact Set.mem_iUnion.mpr ⟨round x, (round_eq_iff x (round x)).mp rfl⟩

theorem volume_cell (z : ι → ℤ) : volume (cell z) = 1 := by
  rw [cell, Real.volume_pi_Ico]
  simp only [show ∀ i, (z i : ℝ) + 1 / 2 - ((z i : ℝ) - 1 / 2) = 1 by
    intro i; ring, ENNReal.ofReal_one, Finset.prod_const_one]

def ditherMeasure : Measure (ι → ℝ) := volume.restrict (cell 0)

instance ditherMeasure_isProbabilityMeasure :
    IsProbabilityMeasure (ditherMeasure (ι := ι)) := by
  constructor
  simp [ditherMeasure, volume_cell]

def dilatedRound (γ : ℝ) (μ : ι → ℝ) (y : ι → ℝ) : ι → ℤ :=
  round (fun i ↦ γ * (μ i + y i))

omit [Fintype ι] in
theorem measurable_dilatedRound (γ : ℝ) (μ : ι → ℝ) :
    Measurable (dilatedRound γ μ) := by
  apply measurable_round.comp
  exact measurable_pi_lambda _ fun i ↦
    measurable_const.mul (measurable_const.add (measurable_pi_apply i))

/-- The actual uniform-dither rounding law, including all lattice labels. -/
def roundingPMF (γ : ℝ) (μ : ι → ℝ) : PMF (ι → ℤ) := by
  let ν := (ditherMeasure (ι := ι)).map (dilatedRound γ μ)
  haveI : IsProbabilityMeasure ν :=
    Measure.isProbabilityMeasure_map (measurable_dilatedRound γ μ).aemeasurable
  exact ν.toPMF

/-- Normalization follows from the pushforward probability measure. -/
theorem roundingPMF_sum (γ : ℝ) (μ : ι → ℝ) :
    ∑' z, roundingPMF γ μ z = 1 := (roundingPMF γ μ).tsum_coe

/-- The source-coordinate overlap formula; it is valid even when `γ = 0`.
For positive `γ`, change of variables gives the manuscript's ratio of the
dilated overlap volume to `γ ^ card ι`.
-/
theorem roundingPMF_eq_overlap (γ : ℝ) (μ : ι → ℝ) (z : ι → ℤ) :
    roundingPMF γ μ z =
      volume ((fun y : ι → ℝ ↦ fun i ↦ γ * (μ i + y i)) ⁻¹' cell z ∩ cell 0) := by
  rw [roundingPMF, Measure.toPMF_apply,
    Measure.map_apply (measurable_dilatedRound γ μ) (measurableSet_singleton z),
    ditherMeasure, Measure.restrict_apply
      ((measurable_dilatedRound γ μ) (measurableSet_singleton z))]
  congr 1
  ext y
  simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff,
    dilatedRound, round_eq_iff]

/-- A positive-mass output satisfies each of the manuscript's coordinate
rounding bounds.  No support or partition hypothesis is supplied.
-/
theorem roundingPMF_support (γ : ℝ) (hγ : 0 ≤ γ) (μ : ι → ℝ) (z : ι → ℤ)
    (hz : roundingPMF γ μ z ≠ 0) (i : ι) :
    |(z i : ℝ) - γ * μ i| ≤ (γ + 1) / 2 := by
  rw [roundingPMF_eq_overlap] at hz
  have hne : ((fun y : ι → ℝ ↦ fun j ↦ γ * (μ j + y j)) ⁻¹' cell z ∩ cell 0) ≠ ∅ :=
    fun hempty ↦ hz (by rw [hempty, measure_empty])
  obtain ⟨y, hy, hy0⟩ := Set.nonempty_iff_ne_empty.mpr hne
  have hround := (round_eq_iff (fun j ↦ γ * (μ j + y j)) z).mpr hy
  have hyi : -(1 / 2 : ℝ) ≤ y i ∧ y i < 1 / 2 := by
    simpa [cell] using hy0 i (Set.mem_univ i)
  have hi : Rounding.nearest (γ * (μ i + y i)) = z i := congrFun hround i
  rw [← hi]
  exact Rounding.dither_error γ (μ i) (y i) hγ hyi

/-- A random input label followed by the concrete cell kernel is an actual
normalized countable law, with the usual sum-of-transition-probabilities formula. -/
def transport (γ : ℝ) (p : PMF (ι → ℤ)) : PMF (ι → ℤ) :=
  p.bind fun z ↦ roundingPMF γ (fun i ↦ (z i : ℝ))

theorem transport_apply (γ : ℝ) (p : PMF (ι → ℤ)) (w : ι → ℤ) :
    transport γ p w = ∑' z, p z * roundingPMF γ (fun i ↦ (z i : ℝ)) w := rfl

section MeasurableDiscretization

variable {X Z : Type*} [MeasurableSpace X] [MeasurableSpace Z]
  [MeasurableSingletonClass Z] [Countable Z]

/-- Actual density mass in each fiber of a measurable rounding map. -/
def binMass (μ : Measure X) (r : X → Z) (f : X → ℝ) (z : Z) : ℝ :=
  ∫ x in r ⁻¹' {z}, f x ∂μ

theorem hasSum_binMass (μ : Measure X) {r : X → Z} (hr : Measurable r)
    {f : X → ℝ} (hf : Integrable f μ) :
    HasSum (binMass μ r f) (∫ x, f x ∂μ) := by
  have hcover : (⋃ z : Z, r ⁻¹' {z}) = Set.univ := by
    ext x
    simp
  have hd : Pairwise fun z w : Z ↦ Disjoint (r ⁻¹' {z}) (r ⁻¹' {w}) := by
    intro z w hzw
    exact Set.disjoint_left.mpr fun x hx hw ↦ hzw (hx.symm.trans hw)
  have h := hasSum_integral_iUnion
    (fun z ↦ hr (measurableSet_singleton z)) hd
    (show IntegrableOn f (⋃ z : Z, r ⁻¹' {z}) μ by simpa [hcover] using hf)
  simpa only [binMass, hcover, setIntegral_univ] using h

omit [MeasurableSpace Z] [MeasurableSingletonClass Z] [Countable Z] in
theorem binMass_nonneg (μ : Measure X) (r : X → Z) {f : X → ℝ}
    (hf : ∀ x, 0 ≤ f x) (z : Z) : 0 ≤ binMass μ r f z :=
  integral_nonneg hf

/-- Discretization by any measurable countable partition contracts the actual
`L¹` distance.  The proof uses the fiber partition, not an assumed kernel law. -/
theorem binMass_l1_contraction (μ : Measure X) {r : X → Z} (hr : Measurable r)
    {f g : X → ℝ} (hf : Integrable f μ) (hg : Integrable g μ) :
    (∑' z, |binMass μ r f z - binMass μ r g z|) ≤ ∫ x, |f x - g x| ∂μ := by
  have hsum := hasSum_binMass μ hr (hf.sub hg).abs
  have hbound (z : Z) :
      |binMass μ r f z - binMass μ r g z| ≤ binMass μ r (fun x ↦ |f x - g x|) z := by
    unfold binMass
    rw [← integral_sub hf.integrableOn hg.integrableOn]
    simpa only [Real.norm_eq_abs] using
      norm_integral_le_integral_norm (f := fun x ↦ f x - g x) (μ := μ.restrict (r ⁻¹' {z}))
  have hs : Summable (fun z ↦ |binMass μ r f z - binMass μ r g z|) :=
    hsum.summable.of_nonneg_of_le (fun _ ↦ abs_nonneg _) hbound
  exact (hs.tsum_le_tsum hbound hsum.summable).trans_eq hsum.tsum_eq

/-- The normalized-density estimate used in the manuscript's local-limit
argument.  Only the reference density's tail is needed. -/
theorem density_l1_local_tail (μ : Measure X) {f g : X → ℝ}
    (hf : Integrable f μ) (hg : Integrable g μ)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x)
    (hmass : (∫ x, f x ∂μ) = ∫ x, g x ∂μ)
    {s : Set X} (hs : MeasurableSet s) :
    (∫ x, |f x - g x| ∂μ) ≤
      2 * (∫ x in s, |f x - g x| ∂μ) + 2 * (∫ x in sᶜ, g x ∂μ) := by
  have hsplit : (∫ x in s, |f x - g x| ∂μ) + (∫ x in sᶜ, |f x - g x| ∂μ) =
      ∫ x, |f x - g x| ∂μ := integral_add_compl hs (hf.sub hg).abs
  have hsplitf := integral_add_compl hs hf
  have hsplitg := integral_add_compl hs hg
  have hlocal : (∫ x in s, g x ∂μ) - (∫ x in s, f x ∂μ) ≤
      ∫ x in s, |f x - g x| ∂μ := by
    rw [← integral_sub hg.integrableOn hf.integrableOn]
    apply integral_mono (hg.sub hf).integrableOn (hf.sub hg).abs.integrableOn
    intro x
    simpa only [neg_sub] using neg_le_abs (f x - g x)
  have htail : (∫ x in sᶜ, |f x - g x| ∂μ) ≤
      (∫ x in sᶜ, f x ∂μ) + ∫ x in sᶜ, g x ∂μ := by
    rw [← integral_add hf.integrableOn hg.integrableOn]
    apply integral_mono (hf.sub hg).abs.integrableOn (hf.add hg).integrableOn
    intro x
    simpa only [abs_of_nonneg (hf0 x), abs_of_nonneg (hg0 x), Pi.add_apply] using
      abs_sub (f x) (g x)
  linarith

/-- A uniform density error on a finite-volume set gives an explicit global
`L¹` bound, without a separate concentration assumption for `f`. -/
theorem density_l1_local_uniform_tail (μ : Measure X) {f g : X → ℝ}
    (hf : Integrable f μ) (hg : Integrable g μ)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x)
    (hmass : (∫ x, f x ∂μ) = ∫ x, g x ∂μ)
    {s : Set X} (hs : MeasurableSet s) (hsfin : μ s ≠ ∞)
    {ε : ℝ} (hlocal : ∀ x ∈ s, |f x - g x| ≤ ε) :
    (∫ x, |f x - g x| ∂μ) ≤
      2 * (μ s).toReal * ε + 2 * (∫ x in sᶜ, g x ∂μ) := by
  have hbound : (∫ x in s, |f x - g x| ∂μ) ≤ (μ s).toReal * ε := by
    have hn := norm_setIntegral_le_of_norm_le_const (lt_top_iff_ne_top.mpr hsfin)
      (f := fun x ↦ |f x - g x|)
      (fun x hx ↦ by simpa only [Real.norm_eq_abs, abs_abs] using hlocal x hx)
    exact (le_abs_self _).trans
      (by simpa only [Real.norm_eq_abs, Measure.real, mul_comm] using hn)
  have h := density_l1_local_tail μ hf hg hf0 hg0 hmass hs
  nlinarith

/-- The same explicit local-error/tail bound holds after rounding the two
densities to the lattice, for any measurable choice of scaled cells. -/
theorem binMass_l1_local_uniform_tail (μ : Measure X) {r : X → Z} (hr : Measurable r)
    {f g : X → ℝ} (hf : Integrable f μ) (hg : Integrable g μ)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x)
    (hmass : (∫ x, f x ∂μ) = ∫ x, g x ∂μ)
    {s : Set X} (hs : MeasurableSet s) (hsfin : μ s ≠ ∞)
    {ε : ℝ} (hlocal : ∀ x ∈ s, |f x - g x| ≤ ε) :
    (∑' z, |binMass μ r f z - binMass μ r g z|) ≤
      2 * (μ s).toReal * ε + 2 * (∫ x in sᶜ, g x ∂μ) :=
  (binMass_l1_contraction μ hr hf hg).trans
    (density_l1_local_uniform_tail μ hf hg hf0 hg0 hmass hs hsfin hlocal)

/-- Uniform local density convergence plus uniform tails of the normalized
reference family implies uniform global `L¹` convergence.  The parameter type
can be a compact set of spectra; no compactness or local limit is assumed
implicitly in this statement. -/
theorem density_l1_uniform_of_local_and_tails {P : Type*}
    (μ : Measure X) (f : ℕ → P → X → ℝ) (g : P → X → ℝ)
    (hf : ∀ n p, Integrable (f n p) μ) (hg : ∀ p, Integrable (g p) μ)
    (hf0 : ∀ n p x, 0 ≤ f n p x) (hg0 : ∀ p x, 0 ≤ g p x)
    (hmass : ∀ n p, (∫ x, f n p x ∂μ) = ∫ x, g p x ∂μ)
    (s : ℕ → Set X) (hs : ∀ k, MeasurableSet (s k)) (hsfin : ∀ k, μ (s k) ≠ ∞)
    (hlocal : ∀ k δ, 0 < δ → ∀ᶠ n in atTop, ∀ p x, x ∈ s k →
      |f n p x - g p x| ≤ δ)
    (htail : ∀ δ, 0 < δ → ∃ k, ∀ p, (∫ x in (s k)ᶜ, g p x ∂μ) ≤ δ) :
    ∀ ε, 0 < ε → ∀ᶠ n in atTop, ∀ p, (∫ x, |f n p x - g p x| ∂μ) < ε := by
  intro ε hε
  obtain ⟨k, hk⟩ := htail (ε / 4) (by positivity)
  let V := (μ (s k)).toReal
  have hV : 0 ≤ V := ENNReal.toReal_nonneg
  let δ := ε / (4 * (V + 1))
  have hδ : 0 < δ := div_pos hε (by positivity)
  have hδeq : 4 * (V + 1) * δ = ε := by
    dsimp [δ]
    field_simp
  filter_upwards [hlocal k δ hδ] with n hn
  intro p
  have hb := density_l1_local_uniform_tail μ (hf n p) (hg p) (hf0 n p) (hg0 p)
    (hmass n p) (hs k) (hsfin k) (hn p)
  change (∫ x, |f n p x - g p x| ∂μ) ≤
    2 * V * δ + 2 * (∫ x in (s k)ᶜ, g p x ∂μ) at hb
  have hkp := hk p
  nlinarith

/-- The uniform comparison survives arbitrary varying measurable lattice
rounding maps, including changing sample sizes and translated cells. -/
theorem binMass_l1_uniform_of_local_and_tails {P : Type*}
    (μ : Measure X) (r : ℕ → P → X → Z) (hr : ∀ n p, Measurable (r n p))
    (f : ℕ → P → X → ℝ) (g : P → X → ℝ)
    (hf : ∀ n p, Integrable (f n p) μ) (hg : ∀ p, Integrable (g p) μ)
    (hf0 : ∀ n p x, 0 ≤ f n p x) (hg0 : ∀ p x, 0 ≤ g p x)
    (hmass : ∀ n p, (∫ x, f n p x ∂μ) = ∫ x, g p x ∂μ)
    (s : ℕ → Set X) (hs : ∀ k, MeasurableSet (s k)) (hsfin : ∀ k, μ (s k) ≠ ∞)
    (hlocal : ∀ k δ, 0 < δ → ∀ᶠ n in atTop, ∀ p x, x ∈ s k →
      |f n p x - g p x| ≤ δ)
    (htail : ∀ δ, 0 < δ → ∃ k, ∀ p, (∫ x in (s k)ᶜ, g p x ∂μ) ≤ δ) :
    ∀ ε, 0 < ε → ∀ᶠ n in atTop, ∀ p,
      (∑' z, |binMass μ (r n p) (f n p) z - binMass μ (r n p) (g p) z|) < ε := by
  intro ε hε
  filter_upwards [density_l1_uniform_of_local_and_tails μ f g hf hg hf0 hg0 hmass
    s hs hsfin hlocal htail ε hε] with n hn
  exact fun p ↦ (binMass_l1_contraction μ (hr n p) (hf n p) (hg p)).trans_lt (hn p)

end MeasurableDiscretization

/-- Piecewise-constant interpolation on the exact unit lattice cells. -/
def interpolate (p : (ι → ℤ) → ℝ) (x : ι → ℝ) : ℝ := p (round x)

omit [Fintype ι] in
theorem interpolate_eq_on_cell (p : (ι → ℤ) → ℝ) (z : ι → ℤ)
    {x : ι → ℝ} (hx : x ∈ cell z) : interpolate p x = p z := by
  rw [interpolate, (round_eq_iff x z).mpr hx]

theorem integrableOn_interpolate (p : (ι → ℤ) → ℝ) (z : ι → ℤ) :
    IntegrableOn (interpolate p) (cell z) := by
  have hc : IntegrableOn (fun _ : ι → ℝ ↦ p z) (cell z) :=
    integrableOn_const (by rw [volume_cell]; exact ENNReal.one_ne_top)
  apply hc.congr
  exact (ae_restrict_iff' (measurableSet_cell z)).mpr (Filter.Eventually.of_forall
    fun x hx ↦ (interpolate_eq_on_cell p z hx).symm)

theorem integral_interpolate_cell (p : (ι → ℤ) → ℝ) (z : ι → ℤ) :
    (∫ x in cell z, interpolate p x) = p z := by
  rw [setIntegral_congr_fun (measurableSet_cell z)
    (fun x hx ↦ interpolate_eq_on_cell p z hx), setIntegral_const]
  simp [Measure.real, volume_cell]

theorem integral_norm_interpolate_cell (p : (ι → ℤ) → ℝ) (z : ι → ℤ) :
    (∫ x in cell z, ‖interpolate p x‖) = |p z| := by
  have heq : (fun x ↦ ‖interpolate p x‖) = interpolate (fun w ↦ |p w|) := by
    funext x
    simp only [interpolate, Real.norm_eq_abs]
  rw [heq, integral_interpolate_cell]

theorem integrable_interpolate {p : (ι → ℤ) → ℝ} (hp : Summable p) :
    Integrable (interpolate p) := by
  have h := integrableOn_iUnion_of_summable_integral_norm
    (integrableOn_interpolate p)
    (show Summable (fun z ↦ ∫ x in cell z, ‖interpolate p x‖) by
      simpa only [integral_norm_interpolate_cell] using hp.abs)
  simpa only [cells_cover, integrableOn_univ] using h

theorem integral_interpolate {p : (ι → ℤ) → ℝ} (hp : Summable p) :
    (∫ x, interpolate p x) = ∑' z, p z := by
  have h := hasSum_integral_iUnion measurableSet_cell cells_disjoint
    (show IntegrableOn (interpolate p) (⋃ z, cell z) by
      simpa only [cells_cover, integrableOn_univ] using integrable_interpolate hp)
  simpa only [cells_cover, setIntegral_univ, integral_interpolate_cell] using h.tsum_eq.symm

/-- The actual Lebesgue interpolation preserves the countable `ℓ¹` distance. -/
theorem interpolate_l1_isometry {p q : (ι → ℤ) → ℝ}
    (hp : Summable p) (hq : Summable q) :
    (∫ x, |interpolate p x - interpolate q x|) = ∑' z, |p z - q z| :=
  integral_interpolate (hp.sub hq).abs

/-- Hellinger affinity is also preserved, with countably many cells. -/
theorem interpolate_affinity {p q : (ι → ℤ) → ℝ}
    (hp0 : ∀ z, 0 ≤ p z) (hq0 : ∀ z, 0 ≤ q z)
    (hp : Summable p) (hq : Summable q) :
    (∫ x, Real.sqrt (interpolate p x) * Real.sqrt (interpolate q x)) =
      ∑' z, Real.sqrt (p z) * Real.sqrt (q z) :=
  integral_interpolate (CountableScheffe.affinity_summable p q hp0 hq0 hp hq)

/-- Lebesgue cell averaging, constructed from the actual fiber integrals. -/
def cellAverage (f : (ι → ℝ) → ℝ) : (ι → ℝ) → ℝ :=
  interpolate (binMass volume round f)

theorem integrable_cellAverage {f : (ι → ℝ) → ℝ} (hf : Integrable f) :
    Integrable (cellAverage f) :=
  integrable_interpolate (hasSum_binMass volume measurable_round hf).summable

theorem integral_cellAverage {f : (ι → ℝ) → ℝ} (hf : Integrable f) :
    (∫ x, cellAverage f x) = ∫ x, f x := by
  rw [cellAverage, integral_interpolate (hasSum_binMass volume measurable_round hf).summable]
  exact (hasSum_binMass volume measurable_round hf).tsum_eq

theorem cellAverage_l1_contraction {f g : (ι → ℝ) → ℝ}
    (hf : Integrable f) (hg : Integrable g) :
    (∫ x, |cellAverage f x - cellAverage g x|) ≤ ∫ x, |f x - g x| := by
  rw [cellAverage, cellAverage, interpolate_l1_isometry
    (hasSum_binMass volume measurable_round hf).summable
    (hasSum_binMass volume measurable_round hg).summable]
  exact binMass_l1_contraction volume measurable_round hf hg

theorem cellAverage_interpolate (p : (ι → ℤ) → ℝ) :
    cellAverage (interpolate p) = interpolate p := by
  have heq : binMass volume round (interpolate p) = p := by
    funext z
    rw [binMass, ← cell_eq_fiber, integral_interpolate_cell]
  rw [cellAverage, heq]

/-- Translation and positive scalar dilation of a density, including its
Jacobian.  The manuscript uses `h = 1 / sqrt N` for interpolation and
`h = sqrt γ` for dilation of a recentered density. -/
def affineDensity (h : ℝ) (a : ι → ℝ) (f : (ι → ℝ) → ℝ) (x : ι → ℝ) : ℝ :=
  (h ^ Fintype.card ι)⁻¹ * f (h⁻¹ • (x - a))

theorem integral_affineDensity (h : ℝ) (hh : 0 < h) (a : ι → ℝ)
    (f : (ι → ℝ) → ℝ) : (∫ x, affineDensity h a f x) = ∫ x, f x := by
  unfold affineDensity
  rw [integral_const_mul]
  have ht : (∫ x : ι → ℝ, f (h⁻¹ • (x - a))) = ∫ x : ι → ℝ, f (h⁻¹ • x) := by
    simpa only [sub_eq_add_neg] using
      integral_add_right_eq_self (fun x : ι → ℝ ↦ f (h⁻¹ • x)) (-a)
  rw [ht, Measure.integral_comp_inv_smul_of_nonneg volume f hh.le]
  simp only [Module.finrank_pi, smul_eq_mul]
  rw [← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hh.ne'), one_mul]

theorem integrable_affineDensity (h : ℝ) (hh : 0 < h) (a : ι → ℝ)
    {f : (ι → ℝ) → ℝ} (hf : Integrable f) : Integrable (affineDensity h a f) := by
  have hd := hf.comp_smul (inv_ne_zero hh.ne')
  have ht := (measurePreserving_add_right (volume : Measure (ι → ℝ)) (-a)).integrable_comp_of_integrable hd
  simpa only [Function.comp_def, sub_eq_add_neg, affineDensity] using
    ht.const_mul ((h ^ Fintype.card ι)⁻¹)

theorem affineDensity_l1_isometry (h : ℝ) (hh : 0 < h) (a : ι → ℝ)
    (f g : (ι → ℝ) → ℝ) :
    (∫ x, |affineDensity h a f x - affineDensity h a g x|) = ∫ x, |f x - g x| := by
  have heq : (fun x ↦ |affineDensity h a f x - affineDensity h a g x|) =
      affineDensity h a (fun x ↦ |f x - g x|) := by
    funext x
    simp only [affineDensity, ← mul_sub, abs_mul,
      abs_of_nonneg (inv_nonneg.mpr (pow_nonneg hh.le _))]
  rw [heq, integral_affineDensity h hh a]

/-- Pulling a density back to unit-cell coordinates is the inverse density
transformation, with the inverse Jacobian. -/
def affinePull (h : ℝ) (a : ι → ℝ) (f : (ι → ℝ) → ℝ) (x : ι → ℝ) : ℝ :=
  h ^ Fintype.card ι * f (a + h • x)

theorem affinePull_eq_affineDensity (h : ℝ) (hh : h ≠ 0) (a : ι → ℝ)
    (f : (ι → ℝ) → ℝ) :
    affinePull h a f = affineDensity h⁻¹ (-(h⁻¹ • a)) f := by
  funext x
  simp only [affinePull, affineDensity, inv_pow, inv_inv, sub_neg_eq_add,
    smul_add, smul_smul, mul_inv_cancel₀ hh, one_smul, add_comm]

theorem integral_affinePull (h : ℝ) (hh : 0 < h) (a : ι → ℝ)
    (f : (ι → ℝ) → ℝ) : (∫ x, affinePull h a f x) = ∫ x, f x := by
  rw [affinePull_eq_affineDensity h hh.ne' a f]
  exact integral_affineDensity h⁻¹ (inv_pos.mpr hh) _ f

theorem integrable_affinePull (h : ℝ) (hh : 0 < h) (a : ι → ℝ)
    {f : (ι → ℝ) → ℝ} (hf : Integrable f) : Integrable (affinePull h a f) := by
  rw [affinePull_eq_affineDensity h hh.ne' a f]
  exact integrable_affineDensity h⁻¹ (inv_pos.mpr hh) _ hf

theorem affineDensity_affinePull (h : ℝ) (hh : h ≠ 0) (a : ι → ℝ)
    (f : (ι → ℝ) → ℝ) : affineDensity h a (affinePull h a f) = f := by
  funext x
  simp only [affineDensity, affinePull, smul_smul, mul_inv_cancel₀ hh, one_smul,
    add_sub_cancel, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hh), one_mul]

/-- Averaging over translated cells of side length `h`, defined concretely
by integration in unit-cell coordinates. -/
def scaledCellAverage (h : ℝ) (a : ι → ℝ) (f : (ι → ℝ) → ℝ) : (ι → ℝ) → ℝ :=
  affineDensity h a (cellAverage (affinePull h a f))

theorem integrable_scaledCellAverage (h : ℝ) (hh : 0 < h) (a : ι → ℝ)
    {f : (ι → ℝ) → ℝ} (hf : Integrable f) : Integrable (scaledCellAverage h a f) :=
  integrable_affineDensity h hh a (integrable_cellAverage (integrable_affinePull h hh a hf))

theorem integral_scaledCellAverage (h : ℝ) (hh : 0 < h) (a : ι → ℝ)
    {f : (ι → ℝ) → ℝ} (hf : Integrable f) :
    (∫ x, scaledCellAverage h a f x) = ∫ x, f x := by
  rw [scaledCellAverage, integral_affineDensity h hh a,
    integral_cellAverage (integrable_affinePull h hh a hf), integral_affinePull h hh a]

theorem scaledCellAverage_l1_contraction (h : ℝ) (hh : 0 < h) (a : ι → ℝ)
    {f g : (ι → ℝ) → ℝ} (hf : Integrable f) (hg : Integrable g) :
    (∫ x, |scaledCellAverage h a f x - scaledCellAverage h a g x|) ≤
      ∫ x, |f x - g x| := by
  rw [scaledCellAverage, scaledCellAverage, affineDensity_l1_isometry h hh a]
  have hb := cellAverage_l1_contraction (integrable_affinePull h hh a hf)
    (integrable_affinePull h hh a hg)
  rw [affinePull_eq_affineDensity h hh.ne' a f,
    affinePull_eq_affineDensity h hh.ne' a g,
    affineDensity_l1_isometry h⁻¹ (inv_pos.mpr hh)] at hb
  simpa only [affinePull_eq_affineDensity h hh.ne' a f,
    affinePull_eq_affineDensity h hh.ne' a g] using hb

theorem scaledCellAverage_eq_integral (h : ℝ) (hh : h ≠ 0) (a : ι → ℝ)
    (f : (ι → ℝ) → ℝ) (x : ι → ℝ) :
    scaledCellAverage h a f x =
      ∫ y in cell (round (h⁻¹ • (x - a))), f (a + h • y) := by
  simp only [scaledCellAverage, affineDensity, cellAverage, interpolate, binMass,
    ← cell_eq_fiber, affinePull, integral_const_mul]
  rw [← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hh), one_mul]

theorem scaledCellAverage_nonneg (h : ℝ) (hh : 0 < h) (a : ι → ℝ)
    {f : (ι → ℝ) → ℝ} (hf0 : ∀ x, 0 ≤ f x) (x : ι → ℝ) :
    0 ≤ scaledCellAverage h a f x := by
  rw [scaledCellAverage_eq_integral h hh.ne']
  exact integral_nonneg fun y ↦ hf0 (a + h • y)

theorem same_scaled_cell_dist_le (h : ℝ) (hh : 0 < h) (a x y : ι → ℝ)
    (hy : y ∈ cell (round (h⁻¹ • (x - a)))) : dist (a + h • y) x ≤ h := by
  let u := h⁻¹ • (x - a)
  have hu : u ∈ cell (round u) := (round_eq_iff u (round u)).mp rfl
  have hnorm : ‖y - u‖ ≤ 1 := by
    apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
    intro i
    have hyi := hy i (Set.mem_univ i)
    have hui := hu i (Set.mem_univ i)
    change (round u i : ℝ) - 1 / 2 ≤ y i ∧ y i < (round u i : ℝ) + 1 / 2 at hyi
    change (round u i : ℝ) - 1 / 2 ≤ u i ∧ u i < (round u i : ℝ) + 1 / 2 at hui
    rw [Real.norm_eq_abs, abs_le]
    change -1 ≤ y i - u i ∧ y i - u i ≤ 1
    constructor <;> linarith
  have heq : a + h • y - x = h • (y - u) := by
    dsimp [u]
    rw [smul_sub, smul_smul, mul_inv_cancel₀ hh.ne', one_smul]
    abel
  rw [dist_eq_norm, heq, norm_smul, Real.norm_eq_abs, abs_of_pos hh]
  nlinarith

/-- The cell-averaging error is controlled by the actual oscillation on one
cell.  Cells have diameter at most `h` in the coordinate supremum norm. -/
theorem scaledCellAverage_error_le (h : ℝ) (hh : 0 < h) (a : ι → ℝ)
    {f : (ι → ℝ) → ℝ} (hf : Integrable f) (x : ι → ℝ) (ε : ℝ)
    (hosc : ∀ y, dist y x ≤ h → |f y - f x| ≤ ε) :
    |scaledCellAverage h a f x - f x| ≤ ε := by
  let z := round (h⁻¹ • (x - a))
  have hi : Integrable (fun y : ι → ℝ ↦ f (a + h • y)) := by
    exact ((measurePreserving_add_left (volume : Measure (ι → ℝ)) a).integrable_comp_of_integrable hf).comp_smul hh.ne'
  have hc : IntegrableOn (fun _ : ι → ℝ ↦ f x) (cell z) :=
    integrableOn_const (by rw [volume_cell]; exact ENNReal.one_ne_top)
  have hconst : (∫ _y in cell z, f x) = f x := by
    simp [Measure.real, volume_cell]
  rw [scaledCellAverage_eq_integral h hh.ne']
  change |(∫ y in cell z, f (a + h • y)) - f x| ≤ ε
  rw [← hconst, ← integral_sub hi.integrableOn hc]
  have hb := norm_setIntegral_le_of_norm_le_const
    (show volume (cell z) < ∞ by rw [volume_cell]; exact ENNReal.one_lt_top)
    (f := fun y : ι → ℝ ↦ f (a + h • y) - f x)
    (fun y hy ↦ by
      simpa only [Real.norm_eq_abs] using hosc (a + h • y)
        (same_scaled_cell_dist_le h hh a x y hy))
  simpa only [Real.norm_eq_abs, Measure.real, volume_cell, ENNReal.toReal_one, mul_one] using hb

/-- Ordinary integrability supplies the reference tails used above. -/
theorem integral_compl_closedBall_tendsto_zero {f : (ι → ℝ) → ℝ} (hf : Integrable f) :
    Tendsto (fun n : ℕ ↦ ∫ x in (Metric.closedBall 0 (n : ℝ))ᶜ, f x) atTop (𝓝 0) := by
  have ht := tendsto_setIntegral_of_antitone
    (fun n : ℕ ↦ (Metric.isClosed_closedBall (x := (0 : ι → ℝ)) (ε := (n : ℝ))).measurableSet.compl)
    (show Antitone (fun n : ℕ ↦ (Metric.closedBall (0 : ι → ℝ) (n : ℝ))ᶜ) by
      intro m n hmn
      exact Set.compl_subset_compl.mpr (Metric.closedBall_subset_closedBall (by exact_mod_cast hmn)))
    ⟨0, hf.integrableOn⟩
  have hempty : (⋂ n : ℕ, (Metric.closedBall (0 : ι → ℝ) (n : ℝ))ᶜ) = ∅ := by
    rw [← Set.compl_iUnion, Metric.iUnion_closedBall_nat, Set.compl_univ]
  simpa only [hempty, setIntegral_empty] using ht

/-- Shrinking-cell averaging converges in `L¹` for every continuous,
nonnegative integrable density, uniformly over every translation of the
lattice.  No Poincaré estimate or averaging-limit premise is required. -/
theorem scaledCellAverage_l1_tendsto_uniform_translation
    {f : (ι → ℝ) → ℝ} (hf : Integrable f) (hf0 : ∀ x, 0 ≤ f x) (hfc : Continuous f)
    (h : ℕ → ℝ) (hh : ∀ n, 0 < h n) (hlim : Tendsto h atTop (𝓝 0)) :
    ∀ ε, 0 < ε → ∀ᶠ n in atTop, ∀ a : ι → ℝ,
      (∫ x, |scaledCellAverage (h n) a f x - f x|) < ε := by
  apply density_l1_uniform_of_local_and_tails volume
    (fun n a ↦ scaledCellAverage (h n) a f) (fun _ : ι → ℝ ↦ f)
    (fun n a ↦ integrable_scaledCellAverage (h n) (hh n) a hf) (fun _ ↦ hf)
    (fun n a ↦ scaledCellAverage_nonneg (h n) (hh n) a hf0) (fun _ ↦ hf0)
    (fun n a ↦ integral_scaledCellAverage (h n) (hh n) a hf)
    (fun k : ℕ ↦ Metric.closedBall 0 (k : ℝ))
    (fun _ ↦ Metric.isClosed_closedBall.measurableSet)
    (fun k ↦ (isCompact_closedBall (0 : ι → ℝ) (k : ℝ)).measure_ne_top)
  · intro k ε hε
    obtain ⟨δ, hδ, hosc⟩ := Metric.uniformContinuousOn_iff.mp
      ((isCompact_closedBall (0 : ι → ℝ) ((k : ℝ) + 1)).uniformContinuousOn_of_continuous hfc.continuousOn) ε hε
    filter_upwards [hlim.eventually (gt_mem_nhds hδ), hlim.eventually (gt_mem_nhds zero_lt_one)] with n hn hn1
    intro a x hx
    apply scaledCellAverage_error_le (h n) (hh n) a hf x ε
    intro y hy
    have hx' : x ∈ Metric.closedBall (0 : ι → ℝ) ((k : ℝ) + 1) :=
      Metric.closedBall_subset_closedBall (by linarith) hx
    have hy' : y ∈ Metric.closedBall (0 : ι → ℝ) ((k : ℝ) + 1) := by
      have hb := dist_triangle y x (0 : ι → ℝ)
      rw [Metric.mem_closedBall] at hx ⊢
      linarith
    simpa only [Real.dist_eq] using (hosc y hy' x hx' (hy.trans_lt hn)).le
  · intro ε hε
    have he := (integral_compl_closedBall_tendsto_zero hf).eventually (gt_mem_nhds hε)
    obtain ⟨k, hk⟩ := he.exists
    exact ⟨k, fun _ ↦ hk.le⟩

omit [Fintype ι] in
theorem cast_add_mem_cell_iff (z : ι → ℤ) (y : ι → ℝ) :
    (fun i ↦ (z i : ℝ) + y i) ∈ cell z ↔ y ∈ cell 0 := by
  simp only [cell, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Ico,
    Pi.zero_apply, Int.cast_zero, zero_sub, zero_add]
  constructor
  · intro h i
    have hi := h i
    constructor <;> linarith
  · intro h i
    have hi := h i
    constructor <;> linarith

/-- The same cell kernel in the original, undithered lattice coordinates. -/
theorem roundingPMF_eq_cell_overlap (γ : ℝ) (z w : ι → ℤ) :
    roundingPMF γ (fun i ↦ (z i : ℝ)) w =
      volume (((fun x : ι → ℝ ↦ γ • x) ⁻¹' cell w) ∩ cell z) := by
  rw [roundingPMF_eq_overlap]
  let a : ι → ℝ := fun i ↦ (z i : ℝ)
  have heq : ((fun y : ι → ℝ ↦ fun i ↦ γ * ((z i : ℝ) + y i)) ⁻¹' cell w ∩ cell 0) =
      (fun y : ι → ℝ ↦ a + y) ⁻¹' (((fun x : ι → ℝ ↦ γ • x) ⁻¹' cell w) ∩ cell z) := by
    ext y
    change (_ ∧ y ∈ cell 0) ↔ (_ ∧ (fun i ↦ (z i : ℝ) + y i) ∈ cell z)
    rw [cast_add_mem_cell_iff]
    rfl
  rw [heq, measure_preimage_add]

/-- Change of variables for a density restricted to one rounded output cell. -/
theorem binMass_affineDensity_zero (γ : ℝ) (hγ : 0 < γ)
    (f : (ι → ℝ) → ℝ) (w : ι → ℤ) :
    binMass volume round (affineDensity γ 0 f) w =
      ∫ y in (fun x : ι → ℝ ↦ γ • x) ⁻¹' cell w, f y := by
  classical
  let S := (fun x : ι → ℝ ↦ γ • x) ⁻¹' cell w
  have hS : MeasurableSet S := (measurable_const_smul γ) (measurableSet_cell w)
  have heq : (cell w).indicator (affineDensity γ 0 f) =
      affineDensity γ 0 (S.indicator f) := by
    funext x
    have hm : γ⁻¹ • x ∈ S ↔ x ∈ cell w := by
      simp only [S, Set.mem_preimage, smul_smul, mul_inv_cancel₀ hγ.ne', one_smul]
    by_cases hx : x ∈ cell w
    · simp only [Set.indicator_of_mem hx, affineDensity, sub_zero,
        Set.indicator_of_mem (hm.mpr hx)]
    · simp only [Set.indicator_of_notMem hx, affineDensity, sub_zero,
        Set.indicator_of_notMem (mt hm.mp hx), mul_zero]
  rw [binMass, ← cell_eq_fiber, ← integral_indicator (measurableSet_cell w), heq,
    integral_affineDensity γ hγ 0, integral_indicator hS]

/-- Exact intertwining for arbitrary absolutely summable real label weights:
the mass of the dilated interpolation in an output cell is the sum of the
actual randomized transition masses. -/
theorem binMass_dilated_interpolate (γ : ℝ) (hγ : 0 < γ)
    {p : (ι → ℤ) → ℝ} (hp : Summable p) (w : ι → ℤ) :
    binMass volume round (affineDensity γ 0 (interpolate p)) w =
      ∑' z, p z * (roundingPMF γ (fun i ↦ (z i : ℝ)) w).toReal := by
  rw [binMass_affineDensity_zero γ hγ]
  let S := (fun x : ι → ℝ ↦ γ • x) ⁻¹' cell w
  have hi : Integrable (interpolate p) (volume.restrict S) :=
    (integrable_interpolate hp).integrableOn
  have hs := hasSum_integral_iUnion (μ := volume.restrict S) measurableSet_cell cells_disjoint
    (show IntegrableOn (interpolate p) (⋃ z, cell z) (volume.restrict S) by
      simpa only [cells_cover, integrableOn_univ] using hi)
  have heach (z : ι → ℤ) :
      (∫ x in cell z, interpolate p x ∂volume.restrict S) =
        p z * (roundingPMF γ (fun i ↦ (z i : ℝ)) w).toReal := by
    rw [setIntegral_congr_fun (measurableSet_cell z)
      (fun x hx ↦ interpolate_eq_on_cell p z hx), setIntegral_const,
      roundingPMF_eq_cell_overlap]
    simp only [Measure.real, Measure.restrict_apply (measurableSet_cell z), smul_eq_mul,
      Set.inter_comm, mul_comm, S]
  simpa only [cells_cover, setIntegral_univ, heach] using hs.tsum_eq.symm

theorem transport_toReal (γ : ℝ) (p : PMF (ι → ℤ)) (w : ι → ℤ) :
    (transport γ p w).toReal =
      ∑' z, (p z).toReal * (roundingPMF γ (fun i ↦ (z i : ℝ)) w).toReal := by
  rw [transport_apply, ENNReal.tsum_toReal_eq
    (fun z ↦ ENNReal.mul_ne_top (p.apply_ne_top z)
      ((roundingPMF γ (fun i ↦ (z i : ℝ))).apply_ne_top w))]
  simp only [ENNReal.toReal_mul]

/-- The manuscript's dilation/averaging identity for the actual randomized
kernel, before fallback: no supplied Markov law or intertwining premise. -/
theorem rounding_intertwining (γ : ℝ) (hγ : 0 < γ) (p : PMF (ι → ℤ)) :
    cellAverage (affineDensity γ 0 (interpolate (fun z ↦ (p z).toReal))) =
      interpolate (fun w ↦ (transport γ p w).toReal) := by
  have hp : Summable (fun z ↦ (p z).toReal) := ENNReal.summable_toReal p.tsum_coe_ne_top
  have heq : binMass volume round (affineDensity γ 0 (interpolate (fun z ↦ (p z).toReal))) =
      fun w ↦ (transport γ p w).toReal := by
    funext w
    rw [binMass_dilated_interpolate γ hγ hp, transport_toReal]
  rw [cellAverage, heq]

theorem affinePull_affineDensity (h : ℝ) (hh : h ≠ 0) (a : ι → ℝ)
    (f : (ι → ℝ) → ℝ) : affinePull h a (affineDensity h a f) = f := by
  funext x
  simp only [affinePull, affineDensity, add_sub_cancel_left, smul_smul,
    inv_mul_cancel₀ hh, one_smul, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hh), one_mul]

/-- The dilated continuous law, put into the chosen output coordinates. -/
def preRoundedDensity (h : ℝ) (a : ι → ℝ) (γ : ℝ) (p : PMF (ι → ℤ)) :
    (ι → ℝ) → ℝ :=
  affineDensity h a (affineDensity γ 0 (interpolate (fun z ↦ (p z).toReal)))

/-- The actual randomized output law interpolated in the chosen coordinates. -/
def roundedDensity (h : ℝ) (a : ι → ℝ) (γ : ℝ) (p : PMF (ι → ℤ)) :
    (ι → ℝ) → ℝ :=
  affineDensity h a (interpolate (fun z ↦ (transport γ p z).toReal))

theorem rounding_intertwining_scaled (h : ℝ) (hh : 0 < h) (a : ι → ℝ)
    (γ : ℝ) (hγ : 0 < γ) (p : PMF (ι → ℤ)) :
    roundedDensity h a γ p = scaledCellAverage h a (preRoundedDensity h a γ p) := by
  rw [roundedDensity, ← rounding_intertwining γ hγ, scaledCellAverage,
    preRoundedDensity, affinePull_affineDensity h hh.ne']

theorem integrable_preRoundedDensity (h : ℝ) (hh : 0 < h) (a : ι → ℝ)
    (γ : ℝ) (hγ : 0 < γ) (p : PMF (ι → ℤ)) :
    Integrable (preRoundedDensity h a γ p) :=
  integrable_affineDensity h hh a (integrable_affineDensity γ hγ 0
    (integrable_interpolate (ENNReal.summable_toReal p.tsum_coe_ne_top)))

theorem preRoundedDensity_nonneg (h : ℝ) (hh : 0 < h) (a : ι → ℝ)
    (γ : ℝ) (hγ : 0 < γ) (p : PMF (ι → ℤ)) (x : ι → ℝ) :
    0 ≤ preRoundedDensity h a γ p x := by
  unfold preRoundedDensity affineDensity interpolate
  exact mul_nonneg (inv_nonneg.mpr (pow_nonneg hh.le _))
    (mul_nonneg (inv_nonneg.mpr (pow_nonneg hγ.le _)) ENNReal.toReal_nonneg)

theorem integral_preRoundedDensity (h : ℝ) (hh : 0 < h) (a : ι → ℝ)
    (γ : ℝ) (hγ : 0 < γ) (p : PMF (ι → ℤ)) :
    (∫ x, preRoundedDensity h a γ p x) = 1 := by
  rw [preRoundedDensity, integral_affineDensity h hh a, integral_affineDensity γ hγ 0,
    integral_interpolate (ENNReal.summable_toReal p.tsum_coe_ne_top),
    ← ENNReal.tsum_toReal_eq p.apply_ne_top, p.tsum_coe, ENNReal.toReal_one]

/-- Concrete two-error bound for the actual rounded output. -/
theorem roundedDensity_l1_comparison (h : ℝ) (hh : 0 < h) (a : ι → ℝ)
    (γ : ℝ) (hγ : 0 < γ) (p : PMF (ι → ℤ))
    {g : (ι → ℝ) → ℝ} (hg : Integrable g) :
    (∫ x, |roundedDensity h a γ p x - g x|) ≤
      (∫ x, |preRoundedDensity h a γ p x - g x|) +
      ∫ x, |scaledCellAverage h a g x - g x| := by
  rw [rounding_intertwining_scaled h hh a γ hγ]
  have hi := integrable_preRoundedDensity h hh a γ hγ p
  have hAi := integrable_scaledCellAverage h hh a hi
  have hAg := integrable_scaledCellAverage h hh a hg
  have htri : (∫ x, |scaledCellAverage h a (preRoundedDensity h a γ p) x - g x|) ≤
      (∫ x, |scaledCellAverage h a (preRoundedDensity h a γ p) x - scaledCellAverage h a g x|) +
      ∫ x, |scaledCellAverage h a g x - g x| := by
    have hadd := integral_add (hAi.sub hAg).abs (hAg.sub hg).abs
    simp only [Pi.sub_apply] at hadd
    rw [← hadd]
    apply integral_mono (hAi.sub hg).abs ((hAi.sub hAg).abs.add (hAg.sub hg).abs)
    intro x
    exact abs_sub_le _ _ _
  have hc := scaledCellAverage_l1_contraction h hh a hi hg
  linarith

/-- Gaussian comparison from a continuous normalized reference density and
an explicit local limit for the dilated input interpolation.  In particular,
there is no Markov-kernel bridge, cell-averaging limit, or output tightness
hypothesis.  The genuinely paper-specific local estimate is `hlocal`.

For the manuscript one takes output mesh `1 / sqrt m`, output translation
`-sqrt m * p`, raw label dilation `γ = m/n`, and the corresponding dilated
Gaussian reference density. -/
theorem roundedDensity_l1_of_local_limit
    (h γ : ℕ → ℝ) (a : ℕ → ι → ℝ) (p : ℕ → PMF (ι → ℤ))
    (hh : ∀ n, 0 < h n) (hγ : ∀ n, 0 < γ n) (hlim : Tendsto h atTop (𝓝 0))
    {g : (ι → ℝ) → ℝ} (hg : Integrable g) (hg0 : ∀ x, 0 ≤ g x)
    (hgc : Continuous g) (hgmass : (∫ x, g x) = 1)
    (hlocal : ∀ k δ, 0 < δ → ∀ᶠ n in atTop, ∀ x ∈ Metric.closedBall 0 (k : ℝ),
      |preRoundedDensity (h n) (a n) (γ n) (p n) x - g x| ≤ δ) :
    ∀ ε, 0 < ε → ∀ᶠ n in atTop,
      (∫ x, |roundedDensity (h n) (a n) (γ n) (p n) x - g x|) < ε := by
  have hsource : ∀ ε, 0 < ε → ∀ᶠ n in atTop,
      (∫ x, |preRoundedDensity (h n) (a n) (γ n) (p n) x - g x|) < ε := by
    have hu := density_l1_uniform_of_local_and_tails volume
      (fun n (_ : Unit) ↦ preRoundedDensity (h n) (a n) (γ n) (p n)) (fun _ : Unit ↦ g)
      (fun n _ ↦ integrable_preRoundedDensity (h n) (hh n) (a n) (γ n) (hγ n) (p n))
      (fun _ ↦ hg)
      (fun n _ ↦ preRoundedDensity_nonneg (h n) (hh n) (a n) (γ n) (hγ n) (p n))
      (fun _ ↦ hg0)
      (fun n _ ↦ (integral_preRoundedDensity (h n) (hh n) (a n) (γ n) (hγ n) (p n)).trans hgmass.symm)
      (fun k : ℕ ↦ Metric.closedBall 0 (k : ℝ))
      (fun _ ↦ Metric.isClosed_closedBall.measurableSet)
      (fun k ↦ (isCompact_closedBall (0 : ι → ℝ) (k : ℝ)).measure_ne_top)
      (fun k δ hδ ↦ (hlocal k δ hδ).mono fun n hn _ ↦ hn)
      (by
        intro δ hδ
        obtain ⟨k, hk⟩ := ((integral_compl_closedBall_tendsto_zero hg).eventually (gt_mem_nhds hδ)).exists
        exact ⟨k, fun _ ↦ hk.le⟩)
    intro ε hε
    exact (hu ε hε).mono fun n hn ↦ hn ()
  intro ε hε
  filter_upwards [hsource (ε / 2) (by positivity),
    scaledCellAverage_l1_tendsto_uniform_translation hg hg0 hgc h hh hlim (ε / 2) (by positivity)] with n hn hnav
  have hb := roundedDensity_l1_comparison (h n) (hh n) (a n) (γ n) (hγ n) (p n) hg
  have ha := hnav (a n)
  linarith

end Cloning.YoungRounding
