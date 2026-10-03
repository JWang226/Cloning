import Cloning.YoungCompatibility
import Cloning.YoungCompatibilityPMF

/-!
# The manuscript's actual randomized Young kernel with fallback

Every row is constructed as the pushforward of the normalized dither PMF.
On incompatible labels it uses exactly the one-row partition specified in the
manuscript. The row agrees with the raw kernel on all typical inputs under
proved numerical conditions.  Consequently the output-law change is bounded
by twice the input atypical probability, and its affinity change by the square
root of that quantity.  Young-law concentration remains a separate input.
-/

noncomputable section
open scoped BigOperators Topology Classical
open Filter

namespace Cloning.YoungCompatibility

/-- The one-row fallback in equation `rounding-kernel`. -/
def oneRow {d : ℕ} (m : ℤ) : Fin (d + 1) → ℤ := fun i ↦ if i = 0 then m else 0

theorem oneRow_isYoung {d : ℕ} (m : ℤ) (hm : 0 ≤ m) :
    IsYoung m (oneRow (d := d) m) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    simp only [oneRow]
    split_ifs <;> omega
  · intro i j hij
    by_cases hi : i = 0
    · simp only [oneRow, hi, ↓reduceIte]
      split_ifs <;> omega
    · have hj : j ≠ 0 := fun hj ↦ hi (le_antisymm (hj ▸ hij) (Fin.zero_le _))
      simp [oneRow, hi, hj]
  · simp [oneRow]

/-- The raw probability row on full affine-lattice labels. -/
def rawKernel {d : ℕ} (γ : ℝ) (m : ℤ) (μ : Fin (d + 1) → ℤ) :
    PMF (Fin (d + 1) → ℤ) :=
  (YoungRounding.roundingPMF γ (fun i : Fin d ↦ (μ i.castSucc : ℝ))).map (complete m)

/-- The exact fallback function in the manuscript. -/
def fallbackLabel {d : ℕ} (n m : ℤ) (μ ν : Fin (d + 1) → ℤ) : Fin (d + 1) → ℤ :=
  if Compatible n m μ ν then ν else oneRow m

/-- The actual normalized Young transition law, including fallback. -/
def fallbackKernel {d : ℕ} (γ : ℝ) (n m : ℤ) (μ : Fin (d + 1) → ℤ) :
    PMF (Fin (d + 1) → ℤ) :=
  (rawKernel γ m μ).map (fallbackLabel n m μ)

theorem fallbackKernel_sum {d : ℕ} (γ : ℝ) (n m : ℤ) (μ : Fin (d + 1) → ℤ) :
    ∑' ν, fallbackKernel γ n m μ ν = 1 := (fallbackKernel γ n m μ).tsum_coe

/-- Fallback really produces a Young output even on atypical input rows. -/
theorem fallbackKernel_support_isYoung {d : ℕ} (γ : ℝ) (n m : ℤ)
    (hm : 0 ≤ m) (μ : Fin (d + 1) → ℤ) (hμ : IsYoung n μ)
    (ν : Fin (d + 1) → ℤ) (hν : fallbackKernel γ n m μ ν ≠ 0) :
    IsYoung m ν := by
  obtain ⟨w, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hν
  unfold fallbackLabel
  split_ifs with h
  · exact compatible_isYoung hμ h
  · exact oneRow_isYoung m hm

/-- On rows whose raw support is compatible, the fallback PMF equals the raw
PMF.  This helper is instantiated below with the proved support theorem. -/
theorem fallbackKernel_eq_raw_of_support {d : ℕ} (γ : ℝ) (n m : ℤ)
    (μ : Fin (d + 1) → ℤ)
    (h : ∀ z, YoungRounding.roundingPMF γ (fun i : Fin d ↦ (μ i.castSucc : ℝ)) z ≠ 0 →
      Compatible n m μ (complete m z)) :
    fallbackKernel γ n m μ = rawKernel γ m μ := by
  unfold fallbackKernel rawKernel
  rw [PMF.map_comp]
  apply PMF.ext
  intro ν
  simp only [PMF.map_apply]
  apply tsum_congr
  intro z
  by_cases hz : YoungRounding.roundingPMF γ (fun i : Fin d ↦ (μ i.castSucc : ℝ)) z = 0
  · simp [hz]
  · simp [Function.comp_apply, fallbackLabel, h z hz]

/-- Typicality uses actual Young labels, plus the unnormalized coordinate
window equivalent to `‖μ/n-p‖∞ ≤ ε` for positive sample size. -/
def Typical {d : ℕ} (n : ℤ) (p : Fin (d + 1) → ℝ) (ε : ℝ)
    (μ : Fin (d + 1) → ℤ) : Prop :=
  IsYoung n μ ∧ ∀ i, |(μ i : ℝ) - (n : ℝ) * p i| ≤ (n : ℝ) * ε

/-- The row identity required for the PMF error theorem is now a conclusion,
proved for the actual randomized kernel under explicit spectral conditions. -/
theorem fallbackKernel_eq_raw_of_typical {d : ℕ} (hd : 1 ≤ d)
    (n m : ℤ) (p : Fin (d + 1) → ℝ) (γ ε a : ℝ)
    (hn : 0 ≤ (n : ℝ)) (hγ : 1 ≤ γ) (ha : 0 ≤ a)
    (hp : ∀ i, a ≤ p i) (hgap : ∀ i j, i < j → a ≤ p i - p j)
    (hε : ε ≤ a / 4)
    (hmargin : 4 * ((d : ℝ) * ((γ + 1) / 2)) ≤ (γ - 1) * (n : ℝ) * a)
    (hm : (m : ℝ) = γ * (n : ℝ))
    (μ : Fin (d + 1) → ℤ) (hμ : Typical n p ε μ) :
    fallbackKernel γ n m μ = rawKernel γ m μ := by
  apply fallbackKernel_eq_raw_of_support
  exact rounding_support_compatible hd n m μ p γ ε a hn hγ ha hp hgap hε hmargin
    hμ.1.2.2 hm hμ.2

/-- Countable-law version of the manuscript's actual fallback estimate. -/
theorem rounding_fallback_l1_bound {d : ℕ} (hd : 1 ≤ d)
    (n m : ℤ) (p : Fin (d + 1) → ℝ) (γ ε a : ℝ)
    (hn : 0 ≤ (n : ℝ)) (hγ : 1 ≤ γ) (ha : 0 ≤ a)
    (hp : ∀ i, a ≤ p i) (hgap : ∀ i j, i < j → a ≤ p i - p j)
    (hε : ε ≤ a / 4)
    (hmargin : 4 * ((d : ℝ) * ((γ + 1) / 2)) ≤ (γ - 1) * (n : ℝ) * a)
    (hm : (m : ℝ) = γ * (n : ℝ)) (P : PMF (Fin (d + 1) → ℤ)) :
    CountableScheffe.l1Distance
      (probability (P.bind (fallbackKernel γ n m)))
      (probability (P.bind (rawKernel γ m))) ≤ 2 * badMass P (Typical n p ε) := by
  apply bind_fallback_l1_bound
  exact fallbackKernel_eq_raw_of_typical hd n m p γ ε a hn hγ ha hp hgap hε hmargin hm

/-- The label-affinity cost of the actual fallback, for every normalized
countable target law, including the Young law at the output sample size. -/
theorem rounding_fallback_affinity_bound {d : ℕ} (hd : 1 ≤ d)
    (n m : ℤ) (p : Fin (d + 1) → ℝ) (γ ε a : ℝ)
    (hn : 0 ≤ (n : ℝ)) (hγ : 1 ≤ γ) (ha : 0 ≤ a)
    (hp : ∀ i, a ≤ p i) (hgap : ∀ i j, i < j → a ≤ p i - p j)
    (hε : ε ≤ a / 4)
    (hmargin : 4 * ((d : ℝ) * ((γ + 1) / 2)) ≤ (γ - 1) * (n : ℝ) * a)
    (hm : (m : ℝ) = γ * (n : ℝ)) (P Q : PMF (Fin (d + 1) → ℤ)) :
    |CountableScheffe.affinity (probability (P.bind (fallbackKernel γ n m))) (probability Q) -
      CountableScheffe.affinity (probability (P.bind (rawKernel γ m))) (probability Q)| ≤
        Real.sqrt (2 * badMass P (Typical n p ε)) := by
  apply bind_fallback_affinity_bound
  exact fallbackKernel_eq_raw_of_typical hd n m p γ ε a hn hγ ha hp hgap hε hmargin hm

/-- The manuscript's compact-spectrum, eventual fallback bound.  Every
quantifier over spectra, input laws and target laws follows the same eventual
sample threshold.  The kernel equality is derived, not assumed. -/
theorem eventually_fallback_error_bounds {d : ℕ} (hd : 1 ≤ d)
    (K : Set (Fin (d + 1) → ℝ)) (hK : IsCompact K)
    (hpos : ∀ p ∈ K, ∀ i, 0 < p i) (hanti : ∀ p ∈ K, StrictAnti p)
    (m : ℕ → ℤ) (γn ε : ℕ → ℝ) (γ : ℝ) (hγ : 1 < γ)
    (hγn : Tendsto γn atTop (𝓝 γ)) (hε : Tendsto ε atTop (𝓝 0))
    (hm : ∀ n, (m n : ℝ) = γn n * (n : ℝ)) :
    ∀ᶠ (n : ℕ) in atTop, ∀ p ∈ K, ∀ P Q : PMF (Fin (d + 1) → ℤ),
      CountableScheffe.l1Distance
        (probability (P.bind (fallbackKernel (γn n) n (m n))))
        (probability (P.bind (rawKernel (γn n) (m n)))) ≤
          2 * badMass P (Typical n p (ε n)) ∧
      |CountableScheffe.affinity (probability (P.bind (fallbackKernel (γn n) n (m n)))) (probability Q) -
        CountableScheffe.affinity (probability (P.bind (rawKernel (γn n) (m n)))) (probability Q)| ≤
          Real.sqrt (2 * badMass P (Typical n p (ε n))) := by
  obtain ⟨a, ha, hp, hgap⟩ := compact_spectra_positive_gap K hK hpos hanti
  filter_upwards [eventually_rounding_support_compatible hd m γn ε γ a ha hγ hγn hε hm]
    with n hn
  intro p hpk P Q
  have hsame (μ : Fin (d + 1) → ℤ) (hμ : Typical n p (ε n) μ) :
      fallbackKernel (γn n) n (m n) μ = rawKernel (γn n) (m n) μ := by
    apply fallbackKernel_eq_raw_of_support
    exact hn p (hp p hpk) (hgap p hpk) μ hμ.1.2.2 hμ.2
  exact ⟨bind_fallback_l1_bound P _ _ _ hsame,
    bind_fallback_affinity_bound P _ _ _ hsame Q⟩

/-- For any sequence of spectra in a compact interior set, concentration is
now the only missing premise for asymptotic invisibility of fallback.  Both
laws and every output target may vary with sample size. -/
theorem fallback_errors_tendsto_zero {d : ℕ} (hd : 1 ≤ d)
    (K : Set (Fin (d + 1) → ℝ)) (hK : IsCompact K)
    (hpos : ∀ p ∈ K, ∀ i, 0 < p i) (hanti : ∀ p ∈ K, StrictAnti p)
    (m : ℕ → ℤ) (γn ε : ℕ → ℝ) (γ : ℝ) (hγ : 1 < γ)
    (hγn : Tendsto γn atTop (𝓝 γ)) (hε : Tendsto ε atTop (𝓝 0))
    (hm : ∀ n, (m n : ℝ) = γn n * (n : ℝ))
    (p : ℕ → Fin (d + 1) → ℝ) (hp : ∀ n, p n ∈ K)
    (P Q : ℕ → PMF (Fin (d + 1) → ℤ))
    (hbad : Tendsto (fun n ↦ badMass (P n) (Typical n (p n) (ε n))) atTop (𝓝 0)) :
    Tendsto (fun n ↦ CountableScheffe.l1Distance
      (probability ((P n).bind (fallbackKernel (γn n) n (m n))))
      (probability ((P n).bind (rawKernel (γn n) (m n))))) atTop (𝓝 0) ∧
    Tendsto (fun n ↦ |CountableScheffe.affinity
      (probability ((P n).bind (fallbackKernel (γn n) n (m n)))) (probability (Q n)) -
      CountableScheffe.affinity (probability ((P n).bind (rawKernel (γn n) (m n))))
        (probability (Q n))|) atTop (𝓝 0) := by
  have hb := eventually_fallback_error_bounds hd K hK hpos hanti m γn ε γ hγ hγn hε hm
  have hbad2 : Tendsto (fun n ↦ 2 * badMass (P n) (Typical n (p n) (ε n))) atTop (𝓝 0) := by
    simpa only [mul_zero] using hbad.const_mul 2
  constructor
  · apply squeeze_zero' (Eventually.of_forall (fun n ↦ tsum_nonneg (fun _ ↦ abs_nonneg _)))
    · exact hb.mono fun n hn ↦ (hn (p n) (hp n) (P n) (Q n)).1
    · exact hbad2
  · apply squeeze_zero' (Eventually.of_forall (fun n ↦ abs_nonneg _))
    · exact hb.mono fun n hn ↦ (hn (p n) (hp n) (P n) (Q n)).2
    · simpa only [Real.sqrt_zero] using hbad2.sqrt

end Cloning.YoungCompatibility
