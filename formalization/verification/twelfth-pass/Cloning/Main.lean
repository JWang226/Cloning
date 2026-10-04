import Cloning.BlockFidelity
import Cloning.Thermal
import Cloning.LAN
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Cloning values and conditional asymptotic assembly

This is a partial formalization, not an unconditional proof of the manuscript's
main theorems. The numerical sector-mixture estimates and the LAN/Gaussian
converse bounds occur explicitly as hypotheses. The limiting and finite-sum
reasoning connecting them is kernel checked.
-/

noncomputable section
open Filter
open scoped BigOperators Topology

namespace Cloning

set_option autoImplicit false

/-- A strictly ordered positive spectrum, normalized exactly as in the paper. -/
structure SimpleSpectrum (d : ℕ) where
  eigenvalue : Fin d → ℝ
  positive : ∀ i, 0 < eigenvalue i
  strictAnti : StrictAnti eigenvalue
  normalized : ∑ i, eigenvalue i = 1

abbrev PairIndex (d : ℕ) := {ij : Fin d × Fin d // ij.1 < ij.2}

def SimpleSpectrum.ratio {d : ℕ} (p : SimpleSpectrum d) (ij : PairIndex d) : ℝ :=
  p.eigenvalue ij.val.2 / p.eigenvalue ij.val.1

theorem SimpleSpectrum.ratio_pos {d : ℕ} (p : SimpleSpectrum d) (ij : PairIndex d) :
    0 < p.ratio ij := div_pos (p.positive _) (p.positive _)

theorem SimpleSpectrum.ratio_lt_one {d : ℕ} (p : SimpleSpectrum d) (ij : PairIndex d) :
    p.ratio ij < 1 := (div_lt_one (p.positive _)).mpr (p.strictAnti ij.property)

/-- Exact formula in `eq:main-values`, with each i<j pair counted once. -/
def orbitalValue {d : ℕ} (g : ℝ) (p : SimpleSpectrum d) : ℝ :=
  ∏ ij : PairIndex d, Thermal.modeFactor g (p.ratio ij)

def classicalValue (g : ℝ) (d : ℕ) : ℝ :=
  Thermal.classicalBase g ^ (((d : ℝ) - 1) / 2)

def universalValue {d : ℕ} (g : ℝ) (p : SimpleSpectrum d) : ℝ :=
  classicalValue g d * orbitalValue g p

/-- PCT's formula expressed through its geometric thermal parameters. -/
def pctValue {d : ℕ} (g : ℝ) (p : SimpleSpectrum d) : ℝ :=
  classicalValue (2 * g - 1) d *
    ∏ ij : PairIndex d, Thermal.fidelity (p.ratio ij) (Thermal.pct g (p.ratio ij))

theorem orbitalValue_pos {d : ℕ} {g : ℝ} (hg : 1 < g) (p : SimpleSpectrum d) :
    0 < orbitalValue g p := by
  apply Finset.prod_pos
  intro ij _
  exact Thermal.modeFactor_pos hg (p.ratio_pos ij).le (p.ratio_lt_one ij)

theorem orbitalValue_le_one {d : ℕ} {g : ℝ} (hg : 1 < g) (p : SimpleSpectrum d) :
    orbitalValue g p ≤ 1 := by
  apply Finset.prod_le_one
  · intro ij _
    exact (Thermal.modeFactor_pos hg (p.ratio_pos ij).le (p.ratio_lt_one ij)).le
  · intro ij _
    exact Thermal.modeFactor_le_one hg (p.ratio_pos ij).le (p.ratio_lt_one ij)

theorem classicalValue_pos {g : ℝ} (hg : 0 < g) (d : ℕ) :
    0 < classicalValue g d := Real.rpow_pos_of_pos (Thermal.classicalBase_pos hg) _

theorem classicalValue_le_one {g : ℝ} (hg : 0 < g) {d : ℕ} (hd : 1 ≤ d) :
    classicalValue g d ≤ 1 := by
  apply Real.rpow_le_one (Thermal.classicalBase_pos hg).le
    (Thermal.classicalBase_le_one hg.le)
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  linarith

theorem universalValue_pos {d : ℕ} {g : ℝ} (hg : 1 < g) (p : SimpleSpectrum d) :
    0 < universalValue g p :=
  mul_pos (classicalValue_pos (by linarith) d) (orbitalValue_pos hg p)

theorem universalValue_le_orbital {d : ℕ} {g : ℝ} (hg : 1 < g)
    (hd : 1 ≤ d) (p : SimpleSpectrum d) : universalValue g p ≤ orbitalValue g p := by
  exact (mul_le_mul_of_nonneg_right (classicalValue_le_one (by linarith) hd)
    (orbitalValue_pos hg p).le).trans_eq (one_mul _)

/-- Strict PCT loss for the explicit limiting formulas, in every dimension
`d ≥ 2`. Identifying these formulas with channel limits is a separate task. -/
theorem pctValue_lt_universalValue {d : ℕ} (hd : 2 ≤ d) {g : ℝ}
    (hg : 1 < g) (p : SimpleSpectrum d) : pctValue g p < universalValue g p := by
  have hg' : 0 < 2 * g - 1 := by linarith
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have he : (0 : ℝ) < ((d : ℝ) - 1) / 2 := by linarith
  have hc : classicalValue (2 * g - 1) d < classicalValue g d :=
    Real.rpow_lt_rpow (Thermal.classicalBase_pos hg').le
      (Thermal.pct_classicalBase_lt hg) he
  have hprod : (∏ ij : PairIndex d,
        Thermal.fidelity (p.ratio ij) (Thermal.pct g (p.ratio ij))) ≤ orbitalValue g p := by
    apply Finset.prod_le_prod
    · intro ij _
      have hqa := Thermal.lt_amplified hg (p.ratio_lt_one ij)
      have hap := Thermal.amplified_lt_pct hg (p.ratio_pos ij) (p.ratio_lt_one ij)
      exact (Thermal.fidelity_pos (p.ratio_pos ij).le (p.ratio_lt_one ij)
        ((p.ratio_pos ij).trans (hqa.trans hap)).le
        (Thermal.pct_lt_one hg (p.ratio_pos ij).le (p.ratio_lt_one ij))).le
    · intro ij _
      exact (Thermal.pct_fidelity_lt_modeFactor hg
        (p.ratio_pos ij) (p.ratio_lt_one ij)).le
  exact (mul_le_mul_of_nonneg_left hprod (classicalValue_pos hg' d).le).trans_lt
    (mul_lt_mul_of_pos_right hc (orbitalValue_pos hg p))

/-- Fully proved convergence of the lifted fidelity from its finite quantitative
ingredients. The label type depends on sample size, as Young diagrams do.
This abstract version retains `hquantum` and `hsector` as interfaces.
`MatrixFidelityAsymptotics` supplies `hquantum` from proved concrete matrix
deletion. The sector, discarded-mass, and label limits remain asymptotic inputs.
The classical trimming, block summation, and convergence are proved here. -/
theorem lifted_fidelity_converges
    {I : ℕ → Type*} [∀ n, Fintype (I n)]
    (p q qG f : (n : ℕ) → I n → ℝ)
    (actual η : ℕ → ℝ) (c l : ℝ)
    (hp : ∀ n i, 0 ≤ p n i) (hqG : ∀ n i, 0 ≤ qG n i)
    (hle : ∀ n i, qG n i ≤ q n i)
    (hps : ∀ n, ∑ i, p n i = 1) (hqs : ∀ n, ∑ i, q n i ≤ 1)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hη : ∀ n, 0 ≤ η n)
    (hsector : ∀ n i, 0 < qG n i → |f n i - c| ≤ η n)
    (hquantum : ∀ n,
      |actual n - ∑ i, Real.sqrt (qG n i) * Real.sqrt (p n i) * f n i| ≤
        Real.sqrt (∑ i, (q n i - qG n i)))
    (hηlimit : Tendsto η atTop (𝓝 0))
    (hmass : Tendsto (fun n => ∑ i, (q n i - qG n i)) atTop (𝓝 0))
    (hlabel : Tendsto (fun n => BlockFidelity.classicalAffinity (q n) (p n))
      atTop (𝓝 l)) : Tendsto actual atTop (𝓝 (c * l)) := by
  have herr := fun n => BlockFidelity.lifted_factorization_bound
    (p n) (q n) (qG n) (f n) (actual n) c (η n)
    (hp n) (hqG n) (hle n) (hps n) (hqs n) hc0 hc1 (hη n) (hsector n) (hquantum n)
  have hsqrt : Tendsto (fun n => Real.sqrt (∑ i, (q n i - qG n i))) atTop (𝓝 0) := by
    simpa using Real.continuous_sqrt.continuousAt.tendsto.comp hmass
  have herror : Tendsto
      (fun n => η n + 2 * Real.sqrt (∑ i, (q n i - qG n i))) atTop (𝓝 0) := by
    simpa using hηlimit.add (hsqrt.const_mul 2)
  have hdiff : Tendsto
      (fun n => actual n - c * BlockFidelity.classicalAffinity (q n) (p n))
      atTop (𝓝 0) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    filter_upwards [herror.eventually_lt_const hε] with n hn
    simpa only [Real.dist_eq, sub_zero] using (herr n).trans_lt hn
  have htotal := hdiff.add (hlabel.const_mul c)
  simpa only [sub_add_cancel, zero_add] using htotal

/-- A uniform sector-factorization error and a uniform label-affinity error
combine without increasing the latter, since the orbital factor is at most 1. -/
theorem uniform_lifted_error {P : Type*}
    (actual affinity c l : P → ℝ) (η ε ζ : ℝ)
    (hc0 : ∀ p, 0 ≤ c p) (hc1 : ∀ p, c p ≤ 1)
    (hζ : 0 ≤ ζ)
    (hfactor : ∀ p, |actual p - c p * affinity p| ≤ η + 2 * Real.sqrt ε)
    (hlabel : ∀ p, |affinity p - l p| ≤ ζ) :
    ∀ p, |actual p - c p * l p| ≤ η + 2 * Real.sqrt ε + ζ := by
  intro p
  have hprod : |c p * affinity p - c p * l p| ≤ ζ := by
    rw [← mul_sub, abs_mul, abs_of_nonneg (hc0 p)]
    exact (mul_le_mul_of_nonneg_left (hlabel p) (hc0 p)).trans
      (by simpa using mul_le_mul_of_nonneg_right (hc1 p) hζ)
  exact (abs_sub_le (actual p) (c p * affinity p) (c p * l p)).trans
    (add_le_add (hfactor p) hprod)

/-- Conditional known-spectrum optimum. The payoff is not secretly defined to
be the answer: it is arbitrary, with candidate lower bounds and two-scale
converse estimates supplied. No quantum/LAN estimate is assumed as an axiom. -/
theorem known_spectrum_optimum_of_bounds
    {d : ℕ} {g : ℝ} (p : SimpleSpectrum d)
    {I : ℕ → Type*} {Orbit : Type*} [Nonempty Orbit]
    (payoff : (n : ℕ) → I n → Orbit → ℝ) (candidate : (n : ℕ) → I n)
    (a b : ℕ → ℝ) (error : ℕ → ℕ → ℝ)
    (hzero : ∀ n i u, 0 ≤ payoff n i u) (hone : ∀ n i u, payoff n i u ≤ 1)
    (hcandidate : ∀ n u, a n ≤ payoff n (candidate n) u)
    (ha : Tendsto a atTop (𝓝 (orbitalValue g p)))
    (hupper : ∀ L, ∀ᶠ n in atTop, LAN.minimaxValue (payoff n) ≤ b L + error L n)
    (herror : ∀ L, Tendsto (error L) atTop (𝓝 0))
    (hb : Tendsto b atTop (𝓝 (orbitalValue g p))) :
    Tendsto (fun n => LAN.minimaxValue (payoff n)) atTop (𝓝 (orbitalValue g p)) :=
  LAN.minimax_converges_of_candidates payoff candidate a b error _
    hzero hone hcandidate ha hupper herror hb

/-- Conditional unknown-spectrum minimax theorem. Here `P` can be the
compact spectral set times the orbit. The uniform candidate approximation
is converted to a bound at the infimum over all parameters. The dense-interior
extension is proved separately in `LAN.upper_bound_infimum_of_dense`.

The uniform quantum achievability and the local Gaussian upper estimates
are still hypotheses, so this is not the unconditional manuscript theorem. -/
theorem unknown_spectrum_optimum_of_bounds
    {d : ℕ} {g : ℝ} (hg : 1 < g)
    {I : ℕ → Type*} {P : Type*} [Nonempty P]
    (spectrum : P → SimpleSpectrum d)
    (payoff : (n : ℕ) → I n → P → ℝ) (candidate : (n : ℕ) → I n)
    (δ b : ℕ → ℝ) (error : ℕ → ℕ → ℝ)
    (hzero : ∀ n i p, 0 ≤ payoff n i p) (hone : ∀ n i p, payoff n i p ≤ 1)
    (hcandidate : ∀ n p,
      |payoff n (candidate n) p - universalValue g (spectrum p)| ≤ δ n)
    (hδ : Tendsto δ atTop (𝓝 0))
    (hupper : ∀ L, ∀ᶠ n in atTop, LAN.minimaxValue (payoff n) ≤ b L + error L n)
    (herror : ∀ L, Tendsto (error L) atTop (𝓝 0))
    (hb : Tendsto b atTop (𝓝 (⨅ p, universalValue g (spectrum p)))) :
    Tendsto (fun n => LAN.minimaxValue (payoff n)) atTop
      (𝓝 (⨅ p, universalValue g (spectrum p))) := by
  let V := ⨅ p, universalValue g (spectrum p)
  have hbelow : BddBelow (Set.range (fun p => universalValue g (spectrum p))) := by
    refine ⟨0, ?_⟩
    rintro x ⟨p, rfl⟩
    exact (universalValue_pos hg (spectrum p)).le
  have hlow : ∀ n p, V - δ n ≤ payoff n (candidate n) p := by
    intro n p
    have hv : V ≤ universalValue g (spectrum p) := ciInf_le hbelow p
    have ha := (abs_le.mp (hcandidate n p)).1
    linarith
  apply LAN.minimax_converges_of_candidates payoff candidate (fun n => V - δ n)
    b error V hzero hone hlow
  · simpa using tendsto_const_nhds.sub hδ
  · exact hupper
  · exact herror
  · exact hb

end Cloning
