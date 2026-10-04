import Cloning.AmplifierWeylThermal
import Cloning.WeylFlatPriorThermal

/-! Trace-norm continuity at vacuum thermal parameters. Pointwise convergence
of normalized occupation laws gives genuine trace-class convergence by the
proved countable Scheffé theorem. -/
noncomputable section
open scoped ComplexOrder Topology BigOperators
open Filter Cloning.InfiniteTraceClass Cloning.ThermalWitness
open Cloning.MultimodeCoherentGaussianMixture
namespace Cloning.Thermal
variable {d : ℕ}

/-- Strictly positive interior spectra approaching every nonnegative thermal
spectrum, including any combination of exact vacuum modes. -/
def positiveApprox (q : Fin d → ℝ) (n : ℕ) (i : Fin d) : ℝ :=
  (q i + ((n : ℝ) + 1)⁻¹) / (1 + ((n : ℝ) + 1)⁻¹)

lemma positiveApprox_pos (q : Fin d → ℝ) (hq0 : ∀ i, 0 ≤ q i) (n : ℕ) (i : Fin d) :
    0 < positiveApprox q n i := by
  unfold positiveApprox
  have h : 0 < ((n : ℝ) + 1)⁻¹ := by positivity
  exact div_pos (add_pos_of_nonneg_of_pos (hq0 i) h) (by linarith)

lemma positiveApprox_lt_one (q : Fin d → ℝ) (hq1 : ∀ i, q i < 1) (n : ℕ) (i : Fin d) :
    positiveApprox q n i < 1 := by
  unfold positiveApprox
  apply (div_lt_one (by positivity : 0 < 1 + ((n : ℝ) + 1)⁻¹)).mpr
  linarith [hq1 i]

lemma positiveApprox_tendsto (q : Fin d → ℝ) (i : Fin d) :
    Tendsto (fun n => positiveApprox q n i) atTop (𝓝 (q i)) := by
  have h : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 (0 : ℝ)) := by
    simpa only [one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  simpa [positiveApprox] using (tendsto_const_nhds.add h).div (tendsto_const_nhds.add h)
    (by norm_num : (1 : ℝ) + 0 ≠ 0)

end Cloning.Thermal
namespace Cloning.MultimodeCoherent
variable {d : ℕ}

/-- Product thermal density operators vary continuously in trace norm all
the way to zero mode parameters. -/
theorem productThermal_tendsto {q : ℕ → Fin d → ℝ} {x : Fin d → ℝ}
    (hq0 : ∀ n i, 0 ≤ q n i) (hq1 : ∀ n i, q n i < 1)
    (hx0 : ∀ i, 0 ≤ x i) (hx1 : ∀ i, x i < 1)
    (hlim : ∀ i, Tendsto (fun n => q n i) atTop (𝓝 (x i))) :
    Tendsto (fun n => vectorMixture (numberBasis d) (productGeometric (q n))) atTop
      (𝓝 (vectorMixture (numberBasis d) (productGeometric x))) := by
  apply vectorMixture_tendsto_of_pointwise (numberBasis d) (numberBasis d).orthonormal.norm_eq_one
    (fun n => productGeometric (q n)) (productGeometric x)
    (fun n => productGeometric_nonneg (hq0 n) (hq1 n)) (productGeometric_nonneg hx0 hx1)
    (fun n => productGeometric_hasSum (hq0 n) (hq1 n)) (productGeometric_hasSum hx0 hx1)
  intro k
  apply tendsto_finset_prod
  intro i _
  exact (tendsto_const_nhds.sub (hlim i)).mul ((hlim i).pow (k i))

lemma thermalPositive_positiveApprox_tendsto (q : Fin d → ℝ)
    (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i < 1) :
    Tendsto (fun n => thermalPositive (Thermal.positiveApprox q n)
      (fun i => (Thermal.positiveApprox_pos q hq0 n i).le)
      (Thermal.positiveApprox_lt_one q hq1 n)) atTop (𝓝 (thermalPositive q hq0 hq1)) := by
  apply tendsto_subtype_rng.mpr
  exact productThermal_tendsto
    (fun n i => (Thermal.positiveApprox_pos q hq0 n i).le)
    (Thermal.positiveApprox_lt_one q hq1) hq0 hq1 (Thermal.positiveApprox_tendsto q)

lemma modeFactor_positiveApprox_tendsto (g : ℝ) (hg : 0 < g) (q : Fin d → ℝ)
    (hq0 : ∀ i, 0 ≤ q i) :
    Tendsto (fun n => ∏ i, Thermal.modeFactor g (Thermal.positiveApprox q n i)) atTop
      (𝓝 (∏ i, Thermal.modeFactor g (q i))) := by
  apply tendsto_finset_prod
  intro i _
  exact (Thermal.modeFactor_continuousAt (ne_of_gt (add_pos_of_pos_of_nonneg hg (hq0 i)))).tendsto.comp
    (tendsto_const_nhds.prodMk_nhds (Thermal.positiveApprox_tendsto q i))

end Cloning.MultimodeCoherent
namespace Cloning.MultimodeAmplifier
open Cloning.MultimodeCoherent
variable {d : ℕ}
set_option backward.isDefEq.respectTransparency false

/-- Exact physical thermal amplification also covers vacuum modes; it follows
by trace-norm continuity of the actual channel, not a formal Gaussian label. -/
theorem gainChannel_productThermal_nonneg (g : ℝ) (hg : 1 < g) {q : Fin d → ℝ}
    (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i < 1) :
    (gainChannel g hg).toLinearMap (vectorMixture (numberBasis d) (productGeometric q)) =
      vectorMixture (numberBasis d) (productGeometric (fun i => Thermal.amplified g (q i))) := by
  let qn := Thermal.positiveApprox q
  have hn0 (n : ℕ) (i : Fin d) : 0 < qn n i := Thermal.positiveApprox_pos q hq0 n i
  have hn1 (n : ℕ) (i : Fin d) : qn n i < 1 := Thermal.positiveApprox_lt_one q hq1 n i
  have hX := productThermal_tendsto (fun n i => (hn0 n i).le) hn1 hq0 hq1
    (Thermal.positiveApprox_tendsto q)
  have hleft := (gainChannel g hg).toPositiveTracePreservingMap.continuous.tendsto
    (vectorMixture (numberBasis d) (productGeometric q)) |>.comp hX
  have hx0 (i : Fin d) : 0 ≤ Thermal.amplified g (q i) :=
    (hq0 i).trans (Thermal.lt_amplified hg (hq1 i)).le
  have hx1 (i : Fin d) : Thermal.amplified g (q i) < 1 :=
    Thermal.amplified_lt_one (by linarith) (hq1 i)
  have hright := productThermal_tendsto
    (fun n i => ((hn0 n i).le.trans (Thermal.lt_amplified hg (hn1 n i)).le))
    (fun n i => Thermal.amplified_lt_one (by linarith) (hn1 n i)) hx0 hx1
    (fun i => by
      unfold Thermal.amplified
      exact tendsto_const_nhds.sub ((tendsto_const_nhds.sub (Thermal.positiveApprox_tendsto q i)).div_const g))
  apply tendsto_nhds_unique hleft
  convert hright using 1
  funext n
  exact gainChannel_productThermal g hg (hn0 n) (hn1 n)

end Cloning.MultimodeAmplifier
