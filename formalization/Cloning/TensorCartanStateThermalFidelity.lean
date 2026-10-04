import Cloning.TensorCartanStateThermal
import Cloning.InfiniteFidelityCornerLimit

/-! The actual amplified thermal target has exhaustive finite corners and the
claimed product root fidelity. -/
noncomputable section
open scoped BigOperators ComplexOrder InnerProductSpace Topology
open Filter
namespace Cloning.TensorLie
open Cloning.TensorLAN Cloning.InfiniteTraceClass Cloning.InfiniteFidelity Cloning.Hybrid
open Cloning.InfiniteFidelityCorner Cloning.InfiniteFiniteCorner
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {d : ℕ}

def cartanThermalPositive (t q : PositiveRoot d → ℝ)
    (ht0 : ∀ a, 0 < t a) (ht1 : ∀ a, t a ≤ 1)
    (hq0 : ∀ a, 0 ≤ q a) (hq1 : ∀ a, q a < 1) : PositiveTraceClass (RootFock d) :=
  ⟨cartanThermalOutput t q, cartanThermalOutput_nonneg t q ht0 ht1 hq0 hq1⟩

def rootThermalPositive (p : Fin d → ℝ) (hp : ∀ a, 0 < p a) (hord : StrictAnti p) :
    PositiveTraceClass (RootFock d) := ⟨rootThermalState p, rootThermalState_nonneg p hp hord⟩

theorem cartanThermalPositive_norm (t q : PositiveRoot d → ℝ)
    (ht0 : ∀ a, 0 < t a) (ht1 : ∀ a, t a ≤ 1)
    (hq0 : ∀ a, 0 ≤ q a) (hq1 : ∀ a, q a < 1) :
    ‖(cartanThermalPositive t q ht0 ht1 hq0 hq1).1‖ = 1 := by
  rw [TraceClass.norm_eq_trace_re_of_nonneg _ (cartanThermalPositive t q ht0 ht1 hq0 hq1).2]
  change (traceCLM (cartanThermalOutput t q)).re = 1
  rw [cartanThermalOutput_trace t q ht0 ht1 hq0 hq1]
  rfl

theorem rootThermalPositive_norm (p : Fin d → ℝ) (hp : ∀ a, 0 < p a) (hord : StrictAnti p) :
    ‖(rootThermalPositive p hp hord).1‖ = 1 := by
  rw [TraceClass.norm_eq_trace_re_of_nonneg _ (rootThermalPositive p hp hord).2]
  change (traceCLM (rootThermalState p)).re = 1
  rw [rootThermalState_trace p hp hord]
  rfl

theorem cartanThermalOutput_cutoff_coefficient (t q : PositiveRoot d → ℝ)
    (ht0 : ∀ a, 0 < t a) (ht1 : ∀ a, t a ≤ 1)
    (hq0 : ∀ a, 0 ≤ q a) (hq1 : ∀ a, q a < 1) (R : ℕ) (i j : CutoffIndex d R) :
    ⟪cutoffNumberFrame d R i, (cartanThermalOutput t q).1 (cutoffNumberFrame d R j)⟫_ℂ =
      if i = j then (amplifiedOccupationWeight t q (cutoffOccupation d R i).val : ℂ) else 0 := by
  change ⟪cutoffNumberFrame d R i,
    (cartanThermalOutput t q).1 (rootNumberFrame d (cutoffOccupation d R j).val)⟫_ℂ = _
  rw [cartanThermalOutput_eigen t q ht0 ht1 hq0 hq1]
  change ⟪cutoffNumberFrame d R i, (_ : ℂ) • cutoffNumberFrame d R j⟫_ℂ = _
  rw [inner_smul_right, orthonormal_iff_ite.mp (cutoffNumberFrame_orthonormal d R)]
  split_ifs with h
  · subst j; rw [mul_one]
  · rw [mul_zero]

theorem rootThermalState_cutoff_coefficient (p : Fin d → ℝ) (hp : ∀ a, 0 < p a)
    (hord : StrictAnti p) (R : ℕ) (i j : CutoffIndex d R) :
    ⟪cutoffNumberFrame d R i, (rootThermalState p).1 (cutoffNumberFrame d R j)⟫_ℂ =
      if i = j then (bosonicOccupationWeight p (cutoffOccupation d R i).val : ℂ) else 0 := by
  change ⟪cutoffNumberFrame d R i,
    (rootThermalState p).1 (rootNumberFrame d (cutoffOccupation d R j).val)⟫_ℂ = _
  rw [rootThermalState_eigen p hp hord]
  change ⟪cutoffNumberFrame d R i, (_ : ℂ) • cutoffNumberFrame d R j⟫_ℂ = _
  rw [inner_smul_right, orthonormal_iff_ite.mp (cutoffNumberFrame_orthonormal d R)]
  split_ifs with h
  · subst j; rw [mul_one]
  · rw [mul_zero]

theorem cartanThermalOutput_cutoff_mass_tendsto (t q : PositiveRoot d → ℝ)
    (ht0 : ∀ a, 0 < t a) (ht1 : ∀ a, t a ≤ 1)
    (hq0 : ∀ a, 0 ≤ q a) (hq1 : ∀ a, q a < 1) :
    Tendsto (fun R => mass (cutoffNumberFrame d R) (cartanThermalOutput t q)) atTop (𝓝 1) := by
  have hs := heightOccupation_sum_tendsto (amplifiedOccupationWeight t q)
    (amplifiedOccupationWeight_hasSum t q ht0 ht1 hq0 hq1).summable
  rw [(amplifiedOccupationWeight_hasSum t q ht0 ht1 hq0 hq1).tsum_eq] at hs
  apply hs.congr
  intro R
  simp only [mass, Matrix.trace, Matrix.diag, matrixOf,
    cartanThermalOutput_cutoff_coefficient t q ht0 ht1 hq0 hq1,
    ↓reduceIte, Complex.re_sum, Complex.ofReal_re]
  exact ((cutoffOccupation d R).sum_comp (fun k => amplifiedOccupationWeight t q k.val)).symm

theorem rootThermalState_cutoff_mass_tendsto (p : Fin d → ℝ) (hp : ∀ a, 0 < p a)
    (hord : StrictAnti p) :
    Tendsto (fun R => mass (cutoffNumberFrame d R) (rootThermalState p)) atTop (𝓝 1) := by
  have hs := heightOccupation_sum_tendsto (bosonicOccupationWeight p)
    (bosonicOccupationWeight_hasSum p hp hord).summable
  rw [(bosonicOccupationWeight_hasSum p hp hord).tsum_eq] at hs
  apply hs.congr
  intro R
  simp only [mass, Matrix.trace, Matrix.diag, matrixOf,
    rootThermalState_cutoff_coefficient p hp hord, ↓reduceIte, Complex.re_sum, Complex.ofReal_re]
  exact ((cutoffOccupation d R).sum_comp (fun k => bosonicOccupationWeight p k.val)).symm

theorem cartanThermalPositive_rootFidelity (t : PositiveRoot d → ℝ)
    (ht0 : ∀ a, 0 < t a) (ht1 : ∀ a, t a ≤ 1)
    (p : Fin d → ℝ) (hp : ∀ a, 0 < p a) (hord : StrictAnti p) :
    (cartanThermalPositive t (rootBoltzmann p) ht0 ht1
      (fun a => (div_pos (hp _) (hp _)).le) (rootBoltzmann_lt_one p hp hord)).rootFidelity
      (rootThermalPositive p hp hord) =
        ∏ a : PositiveRoot d, Cloning.Thermal.fidelity
          (amplifiedRootParameter t (rootBoltzmann p) a) (rootBoltzmann p a) := by
  have hf := Cloning.InfiniteDiagonalFidelity.stateFidelity_productGeometric
    (MultimodeCoherentGaussianMixture.numberBasis (Fintype.card (PositiveRoot d)))
    (amplifiedFockParameter t (rootBoltzmann p)) (rootThermalParameter p)
    (fun i => amplifiedRootParameter_nonneg t (rootBoltzmann p) ht0 ht1
      (fun a => (div_pos (hp _) (hp _)).le) _)
    (fun i => amplifiedRootParameter_lt_one t (rootBoltzmann p) ht0
      (rootBoltzmann_lt_one p hp hord) _)
    (fun i => (div_pos (hp _) (hp _)).le)
    (fun i => rootBoltzmann_lt_one p hp hord _)
  have he := (Fintype.equivFin (PositiveRoot d)).symm.prod_comp
    (fun a => Cloning.Thermal.fidelity (amplifiedRootParameter t (rootBoltzmann p) a)
      (rootBoltzmann p a))
  change _ = _ at hf
  calc
    _ = ∏ i, Cloning.Thermal.fidelity
        (amplifiedFockParameter t (rootBoltzmann p) i) (rootThermalParameter p i) := by
      simpa only [PositiveTraceClass.rootFidelity, cartanThermalPositive, rootThermalPositive,
        cartanThermalOutput_eq_productGeometric, rootThermalState_eq_productGeometric,
        stateFidelity, Cloning.InfiniteDiagonalFidelity.productGeometricState,
        DensityState.vectorMixture] using hf
    _ = _ := he

end Cloning.TensorLie
