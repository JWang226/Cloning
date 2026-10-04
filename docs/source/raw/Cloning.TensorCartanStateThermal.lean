import Cloning.TensorCartanStateOccupation
import Cloning.TensorGibbsThermalIdentification

/-! The limiting Cartan output law is an actual normalized product thermal state. -/
noncomputable section
open scoped BigOperators ComplexOrder InnerProductSpace Topology
namespace Cloning.TensorLie
open Cloning.TensorLAN Cloning.InfiniteTraceClass Cloning.InfiniteFidelity
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {d : ℕ}

def amplifiedRootParameter (t q : PositiveRoot d → ℝ) (a : PositiveRoot d) : ℝ :=
  1 - t a + t a * q a

theorem amplifiedRootParameter_nonneg (t q : PositiveRoot d → ℝ)
    (ht0 : ∀ a, 0 < t a) (ht1 : ∀ a, t a ≤ 1) (hq0 : ∀ a, 0 ≤ q a)
    (a : PositiveRoot d) : 0 ≤ amplifiedRootParameter t q a :=
  add_nonneg (sub_nonneg.mpr (ht1 a)) (mul_nonneg (ht0 a).le (hq0 a))

theorem amplifiedRootParameter_lt_one (t q : PositiveRoot d → ℝ)
    (ht0 : ∀ a, 0 < t a) (hq1 : ∀ a, q a < 1) (a : PositiveRoot d) :
    amplifiedRootParameter t q a < 1 := by
  unfold amplifiedRootParameter
  have := mul_lt_mul_of_pos_left (hq1 a) (ht0 a)
  nlinarith

def amplifiedFockParameter (t q : PositiveRoot d → ℝ)
    (i : Fin (Fintype.card (PositiveRoot d))) : ℝ :=
  amplifiedRootParameter t q ((Fintype.equivFin (PositiveRoot d)).symm i)

theorem amplifiedOccupationWeight_eq_productGeometric
    (t q : PositiveRoot d → ℝ) (k : PositiveRoot d → ℕ) :
    amplifiedOccupationWeight t q k =
      Cloning.ThermalWitness.productGeometric (amplifiedFockParameter t q) (fockOccupation d k) := by
  have he := (Fintype.equivFin (PositiveRoot d)).symm.prod_comp
    (fun a => (1 - amplifiedRootParameter t q a) * amplifiedRootParameter t q a ^ k a)
  calc
    _ = ∏ a, (1 - amplifiedRootParameter t q a) * amplifiedRootParameter t q a ^ k a := by
      apply Finset.prod_congr rfl
      intro a _
      simp only [amplifiedRootParameter]
      ring
    _ = _ := he.symm

theorem amplifiedOccupationWeight_hasSum (t q : PositiveRoot d → ℝ)
    (ht0 : ∀ a, 0 < t a) (ht1 : ∀ a, t a ≤ 1)
    (hq0 : ∀ a, 0 ≤ q a) (hq1 : ∀ a, q a < 1) :
    HasSum (amplifiedOccupationWeight t q) 1 := by
  have he : amplifiedOccupationWeight t q = fun k =>
      Cloning.ThermalWitness.productGeometric (amplifiedFockParameter t q) (fockOccupation d k) :=
    funext (amplifiedOccupationWeight_eq_productGeometric t q)
  rw [he]
  exact ((fockOccupationEquiv d).hasSum_iff
    (f := Cloning.ThermalWitness.productGeometric (amplifiedFockParameter t q))).mpr
    (Cloning.ThermalWitness.productGeometric_hasSum (q := amplifiedFockParameter t q)
      (fun i => amplifiedRootParameter_nonneg t q ht0 ht1 hq0 _)
      (fun i => amplifiedRootParameter_lt_one t q ht0 hq1 _))

theorem amplifiedOccupationWeight_nonneg (t q : PositiveRoot d → ℝ)
    (ht0 : ∀ a, 0 < t a) (ht1 : ∀ a, t a ≤ 1)
    (hq0 : ∀ a, 0 ≤ q a) (hq1 : ∀ a, q a < 1) (k : PositiveRoot d → ℕ) :
    0 ≤ amplifiedOccupationWeight t q k := by
  rw [amplifiedOccupationWeight_eq_productGeometric]
  exact Cloning.ThermalWitness.productGeometric_nonneg (q := amplifiedFockParameter t q)
    (fun i => amplifiedRootParameter_nonneg t q ht0 ht1 hq0 _)
    (fun i => amplifiedRootParameter_lt_one t q ht0 hq1 _) _

def cartanThermalOutput (t q : PositiveRoot d → ℝ) : TraceClass (RootFock d) :=
  vectorMixture (rootNumberFrame d) (amplifiedOccupationWeight t q)

theorem cartanThermalOutput_nonneg (t q : PositiveRoot d → ℝ)
    (ht0 : ∀ a, 0 < t a) (ht1 : ∀ a, t a ≤ 1)
    (hq0 : ∀ a, 0 ≤ q a) (hq1 : ∀ a, q a < 1) :
    0 ≤ (cartanThermalOutput t q).1 :=
  vectorMixture_nonneg _ (rootNumberFrame_orthonormal d).norm_eq_one _
    (amplifiedOccupationWeight_hasSum t q ht0 ht1 hq0 hq1).summable
    (amplifiedOccupationWeight_nonneg t q ht0 ht1 hq0 hq1)

theorem cartanThermalOutput_trace (t q : PositiveRoot d → ℝ)
    (ht0 : ∀ a, 0 < t a) (ht1 : ∀ a, t a ≤ 1)
    (hq0 : ∀ a, 0 ≤ q a) (hq1 : ∀ a, q a < 1) :
    traceCLM (cartanThermalOutput t q) = 1 := by
  rw [cartanThermalOutput, traceCLM_vectorMixture _ (rootNumberFrame_orthonormal d).norm_eq_one _
    (amplifiedOccupationWeight_hasSum t q ht0 ht1 hq0 hq1).summable,
    (amplifiedOccupationWeight_hasSum t q ht0 ht1 hq0 hq1).tsum_eq]
  rfl

theorem cartanThermalOutput_eigen (t q : PositiveRoot d → ℝ)
    (ht0 : ∀ a, 0 < t a) (ht1 : ∀ a, t a ≤ 1)
    (hq0 : ∀ a, 0 ≤ q a) (hq1 : ∀ a, q a < 1) (k : PositiveRoot d → ℕ) :
    (cartanThermalOutput t q).1 (rootNumberFrame d k) =
      (amplifiedOccupationWeight t q k : ℂ) • rootNumberFrame d k := by
  classical
  let L : TraceClass (RootFock d) →L[ℂ] RootFock d :=
    (ContinuousLinearMap.apply ℂ (RootFock d) (rootNumberFrame d k)).comp inclusionCLM
  change L (vectorMixture _ _) = _
  rw [vectorMixture, L.map_tsum (summable_weighted_projectors _
    (rootNumberFrame_orthonormal d).norm_eq_one _
    (amplifiedOccupationWeight_hasSum t q ht0 ht1 hq0 hq1).summable)]
  have he (j : PositiveRoot d → ℕ) : L (vectorProjector (rootNumberFrame d j)) =
      if j = k then rootNumberFrame d k else 0 := by
    change InnerProductSpace.rankOne ℂ (rootNumberFrame d j) (rootNumberFrame d j) (rootNumberFrame d k) = _
    rw [InnerProductSpace.rankOne_apply, orthonormal_iff_ite.mp (rootNumberFrame_orthonormal d) j k]
    split_ifs with hj
    · simp [hj]
    · simp
  simp only [map_smul, he]
  simp

theorem cartanThermalOutput_eq_productGeometric (t q : PositiveRoot d → ℝ) :
    cartanThermalOutput t q =
      vectorMixture (MultimodeCoherentGaussianMixture.numberBasis _)
        (Cloning.ThermalWitness.productGeometric (amplifiedFockParameter t q)) := by
  rw [cartanThermalOutput, vectorMixture, vectorMixture]
  simp_rw [amplifiedOccupationWeight_eq_productGeometric]
  exact (fockOccupationEquiv d).tsum_eq (fun k : Fin (Fintype.card (PositiveRoot d)) → ℕ =>
    (Cloning.ThermalWitness.productGeometric (amplifiedFockParameter t q) k : ℂ) •
      vectorProjector (MultimodeCoherentGaussianMixture.numberBasis _ k))

end Cloning.TensorLie
