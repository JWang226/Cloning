import Cloning.YoungFlatCouplingFinite
import Cloning.YoungUniformLocalScheffe

/-! The common part of two normalized densities gives a finite subcoupling;
its missing mass is exactly half their L¹ distance. -/
noncomputable section
open scoped BigOperators Topology Classical
open MeasureTheory Filter
namespace Cloning.YoungFlatCoupling
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
variable {X I J : Type*} [MeasurableSpace X] [Fintype I] [Fintype J]
variable (μ : Measure X)

def densityBin (Q : X → I) (f : X → ℝ) (i : I) : ℝ :=
  ∫ x, if Q x = i then f x else 0 ∂μ

def densityCommon (Q : X → I) (S : X → J) (f g : X → ℝ) (i : I) (j : J) : ℝ :=
  ∫ x, if Q x = i ∧ S x = j then min (f x) (g x) else 0 ∂μ

theorem integrable_bin (Q : X → I) (f : X → ℝ)
    (hQ : ∀ i, MeasurableSet {x | Q x = i}) (hf : Integrable f μ) (i : I) :
    Integrable (fun x => if Q x = i then f x else 0) μ := by
  exact hf.indicator (hQ i)

theorem densityBin_nonneg (Q : X → I) (f : X → ℝ) (hf : ∀ x, 0 ≤ f x) (i : I) :
    0 ≤ densityBin μ Q f i := by
  apply integral_nonneg
  intro x
  dsimp only
  split_ifs
  · exact hf x
  · exact le_rfl

theorem densityBin_sum (Q : X → I) (f : X → ℝ)
    (hQ : ∀ i, MeasurableSet {x | Q x = i}) (hf : Integrable f μ) :
    (∑ i, densityBin μ Q f i) = ∫ x, f x ∂μ := by
  simp only [densityBin]
  rw [← integral_finset_sum _ (fun i _ => integrable_bin μ Q f hQ hf i)]
  apply integral_congr_ae
  exact ae_of_all _ (fun x => by simp)

theorem densityCommon_row (Q : X → I) (S : X → J) (f g : X → ℝ)
    (hQ : ∀ i, MeasurableSet {x | Q x = i}) (hS : ∀ j, MeasurableSet {x | S x = j})
    (hf : Integrable f μ) (hg : Integrable g μ) (i : I) :
    (∑ j, densityCommon μ Q S f g i j) = densityBin μ Q (fun x => min (f x) (g x)) i := by
  have hmin : Integrable (fun x => min (f x) (g x)) μ := hf.inf hg
  have hi j : Integrable (fun x => if Q x = i ∧ S x = j then min (f x) (g x) else 0) μ :=
    by
      convert hmin.indicator ((hQ i).inter (hS j)) using 1
      funext x
      simp only [Set.indicator_apply, Set.mem_inter_iff, Set.mem_setOf_eq]
  simp only [densityCommon]
  rw [← integral_finset_sum _ (fun j _ => hi j)]
  apply integral_congr_ae
  apply ae_of_all
  intro x
  by_cases h : Q x = i <;> simp [h]

theorem densityCommon_col (Q : X → I) (S : X → J) (f g : X → ℝ)
    (hQ : ∀ i, MeasurableSet {x | Q x = i}) (hS : ∀ j, MeasurableSet {x | S x = j})
    (hf : Integrable f μ) (hg : Integrable g μ) (j : J) :
    (∑ i, densityCommon μ Q S f g i j) = densityBin μ S (fun x => min (f x) (g x)) j := by
  have he : densityCommon μ Q S f g = fun i j => densityCommon μ S Q g f j i := by
    funext i j
    simp only [densityCommon, and_comm, min_comm]
  rw [he, densityCommon_row μ S Q g f hS hQ hg hf]
  simp only [min_comm]

theorem densityCommon_nonneg (Q : X → I) (S : X → J) (f g : X → ℝ)
    (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x) (i : I) (j : J) :
    0 ≤ densityCommon μ Q S f g i j := by
  apply integral_nonneg
  intro x
  dsimp only
  split_ifs
  · exact le_min (hf x) (hg x)
  · exact le_rfl

theorem densityCommon_row_le (Q : X → I) (S : X → J) (f g : X → ℝ)
    (hQ : ∀ i, MeasurableSet {x | Q x = i}) (hS : ∀ j, MeasurableSet {x | S x = j})
    (hf : Integrable f μ) (hg : Integrable g μ) (i : I) :
    ∑ j, densityCommon μ Q S f g i j ≤ densityBin μ Q f i := by
  rw [densityCommon_row μ Q S f g hQ hS hf hg]
  apply integral_mono (integrable_bin μ Q _ hQ (hf.inf hg) i) (integrable_bin μ Q f hQ hf i)
  intro x
  dsimp only
  split_ifs
  · exact min_le_left _ _
  · exact le_rfl

theorem densityCommon_col_le (Q : X → I) (S : X → J) (f g : X → ℝ)
    (hQ : ∀ i, MeasurableSet {x | Q x = i}) (hS : ∀ j, MeasurableSet {x | S x = j})
    (hf : Integrable f μ) (hg : Integrable g μ) (j : J) :
    ∑ i, densityCommon μ Q S f g i j ≤ densityBin μ S g j := by
  rw [densityCommon_col μ Q S f g hQ hS hf hg]
  apply integral_mono (integrable_bin μ S _ hS (hf.inf hg) j) (integrable_bin μ S g hS hg j)
  intro x
  dsimp only
  split_ifs
  · exact min_le_right _ _
  · exact le_rfl

theorem densityCommon_mass (Q : X → I) (S : X → J) (f g : X → ℝ)
    (hQ : ∀ i, MeasurableSet {x | Q x = i}) (hS : ∀ j, MeasurableSet {x | S x = j})
    (hf : Integrable f μ) (hg : Integrable g μ) :
    commonMass (densityCommon μ Q S f g) = ∫ x, min (f x) (g x) ∂μ := by
  simp only [commonMass, densityCommon_row μ Q S f g hQ hS hf hg]
  exact densityBin_sum μ Q _ hQ (hf.inf hg)

theorem density_overlap_defect (f g : X → ℝ) (hf : Integrable f μ) (hg : Integrable g μ)
    (hfm : ∫ x, f x ∂μ = 1) (hgm : ∫ x, g x ∂μ = 1) :
    1 - (∫ x, min (f x) (g x) ∂μ) = (1/2 : ℝ) * ∫ x, |f x-g x| ∂μ := by
  have he : (fun x => |f x-g x|) = fun x => f x+g x-2*min (f x) (g x) := by
    funext x
    by_cases h : f x ≤ g x
    · rw [min_eq_left h, abs_of_nonpos (sub_nonpos.mpr h)]; ring
    · rw [min_eq_right (le_of_not_ge h), abs_of_nonneg (sub_nonneg.mpr (le_of_not_ge h))]; ring
  have hmin : Integrable (fun x => min (f x) (g x)) μ := hf.inf hg
  rw [he]
  erw [integral_sub (hf.add hg) (hmin.const_mul 2), integral_add hf hg,
    integral_const_mul, hfm, hgm]
  ring

end Cloning.YoungFlatCoupling
