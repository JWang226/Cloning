import Cloning.YoungFlatCouplingDensity

/-! Event control for the exact-marginal overlap coupling. -/
noncomputable section
open scoped BigOperators Topology Classical
open MeasureTheory Filter
namespace Cloning.YoungFlatCoupling
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
variable {X I J : Type*} [MeasurableSpace X] [Fintype I] [Fintype J]
variable [MeasurableSpace I] [MeasurableSingletonClass I]
variable [MeasurableSpace J] [MeasurableSingletonClass J]
variable (μ : Measure X)

def densityCoupling (Q : X → I) (S : X → J) (f g : X → ℝ)
    (hQ : Measurable Q) (hS : Measurable S)
    (hf : Integrable f μ) (hg : Integrable g μ)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x)
    (hfm : ∫ x, f x ∂μ = 1) (hgm : ∫ x, g x ∂μ = 1) : PMF (I×J) :=
  completionPMF (densityBin μ Q f) (densityBin μ S g) (densityCommon μ Q S f g)
    ((densityBin_sum μ Q f (fun i => hQ (measurableSet_singleton i)) hf).trans hfm)
    ((densityBin_sum μ S g (fun j => hS (measurableSet_singleton j)) hg).trans hgm)
    (densityCommon_nonneg μ Q S f g hf0 hg0)
    (densityCommon_row_le μ Q S f g (fun i => hQ (measurableSet_singleton i))
      (fun j => hS (measurableSet_singleton j)) hf hg)
    (densityCommon_col_le μ Q S f g (fun i => hQ (measurableSet_singleton i))
      (fun j => hS (measurableSet_singleton j)) hf hg)

theorem densityCoupling_map_fst (Q : X → I) (S : X → J) (f g : X → ℝ)
    (hQ : Measurable Q) (hS : Measurable S)
    (hf : Integrable f μ) (hg : Integrable g μ)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x)
    (hfm : ∫ x, f x ∂μ = 1) (hgm : ∫ x, g x ∂μ = 1) (i : I) :
    ((densityCoupling μ Q S f g hQ hS hf hg hf0 hg0 hfm hgm).map Prod.fst) i =
      ENNReal.ofReal (densityBin μ Q f i) :=
  completionPMF_map_fst _ _ _ _ _ _ _ _ i

theorem densityCoupling_map_snd (Q : X → I) (S : X → J) (f g : X → ℝ)
    (hQ : Measurable Q) (hS : Measurable S)
    (hf : Integrable f μ) (hg : Integrable g μ)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x)
    (hfm : ∫ x, f x ∂μ = 1) (hgm : ∫ x, g x ∂μ = 1) (j : J) :
    ((densityCoupling μ Q S f g hQ hS hf hg hf0 hg0 hfm hgm).map Prod.snd) j =
      ENNReal.ofReal (densityBin μ S g j) :=
  completionPMF_map_snd _ _ _ _ _ _ _ _ j

theorem measurableSet_relation (Q : X → I) (S : X → J)
    (hQ : Measurable Q) (hS : Measurable S) (P : I → J → Prop) :
    MeasurableSet {x | P (Q x) (S x)} :=
  (hQ.prodMk hS) (Set.toFinite {ij : I×J | P ij.1 ij.2}).measurableSet

theorem integrable_relation (Q : X → I) (S : X → J)
    (hQ : Measurable Q) (hS : Measurable S) (P : I → J → Prop)
    (f : X → ℝ) (hf : Integrable f μ) :
    Integrable (fun x => if P (Q x) (S x) then f x else 0) μ :=
  hf.indicator (measurableSet_relation Q S hQ hS P)

theorem densityCommon_event (Q : X → I) (S : X → J) (f g : X → ℝ)
    (hQ : Measurable Q) (hS : Measurable S)
    (hf : Integrable f μ) (hg : Integrable g μ) (P : I → J → Prop) :
    (∑ i, ∑ j, if P i j then densityCommon μ Q S f g i j else 0) =
      ∫ x, if P (Q x) (S x) then min (f x) (g x) else 0 ∂μ := by
  have hmin : Integrable (fun x => min (f x) (g x)) μ := hf.inf hg
  have hi (i : I) (j : J) : Integrable
      (fun x => if Q x=i ∧ S x=j then min (f x) (g x) else 0) μ := by
    convert hmin.indicator ((hQ (measurableSet_singleton i)).inter
      (hS (measurableSet_singleton j))) using 1
    funext x
    simp only [Set.indicator_apply, Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff]
  have he (i : I) (j : J) : (if P i j then densityCommon μ Q S f g i j else 0) =
      ∫ x, if P i j then (if Q x=i ∧ S x=j then min (f x) (g x) else 0) else 0 ∂μ := by
    by_cases h : P i j <;> simp [h, densityCommon]
  have hii (i : I) (j : J) : Integrable
      (fun x => if P i j then (if Q x=i ∧ S x=j then min (f x) (g x) else 0) else 0) μ := by
    by_cases h : P i j
    · simpa only [if_pos h] using hi i j
    · simp only [if_neg h]; exact integrable_zero _ _ _
  simp_rw [he]
  simp_rw [← integral_finset_sum _ (fun j _ => hii _ j)]
  rw [← integral_finset_sum _ (fun i _ => integrable_finset_sum _ (fun j _ => hii i j))]
  apply integral_congr_ae
  apply ae_of_all
  intro x
  have hswap i j : (if P i j then (if Q x=i ∧ S x=j then min (f x) (g x) else 0) else 0) =
      if Q x=i then (if S x=j then (if P i j then min (f x) (g x) else 0) else 0) else 0 := by
    split_ifs <;> simp_all
  simp only [hswap, Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]

theorem densityCoupling_event_le (Q : X → I) (S : X → J) (f g : X → ℝ)
    (hQ : Measurable Q) (hS : Measurable S)
    (hf : Integrable f μ) (hg : Integrable g μ)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x)
    (hfm : ∫ x, f x ∂μ = 1) (hgm : ∫ x, g x ∂μ = 1) (P : I → J → Prop) :
    (∑ ij, if P ij.1 ij.2 then
      (densityCoupling μ Q S f g hQ hS hf hg hf0 hg0 hfm hgm ij).toReal else 0) ≤
      (∫ x, if P (Q x) (S x) then min (f x) (g x) else 0 ∂μ) +
        (1/2 : ℝ) * ∫ x, |f x-g x| ∂μ := by
  simp only [densityCoupling, completionPMF_toReal, Fintype.sum_prod_type]
  convert completionWeight_event_le (densityBin μ Q f) (densityBin μ S g)
    (densityCommon μ Q S f g) ((densityBin_sum μ Q f (fun i => hQ (measurableSet_singleton i)) hf).trans hfm)
    ((densityBin_sum μ S g (fun j => hS (measurableSet_singleton j)) hg).trans hgm)
    (densityCommon_row_le μ Q S f g (fun i => hQ (measurableSet_singleton i))
      (fun j => hS (measurableSet_singleton j)) hf hg)
    (densityCommon_col_le μ Q S f g (fun i => hQ (measurableSet_singleton i))
      (fun j => hS (measurableSet_singleton j)) hf hg) P using 1
  rw [densityCommon_event μ Q S f g hQ hS hf hg P,
    densityCommon_mass μ Q S f g (fun i => hQ (measurableSet_singleton i))
      (fun j => hS (measurableSet_singleton j)) hf hg,
    density_overlap_defect μ f g hf hg hfm hgm]

end Cloning.YoungFlatCoupling
