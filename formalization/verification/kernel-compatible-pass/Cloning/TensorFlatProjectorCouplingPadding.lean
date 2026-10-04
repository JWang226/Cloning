import Cloning.TensorFlatProjectorRankLaw
import Cloning.YoungFlatFidelityBounds

/-! Exact lifting of flat Young couplings into arbitrary ambient rank. -/
noncomputable section
open scoped BigOperators Classical
namespace Cloning.TensorLie
open Cloning.YoungGeneral Cloning.YoungFlat
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

def paddedFlatCoupling {r n m : ℕ} (J : PMF (Shape r n × Shape r m)) (k : ℕ) :
    PMF (Shape (r+k) n × Shape (r+k) m) :=
  J.map (fun z ↦ (padShape z.1 k, padShape z.2 k))

theorem paddedFlatCoupling_map_fst {r n m : ℕ} (J : PMF (Shape r n × Shape r m)) (k : ℕ)
    (hr : 0<r) (hfst : J.map Prod.fst=tensorFlatYoungPMF n r hr) :
    (paddedFlatCoupling J k).map Prod.fst=tensorRankFlatYoungPMF n r k hr := by
  rw [tensorRankFlatYoungPMF_eq_map hr, ← hfst]
  simp only [paddedFlatCoupling, PMF.map_comp, Function.comp_def]

theorem paddedFlatCoupling_map_snd {r n m : ℕ} (J : PMF (Shape r n × Shape r m)) (k : ℕ)
    (hr : 0<r) (hsnd : J.map Prod.snd=tensorFlatYoungPMF m r hr) :
    (paddedFlatCoupling J k).map Prod.snd=tensorRankFlatYoungPMF m r k hr := by
  rw [tensorRankFlatYoungPMF_eq_map hr, ← hsnd]
  simp only [paddedFlatCoupling, PMF.map_comp, Function.comp_def]

theorem pmf_pair_sum_row {α β : Type*} [Fintype α] [Fintype β] (J : PMF (α×β)) (a : α) :
    (∑ b, (J (a,b)).toReal)=(J.map Prod.fst a).toReal := by
  rw [PMF.map_apply, tsum_fintype, Fintype.sum_prod_type, Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
  exact (ENNReal.toReal_sum (fun b _ ↦ PMF.apply_ne_top J (a,b))).symm

theorem pmf_pair_sum_col {α β : Type*} [Fintype α] [Fintype β] (J : PMF (α×β)) (b : β) :
    (∑ a, (J (a,b)).toReal)=(J.map Prod.snd b).toReal := by
  rw [PMF.map_apply, tsum_fintype, Fintype.sum_prod_type]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
  exact (ENNReal.toReal_sum (fun a _ ↦ PMF.apply_ne_top J (a,b))).symm

theorem paddedFlatCoupling_row {r n m : ℕ} (J : PMF (Shape r n × Shape r m)) (k : ℕ)
    (hr : 0<r) (hfst : J.map Prod.fst=tensorFlatYoungPMF n r hr) (μ : Shape (r+k) n) :
    (∑ ν, (paddedFlatCoupling J k (μ,ν)).toReal)=(tensorRankFlatYoungPMF n r k hr μ).toReal := by
  rw [pmf_pair_sum_row, paddedFlatCoupling_map_fst J k hr hfst]

theorem paddedFlatCoupling_col {r n m : ℕ} (J : PMF (Shape r n × Shape r m)) (k : ℕ)
    (hr : 0<r) (hsnd : J.map Prod.snd=tensorFlatYoungPMF m r hr) (ν : Shape (r+k) m) :
    (∑ μ, (paddedFlatCoupling J k (μ,ν)).toReal)=(tensorRankFlatYoungPMF m r k hr ν).toReal := by
  rw [pmf_pair_sum_col, paddedFlatCoupling_map_snd J k hr hsnd]

theorem paddedFlatCoupling_support {r n m : ℕ} (J : PMF (Shape r n × Shape r m)) (k : ℕ)
    (μ : Shape (r+k) n) (ν : Shape (r+k) m) (h : paddedFlatCoupling J k (μ,ν)≠0) :
    ∃ a : Shape r n, ∃ b : Shape r m, padShape a k=μ ∧ padShape b k=ν := by
  by_contra hh
  apply h
  rw [paddedFlatCoupling, PMF.map_apply, tsum_fintype]
  apply Finset.sum_eq_zero
  intro z _
  apply if_neg
  intro he
  exact hh ⟨z.1,z.2,(congrArg Prod.fst he).symm,(congrArg Prod.snd he).symm⟩

end Cloning.TensorLie
