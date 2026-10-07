import Cloning.TensorFlatProjectorCopyCoupling
import Cloning.TensorFlatProjectorTransitionCovariance
import Cloning.TensorFlatProjectorCouplingPadding
import Cloning.YoungFlatCouplingRank
import Cloning.PhysicalFlatConverseOrbit

/-! A concrete physical channel driven by the exact rank-flat Young coupling. -/
noncomputable section
open scoped BigOperators InnerProductSpace Classical Matrix Topology
namespace Cloning.TensorCloning
open Cloning.PCT Cloning.TensorLie Cloning.TensorLAN Cloning.InfiniteTraceClass Cloning.Hybrid
open Cloning.YoungGeneral Cloning.YoungFlat Cloning.YoungFlatCoupling
open Filter
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
variable {n m d r : ℕ}
local instance (n d : ℕ) : FiniteDimensional ℂ (TensorRegister n (Fin d)) :=
  (registerBasis (Fin n → Fin d)).toOrthonormalBasis.toBasis.finiteDimensional_of_finite

def compatibleLabelFidelity (p : Fin d → ℝ) (hp : ∀a,0≤p a)
    (mu : Shape d n) (lam : Shape d m) : ℝ :=
  if PartitionCompatible (fun a => (mu a).val) (fun a => (lam a).val)
  then labelTransitionFidelity p hp mu lam else 0

theorem compatibleLabelFidelity_le_copy (p : Fin d → ℝ) (hp : ∀a,0≤p a)
    (U : unitary (Matrix (Fin d) (Fin d) ℂ))
    (i : SchurCopy n d) (j : SchurCopy m d) :
    compatibleLabelFidelity p hp (physicalCopyShape n d i) (physicalCopyShape m d j) ≤
      nonnegativeTransitionFidelity p hp U i j := by
  unfold compatibleLabelFidelity
  split_ifs with hc
  · rw [physicalCopyShape,physicalCopyShape,labelTransitionFidelity_copy,
      nonnegativeTransitionFidelity_unitary n m d p hp U
        (Unitary.star_mul_self_of_mem U.property) i j hc]
  · exact PositiveTraceClass.rootFidelity_nonneg _ _

def flatLabelCoupling (J : PMF (Shape r n × Shape r m)) (k : ℕ) :
    Shape (r+k) n → Shape (r+k) m → ℝ :=
  fun mu lam => (paddedFlatCoupling J k (mu,lam)).toReal

def flatCoupledChannel (k : ℕ) (hr : 0<r) (J : PMF (Shape r n × Shape r m))
    (hfst : J.map Prod.fst=tensorFlatYoungPMF n r hr)
    (hsnd : J.map Prod.snd=tensorFlatYoungPMF m r hr) :
    QuantumChannel (TensorRegister n (Fin (r+k))) (TensorRegister m (Fin (r+k))) :=
  coupledCopyChannel (rankFlatSpectrum r k) (rankFlatSpectrum_nonneg r k) (rankFlatSpectrum_sum hr)
    (labelCouplingCopies (flatLabelCoupling J k))
    (labelCouplingCopies_nonneg _ (fun _ _ => ENNReal.toReal_nonneg))
    (labelCouplingCopies_row _ _ _ _ (fun _ _ => ENNReal.toReal_nonneg)
      (paddedFlatCoupling_row J k hr hfst) (paddedFlatCoupling_col J k hr hsnd))

theorem coupling_nonzero_partition (hr : 0<r) (J : PMF (Shape r n × Shape r m))
    (hfst : J.map Prod.fst=tensorFlatYoungPMF n r hr)
    (hsnd : J.map Prod.snd=tensorFlatYoungPMF m r hr)
    (mu : Shape r n) (lam : Shape r m) (hJ : (J (mu,lam)).toReal ≠ 0) :
    Antitone (fun a => (mu a).val) ∧ Antitone (fun a => (lam a).val) := by
  constructor
  · by_contra h
    have he := Finset.single_le_sum (fun (b : Shape r m) _ =>
      (show 0 ≤ (J (mu,b)).toReal from ENNReal.toReal_nonneg))
      (Finset.mem_univ lam)
    rw [pmf_pair_sum_row,hfst] at he
    have hz : (tensorFlatYoungPMF n r hr mu).toReal=0 := by
      rw [tensorFlatYoungPMF,tensorYoungPMF_formula,physicalSectorCharacter,dif_neg h,mul_zero]
    rw [hz] at he
    exact hJ (le_antisymm he ENNReal.toReal_nonneg)
  · by_contra h
    have he := Finset.single_le_sum (fun (a : Shape r n) _ =>
      (show 0 ≤ (J (a,lam)).toReal from ENNReal.toReal_nonneg))
      (Finset.mem_univ mu)
    rw [pmf_pair_sum_col,hsnd] at he
    have hz : (tensorFlatYoungPMF m r hr lam).toReal=0 := by
      rw [tensorFlatYoungPMF,tensorYoungPMF_formula,physicalSectorCharacter,dif_neg h,mul_zero]
    rw [hz] at he
    exact hJ (le_antisymm he ENNReal.toReal_nonneg)

theorem flatCoupledChannel_payoff_lower (k : ℕ) (hr : 0<r)
    (J : PMF (Shape r n × Shape r m))
    (hfst : J.map Prod.fst=tensorFlatYoungPMF n r hr)
    (hsnd : J.map Prod.snd=tensorFlatYoungPMF m r hr)
    (U : unitary (Matrix (Fin (r+k)) (Fin (r+k)) ℂ)) :
    coupledFlatFidelity r k n m J ≤
      PhysicalFlatConverse.payoff r k hr n m (flatCoupledChannel k hr J hfst hsnd) U := by
  letI : NeZero (r+k) := ⟨by omega⟩
  let p := rankFlatSpectrum r k
  let hp := rankFlatSpectrum_nonneg r k
  let hs := rankFlatSpectrum_sum (k := k) hr
  let K := flatLabelCoupling J k
  have hK : ∀ mu lam,0≤K mu lam := fun _ _ => ENNReal.toReal_nonneg
  have hrow := paddedFlatCoupling_row J k hr hfst
  have hcol := paddedFlatCoupling_col J k hr hsnd
  have hR := labelCouplingCopies_row p hp hs K hK hrow hcol
  have hC := labelCouplingCopies_col p hp hs K hK hrow hcol
  have hbound := coupledCopyChannel_payoff_lower p hp hs (labelCouplingCopies K)
    (labelCouplingCopies_nonneg K hK) hR hC U
  have hobs := labelCouplingCopies_observable p hp hs K hK hrow hcol (compatibleLabelFidelity p hp)
  have hlower : (∑ mu,∑ lam,K mu lam*compatibleLabelFidelity p hp mu lam) ≤
      PhysicalFlatConverse.payoff r k hr n m (flatCoupledChannel k hr J hfst hsnd) U := by
    rw [← hobs]
    exact (Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ =>
      mul_le_mul_of_nonneg_left (compatibleLabelFidelity_le_copy p hp U i j)
        (labelCouplingCopies_nonneg K hK i j)))).trans (by
          simpa only [Fintype.sum_prod_type] using hbound)
  have he : (∑ mu,∑ lam,K mu lam*compatibleLabelFidelity p hp mu lam) =
      coupledFlatFidelity r k n m J := by
    rw [← Fintype.sum_prod_type (f := fun z : Shape (r+k) n × Shape (r+k) m =>
      K z.1 z.2*compatibleLabelFidelity p hp z.1 z.2)]
    change (∑ z,(paddedFlatCoupling J k z).toReal*compatibleLabelFidelity p hp z.1 z.2)=_
    unfold paddedFlatCoupling
    rw [← pmf_sum_map J (fun z => (padShape z.1 k,padShape z.2 k))
      (fun z => compatibleLabelFidelity p hp z.1 z.2)]
    unfold coupledFlatFidelity
    apply Finset.sum_congr rfl
    intro z _
    by_cases hz : (J z).toReal=0
    · simp [hz]
    obtain ⟨hm,hl⟩ := coupling_nonzero_partition hr J hfst hsnd z.1 z.2 hz
    by_cases hc : PartitionCompatible (fun a => (z.1 a).val) (fun a => (z.2 a).val)
    · have hpad := padPartition_compatible _ _ hc k
      rw [compatibleLabelFidelity,padShape_val,padShape_val,if_pos hpad,labelTransitionFidelity_pad z.1 z.2 hm hl hc k hr,if_pos hc]
    · have hpad : ¬ PartitionCompatible (fun a => (padShape z.1 k a).val)
          (fun a => (padShape z.2 k a).val) := by
        simpa only [padShape_val,padPartition_compatible_iff] using hc
      simp only [compatibleLabelFidelity,if_neg hpad,if_neg hc]
  exact he ▸ hlower

end Cloning.TensorCloning
