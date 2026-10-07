import Cloning.TensorFlatProjectorAchievability

/-! The actual rank-one coupling only visits the one-row physical sectors. -/
noncomputable section
open scoped BigOperators Classical
namespace Cloning.TensorCloning
open Cloning.TensorLie Cloning.TensorLAN Cloning.YoungGeneral
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

/-- Padding a one-dimensional label in a genuine physical copy determines
its sole row from the tensor length. -/
theorem physical_weight_eq_oneRow_of_pad_shape {n k : ℕ}
    (H : PhysicalHighestTensor n (1+k)) (a : Shape 1 n)
    (ha : padShape a k=H.shape) :
    H.weight=padPartition (fun _ : Fin 1 => n) k := by
  have he : H.weight=padPartition (fun i => (a i).val) k := by
    exact (PhysicalHighestTensor.shape_eq_iff H (padShape a k)).mp ha.symm |>.trans
      (padShape_val a k)
  have hs := H.weight_sum
  rw [he,sum_padPartition] at hs
  have ha0 : (a 0).val=n := by simpa only [Fintype.sum_unique] using hs
  rw [he]
  congr 1
  funext i
  simpa only [Subsingleton.elim i 0] using ha0

/-- No multiplicity or selected-copy premise is needed: nonzero mass in the
literal lifted coupling forces both physical copy labels to be one-row. -/
theorem rankOne_copyCoupling_support {n m k : ℕ}
    (J : PMF (Shape 1 n × Shape 1 m))
    (i : SchurCopy n (1+k)) (j : SchurCopy m (1+k))
    (h : labelCouplingCopies (flatLabelCoupling J k) i j≠0) :
    ((recursivePhysicalDecomposition n (1+k)).get i).weight=
        padPartition (fun _ : Fin 1 => n) k ∧
      ((recursivePhysicalDecomposition m (1+k)).get j).weight=
        padPartition (fun _ : Fin 1 => m) k := by
  have hc : paddedFlatCoupling J k (physicalCopyShape n (1+k) i,
      physicalCopyShape m (1+k) j)≠0 := by
    intro hz
    apply h
    simp only [labelCouplingCopies,uniformCopyCoupling,flatLabelCoupling,hz,
      ENNReal.toReal_zero,zero_div]
  obtain ⟨a,b,ha,hb⟩ := paddedFlatCoupling_support J k _ _ hc
  exact ⟨physical_weight_eq_oneRow_of_pad_shape _ a ha,
    physical_weight_eq_oneRow_of_pad_shape _ b hb⟩

/-- The weights in the physical copy mixture sum to one. -/
theorem flat_copyCoupling_sum {r n m : ℕ} (k : ℕ) (hr : 0<r)
    (J : PMF (Shape r n × Shape r m))
    (hfst : J.map Prod.fst=tensorFlatYoungPMF n r hr)
    (hsnd : J.map Prod.snd=tensorFlatYoungPMF m r hr) :
    (∑ z : SchurCopy n (r+k) × SchurCopy m (r+k),
      labelCouplingCopies (flatLabelCoupling J k) z.1 z.2)=1 := by
  rw [Fintype.sum_prod_type]
  calc
    _ = ∑ i, knownCopyWeight n (r+k) (rankFlatSpectrum r k) i := by
      apply Finset.sum_congr rfl
      intro i _
      exact labelCouplingCopies_row (rankFlatSpectrum r k) (rankFlatSpectrum_nonneg r k)
        (rankFlatSpectrum_sum hr) _ (fun _ _ => ENNReal.toReal_nonneg)
        (paddedFlatCoupling_row J k hr hfst) (paddedFlatCoupling_col J k hr hsnd) i
    _ = 1 := knownCopyWeight_sum n (r+k) (rankFlatSpectrum r k)
      (rankFlatSpectrum_nonneg r k) (rankFlatSpectrum_sum hr)

end Cloning.TensorCloning
