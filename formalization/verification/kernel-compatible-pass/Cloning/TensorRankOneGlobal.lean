import Cloning.TensorRankOneTransition
import Cloning.TensorRankOneCoupling
import Cloning.TensorRankOneWernerCovariance

/-! The prescribed rank-one projector cloner is exactly the finite Werner
pure-state cloner on every pure product input. -/
noncomputable section
open scoped BigOperators Classical InnerProductSpace Matrix
namespace Cloning.TensorCloning
open Cloning.TensorLie Cloning.TensorLAN Cloning.PCT Cloning.InfiniteTraceClass
open Cloning.YoungGeneral Cloning.PCTRankAdapted Cloning.FiniteKrausLift Cloning.YoungFlatCoupling
open Cloning.GeneralSymmetricOccupation
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
local instance (n d : ℕ) : FiniteDimensional ℂ (TensorRegister n (Fin d)) :=
  (registerBasis (Fin n → Fin d)).toOrthonormalBasis.toBasis.finiteDimensional_of_finite
variable {n m k : ℕ}

/-- Every exact rank-one label coupling gives the same finite physical
output: all nonzero copy transitions are the literal Werner cloner. -/
theorem flatCoupledChannel_rankOne_rotated (J : PMF (Shape 1 n × Shape 1 m))
    (hfst : J.map Prod.fst=tensorFlatYoungPMF n 1 (by omega))
    (hsnd : J.map Prod.snd=tensorFlatYoungPMF m 1 (by omega)) (hnm : n≤m)
    (U : Matrix (Fin (1+k)) (Fin (1+k)) ℂ) (hU : Uᴴ*U=1) :
    (flatCoupledChannel k (by omega) J hfst hsnd).toLinearMap
      (matrixTensorPower (U*Matrix.diagonal (fun a=>(rankFlatSpectrum 1 k a:ℂ))*Uᴴ) n)=
      pureWernerOutput (s:=k) (by simp [Nat.add_comm])
        (matrixRegister U (registerBasis (Fin (1+k)) 0))
        ((matrixRegister_norm U hU _).trans ((registerBasis _).orthonormal.norm_eq_one _))
        (inputSlots n m hnm) := by
  let K := labelCouplingCopies (flatLabelCoupling J k)
  let W := pureWernerOutput (s:=k) (by simp [Nat.add_comm] : Fintype.card (Fin (1+k))=k+1)
    (matrixRegister U (registerBasis (Fin (1+k)) 0))
    ((matrixRegister_norm U hU _).trans ((registerBasis _).orthonormal.norm_eq_one _))
    (inputSlots n m hnm)
  have ht (i : SchurCopy n (1+k)) (j : SchurCopy m (1+k)) (hij : K i j≠0) :
      (copyTransition n m (1+k) i j).toLinearMap
        (canonicalRotatedGibbs ((recursivePhysicalDecomposition n (1+k)).get i)
          U (rankFlatSpectrum 1 k))=W := by
    obtain ⟨hi,hj⟩ := rankOne_copyCoupling_support J i j hij
    have h0 : ((recursivePhysicalDecomposition n (1+k)).get i).weight 0=n := by
      rw [hi]
      exact padPartition_left (k := k) (fun _ : Fin 1=>n) 0
    rw [canonicalRotatedGibbs,canonicalGibbsDensity_rankOne _ h0]
    change (copyTransition n m (1+k) i j).toLinearMap
      (conjugationLinearMap (partitionTensorAction _ _ U) (vectorProjector _))=W
    rw [copyTransition_covariant n m i j U hU,
      copyTransition_oneRow_highest_werner i j hnm hi hj]
    exact (pureWernerOutput_unitary _ U hU _ _ _).symm
  rw [flatCoupledChannel,coupledCopyChannel_rotated_apply]
  change (∑z : SchurCopy n (1+k)×SchurCopy m (1+k), (K z.1 z.2:ℂ) •
    (copyTransition n m (1+k) z.1 z.2).toLinearMap
      (canonicalRotatedGibbs ((recursivePhysicalDecomposition n (1+k)).get z.1)
        U (rankFlatSpectrum 1 k)))=W
  calc
    _ = ∑z : SchurCopy n (1+k)×SchurCopy m (1+k),(K z.1 z.2:ℂ) • W := by
      apply Finset.sum_congr rfl
      intro z _
      by_cases hz : K z.1 z.2=0
      · simp only [hz,Complex.ofReal_zero,zero_smul]
      · rw [ht z.1 z.2 hz]
    _ = (∑z : SchurCopy n (1+k)×SchurCopy m (1+k),(K z.1 z.2:ℂ)) • W :=
      (Finset.sum_smul ..).symm
    _ = W := by
      rw [← Complex.ofReal_sum,flat_copyCoupling_sum k (by omega) J hfst hsnd,
        Complex.ofReal_one,one_smul]

/-- The fixed prescribed projector cloner, independent of the unknown pure
state, coincides exactly with Werner's map on pure tensor inputs. -/
theorem rankFlatChannel_tensorProjector (k n m : ℕ) (hnm : n≤m)
    (ψ : Register (Fin (1+k))) (hψ : ‖ψ‖=1) :
    (rankFlatChannel 1 k (by omega) n m).toLinearMap
      (vectorProjector (tensorVector (fun _ : Fin n=>ψ)))=
      pureWernerOutput (s:=k) (by simp [Nat.add_comm]) ψ hψ (inputSlots n m hnm) := by
  obtain ⟨U,hU⟩ := exists_unitary_first_column k ψ hψ
  have hh := flatCoupledChannel_rankOne_rotated (k := k) (rankFlatCoupling 1 (by omega) n m)
    (rankFlatCoupling_map_fst 1 (by omega) n m) (rankFlatCoupling_map_snd 1 (by omega) n m)
    hnm (U : Matrix (Fin (1+k)) (Fin (1+k)) ℂ) (Unitary.star_mul_self_of_mem U.property)
  rw [matrixTensorPower_rankOne_rotated] at hh
  apply Subtype.ext
  have he := congrArg Subtype.val hh
  change ((flatCoupledChannel k (by omega) (rankFlatCoupling 1 (by omega) n m)
    (rankFlatCoupling_map_fst 1 (by omega) n m)
    (rankFlatCoupling_map_snd 1 (by omega) n m)).toLinearMap
      (vectorProjector (tensorVector (fun _ : Fin n=>
        matrixRegister (U : Matrix (Fin (1+k)) (Fin (1+k)) ℂ) (registerBasis (Fin (1+k)) 0))))).1=
    pureWernerOperator k (matrixRegister (U : Matrix (Fin (1+k)) (Fin (1+k)) ℂ)
      (registerBasis (Fin (1+k)) 0)) (inputSlots n m hnm) at he
  simpa only [hU] using he

/-- The two manuscript protocols agree exactly at rank one, at every finite
input and output sample size in the cloning regime. -/
theorem rankFlatChannel_eq_rankOnePCT_tensorProjector (k n t : ℕ)
    (ψ : Register (Fin (1+k))) (hψ : ‖ψ‖=1) :
    (rankFlatChannel 1 k (by omega) n (n+t)).toLinearMap
      (vectorProjector (tensorVector (fun _ : Fin n=>ψ)))=
    (Cloning.PhysicalFlatPCT.channel 0 k n t).toLinearMap
      (vectorProjector (tensorVector (fun _ : Fin n=>ψ))) := by
  rw [rankFlatChannel_tensorProjector k n (n+t) (Nat.le_add_right n t) ψ hψ,
    Cloning.PCTRankOne.channel_tensorProjector k n t ψ hψ]

end Cloning.TensorCloning
