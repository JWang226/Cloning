import Cloning.TensorCloningPrescribedRestriction
import Cloning.TensorFlatProjectorAchievability

/-! The manuscript's prescribed channels at every finite sample size:
exact partial trace when m≤n, and the constructed Schur channel when m>n. -/
noncomputable section
open scoped BigOperators InnerProductSpace ComplexOrder Matrix Classical
namespace Cloning.TensorCloning
open Cloning.PCT Cloning.TensorLie Cloning.InfiniteTraceClass Cloning.PCTPhysicalState
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

def prescribedChannel (n m d : ℕ)
    (Φ : QuantumChannel (TensorRegister n (Fin d)) (TensorRegister m (Fin d))) :
    QuantumChannel (TensorRegister n (Fin d)) (TensorRegister m (Fin d)) :=
  if h : m≤n then restrictionChannel n m d h else Φ

theorem prescribedChannel_of_le (n m d : ℕ)
    (Φ : QuantumChannel (TensorRegister n (Fin d)) (TensorRegister m (Fin d))) (h : m≤n) :
    prescribedChannel n m d Φ=restrictionChannel n m d h := by simp only [prescribedChannel,dif_pos h]

theorem prescribedChannel_of_lt (n m d : ℕ)
    (Φ : QuantumChannel (TensorRegister n (Fin d)) (TensorRegister m (Fin d))) (h : n<m) :
    prescribedChannel n m d Φ=Φ := by simp only [prescribedChannel,dif_neg (not_le.mpr h)]

theorem prescribedChannel_tensorState {d : ℕ} (n m : ℕ)
    (Φ : QuantumChannel (TensorRegister n (Fin (d+1))) (TensorRegister m (Fin (d+1))))
    (h : m≤n) (ρ : Cloning.MatrixFidelity.State (Fin (d+1))) :
    (prescribedChannel n m (d+1) Φ).toLinearMap (tensorState ρ n).1=(tensorState ρ m).1 := by
  rw [prescribedChannel_of_le n m (d+1) Φ h,restrictionChannel_tensorState]

theorem prescribedChannel_self (n d : ℕ)
    (Φ : QuantumChannel (TensorRegister n (Fin d)) (TensorRegister n (Fin d)))
    (X : TraceClass (TensorRegister n (Fin d))) :
    (prescribedChannel n n d Φ).toLinearMap X=X := by
  rw [prescribedChannel_of_le n n d Φ le_rfl,restrictionChannel_self]

theorem prescribedChannel_covariant (n m d : ℕ)
    (Φ : QuantumChannel (TensorRegister n (Fin d)) (TensorRegister m (Fin d)))
    (U : Matrix (Fin d) (Fin d) ℂ) (hU : Uᴴ*U=1)
    (hΦ : ∀ X,Φ.toLinearMap (conjugationLinearMap (tensorOperator n U) X)=
      conjugationLinearMap (tensorOperator m U) (Φ.toLinearMap X))
    (X : TraceClass (TensorRegister n (Fin d))) :
    (prescribedChannel n m d Φ).toLinearMap (conjugationLinearMap (tensorOperator n U) X)=
      conjugationLinearMap (tensorOperator m U) ((prescribedChannel n m d Φ).toLinearMap X) := by
  by_cases h : m≤n
  · rw [prescribedChannel_of_le n m d Φ h]
    exact restrictionChannel_covariant n m d h U hU X
  · rw [prescribedChannel_of_lt n m d Φ (not_le.mp h)]
    exact hΦ X

def prescribedKnownSpectrumChannel (n m d : ℕ) (p : Fin d → ℝ)
    (hp : ∀ a,0≤p a) (hs : ∑ a,p a=1) :=
  prescribedChannel n m d (knownSpectrumChannel n m d p hp hs)

def prescribedUniversalChannel (n m d : ℕ) :=
  prescribedChannel n m (d+1) (universalChannel n m d)

def prescribedRankFlatChannel (r k : ℕ) (hr : 0<r) (n m : ℕ) :=
  prescribedChannel n m (r+k) (rankFlatChannel r k hr n m)

theorem prescribedKnownSpectrumChannel_covariant (n m d : ℕ) (p : Fin d → ℝ)
    (hp : ∀ a,0≤p a) (hs : ∑ a,p a=1)
    (U : Matrix (Fin d) (Fin d) ℂ) (hU : Uᴴ*U=1) (X : TraceClass (TensorRegister n (Fin d))) :
    (prescribedKnownSpectrumChannel n m d p hp hs).toLinearMap
      (conjugationLinearMap (tensorOperator n U) X)=
    conjugationLinearMap (tensorOperator m U) ((prescribedKnownSpectrumChannel n m d p hp hs).toLinearMap X) :=
  prescribedChannel_covariant n m d _ U hU (knownSpectrumChannel_covariant n m d p hp hs U hU) X

theorem prescribedUniversalChannel_covariant (n m d : ℕ)
    (U : Matrix (Fin (d+1)) (Fin (d+1)) ℂ) (hU : Uᴴ*U=1)
    (X : TraceClass (TensorRegister n (Fin (d+1)))) :
    (prescribedUniversalChannel n m d).toLinearMap (conjugationLinearMap (tensorOperator n U) X)=
    conjugationLinearMap (tensorOperator m U) ((prescribedUniversalChannel n m d).toLinearMap X) :=
  prescribedChannel_covariant n m (d+1) _ U hU (universalChannel_covariant n m d U hU) X

end Cloning.TensorCloning
