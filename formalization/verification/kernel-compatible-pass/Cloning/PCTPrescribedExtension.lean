import Cloning.TensorCloningPrescribedRestriction
import Cloning.TensorCloningPayoff
import Cloning.WernerAsymptotics

/-! Extend any physical n-to-(n+t) protocol to all requested sample sizes:
exact restriction for m≤n, and the given protocol for m>n. -/
noncomputable section
open scoped Topology
open Filter
namespace Cloning.PCTPrescribed
open Cloning.PCT Cloning.TensorLie Cloning.TensorCloning Cloning.InfiniteTraceClass
open Cloning.PCTPhysicalState
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {d : ℕ}

/-- The small-output branch is literal tensor-prefix partial trace. -/
def extendChannel
    (Φ : ∀ n t : ℕ, QuantumChannel (TensorRegister n (Fin d)) (TensorRegister (n+t) (Fin d)))
    (n m : ℕ) : QuantumChannel (TensorRegister n (Fin d)) (TensorRegister m (Fin d)) :=
  if h : m≤n then restrictionChannel n m d h else by
    have he : n+(m-n)=m := Nat.add_sub_of_le (le_of_lt (lt_of_not_ge h))
    exact he ▸ Φ n (m-n)

theorem extendChannel_of_le
    (Φ : ∀ n t : ℕ, QuantumChannel (TensorRegister n (Fin d)) (TensorRegister (n+t) (Fin d)))
    (n m : ℕ) (h : m≤n) : extendChannel Φ n m=restrictionChannel n m d h := by
  simp only [extendChannel, dif_pos h]

theorem extendChannel_add
    (Φ : ∀ n t : ℕ, QuantumChannel (TensorRegister n (Fin d)) (TensorRegister (n+t) (Fin d)))
    (n t : ℕ) (ht : 0<t) : extendChannel Φ n (n+t)=Φ n t := by
  unfold extendChannel
  rw [dif_neg (by omega : ¬n+t≤n)]
  apply eq_of_heq
  dsimp only
  apply rec_heq_of_heq
    (C := fun q : ℕ => QuantumChannel (TensorRegister n (Fin d)) (TensorRegister q (Fin d)))
    (Nat.add_sub_of_le (by omega : n≤n+t))
  rw [Nat.add_sub_cancel_left]

theorem extendChannel_self
    (Φ : ∀ n t : ℕ, QuantumChannel (TensorRegister n (Fin d)) (TensorRegister (n+t) (Fin d)))
    (n : ℕ) (X : TraceClass (TensorRegister n (Fin d))) :
    (extendChannel Φ n n).toLinearMap X=X := by
  rw [extendChannel_of_le Φ n n le_rfl]
  exact restrictionChannel_self n d le_rfl X

theorem extendChannel_tensorState_of_le [Nonempty (Fin d)]
    (Φ : ∀ n t : ℕ, QuantumChannel (TensorRegister n (Fin d)) (TensorRegister (n+t) (Fin d)))
    (n m : ℕ) (h : m≤n) (ρ : Cloning.MatrixFidelity.State (Fin d)) :
    (extendChannel Φ n m).toLinearMap (tensorState ρ n).1=(tensorState ρ m).1 := by
  cases d with
  | zero => exact Fin.elim0 (Classical.choice (inferInstance : Nonempty (Fin 0)))
  | succ d =>
    rw [extendChannel_of_le Φ n m h]
    exact restrictionChannel_tensorState n m h ρ

theorem extendChannel_payoff_of_le [Nonempty (Fin d)]
    (Φ : ∀ n t : ℕ, QuantumChannel (TensorRegister n (Fin d)) (TensorRegister (n+t) (Fin d)))
    (n m : ℕ) (h : m≤n) (ρ : Cloning.MatrixFidelity.State (Fin d)) :
    statePayoff n m (extendChannel Φ n m) ρ=1 := by
  have he : (tensorState ρ n).map (extendChannel Φ n m).toPositiveTracePreservingMap=
      tensorState ρ m := Subtype.ext (extendChannel_tensorState_of_le Φ n m h ρ)
  change ((tensorState ρ n).map _).rootFidelity (tensorState ρ m)=1
  rw [he, Cloning.Hybrid.PositiveTraceClass.rootFidelity_self, norm_tensorState]

theorem extendChannel_payoff_of_gt [Nonempty (Fin d)]
    (Φ : ∀ n t : ℕ, QuantumChannel (TensorRegister n (Fin d)) (TensorRegister (n+t) (Fin d)))
    (n m : ℕ) (h : n<m) (ρ : Cloning.MatrixFidelity.State (Fin d)) :
    statePayoff n m (extendChannel Φ n m) ρ =
      statePayoff n (n+(m-n)) (Φ n (m-n)) ρ := by
  obtain ⟨t,rfl⟩ := Nat.exists_eq_add_of_le h.le
  rw [Nat.add_sub_cancel_left, extendChannel_add Φ n t (by omega)]

theorem eventually_output_gt_input (m : ℕ → ℕ) {γ : ℝ} (hγ : 1<γ)
    (h : Tendsto (fun n => (m n : ℝ)/n) atTop (𝓝 γ)) : ∀ᶠ n in atTop, n<m n :=
  (Cloning.WernerAsymptotics.eventually_add_le m hγ h 1).mono (fun _ hn => by omega)

theorem addedCopies_ratio (m : ℕ → ℕ) {γ : ℝ} (hγ : 1<γ)
    (h : Tendsto (fun n => (m n : ℝ)/n) atTop (𝓝 γ)) :
    Tendsto (fun n => ((n+(m n-n) : ℕ) : ℝ)/n) atTop (𝓝 γ) := by
  apply h.congr'
  filter_upwards [eventually_output_gt_input m hγ h] with n hn
  rw [Nat.add_sub_of_le hn.le]

theorem eventually_extendChannel_payoff [Nonempty (Fin d)]
    (Φ : ∀ n t : ℕ, QuantumChannel (TensorRegister n (Fin d)) (TensorRegister (n+t) (Fin d)))
    (ρ : Cloning.MatrixFidelity.State (Fin d)) (m : ℕ → ℕ) {γ : ℝ} (hγ : 1<γ)
    (h : Tendsto (fun n => (m n : ℝ)/n) atTop (𝓝 γ)) :
    (fun n => statePayoff n (n+(m n-n)) (Φ n (m n-n)) ρ) =ᶠ[atTop]
      (fun n => statePayoff n (m n) (extendChannel Φ n (m n)) ρ) := by
  filter_upwards [eventually_output_gt_input m hγ h] with n hn
  exact (extendChannel_payoff_of_gt Φ n (m n) hn ρ).symm

end Cloning.PCTPrescribed
