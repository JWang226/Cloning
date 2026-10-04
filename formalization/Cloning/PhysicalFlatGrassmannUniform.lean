import Cloning.PhysicalFlatGrassmannTheorem
import Cloning.TensorCloningUniformCovariance

/-! Uniform convergence of the prescribed physical rank-flat cloner on
the entire Grassmann family, derived from exact finite covariance. -/
noncomputable section
open scoped BigOperators Topology Matrix ComplexOrder
open Filter
namespace Cloning.TensorCloning
open Cloning.PCT Cloning.TensorLie Cloning.TensorLAN Cloning.InfiniteTraceClass Cloning.Hybrid
open Cloning.PCTPhysicalState Cloning.PCTUnitaryTransport
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
local instance (n d : ℕ) : FiniteDimensional ℂ (TensorRegister n (Fin d)) :=
  (registerBasis (Fin n → Fin d)).toOrthonormalBasis.toBasis.finiteDimensional_of_finite

theorem statePayoff_conjugated_of_covariant {d : ℕ} [Nonempty (Fin d)] (n m : ℕ)
    (Φ : QuantumChannel (TensorRegister n (Fin d)) (TensorRegister m (Fin d)))
    (ρ : Cloning.MatrixFidelity.State (Fin d)) (U : unitary (Matrix (Fin d) (Fin d) ℂ))
    (hcov : ∀ A, Φ.toLinearMap (conjugationLinearMap (tensorOperator n U) A) =
      conjugationLinearMap (tensorOperator m U) (Φ.toLinearMap A)) :
    statePayoff n m Φ (conjugatedState ρ U) = statePayoff n m Φ ρ := by
  let A := (tensorState ρ n).map Φ.toPositiveTracePreservingMap
  let B := tensorState ρ m
  have hA : (tensorState (conjugatedState ρ U) n).map Φ.toPositiveTracePreservingMap =
      A.map (unitaryChannel (tensorUnitary U m)).toPositiveTracePreservingMap := by
    apply Subtype.ext
    change Φ.toLinearMap (tensorState (conjugatedState ρ U) n).1 = _
    rw [← tensorState_conjugated, tensor_unitaryChannel_eq_conjugation,
      hcov, ← tensor_unitaryChannel_eq_conjugation]
    rfl
  have hB : tensorState (conjugatedState ρ U) m =
      B.map (unitaryChannel (tensorUnitary U m)).toPositiveTracePreservingMap :=
    Subtype.ext (tensorState_conjugated ρ U m).symm
  change ((tensorState (conjugatedState ρ U) n).map Φ.toPositiveTracePreservingMap).rootFidelity
    (tensorState (conjugatedState ρ U) m) = _
  rw [hA,hB,rootFidelity_unitaryChannel]
  rfl

/-- All complex trace-class inputs satisfy exact finite covariance. -/
theorem rankFlatChannel_covariant (r k : ℕ) (hr : 0<r) (n m : ℕ)
    (U : Matrix (Fin (r+k)) (Fin (r+k)) ℂ) (hU : Uᴴ*U=1)
    (A : TraceClass (TensorRegister n (Fin (r+k)))) :
    (rankFlatChannel r k hr n m).toLinearMap (conjugationLinearMap (tensorOperator n U) A) =
      conjugationLinearMap (tensorOperator m U) ((rankFlatChannel r k hr n m).toLinearMap A) :=
  channel_covariant n m (r+k) _ _ _ U hU A

theorem rankFlatChannel_payoff_constant (r k : ℕ) (hr : 0<r) (n m : ℕ)
    (U : unitary (Matrix (Fin (r+k)) (Fin (r+k)) ℂ)) :
    letI : Nonempty (Fin (r+k)) := ⟨⟨0,by omega⟩⟩
    PhysicalFlatConverse.payoff r k hr n m (rankFlatChannel r k hr n m) U =
      statePayoff n m (rankFlatChannel r k hr n m) (PhysicalFlatConverse.flatState r k hr) := by
  letI : Nonempty (Fin (r+k)) := ⟨⟨0,by omega⟩⟩
  exact statePayoff_conjugated_of_covariant n m _ (PhysicalFlatConverse.flatState r k hr) U
    (rankFlatChannel_covariant r k hr n m U (Unitary.star_mul_self_of_mem U.property))

end Cloning.TensorCloning
namespace Cloning.PhysicalFlatGrassmann
open Cloning.PCT Cloning.TensorLie Cloning.TensorCloning Cloning.InfiniteTraceClass
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
variable (r k : ℕ) (hr : 0<r)

/-- The prescribed channel's payoff is bounded by the all-channel minimax
at every projector, because finite covariance makes its orbit payoff constant. -/
theorem rankFlatChannel_payoff_le_minimax (n m : ℕ) (P : Projector r k) :
    payoff r k hr n m (rankFlatChannel r k hr n m) P ≤ minimaxValue r k hr n m := by
  letI : Nonempty (Fin (r+k)) := ⟨⟨0,by omega⟩⟩
  obtain ⟨U,rfl⟩ := orbitProjector_surjective r k P
  change TensorCloning.statePayoff n m (rankFlatChannel r k hr n m)
    (state hr (orbitProjector r k U)) ≤ _
  rw [state_orbitProjector, minimaxValue_eq_orbit]
  change PhysicalFlatConverse.payoff r k hr n m (rankFlatChannel r k hr n m) U ≤ _
  rw [rankFlatChannel_payoff_constant]
  exact LAN.candidate_le_minimaxValue (PhysicalFlatConverse.payoff r k hr n m)
    (rankFlatChannel r k hr n m)
    (statePayoff n m (rankFlatChannel r k hr n m) (PhysicalFlatConverse.flatState r k hr))
    (PhysicalFlatConverse.payoff_le_one r k hr n m)
    (fun V => (rankFlatChannel_payoff_constant r k hr n m V).ge)
    (PhysicalFlatConverse.payoff_nonneg r k hr n m)

/-- One prescribed, state-independent CPTP channel attains the sharp
value uniformly over all literal rank-r orthogonal projectors. -/
theorem rankFlatChannel_uniform (m : ℕ → ℕ) (γ : ℝ) (hγ : 1<γ)
    (hratio : Tendsto (fun n => (m n : ℝ)/(n : ℝ)) atTop (𝓝 γ))
    (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ n in atTop, ∀ P : Projector r k,
      |payoff r k hr n (m n) (rankFlatChannel r k hr n (m n)) P -
        γ^(-(((r*k : ℕ) : ℝ)/2))| < ε := by
  have hm := Cloning.WernerAsymptotics.output_tendsto_atTop m hγ hratio
  have hl := eventually_rankFlatChannel_payoff_lower r k hr m hm γ hγ hratio ε hε
  have hu := (minimaxValue_tendsto r k hr m γ hγ hratio).eventually
    (eventually_lt_nhds (lt_add_of_pos_right _ hε))
  filter_upwards [hl,hu] with n hn hupper P
  obtain ⟨U,hU⟩ := orbitProjector_surjective r k P
  have he : payoff r k hr n (m n) (rankFlatChannel r k hr n (m n)) P =
      PhysicalFlatConverse.payoff r k hr n (m n) (rankFlatChannel r k hr n (m n)) U := by
    rw [← hU]
    unfold payoff PhysicalFlatConverse.payoff
    rw [state_orbitProjector]
  have hlo := hn U
  have hhi := (rankFlatChannel_payoff_le_minimax r k hr n (m n) P).trans_lt hupper
  rw [abs_lt]
  constructor <;> linarith

end Cloning.PhysicalFlatGrassmann
