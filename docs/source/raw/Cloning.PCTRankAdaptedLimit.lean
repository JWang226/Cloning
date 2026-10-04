import Cloning.PCTRankAdaptedProduct
import Cloning.PCTRankAdaptedFactor
import Mathlib.Topology.Algebra.Order.LiminfLimsup

/-! The exact physical support factor transfers the internal PCT bound to
the ambient embedded-state fidelity without assuming convergence of fidelity. -/
noncomputable section
open scoped BigOperators Topology Matrix MatrixOrder ComplexOrder
open Filter
namespace Cloning.PCTRankAdapted
open Cloning.PCT Cloning.PCTPhysicalState Cloning.InfiniteTraceClass Cloning.Hybrid
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000
set_option linter.unusedSectionVars false
variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
  [Nonempty A] [Nonempty B]

theorem internal_fidelity_le_one {small : ℕ} (hA : Fintype.card (A × A) = small+1)
    (ρ : Cloning.MatrixFidelity.State A) (n t : ℕ) :
    (outputState hA ρ n t).rootFidelity (tensorState ρ (n+t)) ≤ 1 := by
  have h := PositiveTraceClass.rootFidelity_le_sqrt (outputState hA ρ n t) (tensorState ρ (n+t))
  simpa only [norm_outputState, norm_tensorState, Real.sqrt_one, one_mul] using h

/-- A limsup bound on the actual internal state suffices; the ambient
fidelity need not have a limit. -/
theorem embeddedPurificationOutput_limsup_bound {small large : ℕ}
    (hA : Fintype.card (A × A) = small+1) (hB : Fintype.card (B × A) = large+1)
    (J : Matrix B A ℂ) (hJ : Jᴴ * J = 1)
    (ρ : Cloning.MatrixFidelity.State A) (t : ℕ → ℕ) (γ : ℝ) (hγ : 1 < γ)
    (hr : Tendsto (fun n => ((n+t n : ℕ) : ℝ)/n) atTop (𝓝 γ))
    (a : ℝ) (hint : limsup (fun n => (outputState hA ρ n (t n)).rootFidelity
      (tensorState ρ (n+t n))) atTop ≤ a) :
    limsup (fun n => (embeddedPurificationOutput hB J hJ ρ n (t n)).rootFidelity
      (tensorState (embeddedState J hJ ρ) (n+t n))) atTop ≤
      γ ^ (-((large : ℝ)-(small : ℝ))/2) * a := by
  let u : ℕ → ℝ := fun n => Real.sqrt (supportFactor n (n+t n) small large)
  let v : ℕ → ℝ := fun n => (outputState hA ρ n (t n)).rootFidelity (tensorState ρ (n+t n))
  have hu : Tendsto u atTop (𝓝 (γ ^ (-((large : ℝ)-(small : ℝ))/2))) :=
    sqrt_supportFactor_tendsto (fun n => n+t n) hγ hr small large
  have hbu : atTop.IsBoundedUnder (· ≤ ·) u := isBoundedUnder_of_eventually_le
    ((hu.eventually (gt_mem_nhds (lt_add_one _))).mono (fun _ h => h.le))
  have hbv : atTop.IsBoundedUnder (· ≤ ·) v := isBoundedUnder_of_eventually_le
    (Eventually.of_forall (fun n => internal_fidelity_le_one hA ρ n (t n)))
  have hprod := limsup_mul_le
    (Frequently.of_forall (fun n => Real.sqrt_nonneg (supportFactor n (n+t n) small large))) hbu
    (Eventually.of_forall (fun n => PositiveTraceClass.rootFidelity_nonneg
      (outputState hA ρ n (t n)) (tensorState ρ (n+t n)))) hbv
  rw [hu.limsup_eq] at hprod
  have hf : (fun n => (embeddedPurificationOutput hB J hJ ρ n (t n)).rootFidelity
      (tensorState (embeddedState J hJ ρ) (n+t n))) = u*v := by
    funext n
    exact embeddedPurificationOutput_fidelity_factorization hA hB J hJ ρ n (t n)
  rw [hf]
  exact hprod.trans (mul_le_mul_of_nonneg_left hint (Real.rpow_nonneg (by linarith) _))

end Cloning.PCTRankAdapted
