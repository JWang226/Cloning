import Cloning.PCTRankAdaptedLimit

/-! Conversion of the internal eventual count-measurement bound into the
literal ambient PCT limsup bound, including its strict scalar comparison. -/
noncomputable section
open scoped Topology Matrix ComplexOrder
open Filter
namespace Cloning.PCTRankAdapted
open Cloning.PCT Cloning.PCTPhysicalState Cloning.InfiniteTraceClass Cloning.Hybrid
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000
variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
  [Nonempty A] [Nonempty B]

/-- An eventual upper estimate on the actual internal fidelity is enough
for the support-compression theorem. -/
theorem internal_limsup_of_eventually_upper {small : ℕ}
    (hA : Fintype.card (A × A) = small+1)
    (ρ : Cloning.MatrixFidelity.State A) (t : ℕ → ℕ) (a : ℝ)
    (h : ∀ ε > 0, ∀ᶠ n in atTop,
      (outputState hA ρ n (t n)).rootFidelity (tensorState ρ (n+t n)) ≤ a+ε) :
    limsup (fun n => (outputState hA ρ n (t n)).rootFidelity
      (tensorState ρ (n+t n))) atTop ≤ a := by
  apply le_of_forall_pos_le_add
  intro ε hε
  exact limsup_le_of_le
    (isCoboundedUnder_le_of_le atTop (fun n => PositiveTraceClass.rootFidelity_nonneg
      (outputState hA ρ n (t n)) (tensorState ρ (n+t n)))) (h ε hε)

theorem embeddedPurificationOutput_limsup_of_eventually_upper {small large : ℕ}
    (hA : Fintype.card (A × A) = small+1) (hB : Fintype.card (B × A) = large+1)
    (J : Matrix B A ℂ) (hJ : Jᴴ * J = 1)
    (ρ : Cloning.MatrixFidelity.State A) (t : ℕ → ℕ) (γ : ℝ) (hγ : 1 < γ)
    (hr : Tendsto (fun n => ((n+t n : ℕ) : ℝ)/n) atTop (𝓝 γ))
    (a : ℝ) (h : ∀ ε > 0, ∀ᶠ n in atTop,
      (outputState hA ρ n (t n)).rootFidelity (tensorState ρ (n+t n)) ≤ a+ε) :
    limsup (fun n => (embeddedPurificationOutput hB J hJ ρ n (t n)).rootFidelity
      (tensorState (embeddedState J hJ ρ) (n+t n))) atTop ≤
      γ ^ (-((large : ℝ)-(small : ℝ))/2) * a :=
  embeddedPurificationOutput_limsup_bound hA hB J hJ ρ t γ hγ hr a
    (internal_limsup_of_eventually_upper hA ρ t a h)

/-- The rank-adapted PCT scalar bound is strictly below the sharp
Grassmann root-fidelity value as soon as the supported rank exceeds one. -/
theorem rankAdaptedBound_lt_optimal {γ : ℝ} (hγ : 1 < γ) {r : ℕ}
    (hr : 1 < r) (k : ℕ) :
    γ ^ (-(((r*k : ℕ) : ℝ)/2)) *
      (Real.sqrt (2*γ-1)/γ) ^ (((r : ℝ)-1)/2) <
      γ ^ (-(((r*k : ℕ) : ℝ)/2)) := by
  rw [← classicalValue_inflated]
  exact mul_lt_of_lt_one_right (Real.rpow_pos_of_pos (by linarith) _)
    (classicalValue_inflated_lt_one hγ hr)

end Cloning.PCTRankAdapted
