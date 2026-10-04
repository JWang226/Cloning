import Cloning.TensorCloningAchievabilityTypical
import Cloning.TensorCloningAchievabilityCompatibility

/-! Sequential-to-uniform and probability-removal steps for the actual
known-spectrum cloning protocol. -/
noncomputable section
open scoped BigOperators Classical Topology
open Filter
namespace Cloning.TensorCloning
open Cloning.TensorLie Cloning.TensorLAN
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- Uniform control over a varying finite family follows by selecting a
violating subsequence; no globally admissible reference family is needed. -/
theorem eventually_uniform_of_subsequences {A : ℕ → Type*}
    (S P : ∀ N, A N → Prop)
    (hseq : ∀ (φ : ℕ → ℕ), Tendsto φ atTop atTop →
      ∀ (x : ∀ k, A (φ k)), (∀ᶠ k in atTop, S (φ k) (x k)) →
        ∀ᶠ k in atTop, P (φ k) (x k)) :
    ∀ᶠ N in atTop, ∀ x, S N x → P N x := by
  by_contra hbad
  rw [eventually_atTop] at hbad
  push_neg at hbad
  choose φ hφ x hx hfail using hbad
  have hφlim : Tendsto φ atTop atTop := tendsto_atTop_mono hφ tendsto_id
  obtain ⟨k,hk⟩ := (hseq φ hφlim x (Eventually.of_forall hx)).exists
  exact hfail k hk

/-- Once the actual retained sector fidelities are uniformly controlled,
the proved physical Young tails give an eventual bound uniform on the entire
unitary orbit for the concrete channel. -/
theorem eventually_knownSpectrumChannel_payoff_lower_of_typical {d : ℕ}
    (n m : ℕ → ℕ) (hn : Tendsto n atTop atTop) (hm : Tendsto m atTop atTop)
    (p : SimpleSpectrum (d+1)) (c : ℝ) (hc : c ≤ 1)
    (hsector : ∀ η > 0, ∀ᶠ k in atTop,
      ∀ ij : SchurCopy (n k) (d+1) × SchurCopy (m k) (d+1),
        jointTypical (n k) (m k) (d+1) p.eigenvalue ij →
      ∀ U : unitary (Matrix (Fin (d+1)) (Fin (d+1)) ℂ),
        c-η ≤ transitionFidelity (n k) (m k) (d+1) p.eigenvalue p.positive U ij.1 ij.2)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ k in atTop, ∀ U : unitary (Matrix (Fin (d+1)) (Fin (d+1)) ℂ),
      c-ε < spectrumPayoff (n k) (m k)
        (knownSpectrumChannel (n k) (m k) (d+1) p.eigenvalue
          (fun a => (p.positive a).le) p.normalized) p U := by
  have hbad := (copyBadMass_fixed_tendsto_zero p.eigenvalue (fun a => (p.positive a).le)
    p.normalized p.strictAnti.antitone n hn).add
    (copyBadMass_fixed_tendsto_zero p.eigenvalue (fun a => (p.positive a).le)
      p.normalized p.strictAnti.antitone m hm)
  simp only [zero_add] at hbad
  filter_upwards [hsector (ε/3) (by positivity), hbad.eventually (eventually_lt_nhds
    (show 0 < ε/3 by positivity))] with k hk hbk U
  have hh := knownSpectrumChannel_payoff_lower_typical (n k) (m k) p U c (ε/3) hc
    (by positivity) (fun ij hij => hk ij hij U)
  linarith

end Cloning.TensorCloning
