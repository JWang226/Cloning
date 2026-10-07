import Cloning.TensorCloningPrescribed
import Cloning.TensorCloningUniformKnown
import Cloning.TensorCloningUniformUniversal
import Cloning.PhysicalFlatGrassmannUniform

/-! Exact asymptotic limits for the finite-convention prescribed channels. -/
noncomputable section
open scoped BigOperators Topology Matrix Classical
open Filter
namespace Cloning.TensorCloning
open Cloning.PCT Cloning.TensorLie Cloning.InfiniteTraceClass
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

theorem eventually_output_gt_input (m : ℕ → ℕ) (γ : ℝ) (hγ : 1<γ)
    (hgain : Tendsto (fun n => (m n : ℝ)/n) atTop (𝓝 γ)) : ∀ᶠ n in atTop,n<m n := by
  filter_upwards [hgain.eventually (eventually_gt_nhds hγ),eventually_gt_atTop (0 : ℕ)] with n hn hn0
  have he : (n : ℝ)<m n := by
    have hh := (lt_div_iff₀ (show 0<(n : ℝ) by exact_mod_cast hn0)).mp hn
    simpa only [one_mul] using hh
  exact_mod_cast he

theorem eventually_prescribedChannel_eq (d : ℕ) (m : ℕ → ℕ)
    (Φ : (n : ℕ) → QuantumChannel (TensorRegister n (Fin d)) (TensorRegister (m n) (Fin d)))
    (γ : ℝ) (hγ : 1<γ) (hgain : Tendsto (fun n => (m n : ℝ)/n) atTop (𝓝 γ)) :
    ∀ᶠ n in atTop,prescribedChannel n (m n) d (Φ n)=Φ n :=
  (eventually_output_gt_input m γ hγ hgain).mono (fun n hn => prescribedChannel_of_lt n (m n) d (Φ n) hn)

theorem eventually_uniform_prescribedKnownSpectrumChannel_payoff {d : ℕ}
    (K : Set (SimpleSpectrum (d+1))) (hK : IsCompact K)
    (m : ℕ → ℕ) (γ : ℝ) (hγ : 1<γ)
    (hgain : Tendsto (fun n => (m n : ℝ)/n) atTop (𝓝 γ)) (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ n in atTop,∀ p∈K,∀ U : unitary (Matrix (Fin (d+1)) (Fin (d+1)) ℂ),
      |spectrumPayoff n (m n) (prescribedKnownSpectrumChannel n (m n) (d+1) p.eigenvalue
        (fun a => (p.positive a).le) p.normalized) p U-orbitalValue γ p|<ε := by
  filter_upwards [eventually_output_gt_input m γ hγ hgain,
    eventually_uniform_knownSpectrumChannel_payoff K hK m γ hγ hgain ε hε] with n hn hh p hp U
  simpa only [prescribedKnownSpectrumChannel,prescribedChannel_of_lt n (m n) (d+1) _ hn] using hh p hp U

theorem eventually_uniform_prescribedUniversalChannel_payoff {d : ℕ} (hd : 1≤d)
    (K : Set (SimpleSpectrum (d+1))) (hK : IsCompact K)
    (m : ℕ → ℕ) (γ : ℝ) (hγ : 1<γ)
    (hgain : Tendsto (fun n => (m n : ℝ)/n) atTop (𝓝 γ)) (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ n in atTop,∀ p∈K,∀ U : unitary (Matrix (Fin (d+1)) (Fin (d+1)) ℂ),
      |spectrumPayoff n (m n) (prescribedUniversalChannel n (m n) d) p U-universalValue γ p|<ε := by
  filter_upwards [eventually_output_gt_input m γ hγ hgain,
    eventually_uniform_universalChannel_payoff hd K hK m γ hγ hgain ε hε] with n hn hh p hp U
  simpa only [prescribedUniversalChannel,prescribedChannel_of_lt n (m n) (d+1) _ hn] using hh p hp U

theorem prescribedRankFlatChannel_covariant (r k : ℕ) (hr : 0<r) (n m : ℕ)
    (U : Matrix (Fin (r+k)) (Fin (r+k)) ℂ) (hU : Uᴴ*U=1)
    (X : TraceClass (TensorRegister n (Fin (r+k)))) :
    (prescribedRankFlatChannel r k hr n m).toLinearMap (conjugationLinearMap (tensorOperator n U) X)=
      conjugationLinearMap (tensorOperator m U) ((prescribedRankFlatChannel r k hr n m).toLinearMap X) :=
  prescribedChannel_covariant n m (r+k) _ U hU (rankFlatChannel_covariant r k hr n m U hU) X

theorem prescribedRankFlatChannel_uniform (r k : ℕ) (hr : 0<r)
    (m : ℕ → ℕ) (γ : ℝ) (hγ : 1<γ)
    (hgain : Tendsto (fun n => (m n : ℝ)/n) atTop (𝓝 γ)) (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ n in atTop,∀ P : Cloning.PhysicalFlatGrassmann.Projector r k,
      |Cloning.PhysicalFlatGrassmann.payoff r k hr n (m n) (prescribedRankFlatChannel r k hr n (m n)) P-
        γ^(-(((r*k : ℕ) : ℝ)/2))|<ε := by
  filter_upwards [eventually_output_gt_input m γ hγ hgain,
    Cloning.PhysicalFlatGrassmann.rankFlatChannel_uniform r k hr m γ hγ hgain ε hε] with n hn hh P
  simpa only [prescribedRankFlatChannel,prescribedChannel_of_lt n (m n) (r+k) _ hn] using hh P

end Cloning.TensorCloning
