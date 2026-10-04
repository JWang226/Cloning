import Cloning.TensorCloningUniformBlocks
import Cloning.TensorCloningUniformCovariance
import Cloning.TensorCloningUniversalError
import Cloning.PhysicalCloningConverseUnknown

/-! Exact compact-uniform fidelity convergence of the prescribed physical
known-spectrum channel, uniformly over every unknown eigenbasis. -/
noncomputable section
open scoped BigOperators InnerProductSpace ComplexOrder Classical Matrix Topology
open Filter
namespace Cloning.TensorCloning
open Cloning.PCT Cloning.TensorLie Cloning.TensorLAN Cloning.InfiniteTraceClass Cloning.Hybrid
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 200000

theorem known_joint_marginal {d : ℕ} (n m : ℕ) (p : SimpleSpectrum d) (j : SchurCopy m d) :
    (∑ i,jointCopyWeight n m d p.eigenvalue (i,j)) = knownCopyWeight m d p.eigenvalue j := by
  simp only [jointCopyWeight, ← Finset.sum_mul,
    knownCopyWeight_sum n d p.eigenvalue (fun a => (p.positive a).le) p.normalized, one_mul]

theorem known_joint_sum {d : ℕ} (n m : ℕ) (p : SimpleSpectrum d) :
    (∑ j,∑ i,jointCopyWeight n m d p.eigenvalue (i,j))=1 := by
  simp_rw [known_joint_marginal n m p]
  exact knownCopyWeight_sum m d p.eigenvalue (fun a => (p.positive a).le) p.normalized

theorem known_copyAffinity {d : ℕ} (n m : ℕ) (p : SimpleSpectrum d) :
    Cloning.BlockFidelity.classicalAffinity (fun j => ∑ i,jointCopyWeight n m d p.eigenvalue (i,j))
      (knownCopyWeight m d p.eigenvalue) = 1 := by
  simp_rw [known_joint_marginal n m p]
  rw [Cloning.BlockFidelity.classicalAffinity_self _ (knownCopyWeight_nonneg _ _ _),
    knownCopyWeight_sum m d p.eigenvalue (fun a => (p.positive a).le) p.normalized]

theorem knownSpectrumChannel_payoff_abs_error {d : ℕ} (n m : ℕ) (p : SimpleSpectrum (d+1))
    (γ : ℝ) (hγ : 1 < γ) (η : ℝ) (hη : 0 ≤ η)
    (hret : ∀ j : SchurCopy m (d+1), copyTypical m (d+1) p.eigenvalue j →
      ∀ (q : {i : SchurCopy n (d+1) // copyTypical n (d+1) p.eigenvalue i} → ℝ)
        (hq : ∀ i, 0 ≤ q i), (∑ i,q i)=1 →
      |retainedCopyFidelity n m (d+1) p.eigenvalue p.positive j
        (copyTypical n (d+1) p.eigenvalue) q hq - orbitalValue γ p| ≤ η)
    (U : unitary (Matrix (Fin (d+1)) (Fin (d+1)) ℂ)) :
    |spectrumPayoff n m (knownSpectrumChannel n m (d+1) p.eigenvalue
      (fun a => (p.positive a).le) p.normalized) p U-orbitalValue γ p| ≤
      η+2*Real.sqrt (jointBadMass n m (d+1) p.eigenvalue) := by
  rw [knownSpectrumChannel_payoff_unitary]
  let w := fun i j => jointCopyWeight n m (d+1) p.eigenvalue (i,j)
  let keep := fun i j => jointTypical n m (d+1) p.eigenvalue (i,j)
  have hw : ∀ i j, 0 ≤ w i j := fun i j => jointCopyWeight_nonneg _ _ _ _ (i,j)
  have hf := copyBlocks_factorization_bound n m p 1 w hw (known_joint_sum n m p).le keep
    (orbitalValue γ p) η (orbitalValue_pos hγ p).le (orbitalValue_le_one hγ p) hη (by
      intro j hr
      have hj : copyTypical m (d+1) p.eigenvalue j := by
        by_contra hj
        simp only [retainedCopyWeight,PositiveTraceClass.maskedWeight,keep,jointTypical,hj,and_false,
          if_false,Finset.sum_const_zero] at hr
        exact lt_irrefl 0 hr
      rw [retainedCopyWeight_sum] at hr
      simp only [OneMemClass.coe_one]
      rw [normalizedCopyBlock_rootFidelity_one n m (d+1) p.eigenvalue p.positive w hw keep j hr]
      have hk : (fun i => keep i j) = copyTypical n (d+1) p.eigenvalue := by
        funext i
        exact propext (by simp only [keep,jointTypical,hj,and_true])
      have hret' := hret j hj
      rw [← hk] at hret'
      exact hret' _ _ (retainedCopyProbability_sum _ _ _ _ _ _ hr))
  have hp := spectrumPayoff_eq_copyBlocks n m
    (knownSpectrumChannel n m (d+1) p.eigenvalue (fun a => (p.positive a).le) p.normalized) p 1 w hw
    (knownSpectrumChannel_rotated_apply n m (d+1) p.eigenvalue p.positive p.normalized 1)
  rw [← hp] at hf
  have ha : Cloning.BlockFidelity.classicalAffinity (fun j => ∑ i,w i j)
      (knownCopyWeight m (d+1) p.eigenvalue) = 1 := known_copyAffinity n m p
  rw [ha,mul_one] at hf
  have hd : (∑ j,∑ i,if keep i j then 0 else w i j)=jointBadMass n m (d+1) p.eigenvalue := by
    rw [jointBadMass,Fintype.sum_prod_type,Finset.sum_comm]
  simpa only [hd] using hf

/-- The concrete known-spectrum physical channel has its exact orbital
fidelity limit uniformly over every compact set of spectra and all unitaries. -/
theorem eventually_uniform_knownSpectrumChannel_payoff {d : ℕ}
    (K : Set (SimpleSpectrum (d+1))) (hK : IsCompact K)
    (m : ℕ → ℕ) (γ : ℝ) (hγ : 1 < γ)
    (hgain : Tendsto (fun n => (m n : ℝ)/n) atTop (𝓝 γ)) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ p ∈ K, ∀ U : unitary (Matrix (Fin (d+1)) (Fin (d+1)) ℂ),
      |spectrumPayoff n (m n) (knownSpectrumChannel n (m n) (d+1) p.eigenvalue
        (fun a => (p.positive a).le) p.normalized) p U-orbitalValue γ p| < ε := by
  have hm := PhysicalCloningConverse.output_size_tendsto m γ (by linarith) hgain
  have ht : Tendsto (fun n => Real.sqrt (universalTailEnvelope d n + universalTailEnvelope d (m n)))
      atTop (𝓝 0) := by
    simpa only [zero_add,Real.sqrt_zero] using
      ((universalTailEnvelope_tendsto_zero d).add ((universalTailEnvelope_tendsto_zero d).comp hm)).sqrt
  filter_upwards [eventually_uniform_known_retainedCopyFidelity K hK m hm γ hγ hgain (ε/2) (by positivity),
    ht.eventually (eventually_lt_nhds (show (0 : ℝ) < ε/4 by positivity)),
    eventually_ge_atTop 1,hm.eventually (eventually_ge_atTop 1)] with n hr ht hn hm1 p hp U
  have hf := knownSpectrumChannel_payoff_abs_error n (m n) p γ hγ (ε/2) (by positivity)
    (fun j hj q hq hs => (hr p hp j hj q hq hs).le) U
  have hj := jointBadMass_le n (m n) (d+1) p.eigenvalue (fun a => (p.positive a).le) p.normalized
  have htail := hj.trans (add_le_add (copyBadMass_le_universalTailEnvelope n hn p)
    (copyBadMass_le_universalTailEnvelope (m n) hm1 p))
  have hb := Real.sqrt_le_sqrt htail
  linarith

end Cloning.TensorCloning
