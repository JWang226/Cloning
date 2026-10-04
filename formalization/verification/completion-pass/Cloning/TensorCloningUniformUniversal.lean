import Cloning.TensorCloningUniformBlocks
import Cloning.TensorCloningUniformCovariance
import Cloning.TensorCloningUniversalClassical
import Cloning.PhysicalCloningConverseUnknown

/-! Exact compact-uniform fidelity convergence of the single prescribed
spectrum-independent physical cloning channel. -/
noncomputable section
open scoped BigOperators InnerProductSpace ComplexOrder Classical Matrix Topology
open Filter
namespace Cloning.TensorCloning
open Cloning.PCT Cloning.TensorLie Cloning.TensorLAN Cloning.InfiniteTraceClass Cloning.Hybrid
open Cloning.InfiniteFidelityHilbertSum Cloning.YoungCompatibility Cloning.YoungHyperplane
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 200000

theorem universal_joint_sum (n m d : ℕ) (p : SimpleSpectrum (d+1)) :
    (∑ j,∑ i,universalJointWeight n m d p.eigenvalue i j)=1 := by
  simp_rw [universalJointWeight_marginal n m d p.eigenvalue (fun a => (p.positive a).le) p.normalized]
  simpa only [tsum_fintype] using tsum_probability
    (universalOutputCopyPMF n m d p.eigenvalue (fun a => (p.positive a).le) p.normalized)

theorem universal_copyAffinity (n m d : ℕ) (p : SimpleSpectrum (d+1)) :
    Cloning.BlockFidelity.classicalAffinity (fun j => ∑ i,universalJointWeight n m d p.eigenvalue i j)
      (knownCopyWeight m (d+1) p.eigenvalue) = universalAffinity n m d p := by
  rw [universalAffinity, ← universalOutputCopyPMF_affinity n m d p.eigenvalue
    (fun a => (p.positive a).le) p.normalized]
  simp only [Cloning.BlockFidelity.classicalAffinity, CountableScheffe.affinity, tsum_fintype,
    universalJointWeight_marginal n m d p.eigenvalue (fun a => (p.positive a).le) p.normalized,
    probability, physicalCopyPMF_toReal, knownCopyWeight]

theorem universalChannel_payoff_abs_error {d : ℕ} (n m : ℕ) (p : SimpleSpectrum (d+1))
    (γ : ℝ) (hγ : 1 < γ) (η : ℝ) (hη : 0 ≤ η)
    (hret : ∀ j : SchurCopy m (d+1),
      ∀ (q : {i : SchurCopy n (d+1) // universalKeep n m d p.eigenvalue i j} → ℝ)
        (hq : ∀ i, 0 ≤ q i), (∑ i,q i)=1 →
      |retainedCopyFidelity n m (d+1) p.eigenvalue p.positive j
        (fun i => universalKeep n m d p.eigenvalue i j) q hq - orbitalValue γ p| ≤ η)
    (U : unitary (Matrix (Fin (d+1)) (Fin (d+1)) ℂ)) :
    |spectrumPayoff n m (universalChannel n m d) p U-universalValue γ p| ≤
      η+2*Real.sqrt (copyBadMass n (d+1) p.eigenvalue) +
        |universalAffinity n m d p-classicalValue γ (d+1)| := by
  rw [universalChannel_payoff_unitary]
  have hf := copyBlocks_factorization_bound n m p 1 (universalJointWeight n m d p.eigenvalue)
    (universalJointWeight_nonneg n m d p.eigenvalue) (universal_joint_sum n m d p).le
    (universalKeep n m d p.eigenvalue) (orbitalValue γ p) η (orbitalValue_pos hγ p).le
    (orbitalValue_le_one hγ p) hη (by
      intro j hr
      rw [retainedCopyWeight_sum] at hr
      simp only [OneMemClass.coe_one]
      rw [normalizedCopyBlock_rootFidelity_one n m (d+1) p.eigenvalue p.positive
        (universalJointWeight n m d p.eigenvalue) (universalJointWeight_nonneg n m d p.eigenvalue)
        (universalKeep n m d p.eigenvalue) j hr]
      exact hret j _ _ (retainedCopyProbability_sum _ _ _ _ _ _ hr))
  have hp := spectrumPayoff_eq_copyBlocks n m (universalChannel n m d) p 1
    (universalJointWeight n m d p.eigenvalue) (universalJointWeight_nonneg n m d p.eigenvalue)
    (universalChannel_rotated_apply n m d p.eigenvalue p.positive 1)
  rw [← hp,universal_copyAffinity] at hf
  have hd : (∑ j,∑ i,if universalKeep n m d p.eigenvalue i j then 0 else universalJointWeight n m d p.eigenvalue i j) =
      copyBadMass n (d+1) p.eigenvalue := by
    have hh := universal_discarded_mass n m d p.eigenvalue
    rw [Fintype.sum_prod_type] at hh
    rw [Finset.sum_comm]
    exact hh
  rw [hd] at hf
  have he := abs_sub_le (spectrumPayoff n m (universalChannel n m d) p 1)
    (orbitalValue γ p*universalAffinity n m d p) (universalValue γ p)
  have hb : |orbitalValue γ p*universalAffinity n m d p-universalValue γ p| ≤
      |universalAffinity n m d p-classicalValue γ (d+1)| := by
    rw [universalValue,mul_comm (classicalValue γ (d+1)),← mul_sub,abs_mul,
      abs_of_nonneg (orbitalValue_pos hγ p).le]
    exact mul_le_of_le_one_left (abs_nonneg _) (orbitalValue_le_one hγ p)
  linarith

/-- One actual exactly covariant channel, independent of the spectrum,
converges in fidelity uniformly on every compact spectral family and every
unknown unitary eigenbasis. -/
theorem eventually_uniform_universalChannel_payoff {d : ℕ} (hd : 1 ≤ d)
    (K : Set (SimpleSpectrum (d+1))) (hK : IsCompact K)
    (m : ℕ → ℕ) (γ : ℝ) (hγ : 1 < γ)
    (hgain : Tendsto (fun n => (m n : ℝ)/n) atTop (𝓝 γ)) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ p ∈ K, ∀ U : unitary (Matrix (Fin (d+1)) (Fin (d+1)) ℂ),
      |spectrumPayoff n (m n) (universalChannel n (m n) d) p U-universalValue γ p| < ε := by
  have hm := PhysicalCloningConverse.output_size_tendsto m γ (by linarith) hgain
  have ht : Tendsto (fun n => Real.sqrt (universalTailEnvelope d n)) atTop (𝓝 0) := by
    simpa only [Real.sqrt_zero] using (universalTailEnvelope_tendsto_zero d).sqrt
  filter_upwards [eventually_uniform_universal_retainedCopyFidelity hd K hK m γ hγ hgain (ε/3) (by positivity),
    eventually_uniform_universalAffinity hd K hK m hm γ hγ hgain (ε/3) (by positivity),
    ht.eventually (eventually_lt_nhds (show (0 : ℝ) < ε/6 by positivity)),eventually_ge_atTop 1]
    with n hr ha ht hn p hp U
  have hf := universalChannel_payoff_abs_error n (m n) p γ hγ (ε/3) (by positivity)
    (fun j q hq hs => (hr p hp j q hq hs).le) U
  have hb := Real.sqrt_le_sqrt (copyBadMass_le_universalTailEnvelope n hn p)
  have hclass := ha p hp
  linarith

end Cloning.TensorCloning
