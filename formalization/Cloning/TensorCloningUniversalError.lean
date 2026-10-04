import Cloning.TensorCloningUniversalProbability

/-! A quantitative global error bound for the literal universal cloner. -/
noncomputable section
open scoped BigOperators Classical Topology Matrix
namespace Cloning.TensorCloning
open Cloning.TensorLie Cloning.TensorLAN Cloning.YoungGeneral Cloning.YoungCompatibility
open Cloning.YoungHyperplane Filter
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

def universalAffinity (n m d : ℕ) (p : SimpleSpectrum (d+1)) : ℝ :=
  CountableScheffe.affinity
    (probability (tensorYoungFallbackOutput d n m ((m : ℝ)/(n : ℝ)) p.eigenvalue
      (fun a ↦ (p.positive a).le) p.normalized))
    (probability (tensorYoungIntegerPMF d m p.eigenvalue (fun a ↦ (p.positive a).le) p.normalized))

theorem universalAffinity_nonneg (n m d : ℕ) (p : SimpleSpectrum (d+1)) :
    0 ≤ universalAffinity n m d p :=
  tsum_nonneg (fun _ ↦ mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))

theorem universalAffinity_le_one (n m d : ℕ) (p : SimpleSpectrum (d+1)) :
    universalAffinity n m d p ≤ 1 := by
  have h := CountableScheffe.affinity_le_sqrt_mass
    (probability (tensorYoungFallbackOutput d n m ((m : ℝ)/(n : ℝ)) p.eigenvalue
      (fun a ↦ (p.positive a).le) p.normalized))
    (probability (tensorYoungIntegerPMF d m p.eigenvalue (fun a ↦ (p.positive a).le) p.normalized))
    (fun _ ↦ ENNReal.toReal_nonneg) (fun _ ↦ ENNReal.toReal_nonneg)
    (hasSum_probability _).summable (hasSum_probability _).summable
  simpa only [tsum_probability, Real.sqrt_one, one_mul] using h

theorem universalChannel_payoff_lower_error {d : ℕ} (n m : ℕ)
    (p : SimpleSpectrum (d+1)) (U : unitary (Matrix (Fin (d+1)) (Fin (d+1)) ℂ))
    (γ : ℝ) (hγ : 1 < γ) (η : ℝ) (hη : 0 ≤ η)
    (hsector : ∀ i j, universalKeep n m d p.eigenvalue i j →
      orbitalValue γ p - η ≤ transitionFidelity n m (d+1) p.eigenvalue p.positive U i j) :
    universalValue γ p - η - |universalAffinity n m d p - classicalValue γ (d+1)| -
      Real.sqrt (copyBadMass n (d+1) p.eigenvalue) ≤ spectrumPayoff n m (universalChannel n m d) p U := by
  let c := max 0 (orbitalValue γ p - η)
  have hc0 : 0 ≤ c := le_max_left _ _
  have hc1 : c ≤ 1 := max_le (by norm_num) (by linarith [orbitalValue_le_one hγ p])
  have hg : ∀ i j, universalKeep n m d p.eigenvalue i j →
      c ≤ transitionFidelity n m (d+1) p.eigenvalue p.positive U i j := by
    intro i j hij
    exact max_le (transitionFidelity_nonneg _ _ _ _ _ _ _ _) (hsector i j hij)
  have h := universalChannel_payoff_lower n m p U (universalKeep n m d p.eigenvalue) c hc0 hc1 hg
  rw [universal_discarded_mass] at h
  change c * universalAffinity n m d p - _ ≤ _ at h
  have ha0 := universalAffinity_nonneg n m d p
  have ha1 := universalAffinity_le_one n m d p
  have hca := mul_le_mul_of_nonneg_right (le_max_right 0 (orbitalValue γ p-η)) ha0
  have heta := mul_le_mul_of_nonneg_left ha1 hη
  have hcst := mul_le_mul_of_nonneg_left
    (neg_le_abs (universalAffinity n m d p - classicalValue γ (d+1))) (orbitalValue_pos hγ p).le
  have habs := mul_le_mul_of_nonneg_right (orbitalValue_le_one hγ p)
    (abs_nonneg (universalAffinity n m d p - classicalValue γ (d+1)))
  unfold universalValue
  change max 0 (orbitalValue γ p - η) * _ - _ ≤ _ at h
  nlinarith

/-- A uniform physical Young-tail envelope, independent of the spectrum. -/
def universalTailEnvelope (d n : ℕ) : ℝ :=
  ((((d+1 : ℕ) : ℝ)+1)^Fintype.card (PositiveRoot (d+1))) *
    (((n : ℝ)+1)^Fintype.card (PositiveRoot (d+1)) * concentrationEnvelope (d+1) n)

theorem copyBadMass_le_universalTailEnvelope {d : ℕ} (n : ℕ) (hn : 1 ≤ n)
    (p : SimpleSpectrum (d+1)) : copyBadMass n (d+1) p.eigenvalue ≤ universalTailEnvelope d n := by
  rw [copyBadMass_eq_tail n (d+1) p.eigenvalue (fun a ↦ (p.positive a).le) p.normalized]
  exact tensorYoungPMF_tail_shrinking_le n hn p.eigenvalue (fun a ↦ (p.positive a).le)
    p.normalized p.strictAnti.antitone

theorem universalTailEnvelope_tendsto_zero (d : ℕ) :
    Tendsto (universalTailEnvelope d) atTop (𝓝 0) := by
  simpa only [universalTailEnvelope, mul_zero] using
    (polynomial_concentrationEnvelope_tendsto_zero (d+1) (Fintype.card (PositiveRoot (d+1)))).const_mul
      ((((d+1 : ℕ) : ℝ)+1)^Fintype.card (PositiveRoot (d+1)))

end Cloning.TensorCloning
