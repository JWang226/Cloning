import Cloning.TensorCloningSectorCovariance
import Cloning.TensorCartanStateFidelity
import Cloning.TensorCloningAchievabilityCompatibility
import Cloning.TensorCloningAchievabilityValue

/-! The actual conditional sector payoff converges to the orbital value on
independent typical source and target labels. -/
noncomputable section
open scoped BigOperators InnerProductSpace Classical Topology
open Filter
namespace Cloning.TensorCloning
open Cloning.PCT Cloning.TensorLie Cloning.TensorLAN Cloning.InfiniteTraceClass Cloning.Hybrid
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
variable {d : ℕ}
local instance (n d : ℕ) : FiniteDimensional ℂ (TensorRegister n (Fin d)) :=
  (registerBasis (Fin n → Fin d)).toOrthonormalBasis.toBasis.finiteDimensional_of_finite

def partitionTransitionFidelity (μ ν : Fin d → ℕ) (hμ : Antitone μ) (hν : Antitone ν)
    (p : Fin d → ℝ) (hp : ∀ a, 0 < p a) : ℝ :=
  ((partitionGibbsPositive μ hμ p hp).map
    (partitionTransitionChannel μ ν hμ hν).toPositiveTracePreservingMap).rootFidelity
    (partitionGibbsPositive ν hν p hp)

theorem copySectorState_one_eq {n : ℕ} (H : PhysicalHighestTensor n d)
    (p : Fin d → ℝ) (hp : ∀ a, 0 < p a) :
    copySectorState H 1 p hp = partitionGibbsPositive H.weight H.weight_antitone p hp :=
  Subtype.ext (canonicalRotatedGibbs_one H p)

theorem transitionFidelity_one_eq (n m : ℕ) (p : Fin d → ℝ) (hp : ∀ a, 0 < p a)
    (i : SchurCopy n d) (j : SchurCopy m d) :
    transitionFidelity n m d p hp 1 i j =
      partitionTransitionFidelity ((recursivePhysicalDecomposition n d).get i).weight
        ((recursivePhysicalDecomposition m d).get j).weight
        ((recursivePhysicalDecomposition n d).get i).weight_antitone
        ((recursivePhysicalDecomposition m d).get j).weight_antitone p hp := by
  dsimp only [transitionFidelity]
  rw [copySectorState_one_eq, copySectorState_one_eq]
  rfl

theorem partitionTransitionFidelity_add (μ τ : Fin d → ℕ)
    (hμ : Antitone μ) (hτ : Antitone τ) (p : Fin d → ℝ) (hp : ∀ a, 0 < p a) :
    partitionTransitionFidelity μ (fun a => μ a+τ a) hμ (sumPartition_antitone μ τ hμ hτ) p hp =
      (cartanGibbsPositive μ τ hμ hτ p hp).rootFidelity
        (partitionGibbsPositive (fun a => μ a+τ a) (sumPartition_antitone μ τ hμ hτ) p hp) := by
  unfold partitionTransitionFidelity
  rw [partitionTransitionChannel_add]
  rfl

/-- The difference partition may fail at finitely many initial indices.
Repairing those indices proves the same actual real-valued payoff limit. -/
theorem partitionTransitionFidelity_tendsto_moving
    (μ ν : ℕ → Fin d → ℕ) (hμ : ∀ k, Antitone (μ k)) (hν : ∀ k, Antitone (ν k))
    (δμ δτ : ℕ → ℝ) (hδμ : Tendsto δμ atTop atTop) (hδτ : Tendsto δτ atTop atTop)
    (hc : ∀ᶠ k in atTop, PartitionCompatible (μ k) (ν k))
    (hgμ : ∀ᶠ k in atTop, ∀ a : PositiveRoot d, δμ k ≤ rootGap (μ k) a)
    (hgτ : ∀ᶠ k in atTop, ∀ a : PositiveRoot d, δτ k ≤ rootGap (fun i => ν k i-μ k i) a)
    (pN : ℕ → Fin d → ℝ) (hpN : ∀ k a, 0 < pN k a)
    (p : SimpleSpectrum d) (hlim : ∀ a, Tendsto (fun k => pN k a) atTop (𝓝 (p.eigenvalue a)))
    (γ : ℝ) (hγ : 1 < γ)
    (ht : ∀ a : PositiveRoot d, Tendsto (fun k => rootFraction (μ k) (fun i => ν k i-μ k i) a)
      atTop (𝓝 γ⁻¹)) :
    Tendsto (fun k => partitionTransitionFidelity (μ k) (ν k) (hμ k) (hν k) (pN k) (hpN k))
      atTop (𝓝 (orbitalValue γ p)) := by
  let τ : ℕ → Fin d → ℕ := fun k => if Antitone (fun a => ν k a-μ k a) then
    (fun a => ν k a-μ k a) else fun _ => 0
  have hτ (k : ℕ) : Antitone (τ k) := by
    dsimp only [τ]
    split_ifs with h
    · exact h
    · intro a b _; rfl
  have he : ∀ᶠ k in atTop, τ k = (fun a => ν k a-μ k a) :=
    hc.mono (fun k hk => by simp only [τ, if_pos hk.2])
  have hτgap : ∀ᶠ k in atTop, ∀ a : PositiveRoot d, δτ k ≤ rootGap (τ k) a := by
    filter_upwards [he,hgτ] with k hk hg
    simpa only [hk] using hg
  have hτfraction (a : PositiveRoot d) : Tendsto (fun k => rootFraction (μ k) (τ k) a) atTop (𝓝 γ⁻¹) :=
    (ht a).congr' (he.mono (fun k hk => by
      change rootFraction (μ k) (fun i => ν k i-μ k i) a = rootFraction (μ k) (τ k) a
      rw [hk]))
  have hf := cartanGibbsPositive_rootFidelity_tendsto μ τ hμ hτ δμ δτ hδμ hδτ hgμ hτgap
    (fun _ => γ⁻¹) (fun _ => inv_pos.mpr (by linarith))
    (fun _ => (inv_le_one₀ (by linarith : 0 < γ)).mpr hγ.le) hτfraction
    pN hpN p.eigenvalue p.positive p.strictAnti hlim
  rw [cartanThermalProduct_eq_orbitalValue p γ hγ] at hf
  apply hf.congr'
  filter_upwards [he,hc] with k hk hck
  have hs : (fun a => μ k a+τ k a) = ν k := by
    funext a
    rw [hk]
    exact Nat.add_sub_of_le (hck.1 a)
  have hh := partitionTransitionFidelity_add (μ k) (τ k) (hμ k) (hτ k) (pN k) (hpN k)
  simpa only [hs] using hh.symm

theorem partitionTransitionFidelity_tendsto
    (μ ν : ℕ → Fin d → ℕ) (hμ : ∀ k, Antitone (μ k)) (hν : ∀ k, Antitone (ν k))
    (δμ δτ : ℕ → ℝ) (hδμ : Tendsto δμ atTop atTop) (hδτ : Tendsto δτ atTop atTop)
    (hc : ∀ᶠ k in atTop, PartitionCompatible (μ k) (ν k))
    (hgμ : ∀ᶠ k in atTop, ∀ a : PositiveRoot d, δμ k ≤ rootGap (μ k) a)
    (hgτ : ∀ᶠ k in atTop, ∀ a : PositiveRoot d, δτ k ≤ rootGap (fun i => ν k i-μ k i) a)
    (p : SimpleSpectrum d) (γ : ℝ) (hγ : 1 < γ)
    (ht : ∀ a : PositiveRoot d, Tendsto (fun k => rootFraction (μ k) (fun i => ν k i-μ k i) a)
      atTop (𝓝 γ⁻¹)) :
    Tendsto (fun k => partitionTransitionFidelity (μ k) (ν k) (hμ k) (hν k) p.eigenvalue p.positive)
      atTop (𝓝 (orbitalValue γ p)) :=
  partitionTransitionFidelity_tendsto_moving μ ν hμ hν δμ δτ hδμ hδτ hc hgμ hgτ
    (fun _ => p.eigenvalue) (fun _ => p.positive) p (fun _ => tendsto_const_nhds) γ hγ ht

/-- Typicality and the physical sample-size ratio discharge every Cartan
asymptotic hypothesis. There is no supplied conditional-fidelity limit. -/
theorem partitionTransitionFidelity_tendsto_of_typical
    (n m : ℕ → ℕ) (hn : Tendsto n atTop atTop) (hm : Tendsto m atTop atTop)
    (μ ν : ℕ → Fin d → ℕ) (hμ : ∀ k, Antitone (μ k)) (hν : ∀ k, Antitone (ν k))
    (p : SimpleSpectrum d) (γ : ℝ) (hγ : 1 < γ)
    (hgain : Tendsto (fun k => (m k : ℝ)/(n k : ℝ)) atTop (𝓝 γ))
    (hμtyp : ∀ᶠ k in atTop, TypicalLabel (n k) p.eigenvalue (μ k))
    (hνtyp : ∀ᶠ k in atTop, TypicalLabel (m k) p.eigenvalue (ν k)) :
    Tendsto (fun k => partitionTransitionFidelity (μ k) (ν k) (hμ k) (hν k) p.eigenvalue p.positive)
      atTop (𝓝 (orbitalValue γ p)) := by
  obtain ⟨δμ,δτ,hδμ,hδτ,hc,hgμ,hgτ,ht⟩ := typical_pair_cartan_parameters n m hn hm μ ν
    p.eigenvalue p.positive p.strictAnti γ hγ hgain hμtyp hνtyp
  exact partitionTransitionFidelity_tendsto μ ν hμ hν δμ δτ hδμ hδτ hc hgμ hgτ p γ hγ ht

end Cloning.TensorCloning
