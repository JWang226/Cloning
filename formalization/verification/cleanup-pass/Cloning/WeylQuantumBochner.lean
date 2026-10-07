import Cloning.WeylGNSAction
import Cloning.WeylFockRepresentation
import Cloning.WeylIdlerUniqueness

/-! Finite-mode quantum Bochner reconstruction: normalized continuous Weyl
positive functions are characteristic functions of actual density operators.
Existence is proved by the GNS action, Gaussian vacuum projection, actual Fock
Hilbert sum and trace-norm partial trace; no representation theorem is assumed. -/
noncomputable section
open scoped BigOperators Topology InnerProductSpace ComplexOrder
namespace Cloning.WeylGNS
open MultimodeCoherent InfiniteTraceClass
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
variable {d : ℕ}

/-- Every normalized continuous Weyl-positive function has an actual density
operator on the standard Fock space, in any finite number of modes. -/
theorem exists_density_characteristic (g : (Fin d → ℂ) → ℂ)
    (hg0 : g 0=1) (hgcont : Continuous g) (hgpos : IsWeylCharacteristicPositive g) :
    ∃ σ : TraceClass (Fock d), 0≤σ.1 ∧ traceCLM σ=1 ∧
      ∀ a : Fin d → ℂ, tracePairing σ (displacement a)=g a := by
  letI : Fact (PositiveKernel.IsNormalizedPositive (kernel g)) :=
    ⟨normalizedPositive_kernel hgpos hg0⟩
  obtain ⟨σ,hσ,ht,hc⟩ := (regularWeyl g hgcont).exists_density_characteristic
    (feature g 0) (norm_feature g 0)
  refine ⟨σ,hσ,ht,fun a => ?_⟩
  exact (hc a).trans (origin_characteristic g a)

/-- The reconstructed density operator is unique among all trace-class
operators with the prescribed characteristic function. -/
theorem existsUnique_density_characteristic (g : (Fin d → ℂ) → ℂ)
    (hg0 : g 0=1) (hgcont : Continuous g) (hgpos : IsWeylCharacteristicPositive g) :
    ∃! σ : TraceClass (Fock d), 0≤σ.1 ∧ traceCLM σ=1 ∧
      ∀ a : Fin d → ℂ, tracePairing σ (displacement a)=g a := by
  obtain ⟨σ,hσ,ht,hc⟩ := exists_density_characteristic g hg0 hgcont hgpos
  refine ⟨σ,⟨hσ,ht,hc⟩,?_⟩
  intro τ hτ
  apply characteristic_injective
  funext a
  exact (hτ.2.2 a).trans (hc a).symm

/-- The scalar-gain covariant channel's joint idler now exists as an actual
positive trace-class operator, and is unique. The idler need not be Gaussian,
diagonal or a product state. -/
theorem covariantChannel_existsUnique_idler
    (Φ : QuantumChannel (Fock d) (Fock d)) (r : ℝ) (hr : 1<r)
    (hΦ : ∀ a T, Φ.toLinearMap (displacementTraceMap a T)=
      displacementTraceMap (r • a) (Φ.toLinearMap T)) :
    ∃! σ : TraceClass (Fock d), 0≤σ.1 ∧ traceCLM σ=1 ∧
      ∀ a, tracePairing σ (displacement a)=amplifierIdlerFunction (weylMultiplier Φ.heisenberg r) r a := by
  obtain ⟨hg0,hgc,hgp,_,_⟩ := quantumChannel_idler_characteristic_data Φ r hr hΦ
  exact existsUnique_density_characteristic _ hg0 hgc hgp

end Cloning.WeylGNS
