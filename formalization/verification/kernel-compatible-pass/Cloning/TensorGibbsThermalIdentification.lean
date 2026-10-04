import Cloning.TensorGibbsThermalCutoff
import Cloning.InfiniteDiagonalFidelity
import Cloning.ThermalWitness

/-! The Fock target is exactly the existing product-geometric density, with
the physical ordered root ratios in the canonical finite mode enumeration. -/
noncomputable section
open scoped BigOperators
namespace Cloning.TensorLie
open Cloning.TensorLAN Cloning.InfiniteTraceClass
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {d : ℕ}

def rootThermalParameter (p : Fin d → ℝ) (i : Fin (Fintype.card (PositiveRoot d))) : ℝ :=
  rootBoltzmann p ((Fintype.equivFin (PositiveRoot d)).symm i)

def fockOccupationEquiv (d : ℕ) : (PositiveRoot d → ℕ) ≃ (Fin (Fintype.card (PositiveRoot d)) → ℕ) :=
  Equiv.arrowCongr (Fintype.equivFin (PositiveRoot d)) (Equiv.refl ℕ)

@[simp] theorem fockOccupationEquiv_apply (k : PositiveRoot d → ℕ) :
    fockOccupationEquiv d k = fockOccupation d k := rfl

theorem bosonicOccupationWeight_eq_productGeometric (p : Fin d → ℝ) (k : PositiveRoot d → ℕ) :
    bosonicOccupationWeight p k = ThermalWitness.productGeometric (rootThermalParameter p)
      (fockOccupation d k) := by
  rw [bosonicOccupationWeight, wordBoltzmann_canonicalWord, ← Finset.prod_mul_distrib]
  have he := (Fintype.equivFin (PositiveRoot d)).symm.prod_comp
    (fun r => (1-rootBoltzmann p r) * rootBoltzmann p r ^ k r)
  exact he.symm

theorem rootThermalState_eq_productGeometric (p : Fin d → ℝ) :
    rootThermalState p = vectorMixture (MultimodeCoherentGaussianMixture.numberBasis _)
      (ThermalWitness.productGeometric (rootThermalParameter p)) := by
  rw [rootThermalState, vectorMixture, vectorMixture]
  simp_rw [bosonicOccupationWeight_eq_productGeometric]
  exact (fockOccupationEquiv d).tsum_eq (fun k : Fin (Fintype.card (PositiveRoot d)) → ℕ =>
    (ThermalWitness.productGeometric (rootThermalParameter p) k : ℂ) •
      vectorProjector (MultimodeCoherentGaussianMixture.numberBasis _ k))

theorem rootThermalState_eq_productGeometricState (p : Fin d → ℝ)
    (hp : ∀ a, 0 < p a) (hord : StrictAnti p) :
    (rootThermalState p).1 =
      (InfiniteDiagonalFidelity.productGeometricState (MultimodeCoherentGaussianMixture.numberBasis _)
        (rootThermalParameter p) (fun i => (div_pos (hp _) (hp _)).le)
        (fun i => rootBoltzmann_lt_one p hp hord _)).op := by
  rw [rootThermalState_eq_productGeometric]
  rfl

end Cloning.TensorLie
