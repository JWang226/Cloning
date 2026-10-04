import Cloning.TensorCartanStateThermal
import Cloning.Main

/-! The literal Cartan thermal product equals the stated orbital value. -/
noncomputable section
open scoped BigOperators Classical
namespace Cloning.TensorCloning
open Cloning.TensorLie

theorem amplifiedRootParameter_inv_eq {d : ℕ} (γ : ℝ) (q : PositiveRoot d → ℝ)
    (a : PositiveRoot d) :
    amplifiedRootParameter (fun _ => γ⁻¹) q a = Thermal.amplified γ (q a) := by
  unfold amplifiedRootParameter Thermal.amplified
  ring

theorem cartanThermalProduct_eq_orbitalValue {d : ℕ} (p : SimpleSpectrum d)
    (γ : ℝ) (hγ : 1 < γ) :
    (∏ a : PositiveRoot d, Thermal.fidelity
      (amplifiedRootParameter (fun _ => γ⁻¹) (rootBoltzmann p.eigenvalue) a)
      (rootBoltzmann p.eigenvalue a)) = orbitalValue γ p := by
  unfold orbitalValue
  apply Finset.prod_congr rfl
  intro a _
  rw [amplifiedRootParameter_inv_eq]
  have he : Thermal.fidelity (Thermal.amplified γ (rootBoltzmann p.eigenvalue a))
      (rootBoltzmann p.eigenvalue a) =
      Thermal.fidelity (rootBoltzmann p.eigenvalue a)
        (Thermal.amplified γ (rootBoltzmann p.eigenvalue a)) := by
    simp only [Thermal.fidelity, mul_comm]
  rw [he]
  exact Thermal.fidelity_amplified_eq_modeFactor hγ (p.ratio_pos a).le (p.ratio_lt_one a)

end Cloning.TensorCloning
