import Cloning.TensorGibbsTrace
import Cloning.TensorGibbsDecay

/-! Uniform summable tails of the literal physical sector partition function.
The envelope is independent of the tensor size and highest weight. -/
noncomputable section
open scoped BigOperators InnerProductSpace Topology
open Filter
namespace Cloning.TensorLie
open Cloning.PCT Cloning.InfiniteTraceClass
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {n d : ℕ}

local instance : FiniteDimensional ℂ (TensorRegister n (Fin d)) :=
  (registerBasis (Fin n → Fin d)).toOrthonormalBasis.toBasis.finiteDimensional_of_finite

variable (Ω : TensorRegister n (Fin d)) (mu : Fin d → ℕ)
    (hweight : ∀ a, collectiveGenerator n a a Ω = (mu a : ℂ) • Ω)
    (hraise : ∀ a b, a < b → collectiveGenerator n a b Ω = 0)

def sectorHeightMass (p : Fin d → ℝ) (H : ℕ) : ℝ :=
  sectorHeightTrace Ω mu hweight hraise p H / (∏ a, p a ^ mu a)

theorem sectorHeightMass_nonneg (p : Fin d → ℝ) (hp : ∀ a, 0 < p a) (H : ℕ) :
    0 ≤ sectorHeightMass Ω mu hweight hraise p H :=
  div_nonneg (sectorHeightTrace_nonneg Ω mu hweight hraise p (fun a => (hp a).le) H)
    (Finset.prod_nonneg (fun a _ => pow_nonneg (hp a).le _))

theorem sectorHeightMass_summable (p : Fin d → ℝ) :
    Summable (sectorHeightMass Ω mu hweight hraise p) :=
  (sectorHeightTrace_summable Ω mu hweight hraise p).div_const _

theorem sectorPartitionFunction_div_highest (p : Fin d → ℝ) (hp : ∀ a, 0 < p a) :
    sectorPartitionFunction Ω mu hweight hraise p / (∏ a, p a ^ mu a) =
      ∑' H : ℕ, sectorHeightMass Ω mu hweight hraise p H := by
  rw [sectorPartitionFunction_eq_tsum_height Ω mu hweight hraise p (fun a => (hp a).le),
    ← tsum_div_const]
  rfl

theorem sectorHeightMass_le_envelope (p : Fin d → ℝ) (hp : ∀ a, 0 < p a)
    (θ : ℝ) (hθ : 0 ≤ θ)
    (hroot : ∀ r : PositiveRoot d, rootBoltzmann p r ≤ θ ^ r.height) (H : ℕ) :
    sectorHeightMass Ω mu hweight hraise p H ≤ heightEnvelope d θ H := by
  have hm : 0 < ∏ a, p a ^ mu a := Finset.prod_pos (fun a _ => pow_pos (hp a) _)
  apply (div_le_iff₀ hm).mpr
  have hh := sectorHeightTrace_le Ω mu hweight hraise p hp θ hθ hroot H
  simpa only [heightEnvelope, mul_assoc, mul_left_comm, mul_comm] using hh

def heightTailEnvelope (d : ℕ) (θ : ℝ) (R : ℕ) : ℝ :=
  ∑' H : ℕ, heightEnvelope d θ (H + R)

theorem heightTailEnvelope_tendsto_zero (d : ℕ) (θ : ℝ) :
    Tendsto (heightTailEnvelope d θ) atTop (𝓝 0) :=
  tendsto_sum_nat_add (heightEnvelope d θ)

theorem sectorHeightMass_tail_le (p : Fin d → ℝ) (hp : ∀ a, 0 < p a)
    (θ : ℝ) (hθ : 0 < θ) (hθ1 : θ < 1)
    (hroot : ∀ r : PositiveRoot d, rootBoltzmann p r ≤ θ ^ r.height) (R : ℕ) :
    (∑' H : ℕ, sectorHeightMass Ω mu hweight hraise p (H + R)) ≤
      heightTailEnvelope d θ R := by
  apply Summable.tsum_le_tsum
    (fun H => sectorHeightMass_le_envelope Ω mu hweight hraise p hp θ hθ.le hroot (H+R))
  · exact (summable_nat_add_iff R).mpr (sectorHeightMass_summable Ω mu hweight hraise p)
  · exact (summable_nat_add_iff R).mpr (heightEnvelope_summable (d := d) θ hθ hθ1)

theorem sectorPartitionFunction_cutoff_error (p : Fin d → ℝ) (hp : ∀ a, 0 < p a)
    (θ : ℝ) (hθ : 0 < θ) (hθ1 : θ < 1)
    (hroot : ∀ r : PositiveRoot d, rootBoltzmann p r ≤ θ ^ r.height) (R : ℕ) :
    0 ≤ sectorPartitionFunction Ω mu hweight hraise p / (∏ a, p a ^ mu a) -
      ∑ H ∈ Finset.range R, sectorHeightMass Ω mu hweight hraise p H ∧
    sectorPartitionFunction Ω mu hweight hraise p / (∏ a, p a ^ mu a) -
      ∑ H ∈ Finset.range R, sectorHeightMass Ω mu hweight hraise p H ≤
        heightTailEnvelope d θ R := by
  rw [sectorPartitionFunction_div_highest Ω mu hweight hraise p hp,
    ← (sectorHeightMass_summable Ω mu hweight hraise p).sum_add_tsum_nat_add R,
    add_sub_cancel_left]
  exact ⟨tsum_nonneg (fun H => sectorHeightMass_nonneg Ω mu hweight hraise p hp (H+R)),
    sectorHeightMass_tail_le Ω mu hweight hraise p hp θ hθ hθ1 hroot R⟩

end Cloning.TensorLie
