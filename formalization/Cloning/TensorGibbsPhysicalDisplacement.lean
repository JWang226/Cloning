import Cloning.TensorGibbsLocalUnitary
import Cloning.TensorGibbsStateLimit
import Cloning.TensorLocalUnitaryPhysicalWeyl
import Cloning.WeylMultimodeChannel

/-! Actual physically rotated sector Gibbs states and the corresponding
Weyl-displaced product thermal state, with exact vector-coordinate adapters. -/
noncomputable section
open scoped BigOperators InnerProductSpace ComplexOrder Topology Matrix.Norms.L2Operator
open Filter NormedSpace
namespace Cloning.TensorLie
open Cloning.PCT Cloning.TensorLAN Cloning.TensorLocalUnitary Cloning.PCTLocalChart
open Cloning.InfiniteTraceClass Cloning.MultimodeCoherent
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
variable {n d : ℕ}
local instance (n d : ℕ) : FiniteDimensional ℂ (TensorRegister n (Fin d)) :=
  (registerBasis (Fin n → Fin d)).toOrthonormalBasis.toBasis.finiteDimensional_of_finite

def sectorDisplacedGibbs (Ω : TensorRegister n (Fin d)) (mu : Fin d → ℕ)
    (hweight : ∀ a, collectiveGenerator n a a Ω = (mu a : ℂ) • Ω)
    (hraise : ∀ a b, a < b → collectiveGenerator n a b Ω = 0)
    (r p : Fin d → ℝ) (t : ℝ) (z : PositiveRoot d → ℂ) : TraceClass (cyclicSector Ω) :=
  (QuantumChannel.ofIsometry (sectorOrbitalUnitary Ω mu hweight hraise p t z).toLinearIsometry).toLinearMap
    (sectorGibbsDensity Ω mu hweight hraise r)

def rootDisplacedThermal (p : Fin d → ℝ) (z : PositiveRoot d → ℂ) : TraceClass (RootFock d) :=
  (displacementChannel (rootFockAmplitude z)).toLinearMap (rootThermalState p)

theorem thermal_cutoff_mass_le_one (p : Fin d → ℝ) (hp : ∀ a, 0 < p a)
    (hord : StrictAnti p) (R : ℕ) :
    (∑ i : CutoffIndex d R, bosonicOccupationWeight p (cutoffOccupation d R i).val) ≤ 1 := by
  have ht := rootThermalCutoff_error p hp hord R
  have hn := norm_nonneg (rootThermalState p-rootThermalCutoff p R)
  rw [ht] at hn
  rw [(cutoffOccupation d R).sum_comp (fun k => bosonicOccupationWeight p k.val)]
  linarith

theorem physical_cutoff_mass_le_one (Ω : TensorRegister n (Fin d)) (mu : Fin d → ℕ)
    (hweight : ∀ a, collectiveGenerator n a a Ω = (mu a : ℂ) • Ω)
    (hraise : ∀ a b, a < b → collectiveGenerator n a b Ω = 0)
    (hΩ : ‖Ω‖ = 1) (p : Fin d → ℝ) (hp : ∀ a, 0 < p a) (R : ℕ)
    (hr : CutoffReady Ω mu R) :
    (∑ i : CutoffIndex d R, sectorOccupationWeight Ω mu hweight hraise p (cutoffOccupation d R i).val) ≤ 1 := by
  have hh := sectorGibbsCutoff_error Ω mu hweight hraise hΩ p hp R hr.2
  have hn := norm_nonneg (sectorGibbsDensity Ω mu hweight hraise p-sectorGibbsCutoff Ω mu hweight hraise p R)
  rw [hh] at hn
  linarith

theorem weighted_finite_error_le {ι : Type*} [Fintype ι] (a e : ι → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hs : (∑ i, a i) ≤ 1) (η : ℝ) (hη : 0 ≤ η) (he : ∀ i, e i ≤ η) :
    ∑ i, a i * e i ≤ η := by
  calc
    _ ≤ ∑ i, a i * η := Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (he i) (ha i))
    _ = (∑ i, a i) * η := (Finset.sum_mul _ _ _).symm
    _ ≤ 1*η := mul_le_mul_of_nonneg_right hs hη
    _ = η := one_mul _

theorem sector_orbital_vector_error_eq_ambient (Ω : TensorRegister n (Fin d)) (mu : Fin d → ℕ)
    (hweight : ∀ a, collectiveGenerator n a a Ω = (mu a : ℂ) • Ω)
    (hraise : ∀ a b, a < b → collectiveGenerator n a b Ω = 0)
    (p : Fin d → ℝ) (t : ℝ) (z z0 : PositiveRoot d → ℂ) (R Q : ℕ)
    (hq : CutoffReady Ω mu Q) (i : CutoffIndex d R) :
    ‖sectorFockTransport Ω mu Q hq
        (sectorOrbitalUnitary Ω mu hweight hraise p t z (cutoffSectorFrame Ω mu R i)) -
      displacement (rootFockAmplitude z0) (cutoffNumberFrame d R i)‖ =
    ‖cutoffEmbedding Ω mu Q (tensorOperator n (exp (t • orbitalGenerator p z)) (cutoffFrame Ω mu R i)) -
      displacement (rootFockAmplitude z0) (cutoffNumberFrame d R i)‖ := by
  rw [sectorFockTransport_eq_cutoffEmbedding, sectorOrbitalUnitary_coe]
  rfl

theorem sector_orbital_reverse_vector_error_eq_ambient (Ω : TensorRegister n (Fin d)) (mu : Fin d → ℕ)
    (hweight : ∀ a, collectiveGenerator n a a Ω = (mu a : ℂ) • Ω)
    (hraise : ∀ a b, a < b → collectiveGenerator n a b Ω = 0)
    (p : Fin d → ℝ) (t : ℝ) (z z0 : PositiveRoot d → ℂ) (R Q : ℕ)
    (hq : CutoffReady Ω mu Q) (i : CutoffIndex d R) :
    ‖(sectorFockTransport Ω mu Q hq).adjoint
        (displacement (rootFockAmplitude z0) (cutoffNumberFrame d R i)) -
      sectorOrbitalUnitary Ω mu hweight hraise p t z (cutoffSectorFrame Ω mu R i)‖ =
    ‖(cutoffEmbedding Ω mu Q).adjoint (displacement (rootFockAmplitude z0) (cutoffNumberFrame d R i)) -
      tensorOperator n (exp (t • orbitalGenerator p z)) (cutoffFrame Ω mu R i)‖ := by
  change ‖((sectorFockTransport Ω mu Q hq).adjoint
      (displacement (rootFockAmplitude z0) (cutoffNumberFrame d R i)) : TensorRegister n (Fin d)) -
      (sectorOrbitalUnitary Ω mu hweight hraise p t z (cutoffSectorFrame Ω mu R i) : TensorRegister n (Fin d))‖ = _
  rw [sectorFockTransport_adjoint_coe, sectorOrbitalUnitary_coe]
  rfl

end Cloning.TensorLie
