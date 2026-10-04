import Cloning.TensorGibbsDisplacedState
import Cloning.TensorLocalUnitaryCoordinates
import Cloning.TensorLocalUnitaryFockPolynomial

/-! Exact physical local unitaries on the actual cyclic sector and literal
agreement of ambient and sector cutoff coordinate maps, including adjoints. -/
noncomputable section
open scoped BigOperators InnerProductSpace Matrix Topology Matrix.Norms.L2Operator
open NormedSpace
namespace Cloning.TensorLie
open Cloning.PCT Cloning.TensorLAN Cloning.TensorLocalUnitary Cloning.PCTLocalChart
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
variable {n d : ℕ}
local instance : NormedAlgebra ℚ (Matrix (Fin d) (Fin d) ℂ) :=
  NormedAlgebra.restrictScalars ℚ ℂ _
local instance : FiniteDimensional ℂ (TensorRegister n (Fin d)) :=
  (registerBasis (Fin n → Fin d)).toOrthonormalBasis.toBasis.finiteDimensional_of_finite

theorem orbitalGenerator_star (p : Fin d → ℝ) (z : PositiveRoot d → ℂ) :
    (orbitalGenerator p z)ᴴ = -orbitalGenerator p z := by
  ext i j
  by_cases hij : i < j
  · simp [Matrix.conjTranspose_apply, orbitalGenerator, hij, not_lt_of_gt hij,
      star_div₀, Complex.star_def, Complex.conj_ofReal, neg_div]
  · by_cases hji : j < i
    · simp [Matrix.conjTranspose_apply, orbitalGenerator, hij, hji,
        star_div₀, Complex.star_def, Complex.conj_ofReal, neg_div]
    · simp [Matrix.conjTranspose_apply, orbitalGenerator, hij, hji]

theorem orbitalExp_unitary (p : Fin d → ℝ) (t : ℝ) (z : PositiveRoot d → ℂ) :
    (exp (t • orbitalGenerator p z))ᴴ * exp (t • orbitalGenerator p z) = 1 := by
  apply Unitary.star_mul_self_of_mem
  apply exp_mem_unitary_of_mem_skewAdjoint
  change star (t • orbitalGenerator p z) = -(t • orbitalGenerator p z)
  rw [star_smul, star_trivial]
  change t • (orbitalGenerator p z)ᴴ = _
  rw [orbitalGenerator_star, smul_neg]

variable (Ω : TensorRegister n (Fin d)) (mu : Fin d → ℕ)
    (hweight : ∀ a, collectiveGenerator n a a Ω = (mu a : ℂ) • Ω)
    (hraise : ∀ a b, a < b → collectiveGenerator n a b Ω = 0)

def sectorOrbitalUnitary (p : Fin d → ℝ) (t : ℝ) (z : PositiveRoot d → ℂ) :
    cyclicSector Ω ≃ₗᵢ[ℂ] cyclicSector Ω :=
  cyclicUnitary Ω (fun a => (mu a : ℂ)) hweight hraise
    (exp (t • orbitalGenerator p z)) (orbitalExp_unitary p t z)

@[simp] theorem sectorOrbitalUnitary_coe (p : Fin d → ℝ) (t : ℝ) (z : PositiveRoot d → ℂ)
    (x : cyclicSector Ω) :
    (sectorOrbitalUnitary Ω mu hweight hraise p t z x : TensorRegister n (Fin d)) =
      tensorOperator n (exp (t • orbitalGenerator p z)) x := rfl

theorem sectorOrbitalUnitary_eq_rootExp (p : Fin d → ℝ) (t : ℝ) (z : PositiveRoot d → ℂ)
    (hgap : ∀ a : PositiveRoot d, 0 < rootGap mu a) (x : cyclicSector Ω) :
    (sectorOrbitalUnitary Ω mu hweight hraise p t z x : TensorRegister n (Fin d)) =
      exp (rootGenerator (n := n) mu (scaledRootParameter p mu t z)) x := by
  rw [sectorOrbitalUnitary_coe, tensorOperator_local_orbital p mu hgap]

def sectorRootUnitary (z : PositiveRoot d → ℂ) : cyclicSector Ω ≃ₗᵢ[ℂ] cyclicSector Ω :=
  sectorOrbitalUnitary Ω mu hweight hraise (fun a => (mu a : ℝ)) 1 z

theorem sectorRootUnitary_coe (z : PositiveRoot d → ℂ)
    (hgap : ∀ a : PositiveRoot d, 0 < rootGap mu a) (x : cyclicSector Ω) :
    (sectorRootUnitary Ω mu hweight hraise z x : TensorRegister n (Fin d)) =
      exp (rootGenerator (n := n) mu z) x := by
  rw [sectorRootUnitary, sectorOrbitalUnitary_eq_rootExp Ω mu hweight hraise _ _ _ hgap]
  have he : scaledRootParameter (fun a => (mu a : ℝ)) mu 1 z = z := by
    funext a
    have hs : Real.sqrt ((mu a.val.1 : ℝ) - mu a.val.2) ≠ 0 :=
      (Real.sqrt_pos.mpr (hgap a)).ne'
    simp [scaledRootParameter, hs]
  rw [he]

theorem sectorFockTransport_eq_cutoffEmbedding (Q : ℕ) (hq : CutoffReady Ω mu Q)
    (x : cyclicSector Ω) :
    sectorFockTransport Ω mu Q hq x = cutoffEmbedding Ω mu Q (x : TensorRegister n (Fin d)) := by
  simp only [sectorFockTransport, frameTransport_apply_sum, sectorCutoffBasis_coe, cutoffEmbedding_apply]
  rfl

theorem cutoffEmbedding_eq_sectorFockTransport_comp_projection (Q : ℕ) (hq : CutoffReady Ω mu Q) :
    cutoffEmbedding Ω mu Q = (sectorFockTransport Ω mu Q hq).comp (cyclicSector Ω).orthogonalProjection := by
  ext x
  rw [ContinuousLinearMap.comp_apply]
  simp only [sectorFockTransport, frameTransport_apply_sum, sectorCutoffBasis_coe,
    (cyclicSector Ω).inner_orthogonalProjection_eq_of_mem_left, cutoffEmbedding_apply]
  rfl

theorem sectorFockTransport_adjoint_coe (Q : ℕ) (hq : CutoffReady Ω mu Q) (y : RootFock d) :
    ((sectorFockTransport Ω mu Q hq).adjoint y : TensorRegister n (Fin d)) =
      (cutoffEmbedding Ω mu Q).adjoint y := by
  rw [cutoffEmbedding_eq_sectorFockTransport_comp_projection Ω mu Q hq,
    ContinuousLinearMap.adjoint_comp, Submodule.adjoint_orthogonalProjection]
  rfl

end Cloning.TensorLie
