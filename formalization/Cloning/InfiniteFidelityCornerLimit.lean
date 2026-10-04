import Cloning.InfiniteGentleCompression
import Cloning.InfiniteFiniteCorner
import Cloning.HybridStates
import Cloning.MatrixFidelitySymmetry

/-! Actual fidelity convergence for states on varying Hilbert spaces from
finite matrix entries. Unit total mass and the limiting corner masses derive
all source tail bounds through gentle compression. -/
noncomputable section
open scoped BigOperators InnerProductSpace ComplexOrder Topology Classical
open Filter
namespace Cloning.InfiniteFidelityCorner
open Cloning.InfiniteTraceClass Cloning.InfiniteFiniteCorner Cloning.Hybrid
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def mass (v : ι → H) (A : TraceClass H) : ℝ := (Matrix.trace (matrixOf v A.1)).re

def modulus (a b : ℝ) : ℝ :=
  Real.sqrt (2 * Real.sqrt (1-a)) + Real.sqrt (2 * Real.sqrt (1-b))

theorem continuous_modulus : Continuous (fun x : ℝ × ℝ => modulus x.1 x.2) := by
  unfold modulus
  fun_prop

private theorem projection_star {v : ι → H} (hv : Orthonormal ℂ v) :
    IsStarProjection (projection v) := by
  constructor
  · change ofMatrix v 1 * ofMatrix v 1 = ofMatrix v 1
    rw [← ofMatrix_mul hv, one_mul]
  · change star (ofMatrix v 1) = ofMatrix v 1
    rw [← ofMatrix_conjTranspose, Matrix.conjTranspose_one]

private theorem corner_eq_sandwich (v : ι → H) (A : TraceClass H) :
    matrixLift v (matrixOf v A.1) = sandwichCLM (projection v) (projection v) A := by
  apply Subtype.ext
  exact ofMatrix_matrixOf v A.1

theorem norm_corner_eq_mass (v : ι → H) (hv : Orthonormal ℂ v)
    (A : PositiveTraceClass H) : ‖matrixLift v (matrixOf v A.1.1)‖ = mass v A.1 := by
  rw [TraceClass.norm_eq_trace_re_of_nonneg _ (ofMatrix_nonneg hv (matrixOf_posSemidef v A.2))]
  exact congrArg Complex.re (trace_ofMatrix hv _)

/-- Finite matrix fidelity differs from the actual fidelity by a modulus of
the two discarded trace masses. No diagonal or support hypothesis is used. -/
theorem abs_rootFidelity_sub_corner_le (v : ι → H) (hv : Orthonormal ℂ v)
    (A B : PositiveTraceClass H) (hA : ‖A.1‖ = 1) (hB : ‖B.1‖ = 1) :
    |A.rootFidelity B - MatrixFidelity.fidelity (matrixOf v A.1.1) (matrixOf v B.1.1)| ≤
      modulus (mass v A.1) (mass v B.1) := by
  let C : PositiveTraceClass H := ⟨matrixLift v (matrixOf v A.1.1),
    ofMatrix_nonneg hv (matrixOf_posSemidef v A.2)⟩
  let D : PositiveTraceClass H := ⟨matrixLift v (matrixOf v B.1.1),
    ofMatrix_nonneg hv (matrixOf_posSemidef v B.2)⟩
  have hC : ‖C.1‖ ≤ 1 := by
    dsimp only [C]
    rw [corner_eq_sandwich]
    exact (norm_sandwich_projection_le (projection_star hv) A.1).trans_eq hA
  have hgA : ‖A.1-C.1‖ ≤ 2 * Real.sqrt (1-mass v A.1) := by
    have hh := gentle_compression_unit (projection_star hv) A.1 A.2 hA
    rw [← corner_eq_sandwich, norm_corner_eq_mass v hv A] at hh
    exact hh
  have hgB : ‖B.1-D.1‖ ≤ 2 * Real.sqrt (1-mass v B.1) := by
    have hh := gentle_compression_unit (projection_star hv) B.1 B.2 hB
    rw [← corner_eq_sandwich, norm_corner_eq_mass v hv B] at hh
    exact hh
  have hf := PositiveTraceClass.rootFidelity_continuity A B C D
  have he : C.rootFidelity D = MatrixFidelity.fidelity (matrixOf v A.1.1) (matrixOf v B.1.1) :=
    fidelity_ofMatrix hv (matrixOf_posSemidef v A.2) (matrixOf_posSemidef v B.2)
  rw [he, hB, Real.sqrt_one, mul_one] at hf
  apply hf.trans
  unfold modulus
  exact add_le_add (Real.sqrt_le_sqrt hgA)
    ((mul_le_mul (Real.sqrt_le_sqrt hgB)
      (by simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hC)
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)).trans_eq (mul_one _))

section Varying
variable {G : ℕ → Type*}
  [∀ N, NormedAddCommGroup (G N)] [∀ N, InnerProductSpace ℂ (G N)] [∀ N, CompleteSpace (G N)]
variable (I : ℕ → Type*) [∀ R, Fintype (I R)] [∀ R, DecidableEq (I R)]

/-- Varying-Hilbert quantum fidelity convergence from actual finite entries.
Only limiting corner masses are required to exhaust the two unit states;
there is no tail or trace-norm convergence premise for the physical states. -/
theorem tendsto_rootFidelity_of_corner_coefficients
    (A B : ∀ N, PositiveTraceClass (G N)) (C D : PositiveTraceClass H)
    (hA : ∀ N, ‖(A N).1‖ = 1) (hB : ∀ N, ‖(B N).1‖ = 1)
    (hC : ‖C.1‖ = 1) (hD : ‖D.1‖ = 1)
    (v : ∀ N R, I R → G N) (w : ∀ R, I R → H)
    (hv : ∀ R, ∀ᶠ N in atTop, Orthonormal ℂ (v N R))
    (hw : ∀ R, Orthonormal ℂ (w R))
    (hCA : ∀ R i j, Tendsto (fun N => ⟪v N R i, (A N).1.1 (v N R j)⟫_ℂ)
      atTop (𝓝 ⟪w R i, C.1.1 (w R j)⟫_ℂ))
    (hDB : ∀ R i j, Tendsto (fun N => ⟪v N R i, (B N).1.1 (v N R j)⟫_ℂ)
      atTop (𝓝 ⟪w R i, D.1.1 (w R j)⟫_ℂ))
    (hCm : Tendsto (fun R => mass (w R) C.1) atTop (𝓝 1))
    (hDm : Tendsto (fun R => mass (w R) D.1) atTop (𝓝 1)) :
    Tendsto (fun N => (A N).rootFidelity (B N)) atTop (𝓝 (C.rootFidelity D)) := by
  have hmod : Tendsto (fun R => modulus (mass (w R) C.1) (mass (w R) D.1)) atTop (𝓝 0) := by
    simpa only [modulus, sub_self, Real.sqrt_zero, mul_zero, zero_add] using
      continuous_modulus.continuousAt.tendsto.comp (hCm.prodMk_nhds hDm)
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨R,hR⟩ := (hmod.eventually (eventually_lt_nhds (show 0 < ε/3 by positivity))).exists
  have hMA : Tendsto (fun N => matrixOf (v N R) (A N).1.1) atTop
      (𝓝 (matrixOf (w R) C.1.1)) :=
    tendsto_pi_nhds.mpr (fun i => tendsto_pi_nhds.mpr (fun j => hCA R i j))
  have hMB : Tendsto (fun N => matrixOf (v N R) (B N).1.1) atTop
      (𝓝 (matrixOf (w R) D.1.1)) :=
    tendsto_pi_nhds.mpr (fun i => tendsto_pi_nhds.mpr (fun j => hDB R i j))
  have hf := MatrixFidelity.tendsto_fidelity (matrixOf_posSemidef (w R) C.2)
    (matrixOf_posSemidef (w R) D.2)
    (fun N => matrixOf_posSemidef (v N R) (A N).2)
    (fun N => matrixOf_posSemidef (v N R) (B N).2) hMA hMB
  have hmA : Tendsto (fun N => mass (v N R) (A N).1) atTop (𝓝 (mass (w R) C.1)) := by
    exact Complex.continuous_re.continuousAt.tendsto.comp
      (tendsto_finset_sum _ (fun i _ => hCA R i i))
  have hmB : Tendsto (fun N => mass (v N R) (B N).1) atTop (𝓝 (mass (w R) D.1)) := by
    exact Complex.continuous_re.continuousAt.tendsto.comp
      (tendsto_finset_sum _ (fun i _ => hDB R i i))
  have hbound : Tendsto (fun N => modulus (mass (v N R) (A N).1) (mass (v N R) (B N).1) +
      |MatrixFidelity.fidelity (matrixOf (v N R) (A N).1.1) (matrixOf (v N R) (B N).1.1) -
        MatrixFidelity.fidelity (matrixOf (w R) C.1.1) (matrixOf (w R) D.1.1)| +
      modulus (mass (w R) C.1) (mass (w R) D.1)) atTop
      (𝓝 (2 * modulus (mass (w R) C.1) (mass (w R) D.1))) := by
    have hh := continuous_modulus.continuousAt.tendsto.comp (hmA.prodMk_nhds hmB)
    convert (hh.add (hf.sub_const _).abs).add_const (modulus (mass (w R) C.1) (mass (w R) D.1)) using 1 <;>
      simp only [sub_self, abs_zero, add_zero, two_mul]
  filter_upwards [hv R, hbound.eventually (eventually_lt_nhds (show
      2 * modulus (mass (w R) C.1) (mass (w R) D.1) < ε by linarith))] with N hvN hbN
  rw [Real.dist_eq]
  have hsource := abs_rootFidelity_sub_corner_le (v N R) hvN (A N) (B N) (hA N) (hB N)
  have htarget := abs_rootFidelity_sub_corner_le (w R) (hw R) C D hC hD
  have ht := abs_sub_le ((A N).rootFidelity (B N))
    (MatrixFidelity.fidelity (matrixOf (v N R) (A N).1.1) (matrixOf (v N R) (B N).1.1)) (C.rootFidelity D)
  have ht' := abs_sub_le
    (MatrixFidelity.fidelity (matrixOf (v N R) (A N).1.1) (matrixOf (v N R) (B N).1.1))
    (MatrixFidelity.fidelity (matrixOf (w R) C.1.1) (matrixOf (w R) D.1.1)) (C.rootFidelity D)
  rw [abs_sub_comm (C.rootFidelity D)] at htarget
  linarith

end Varying
end Cloning.InfiniteFidelityCorner
