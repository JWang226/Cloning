import Cloning.TensorGibbsPureTransfer
import Cloning.TensorGibbsStateTransfer

/-! Displaced mixed-state comparison follows from literal vector errors and
finite positive spectral truncations. The physical and Fock displacements are
actual linear isometries; channel action is derived on all inputs. -/
noncomputable section
open scoped BigOperators InnerProductSpace ComplexOrder
namespace Cloning.InfiniteTraceClass
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem QuantumChannel.ofIsometry_frameMatrix_diagonal (U : H →ₗᵢ[ℂ] K)
    (x : ι → H) (a : ι → ℝ) :
    (QuantumChannel.ofIsometry U).toLinearMap (frameMatrix x (Matrix.diagonal (fun i => (a i : ℂ)))) =
      frameMatrix (fun i => U (x i)) (Matrix.diagonal (fun i => (a i : ℂ))) := by
  simp only [frameMatrix_diagonal, map_sum, map_smul, QuantumChannel.ofIsometry_vectorProjector]

/-- Finite physical and Fock truncations give an explicit displaced-state
error, with vector-to-state continuity and fallback trace both included. -/
theorem displaced_mixture_channel_error (V : H →L[ℂ] K)
    (hV : ∀ x, ‖V x‖ ≤ ‖x‖) (σ : DensityState K)
    (U : H →ₗᵢ[ℂ] H) (W : K →ₗᵢ[ℂ] K)
    (A : TraceClass H) (hA : 0 ≤ A.1) (B : TraceClass K) (hB : 0 ≤ B.1)
    (x : ι → H) (y : ι → K) (hx : ∀ i, ‖x i‖ = 1) (hy : ∀ i, ‖y i‖ = 1)
    (a b : ι → ℝ) (hb : ∀ i, 0 ≤ b i) :
    ‖(QuantumChannel.ofContraction V hV σ).toLinearMap ((QuantumChannel.ofIsometry U).toLinearMap A) -
      (QuantumChannel.ofIsometry W).toLinearMap B‖ ≤
      ‖A - frameMatrix x (Matrix.diagonal (fun i => (a i : ℂ)))‖ +
      (∑ i, |a i-b i|) + 4 * (∑ i, b i * ‖V (U (x i)) - W (y i)‖) +
      ‖B - frameMatrix y (Matrix.diagonal (fun i => (b i : ℂ)))‖ := by
  let F := QuantumChannel.ofContraction V hV σ
  let S := QuantumChannel.ofIsometry U
  let T := QuantumChannel.ofIsometry W
  let X := frameMatrix x (Matrix.diagonal (fun i => (b i : ℂ)))
  let Y := frameMatrix y (Matrix.diagonal (fun i => (b i : ℂ)))
  have hX : 0 ≤ X.1 := frameMatrix_diagonal_nonneg x b hb
  have hY : 0 ≤ Y.1 := frameMatrix_diagonal_nonneg y b hb
  have hfirst : ‖F.toLinearMap (S.toLinearMap A) - F.toLinearMap (S.toLinearMap X)‖ ≤
      ‖A - frameMatrix x (Matrix.diagonal (fun i => (a i : ℂ)))‖ + ∑ i, |a i-b i| := by
    apply (F.toPositiveTracePreservingMap.norm_map_sub_le _ _ (S.map_nonneg A hA) (S.map_nonneg X hX)).trans
    apply (S.toPositiveTracePreservingMap.norm_map_sub_le _ _ hA hX).trans
    exact (norm_sub_le_norm_sub_add_norm_sub A
      (frameMatrix x (Matrix.diagonal (fun i => (a i : ℂ)))) X).trans
      (add_le_add (le_refl _) (frameMatrix_diagonal_sub_norm_le x hx a b))
  have hmiddle : ‖F.toLinearMap (S.toLinearMap X) - T.toLinearMap Y‖ ≤
      4 * ∑ i, b i * ‖V (U (x i)) - W (y i)‖ := by
    dsimp only [F,S,T,X,Y]
    rw [QuantumChannel.ofIsometry_frameMatrix_diagonal, QuantumChannel.ofIsometry_frameMatrix_diagonal]
    exact QuantumChannel.ofContraction_mixture_error V hV σ _ _
      (fun i => (U.norm_map _).trans (hx i)) (fun i => (W.norm_map _).trans (hy i)) b hb
  have hlast : ‖T.toLinearMap Y - T.toLinearMap B‖ ≤ ‖B-Y‖ := by
    rw [norm_sub_rev B]
    exact T.toPositiveTracePreservingMap.norm_map_sub_le _ _ hY hB
  have ht := norm_sub_le_norm_sub_add_norm_sub (F.toLinearMap (S.toLinearMap A))
    (F.toLinearMap (S.toLinearMap X)) (T.toLinearMap B)
  have ht' := norm_sub_le_norm_sub_add_norm_sub (F.toLinearMap (S.toLinearMap X))
    (T.toLinearMap Y) (T.toLinearMap B)
  change ‖F.toLinearMap (S.toLinearMap A) - T.toLinearMap B‖ ≤ _
  linarith

end Cloning.InfiniteTraceClass
