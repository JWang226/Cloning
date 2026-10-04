import Cloning.PhysicalFlatConverseJensen

/-! The averaged physical target orbit, and its finite-copy Cauchy--Schwarz
bound, including zero-rank support projections. -/
noncomputable section
open scoped BigOperators InnerProductSpace Matrix Topology Matrix.Norms.L2Operator MatrixOrder ComplexOrder
open MeasureTheory
namespace Cloning.PhysicalFlatConverse
open Cloning.TensorLie Cloning.MatrixFidelity Cloning.PCTPurificationChannel
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
variable {d : ℕ} [Nonempty (Fin d)]

theorem partitionActionMatrix_inv (mu : Fin d → ℕ) (hmu : Antitone mu)
    (U : unitary (Matrix (Fin d) (Fin d) ℂ)) :
    partitionActionMatrix mu hmu ((U⁻¹ : unitary (Matrix (Fin d) (Fin d) ℂ)) : Matrix (Fin d) (Fin d) ℂ) = (partitionActionMatrix mu hmu U)ᴴ := by
  rw [← Unitary.star_eq_inv]
  exact partitionActionMatrix_star mu hmu U

theorem partition_fidelity_move_unitary (mu : Fin d → ℕ) (hmu : Antitone mu)
    (M T : Matrix (PartitionIndex mu hmu) (PartitionIndex mu hmu) ℂ)
    (hM : M.PosSemidef) (hT : T.PosSemidef)
    (U : unitary (Matrix (Fin d) (Fin d) ℂ)) :
    fidelity M (partitionActionMatrix mu hmu U * T * (partitionActionMatrix mu hmu U)ᴴ) =
      fidelity (partitionActionMatrix mu hmu ((U⁻¹ : unitary (Matrix (Fin d) (Fin d) ℂ)) : Matrix (Fin d) (Fin d) ℂ) * M * (partitionActionMatrix mu hmu ((U⁻¹ : unitary (Matrix (Fin d) (Fin d) ℂ)) : Matrix (Fin d) (Fin d) ℂ))ᴴ) T := by
  let V := partitionActionMatrix mu hmu U
  have hV : Vᴴ * V = 1 := partitionActionMatrix_unitary mu hmu U
  have hV' : V * Vᴴ = 1 := mul_eq_one_comm.mp hV
  have he : V * (Vᴴ * M * V) * Vᴴ = M := by
    calc
      _ = (V*Vᴴ)*M*(V*Vᴴ) := by noncomm_ring
      _ = M := by rw [hV',one_mul,mul_one]
  have hh := fidelity_unitary_conjugation V hV (hM.conjTranspose_mul_mul_same V) hT
  rw [he] at hh
  simpa only [partitionActionMatrix_inv, Matrix.conjTranspose_conjTranspose, V] using hh

theorem integral_partition_target_fidelity_eq (mu : Fin d → ℕ) (hmu : Antitone mu)
    (M T : Matrix (PartitionIndex mu hmu) (PartitionIndex mu hmu) ℂ)
    (hM : M.PosSemidef) (hT : T.PosSemidef) :
    (∫ U : unitary (Matrix (Fin d) (Fin d) ℂ),
      fidelity M (partitionActionMatrix mu hmu ((U⁻¹ : unitary (Matrix (Fin d) (Fin d) ℂ)) : Matrix (Fin d) (Fin d) ℂ) * T * (partitionActionMatrix mu hmu ((U⁻¹ : unitary (Matrix (Fin d) (Fin d) ℂ)) : Matrix (Fin d) (Fin d) ℂ))ᴴ) ∂unitaryHaar) =
    (∫ U : unitary (Matrix (Fin d) (Fin d) ℂ),
      fidelity (partitionActionMatrix mu hmu U * M * (partitionActionMatrix mu hmu U)ᴴ) T ∂unitaryHaar) := by
  apply integral_congr_ae
  apply ae_of_all
  intro U
  have he := partition_fidelity_move_unitary mu hmu M T hM hT (U⁻¹)
  simpa only [inv_inv] using he

theorem integral_partition_target_projector_le (mu : Fin d → ℕ) (hmu : Antitone mu)
    (M P : Matrix (PartitionIndex mu hmu) (PartitionIndex mu hmu) ℂ)
    (hM : M.PosSemidef) (hP : P.PosSemidef) (hPP : P*P=P) (c : ℝ) (hc : 0 ≤ c) :
    (∫ U : unitary (Matrix (Fin d) (Fin d) ℂ),
      fidelity M (partitionActionMatrix mu hmu ((U⁻¹ : unitary (Matrix (Fin d) (Fin d) ℂ)) : Matrix (Fin d) (Fin d) ℂ) * (c • P) * (partitionActionMatrix mu hmu ((U⁻¹ : unitary (Matrix (Fin d) (Fin d) ℂ)) : Matrix (Fin d) (Fin d) ℂ))ᴴ)
        ∂unitaryHaar) ≤
      Real.sqrt (M.trace.re * (c * P.trace.re ^ 2) / (partitionDimension mu hmu : ℝ)) := by
  rw [integral_partition_target_fidelity_eq mu hmu M (c • P) hM (hP.smul hc)]
  apply (integral_partition_fidelity_le mu hmu M (c • P) hM (hP.smul hc)).trans_eq
  rw [fidelity_identity_projector _ c
    (div_nonneg (trace_re_nonneg hM) (Nat.cast_nonneg _)) hc hP hPP]
  have hs : 0 ≤ P.trace.re := trace_re_nonneg hP
  have hrad : 0 ≤ (M.trace.re / (partitionDimension mu hmu : ℝ)) * c :=
    mul_nonneg (div_nonneg (trace_re_nonneg hM) (Nat.cast_nonneg _)) hc
  have hsq : (Real.sqrt ((M.trace.re / (partitionDimension mu hmu : ℝ))*c) * P.trace.re)^2 =
      M.trace.re * (c * P.trace.re^2) / (partitionDimension mu hmu : ℝ) := by
    rw [mul_pow,Real.sq_sqrt hrad]
    ring
  rw [← hsq, Real.sqrt_sq (mul_nonneg (Real.sqrt_nonneg _) hs)]

theorem integrable_partition_target_fidelity (mu : Fin d → ℕ) (hmu : Antitone mu)
    (M T : Matrix (PartitionIndex mu hmu) (PartitionIndex mu hmu) ℂ)
    (hM : M.PosSemidef) (hT : T.PosSemidef) :
    Integrable (fun U : unitary (Matrix (Fin d) (Fin d) ℂ) =>
      fidelity M (partitionActionMatrix mu hmu ((U⁻¹ : unitary (Matrix (Fin d) (Fin d) ℂ)) : Matrix (Fin d) (Fin d) ℂ) * T * (partitionActionMatrix mu hmu ((U⁻¹ : unitary (Matrix (Fin d) (Fin d) ℂ)) : Matrix (Fin d) (Fin d) ℂ))ᴴ)) unitaryHaar := by
  have hp : Continuous (fun U : unitary (Matrix (Fin d) (Fin d) ℂ) =>
      (M,partitionActionMatrix mu hmu ((U⁻¹ : unitary (Matrix (Fin d) (Fin d) ℂ)) : Matrix (Fin d) (Fin d) ℂ) * T * (partitionActionMatrix mu hmu ((U⁻¹ : unitary (Matrix (Fin d) (Fin d) ℂ)) : Matrix (Fin d) (Fin d) ℂ))ᴴ)) :=
    continuous_const.prodMk ((continuous_partitionSandwich mu hmu T).comp continuous_inv)
  have hg : ContinuousOn (fun X : Matrix (PartitionIndex mu hmu) _ ℂ => fidelity M X)
      {X | X.PosSemidef} := by
    apply (continuousOn_fidelity (n := PartitionIndex mu hmu)).comp
      (show Continuous (fun X : Matrix (PartitionIndex mu hmu) _ ℂ => (M,X)) from
        continuous_const.prodMk continuous_id).continuousOn
    intro X hX
    exact ⟨hM,hX⟩
  have hh := hg.comp_continuous ((continuous_partitionSandwich mu hmu T).comp continuous_inv)
    (fun U : unitary (Matrix (Fin d) (Fin d) ℂ) => hT.mul_mul_conjTranspose_same
      (partitionActionMatrix mu hmu ((U⁻¹ : unitary (Matrix (Fin d) (Fin d) ℂ)) : Matrix (Fin d) (Fin d) ℂ)))
  exact hh.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- Sum over actual irreducible copies, with no condition on repeated labels
or on vanishing target support ranks. -/
theorem integral_partition_copy_projectors_le {ι : Type*} [Fintype ι]
    (mu : ι → Fin d → ℕ) (hmu : ∀ i, Antitone (mu i))
    (M P : ∀ i, Matrix (PartitionIndex (mu i) (hmu i)) (PartitionIndex (mu i) (hmu i)) ℂ)
    (hM : ∀ i, (M i).PosSemidef) (hP : ∀ i, (P i).PosSemidef)
    (hPP : ∀ i, P i * P i = P i) (c : ι → ℝ) (hc : ∀ i, 0 ≤ c i) :
    (∫ U : unitary (Matrix (Fin d) (Fin d) ℂ), ∑ i,
      fidelity (M i) (partitionActionMatrix (mu i) (hmu i) ((U⁻¹ : unitary (Matrix (Fin d) (Fin d) ℂ)) : Matrix (Fin d) (Fin d) ℂ) * (c i • P i) *
        (partitionActionMatrix (mu i) (hmu i) ((U⁻¹ : unitary (Matrix (Fin d) (Fin d) ℂ)) : Matrix (Fin d) (Fin d) ℂ))ᴴ) ∂unitaryHaar) ≤
      Real.sqrt ((∑ i, (M i).trace.re) *
        ∑ i, c i * (P i).trace.re ^ 2 / (partitionDimension (mu i) (hmu i) : ℝ)) := by
  rw [integral_finset_sum _ (fun i _ => integrable_partition_target_fidelity
    (mu i) (hmu i) (M i) (c i • P i) (hM i) ((hP i).smul (hc i)))]
  apply (Finset.sum_le_sum (fun i _ => integral_partition_target_projector_le
    (mu i) (hmu i) (M i) (P i) (hM i) (hP i) (hPP i) (c i) (hc i))).trans
  exact Cloning.Projector.block_fidelity_le_of_mass_le Finset.univ
    (fun i => (M i).trace.re) (fun i => c i*(P i).trace.re^2)
    (fun i => (partitionDimension (mu i) (hmu i) : ℝ)) _
    (fun i _ => trace_re_nonneg (hM i)) (fun i _ => mul_nonneg (hc i) (sq_nonneg _))
    (fun i _ => Nat.cast_pos.mpr (partitionDimension_pos (mu i) (hmu i))) le_rfl

end Cloning.PhysicalFlatConverse
