import Cloning.HeisenbergDualWeyl

/-! Continuity of the actual scalar Weyl multiplier follows from normal
trace duality and the nonvanishing vacuum Gaussian, without a characteristic
function regularity assumption. -/

noncomputable section
open scoped ComplexOrder InnerProductSpace Topology BigOperators
open Filter

namespace Cloning.MultimodeCoherent
open Cloning.InfiniteTraceClass
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
variable {d : ℕ}

/-- A positive trace-class input has a continuous Weyl characteristic
function. The proof uses its convergent rank-one expansion. -/
theorem continuous_tracePairing_displacement_of_nonneg
    (T : TraceClass (Fock d)) (hT : 0 ≤ T.1) :
    Continuous (fun b => tracePairing T (displacement b)) := by
  obtain ⟨w, e, _⟩ := exists_hilbertBasis ℂ (Fock d)
  let v : w → Fock d := fun i => CFC.sqrt T.1 (e i)
  have hs : HasSum (fun i => vectorProjector (v i)) T :=
    positive_rankOne_series hT T.2 e
  have hm : Summable (fun i => ‖vectorProjector (v i)‖) :=
    (positive_rankOne_mass hT T.2 e).summable
  have heq (b : Fin d → ℂ) :
      (∑' i, ⟪v i, displacement b (v i)⟫_ℂ) = tracePairing T (displacement b) := by
    have h := hs.mapL (tracePairingCLM.flip (displacement b))
    simpa only [ContinuousLinearMap.flip_apply, tracePairingCLM_apply,
      show ∀ x : Fock d, vectorProjector x = rankOneOperator x x from fun _ => rfl,
      tracePairing_rankOneOperator] using h.tsum_eq
  apply continuous_iff_continuousAt.mpr
  intro b
  have hl : Tendsto (fun b => ∑' i, ⟪v i, displacement b (v i)⟫_ℂ) (𝓝 b)
      (𝓝 (∑' i, ⟪v i, displacement b (v i)⟫_ℂ)) := by
    apply tendsto_tsum_of_dominated_convergence hm
    · intro i
      exact (continuous_const.inner (continuous_displacement (v i))).tendsto b
    · apply Eventually.of_forall
      intro a i
      calc
        ‖⟪v i, displacement a (v i)⟫_ℂ‖ ≤ ‖v i‖ * ‖displacement a (v i)‖ :=
          norm_inner_le_norm _ _
        _ = ‖vectorProjector (v i)‖ := by rw [displacement_norm, norm_vectorProjector, pow_two]
  simpa only [heq] using hl

/-- Every complex trace-class operator has a continuous Weyl characteristic
function, including off-diagonal and non-self-adjoint inputs. -/
theorem continuous_tracePairing_displacement (T : TraceClass (Fock d)) :
    Continuous (fun b => tracePairing T (displacement b)) := by
  have hsa (A : TraceClass (Fock d)) (hA : IsSelfAdjoint A.1) :
      Continuous (fun b => tracePairing A (displacement b)) := by
    have h := (continuous_tracePairing_displacement_of_nonneg _
      (TraceClass.positivePart_nonneg A hA)).sub
      (continuous_tracePairing_displacement_of_nonneg _ (TraceClass.negativePart_nonneg A hA))
    convert h using 1
    funext b
    have hh := congrArg (fun T : TraceClass (Fock d) => tracePairing T (displacement b))
      (TraceClass.positivePart_sub_negativePart A hA)
    simpa only [← tracePairingCLM_apply, map_sub, ContinuousLinearMap.sub_apply] using hh.symm
  have h := (hsa _ (TraceClass.realComponent_isSelfAdjoint T)).add
    ((continuous_const : Continuous (fun _ : Fin d → ℂ => Complex.I)).mul
      (hsa _ (TraceClass.imaginaryComponent_isSelfAdjoint T)))
  convert h using 1
  funext b
  have hh := congrArg (fun T : TraceClass (Fock d) => tracePairing T (displacement b))
    (TraceClass.realComponent_add_I_smul_imaginaryComponent T)
  simpa only [← tracePairingCLM_apply, map_add, map_smul,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul] using hh.symm

/-- The vacuum characteristic function never vanishes. -/
theorem vacuum_characteristic_ne_zero (b : Fin d → ℂ) :
    ⟪coherentVector 0, displacement b (coherentVector 0)⟫_ℂ ≠ 0 := by
  rw [vacuum_characteristic]
  exact Finset.prod_ne_zero_iff.mpr (fun i _ => Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _))

/-- Normality supplies continuity of the scalar multiplier of an actual
bounded covariant trace-class map. -/
theorem continuous_traceClass_weylMultiplier
    (Φ : TraceClass (Fock d) →L[ℂ] TraceClass (Fock d)) (r : ℝ)
    (hΦ : ∀ a T, Φ (displacementTraceMap a T) =
      displacementTraceMap (r • a) (Φ T)) :
    Continuous (weylMultiplier (heisenbergDual Φ) r) := by
  have heq (b : Fin d → ℂ) : weylMultiplier (heisenbergDual Φ) r b =
      tracePairing (Φ (coherentProjector 0)) (displacement b) /
        ⟪coherentVector 0, displacement (r • b) (coherentVector 0)⟫_ℂ := by
    apply (eq_div_iff (vacuum_characteristic_ne_zero (r • b))).mpr
    have h := congrArg (fun A : Fock d →L[ℂ] Fock d =>
      ⟪coherentVector 0, A (coherentVector 0)⟫_ℂ)
      (traceClass_covariant_weyl_multiplier Φ r hΦ b)
    simpa only [heisenbergDual_inner, ContinuousLinearMap.smul_apply,
      inner_smul_right] using h.symm
  have hfun := funext heq
  rw [hfun]
  apply (continuous_tracePairing_displacement (Φ (coherentProjector 0))).div
  · exact continuous_const.inner
      ((continuous_displacement (coherentVector 0)).comp (continuous_const.smul continuous_id))
  · exact fun b => vacuum_characteristic_ne_zero (r • b)

end Cloning.MultimodeCoherent
