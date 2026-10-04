import Cloning.AmplifierWeylMultimode
import Cloning.AmplifierWeylCovariance

/-! Exact actual multimode Weyl covariance, including arbitrary complex
input coherences and independent mode gains. -/
noncomputable section
open scoped ComplexOrder InnerProductSpace Topology BigOperators
namespace Cloning.MultimodeAmplifier
open Cloning.InfiniteTraceClass Cloning.MultimodeCoherent
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
variable {d : ℕ}

lemma amplifier_phase_split {s t r : Fin d → ℝ}
    (h : ∀ i, s i + t i ^ 2 * r i = r i) (a v : Fin d → ℂ) :
    displacementPhase (-a) (fun i => (s i : ℂ) * v i) *
      displacementPhase (fun i => -((t i * r i : ℝ) : ℂ) * a i)
        (fun i => (t i : ℂ) * v i) =
      displacementPhase (-(fun i => (r i : ℂ) * a i)) v := by
  simp only [displacementPhase, ← Finset.prod_mul_distrib, Pi.neg_apply]
  exact Finset.prod_congr rfl (fun i _ => Cloning.BosonicAmplifier.amplifier_phase_split (h i) (a i) (v i))

lemma displacement_coherent_matrixCoefficient (a : Fin d → ℂ)
    (A : TraceClass (Fock d)) (v w : Fin d → ℂ) :
    ⟪coherentVector v, (displacementTraceMap a A).1 (coherentVector w)⟫_ℂ =
      star (displacementPhase (-a) v) * displacementPhase (-a) w *
        ⟪coherentVector (-a + v), A.1 (coherentVector (-a + w))⟫_ℂ := by
  rw [displacementTraceMap, inner_sandwichCLM, ContinuousLinearMap.star_eq_adjoint,
    displacement_adjoint, displacement_coherentVector, displacement_coherentVector,
    map_smul, inner_smul_left, inner_smul_right]
  simp only [Complex.star_def]
  ring

/-- Weyl covariance is a theorem of the constructed CPTP channel, not a
hypothesis in its definition. -/
theorem channel_weyl_covariant (q : Fin d → ℝ)
    (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i < 1) (a : Fin d → ℂ) (A : TraceClass (Fock d)) :
    (channel q hq0 hq1).toLinearMap (displacementTraceMap a A) =
      displacementTraceMap (fun i => ((((Real.sqrt (1 - q i))⁻¹ : ℝ) : ℂ) * a i))
        ((channel q hq0 hq1).toLinearMap A) := by
  let s : Fin d → ℝ := fun i => Real.sqrt (1 - q i)
  let t : Fin d → ℝ := fun i => Real.sqrt (q i)
  let r : Fin d → ℝ := fun i => (s i)⁻¹
  let S : (Fin d → ℂ) → (Fin d → ℂ) := fun z i => (s i : ℂ) * z i
  let T : (Fin d → ℂ) → (Fin d → ℂ) := fun z i => (t i : ℂ) * z i
  let R : (Fin d → ℂ) → (Fin d → ℂ) := fun z i => (r i : ℂ) * z i
  let e : Fin d → ℂ := fun i => -((t i * r i : ℝ) : ℂ) * a i
  have hs (i : Fin d) : 0 < s i := Real.sqrt_pos.mpr (sub_pos.mpr (hq1 i))
  have hsr (i : Fin d) : (s i : ℂ) * (r i : ℂ) = 1 := by
    change (s i : ℂ) * (((s i)⁻¹ : ℝ) : ℂ) = 1
    rw [← Complex.ofReal_mul, mul_inv_cancel₀ (hs i).ne', Complex.ofReal_one]
  have hsplit (i : Fin d) : s i + t i ^ 2 * r i = r i := by
    have hs2 : s i ^ 2 = 1 - q i := Real.sq_sqrt (sub_nonneg.mpr (hq1 i).le)
    have ht2 : t i ^ 2 = q i := Real.sq_sqrt (hq0 i)
    dsimp only [r]
    apply mul_right_cancel₀ (hs i).ne'
    field_simp [(hs i).ne']
    nlinarith [hs2, ht2]
  apply Subtype.ext
  apply continuousLinearMap_ext_coherent
  intro w
  apply sub_eq_zero.mp
  apply coherentVector_total
  intro v
  change ⟪coherentVector v,
    ((channel q hq0 hq1).toLinearMap (displacementTraceMap a A)).1 (coherentVector w) -
      (displacementTraceMap (R a) ((channel q hq0 hq1).toLinearMap A)).1 (coherentVector w)⟫_ℂ = 0
  rw [inner_sub_right, sub_eq_zero]
  rw [channel_coherent_matrixCoefficient, displacement_coherent_matrixCoefficient,
    displacement_coherent_matrixCoefficient, channel_coherent_matrixCoefficient]
  change (((∏ i, (1 - q i) : ℝ) : ℂ) * ⟪coherentVector (T v), coherentVector (T w)⟫_ℂ) *
      (star (displacementPhase (-a) (S v)) * displacementPhase (-a) (S w) *
        ⟪coherentVector (-a + S v), A.1 (coherentVector (-a + S w))⟫_ℂ) =
    star (displacementPhase (-(R a)) v) * displacementPhase (-(R a)) w *
      ((((∏ i, (1 - q i) : ℝ) : ℂ) *
        ⟪coherentVector (T (-(R a) + v)), coherentVector (T (-(R a) + w))⟫_ℂ) *
        ⟪coherentVector (S (-(R a) + v)), A.1 (coherentVector (S (-(R a) + w)))⟫_ℂ)
  have harg (z : Fin d → ℂ) : S (-(R a) + z) = -a + S z := by
    funext i
    change (s i : ℂ) * (-((r i : ℂ) * a i) + z i) = -a i + (s i : ℂ) * z i
    calc
      _ = -((s i : ℂ) * (r i : ℂ)) * a i + (s i : ℂ) * z i := by ring
      _ = _ := by rw [hsr]; ring
  rw [harg, harg]
  have hnoise := inner_displacedCoherent e (T v) (T w)
  simp only [displacedCoherent, inner_smul_left, inner_smul_right] at hnoise
  have hargt (z : Fin d → ℂ) : e + T z = T (-(R a) + z) := by
    funext i
    dsimp only [e, T, R, Pi.add_apply, Pi.neg_apply]
    push_cast
    ring
  rw [hargt, hargt] at hnoise
  have hp (z : Fin d → ℂ) : displacementPhase (-a) (S z) * displacementPhase e (T z) =
      displacementPhase (-(R a)) z := amplifier_phase_split hsplit a z
  rw [← hnoise, ← hp v, ← hp w]
  simp only [Complex.star_def, map_mul]
  ring

/-- Common-gain covariance in exactly the convention of the orbital model. -/
theorem channel_weyl_covariant_gain (g : ℝ) (hg : 1 < g)
    (a : Fin d → ℂ) (A : TraceClass (Fock d)) :
    (channel (fun _ => 1 - 1 / g) (fun _ => Cloning.BosonicAmplifier.gainNoise_nonneg hg)
      (fun _ => Cloning.BosonicAmplifier.gainNoise_lt_one hg)).toLinearMap
        (displacementTraceMap a A) =
    displacementTraceMap ((Real.sqrt g) • a)
      ((channel (fun _ => 1 - 1 / g) (fun _ => Cloning.BosonicAmplifier.gainNoise_nonneg hg)
        (fun _ => Cloning.BosonicAmplifier.gainNoise_lt_one hg)).toLinearMap A) := by
  have he : (Real.sqrt (1 - (1 - 1 / g)))⁻¹ = Real.sqrt g := by
    rw [show 1 - (1 - 1 / g) = g⁻¹ by ring, Real.sqrt_inv, inv_inv]
  simpa only [he, Pi.smul_apply, Complex.real_smul] using channel_weyl_covariant
    (fun _ : Fin d => 1 - 1 / g) (fun _ => Cloning.BosonicAmplifier.gainNoise_nonneg hg)
    (fun _ => Cloning.BosonicAmplifier.gainNoise_lt_one hg) a A

end Cloning.MultimodeAmplifier
