import Cloning.AmplifierWeylCoherent
import Cloning.WeylChannel

/-! Actual Weyl covariance of the physical quantum-limited amplifier,
proved from its complete coherent matrix kernel and the exact Weyl phases. -/
noncomputable section
open scoped ComplexOrder InnerProductSpace Topology BigOperators
namespace Cloning.BosonicAmplifier
open Cloning.InfiniteTraceClass
open Cloning.ComplexCoherent
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

lemma amplifier_phase_split {s t r : ℝ} (h : s + t ^ 2 * r = r) (a v : ℂ) :
    displacementPhase (-a) ((s : ℂ) * v) *
      displacementPhase (-((t * r : ℝ) : ℂ) * a) ((t : ℂ) * v) =
      displacementPhase (-((r : ℂ) * a)) v := by
  simp only [displacementPhase, ← Complex.exp_add]
  congr 1
  push_cast
  simp only [map_neg, map_mul, Complex.conj_ofReal]
  have hc : (s : ℂ) + (t : ℂ) ^ 2 * (r : ℂ) = (r : ℂ) := by exact_mod_cast h
  linear_combination ((-(a * starRingEnd ℂ v) + starRingEnd ℂ a * v) / 2) * hc

lemma displacement_coherent_matrixCoefficient (a : ℂ) (A : TraceClass Fock) (v w : ℂ) :
    ⟪coherentVector v, (displacementTraceMap a A).1 (coherentVector w)⟫_ℂ =
      star (displacementPhase (-a) v) * displacementPhase (-a) w *
        ⟪coherentVector (-a + v), A.1 (coherentVector (-a + w))⟫_ℂ := by
  rw [displacementTraceMap, inner_sandwichCLM, ContinuousLinearMap.star_eq_adjoint,
    displacement_adjoint, displacement_coherentVector, displacement_coherentVector,
    map_smul, inner_smul_left, inner_smul_right]
  simp only [Complex.star_def]
  ring

/-- Exact covariance of the constructed countable-Kraus amplifier on all
complex trace-class inputs. The gain is the physical reciprocal attenuation. -/
theorem channel_weyl_covariant (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (a : ℂ) (A : TraceClass Fock) :
    (channel q hq0 hq1).toLinearMap (displacementTraceMap a A) =
      displacementTraceMap ((((Real.sqrt (1 - q))⁻¹ : ℝ) : ℂ) * a)
        ((channel q hq0 hq1).toLinearMap A) := by
  let s : ℝ := Real.sqrt (1 - q)
  let t : ℝ := Real.sqrt q
  let r : ℝ := s⁻¹
  have hs : 0 < s := Real.sqrt_pos.mpr (sub_pos.mpr hq1)
  have hs2 : s ^ 2 = 1 - q := Real.sq_sqrt (sub_nonneg.mpr hq1.le)
  have ht2 : t ^ 2 = q := Real.sq_sqrt hq0
  have hsr : (s : ℂ) * (r : ℂ) = 1 := by
    change (s : ℂ) * ((s⁻¹ : ℝ) : ℂ) = 1
    rw [← Complex.ofReal_mul, mul_inv_cancel₀ hs.ne', Complex.ofReal_one]
  have hsplit : s + t ^ 2 * r = r := by
    dsimp only [r]
    apply (mul_right_cancel₀ hs.ne')
    field_simp
    nlinarith [hs2, ht2]
  apply Subtype.ext
  apply continuousLinearMap_ext_coherent
  intro w
  apply sub_eq_zero.mp
  apply coherentVector_total
  intro v
  change ⟪coherentVector v,
    ((channel q hq0 hq1).toLinearMap (displacementTraceMap a A)).1 (coherentVector w) -
      (displacementTraceMap ((r : ℂ) * a) ((channel q hq0 hq1).toLinearMap A)).1
        (coherentVector w)⟫_ℂ = 0
  rw [inner_sub_right, sub_eq_zero]
  rw [channel_coherent_matrixCoefficient, displacement_coherent_matrixCoefficient,
    displacement_coherent_matrixCoefficient, channel_coherent_matrixCoefficient]
  change ((1 - q : ℂ) * ⟪coherentVector ((t : ℂ) * v), coherentVector ((t : ℂ) * w)⟫_ℂ) *
      (star (displacementPhase (-a) ((s : ℂ) * v)) * displacementPhase (-a) ((s : ℂ) * w) *
        ⟪coherentVector (-a + (s : ℂ) * v), A.1 (coherentVector (-a + (s : ℂ) * w))⟫_ℂ) =
    star (displacementPhase (-((r : ℂ) * a)) v) * displacementPhase (-((r : ℂ) * a)) w *
      (((1 - q : ℂ) *
        ⟪coherentVector ((t : ℂ) * (-((r : ℂ) * a) + v)),
          coherentVector ((t : ℂ) * (-((r : ℂ) * a) + w))⟫_ℂ) *
        ⟪coherentVector ((s : ℂ) * (-((r : ℂ) * a) + v)),
          A.1 (coherentVector ((s : ℂ) * (-((r : ℂ) * a) + w)))⟫_ℂ)
  have harg (z : ℂ) : (s : ℂ) * (-((r : ℂ) * a) + z) = -a + (s : ℂ) * z := by
    calc
      _ = -((s : ℂ) * (r : ℂ)) * a + (s : ℂ) * z := by ring
      _ = _ := by rw [hsr]; ring
  rw [harg, harg]
  have hnoise := inner_displacedCoherent (-((t * r : ℝ) : ℂ) * a) ((t : ℂ) * v) ((t : ℂ) * w)
  simp only [displacedCoherent, inner_smul_left, inner_smul_right] at hnoise
  have hargt (z : ℂ) : -((t * r : ℝ) : ℂ) * a + (t : ℂ) * z =
      (t : ℂ) * (-((r : ℂ) * a) + z) := by push_cast; ring
  rw [hargt, hargt] at hnoise
  rw [← hnoise, ← amplifier_phase_split hsplit a v, ← amplifier_phase_split hsplit a w]
  simp only [Complex.star_def, map_mul]
  ring

/-- The physical gain convention used in the Gaussian orbital model. -/
theorem channel_weyl_covariant_gain (g : ℝ) (hg : 1 < g) (a : ℂ) (A : TraceClass Fock) :
    (channel (1 - 1 / g) (gainNoise_nonneg hg) (gainNoise_lt_one hg)).toLinearMap
      (displacementTraceMap a A) =
    displacementTraceMap ((Real.sqrt g : ℂ) * a)
      ((channel (1 - 1 / g) (gainNoise_nonneg hg) (gainNoise_lt_one hg)).toLinearMap A) := by
  have he : (Real.sqrt (1 - (1 - 1 / g)))⁻¹ = Real.sqrt g := by
    rw [show 1 - (1 - 1 / g) = g⁻¹ by ring, Real.sqrt_inv, inv_inv]
  simpa only [he] using channel_weyl_covariant (1 - 1 / g)
    (gainNoise_nonneg hg) (gainNoise_lt_one hg) a A

end Cloning.BosonicAmplifier
