import Cloning.PCTJointGaussianChart
import Cloning.HybridFlatBox

/-! The literal trace-zero score box, transported through the constructed
whitening chart. Its product with the oscillator box is a compact convex body
with zero in its interior, so real-radius flat-prior theorems apply to the
manuscript's score window as well as rectangular whitening windows. -/
noncomputable section
open scoped Topology BigOperators
open Filter MeasureTheory
namespace Cloning.PCTJointGaussianWhitening
open Cloning.Hybrid Cloning.PCTJointGaussianLaw
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {A : Type*} [Fintype A] [LinearOrder A] {k : ℕ}

theorem oscillatorBox_convex (s : ℕ) :
    Convex ℝ (Cloning.MultimodeCoherent.phaseSpaceUnitBox s) := by
  intro x hx y hy a c ha hc hac
  have hbound {u v : ℝ} (hu : |u|≤1) (hv : |v|≤1) : |a*u+c*v|≤1 := by
    calc
      |a*u+c*v|≤|a*u|+|c*v| := abs_add_le _ _
      _ = a*|u|+c*|v| := by rw [abs_mul,abs_mul,abs_of_nonneg ha,abs_of_nonneg hc]
      _ ≤ 1 := by nlinarith
  intro j
  exact ⟨by simpa using hbound (hx j).1 (hy j).1,
    by simpa using hbound (hx j).2 (hy j).2⟩

theorem oscillatorBox_zero_interior (s : ℕ) :
    (0 : Fin s→ℂ) ∈ interior (Cloning.MultimodeCoherent.phaseSpaceUnitBox s) := by
  apply mem_interior_iff_mem_nhds.mpr
  apply mem_of_superset (Metric.ball_mem_nhds (0 : Fin s→ℂ) (by norm_num : (0:ℝ)<1))
  intro z hz j
  have hn : ‖z‖<1 := by simpa only [Metric.mem_ball,dist_zero_right] using hz
  exact ⟨(Complex.abs_re_le_norm _).trans ((norm_le_pi_norm z j).trans hn.le),
    (Complex.abs_im_le_norm _).trans ((norm_le_pi_norm z j).trans hn.le)⟩

def scoreUnitBody (p : A→ℝ) (hp : ∀a,0<p a)
    (b : OrthonormalBasis (Fin (k+1)) ℝ (EuclideanSpace ℝ A))
    (hb : b 0 = sqrtSpectrum p) (s : ℕ) : Set (PhaseSpace k s) :=
  ((whiteningContinuousEquiv p hp b hb) '' Metric.closedBall (0 : scoreHyperplane A) 1) ×ˢ
    Cloning.MultimodeCoherent.phaseSpaceUnitBox s

theorem mem_scoreUnitBody (p : A→ℝ) (hp : ∀a,0<p a)
    (b : OrthonormalBasis (Fin (k+1)) ℝ (EuclideanSpace ℝ A))
    (hb : b 0 = sqrtSpectrum p) (s : ℕ) (ξ : PhaseSpace k s) :
    ξ∈scoreUnitBody p hp b hb s ↔
      (∀a,|unwhiten p b ξ.1 a|≤1) ∧ (∀j,|(ξ.2 j).re|≤1 ∧ |(ξ.2 j).im|≤1) := by
  have he : ξ.1∈(whiteningContinuousEquiv p hp b hb) ''
      Metric.closedBall (0 : scoreHyperplane A) 1 ↔ ∀a,|unwhiten p b ξ.1 a|≤1 := by
    let e := whiteningContinuousEquiv p hp b hb
    change ξ.1 ∈ e.toEquiv '' Metric.closedBall (0 : scoreHyperplane A) 1 ↔ _
    rw [e.toEquiv.image_eq_preimage_symm]
    change dist (e.symm ξ.1) 0 ≤ 1 ↔ _
    rw [dist_zero_right]
    change ‖unwhiten p b ξ.1‖ ≤ 1 ↔ _
    rw [pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ)≤1)]
    simp only [Real.norm_eq_abs]
  exact and_congr_left (fun _ => he)

theorem scoreUnitBody_compact (p : A→ℝ) (hp : ∀a,0<p a)
    (b : OrthonormalBasis (Fin (k+1)) ℝ (EuclideanSpace ℝ A))
    (hb : b 0 = sqrtSpectrum p) (s : ℕ) : IsCompact (scoreUnitBody p hp b hb s) :=
  ((isCompact_closedBall (0 : scoreHyperplane A) 1).image
    (whiteningContinuousEquiv p hp b hb).continuous).prod
    (Cloning.MultimodeCoherent.phaseSpaceUnitBox_compact s)

theorem scoreUnitBody_convex (p : A→ℝ) (hp : ∀a,0<p a)
    (b : OrthonormalBasis (Fin (k+1)) ℝ (EuclideanSpace ℝ A))
    (hb : b 0 = sqrtSpectrum p) (s : ℕ) : Convex ℝ (scoreUnitBody p hp b hb s) :=
  ((convex_closedBall (0 : scoreHyperplane A) 1).linear_image
    (whiteningContinuousEquiv p hp b hb).toLinearMap).prod (oscillatorBox_convex s)

theorem scoreUnitBody_zero_interior (p : A→ℝ) (hp : ∀a,0<p a)
    (b : OrthonormalBasis (Fin (k+1)) ℝ (EuclideanSpace ℝ A))
    (hb : b 0 = sqrtSpectrum p) (s : ℕ) :
    (0 : PhaseSpace k s) ∈ interior (scoreUnitBody p hp b hb s) := by
  rw [scoreUnitBody,interior_prod_eq]
  refine ⟨?_,oscillatorBox_zero_interior s⟩
  apply (whiteningContinuousEquiv p hp b hb).isOpenMap.image_interior_subset
  refine ⟨0,Metric.ball_subset_interior_closedBall (Metric.mem_ball_self (by norm_num)),?_⟩
  exact map_zero _

theorem unwhiten_smul (p : A→ℝ) (hp : ∀a,0<p a)
    (b : OrthonormalBasis (Fin (k+1)) ℝ (EuclideanSpace ℝ A))
    (hb : b 0 = sqrtSpectrum p) (c : ℝ) (x : Fin k→ℝ) :
    unwhiten p b (c • x) = c • unwhiten p b x := by
  exact congrArg Subtype.val ((whiteningContinuousEquiv p hp b hb).symm.map_smul c x)

/-- Exact scaling identifies the nonrectangular whitened body with the
literal score-hyperplane and oscillator-coordinate box at radius L. -/
theorem smul_scoreWindow_iff (p : A→ℝ) (hp : ∀a,0<p a)
    (b : OrthonormalBasis (Fin (k+1)) ℝ (EuclideanSpace ℝ A))
    (hb : b 0 = sqrtSpectrum p) (s : ℕ) {L : ℝ} (hL : 0<L) (ξ : PhaseSpace k s) :
    ((∀a,|unwhiten p b (L • ξ).1 a|≤L) ∧
      (∀j,|((L • ξ).2 j).re|≤L ∧ |((L • ξ).2 j).im|≤L)) ↔
      ξ∈scoreUnitBody p hp b hb s := by
  have he (t : ℝ) : |L*t|≤L ↔ |t|≤1 := by
    rw [abs_mul,abs_of_pos hL]
    simpa only [mul_one] using
      (mul_le_mul_iff_right₀ hL : L*|t|≤L*1 ↔ |t|≤1)
  rw [mem_scoreUnitBody]
  simp only [Prod.smul_fst,Prod.smul_snd,unwhiten_smul p hp b hb,
    Pi.smul_apply,Complex.smul_re,Complex.smul_im,smul_eq_mul,he]

theorem scoreWindow_eq_dilate (p : A→ℝ) (hp : ∀a,0<p a)
    (b : OrthonormalBasis (Fin (k+1)) ℝ (EuclideanSpace ℝ A))
    (hb : b 0 = sqrtSpectrum p) (s : ℕ) {L : ℝ} (hL : 0<L) :
    {ξ : PhaseSpace k s | (∀a,|unwhiten p b ξ.1 a|≤L) ∧
      (∀j,|(ξ.2 j).re|≤L ∧ |(ξ.2 j).im|≤L)} =
      (fun ξ => L • ξ) '' scoreUnitBody p hp b hb s := by
  ext ξ
  constructor
  · intro hξ
    have he : L • (L⁻¹ • ξ)=ξ := smul_inv_smul₀ hL.ne' ξ
    refine ⟨L⁻¹ • ξ,?_,he⟩
    apply (smul_scoreWindow_iff p hp b hb s hL (L⁻¹ • ξ)).mp
    simpa only [he] using hξ
  · rintro ⟨z,hz,rfl⟩
    exact (smul_scoreWindow_iff p hp b hb s hL z).mpr hz

end Cloning.PCTJointGaussianWhitening
