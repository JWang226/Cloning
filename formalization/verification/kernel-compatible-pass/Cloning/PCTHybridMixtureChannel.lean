import Cloning.PCTHybridMixtureGaussian

/-! The physical tangent Gaussian average is an actual hybrid CPTP channel
on every input, and its action on the Gaussian–thermal reference is exactly
the PCT comparison state. -/
noncomputable section
open MeasureTheory
open scoped ComplexOrder InnerProductSpace Topology BigOperators
namespace Cloning.PCTHybridMixture
open Cloning.PCT Cloning.PCTReducedGaussian Cloning.PCTGaussianCovariance
open Cloning.PCTGaussianOutput Cloning.PCTJointGaussianLaw
open Cloning.PCTJointGaussianWhitening
open Cloning.InfiniteTraceClass Cloning.Hybrid Cloning.MultimodeCoherent
open Cloning.MultimodeCoherentGaussianMixture
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
variable {A : Type*} [Fintype A] [LinearOrder A] {k s d : ℕ}

/-- Gaussian averaging of the actual joint translation channels. Complete
positivity and trace preservation hold on the whole hybrid L¹ space. -/
def tangentMixtureChannel
    (u : Fin (s + 1) → Register (A × A)) (p : A → ℝ)
    (b : Fin (k + 1) → EuclideanSpace ℝ A) (e : Fin d ≃ OrbitalPair A)
    (g : ℝ) (hg : 1 < g) : HybridChannel k d := by
  letI := gaussianProductMeasure_probability (fun _ : Fin s => sub_pos.mpr hg)
  exact Channel.average (gaussianProductMeasure (fun _ : Fin s => g-1))
    (fun z => translationChannel (whitenedJointTangent u p b e z))
    (fun X => ((continuous_hybridTranslation X).comp
      (continuous_whitenedJointTangent u p b e)).aestronglyMeasurable)

@[simp] theorem tangentMixtureChannel_apply
    (u : Fin (s + 1) → Register (A × A)) (p : A → ℝ)
    (b : Fin (k + 1) → EuclideanSpace ℝ A) (e : Fin d ≃ OrbitalPair A)
    (g : ℝ) (hg : 1 < g) (X : HybridSpace k d) :
    (tangentMixtureChannel u p b e g hg).map X =
      ∫ z, hybridTranslation (whitenedJointTangent u p b e z) X
        ∂gaussianProductMeasure (fun _ : Fin s => g-1) := rfl

/-- The tangent mixture is contractive even on arbitrary complex L¹ inputs. -/
theorem norm_tangentMixtureChannel_le
    (u : Fin (s + 1) → Register (A × A)) (p : A → ℝ)
    (b : Fin (k + 1) → EuclideanSpace ℝ A) (e : Fin d ≃ OrbitalPair A)
    (g : ℝ) (hg : 1 < g) (X : HybridSpace k d) :
    ‖(tangentMixtureChannel u p b e g hg).map X‖ ≤ ‖X‖ := by
  letI := gaussianProductMeasure_probability (fun _ : Fin s => sub_pos.mpr hg)
  rw [tangentMixtureChannel_apply]
  calc
    _ ≤ ∫ z, ‖hybridTranslation (whitenedJointTangent u p b e z) X‖
        ∂gaussianProductMeasure (fun _ : Fin s => g-1) := norm_integral_le_integral_norm _
    _ = ‖X‖ := by simp only [norm_hybridTranslation, integral_const, probReal_univ, one_smul]

/-- Exact action of the actual CPTP tangent channel on the reference state. -/
theorem tangentMixtureChannel_gaussianThermalPositive
    (u : OrthonormalBasis (Fin (s + 1)) ℂ (Register (A × A)))
    (p : A → ℝ) (hp : ∀ a, 0 < p a)
    (hu : u 0 = coefficientVector (schmidtCoefficients p))
    (hgap : ∀ i j, i < j → 0 < p i - p j)
    (b : OrthonormalBasis (Fin (k + 1)) ℝ (EuclideanSpace ℝ A))
    (hb : b 0 = sqrtSpectrum p) (e : Fin d ≃ OrbitalPair A)
    (g : ℝ) (hg : 1 < g) :
    let q : Fin d → ℝ := fun i => p (e i).1.2 / p (e i).1.1
    let hq0 : ∀ i, 0 ≤ q i := fun i => (div_pos (hp _) (hp _)).le
    let hq1 : ∀ i, q i < 1 := fun i =>
      (div_lt_one (hp _)).mpr (by linarith [hgap _ _ (e i).2])
    (tangentMixtureChannel u p b e g hg).map
      (gaussianThermalPositive (fun _ : Fin k => 1/2) (fun _ => by norm_num) q hq0 hq1).1 =
      (pctGaussianThermalPositive (fun _ : Fin k => 1/2) (fun _ => by norm_num)
        g hg q hq0 hq1).1 := by
  exact tangent_hybrid_average_eq_pctGaussianThermalPositive u p hp hu hgap b hb e g hg

theorem tangentMixtureChannel_map_positive
    (u : OrthonormalBasis (Fin (s + 1)) ℂ (Register (A × A)))
    (p : A → ℝ) (hp : ∀ a, 0 < p a)
    (hu : u 0 = coefficientVector (schmidtCoefficients p))
    (hgap : ∀ i j, i < j → 0 < p i - p j)
    (b : OrthonormalBasis (Fin (k + 1)) ℝ (EuclideanSpace ℝ A))
    (hb : b 0 = sqrtSpectrum p) (e : Fin d ≃ OrbitalPair A)
    (g : ℝ) (hg : 1 < g) :
    let q : Fin d → ℝ := fun i => p (e i).1.2 / p (e i).1.1
    let hq0 : ∀ i, 0 ≤ q i := fun i => (div_pos (hp _) (hp _)).le
    let hq1 : ∀ i, q i < 1 := fun i =>
      (div_lt_one (hp _)).mpr (by linarith [hgap _ _ (e i).2])
    (gaussianThermalPositive (fun _ : Fin k => 1/2) (fun _ => by norm_num) q hq0 hq1).map
      (tangentMixtureChannel u p b e g hg) =
      pctGaussianThermalPositive (fun _ : Fin k => 1/2) (fun _ => by norm_num) g hg q hq0 hq1 := by
  apply Subtype.ext
  exact tangentMixtureChannel_gaussianThermalPositive u p hp hu hgap b hb e g hg

/-- The root fidelity of the actual tangent channel's output is the
manuscript's PCT scalar for a physical simple spectrum. -/
theorem tangentMixtureChannel_fidelity_eq_pctValue
    (u : OrthonormalBasis (Fin (s + 1)) ℂ (Register (Fin (k+1) × Fin (k+1))))
    (p : SimpleSpectrum (k+1))
    (hu : u 0 = coefficientVector (schmidtCoefficients p.eigenvalue))
    (b : OrthonormalBasis (Fin (k+1)) ℝ (EuclideanSpace ℝ (Fin (k+1))))
    (hb : b 0 = sqrtSpectrum p.eigenvalue) (e : Fin d ≃ PairIndex (k+1))
    (g : ℝ) (hg : 1 < g) :
    let R := gaussianThermalPositive (fun _ : Fin k => 1/2) (fun _ => by norm_num)
      (fun i => p.ratio (e i)) (fun i => (p.ratio_pos (e i)).le) (fun i => p.ratio_lt_one (e i))
    (R.map (tangentMixtureChannel u p.eigenvalue b e g hg)).rootFidelity R = pctValue g p := by
  dsimp only
  simp only [SimpleSpectrum.ratio]
  rw [tangentMixtureChannel_map_positive u p.eigenvalue p.positive hu
    (fun i j hij => sub_pos.mpr (p.strictAnti hij)) b hb e g hg]
  simpa only [SimpleSpectrum.ratio] using
    pctGaussianThermalPositive_rootFidelity_eq_pctValue
      (fun _ : Fin k => 1/2) (fun _ => by norm_num) g hg p e

/-- The required whitening frame is constructed from the spectrum. The
result supplies an actual hybrid CPTP channel with the exact PCT fidelity. -/
theorem exists_tangentMixtureChannel_fidelity
    (u : OrthonormalBasis (Fin (s + 1)) ℂ (Register (Fin (k+1) × Fin (k+1))))
    (p : SimpleSpectrum (k+1))
    (hu : u 0 = coefficientVector (schmidtCoefficients p.eigenvalue))
    (e : Fin d ≃ PairIndex (k+1)) (g : ℝ) (hg : 1 < g) :
    ∃ b : OrthonormalBasis (Fin (k+1)) ℝ (EuclideanSpace ℝ (Fin (k+1))),
      b 0 = sqrtSpectrum p.eigenvalue ∧
      let R := gaussianThermalPositive (fun _ : Fin k => 1/2) (fun _ => by norm_num)
        (fun i => p.ratio (e i)) (fun i => (p.ratio_pos (e i)).le) (fun i => p.ratio_lt_one (e i))
      (R.map (tangentMixtureChannel u p.eigenvalue b e g hg)).rootFidelity R = pctValue g p := by
  obtain ⟨b, hb⟩ := exists_whitening_frame (by simp : Fintype.card (Fin (k+1)) = k+1)
    p.eigenvalue (fun i => (p.positive i).le) p.normalized
  exact ⟨b, hb, tangentMixtureChannel_fidelity_eq_pctValue u p hu b hb e g hg⟩

end Cloning.PCTHybridMixture
