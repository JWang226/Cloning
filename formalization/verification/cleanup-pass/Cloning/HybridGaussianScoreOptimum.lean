import Cloning.HybridGaussianFlatBody
import Cloning.HybridScorePolytope
import Cloning.PCTPhysicalFidelityLAN

/-! The Gaussian optimum on the literal score-hyperplane box, expressed in
the proved whitening coordinates. Both averaging and optimization are actual:
normalized Lebesgue integral on the exact transported polytope, and all CPTP
hybrid competitors before the real-radius limit. -/
noncomputable section
open scoped ComplexOrder InnerProductSpace Topology BigOperators
open Filter MeasureTheory
namespace Cloning.PCTJointGaussianWhitening
open Cloning.Hybrid Cloning.PCTPhysicalFidelity
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
variable {A : Type*} [Fintype A] [LinearOrder A] {k s : ℕ}

def scorePhaseBody (p : A→ℝ) (hp : ∀a,0<p a)
    (b : OrthonormalBasis (Fin (k+1)) ℝ (EuclideanSpace ℝ A))
    (hb : b 0=sqrtSpectrum p) (s : ℕ) : PhaseBody k s where
  carrier := scoreUnitBody p hp b hb s
  compact := scoreUnitBody_compact p hp b hb s
  convex := scoreUnitBody_convex p hp b hb s
  zero_interior := scoreUnitBody_zero_interior p hp b hb s

/-- Membership in the averaged region is exactly the physical score and
oscillator coordinate cutoff, not a rectangular cutoff after whitening. -/
theorem scorePhaseBody_dilate_eq (p : A→ℝ) (hp : ∀a,0<p a)
    (b : OrthonormalBasis (Fin (k+1)) ℝ (EuclideanSpace ℝ A))
    (hb : b 0=sqrtSpectrum p) (s : ℕ) {L : ℝ} (hL : 0<L) :
    (scorePhaseBody p hp b hb s).dilate L=
      {ξ : PhaseSpace k s | (∀a,|unwhiten p b ξ.1 a|≤L) ∧
        (∀j,|(ξ.2 j).re|≤L ∧ |(ξ.2 j).im|≤L)} :=
  (scoreWindow_eq_dilate p hp b hb s hL).symm

/-- The exact normalized flat-prior optimization on the transported physical
score box and oscillator box at radius L. -/
def scoreGaussianOptimal (p : SimpleSpectrum (k+1))
    (b : OrthonormalBasis (Fin (k+1)) ℝ (EuclideanSpace ℝ (Fin (k+1))))
    (hb : b 0=sqrtSpectrum p.eigenvalue) (e : Fin s ≃ PairIndex (k+1))
    (g L : ℝ) : ℝ :=
  sSup (Set.range fun Λ : HybridChannel k s =>
    (volume.real ((scorePhaseBody p.eigenvalue p.positive b hb s).dilate L))⁻¹ *
      ∫ ξ in (scorePhaseBody p.eigenvalue p.positive b hb s).dilate L,
        orbitPayoff (Real.sqrt g) Λ (reference p e) (reference p e) ξ)

theorem scoreGaussianOptimal_eq (p : SimpleSpectrum (k+1))
    (b : OrthonormalBasis (Fin (k+1)) ℝ (EuclideanSpace ℝ (Fin (k+1))))
    (hb : b 0=sqrtSpectrum p.eigenvalue) (e : Fin s ≃ PairIndex (k+1))
    (g : ℝ) {L : ℝ} (hL : 0<L) :
    scoreGaussianOptimal p b hb e g L=
      (scorePhaseBody p.eigenvalue p.positive b hb s).optimalPayoff
        (Real.sqrt g) (reference p e) (reference p e) L := by
  unfold scoreGaussianOptimal PhaseBody.optimalPayoff
  congr 1
  apply congrArg Set.range
  funext Λ
  exact ((scorePhaseBody p.eigenvalue p.positive b hb s).payoff_eq_normalized_dilate
    (Real.sqrt g) Λ (reference p e) (reference p e) hL).symm

/-- The full Gaussian amplification theorem at the actual physical score
window. No product, covariance, or Gaussian restriction is imposed on the
channel supremum, and L ranges over all real radii. -/
theorem scoreGaussianOptimal_tendsto (p : SimpleSpectrum (k+1))
    (b : OrthonormalBasis (Fin (k+1)) ℝ (EuclideanSpace ℝ (Fin (k+1))))
    (hb : b 0=sqrtSpectrum p.eigenvalue) (e : Fin s ≃ PairIndex (k+1))
    (g : ℝ) (hg : 1<g) :
    Tendsto (scoreGaussianOptimal p b hb e g) atTop (𝓝 (universalValue g p)) := by
  have h := (scorePhaseBody p.eigenvalue p.positive b hb s).gaussian_optimalPayoff_tendsto
    (fun _ => 1/2) (fun _ => by norm_num) g hg
    (fun i => p.ratio (e i)) (fun i => (p.ratio_pos (e i)).le) (fun i => p.ratio_lt_one (e i))
  have hprod := e.prod_comp (fun ij => Thermal.modeFactor g (p.ratio ij))
  have hlim : Tendsto ((scorePhaseBody p.eigenvalue p.positive b hb s).optimalPayoff
      (Real.sqrt g) (reference p e) (reference p e)) atTop (𝓝 (universalValue g p)) := by
    simpa only [reference,universalValue,classicalValue,orbitalValue,
      Nat.cast_add,Nat.cast_one,add_sub_cancel_right,hprod] using h
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
  exact (scoreGaussianOptimal_eq p b hb e g hL).symm

/-- The named flat-prior converse on the same actual score window. -/
theorem scoreGaussianOptimal_limsup_le (p : SimpleSpectrum (k+1))
    (b : OrthonormalBasis (Fin (k+1)) ℝ (EuclideanSpace ℝ (Fin (k+1))))
    (hb : b 0=sqrtSpectrum p.eigenvalue) (e : Fin s ≃ PairIndex (k+1))
    (g : ℝ) (hg : 1<g) :
    limsup (scoreGaussianOptimal p b hb e g) atTop≤universalValue g p :=
  (scoreGaussianOptimal_tendsto p b hb e g hg).limsup_eq.le

end Cloning.PCTJointGaussianWhitening
