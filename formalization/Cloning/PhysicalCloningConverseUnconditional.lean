import Cloning.PhysicalCloningConverseKnown
import Cloning.TensorLANEmbeddingCompactLAN

/-! Unconditional converses for the literal physical cloning problem.
The actual compact-window mixed LAN channels discharge every analytic
approximation premise in the all-channel Gaussian converse. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace Cloning.PhysicalCloningConverse
open Cloning.TensorCloning Cloning.PCTJointGaussianWhitening Cloning.TensorLAN
set_option backward.isDefEq.respectTransparency false
variable {k : ℕ}

/-- The known-spectrum upper bound over all physical quantum channels. -/
theorem limsup_knownSpectrumValue_le (p : SimpleSpectrum (k+1))
    (m : ℕ → ℕ) (g : ℝ) (hg : 1 < g)
    (hratio : Tendsto (fun n => (m n : ℝ)/(n : ℝ)) atTop (𝓝 g)) :
    limsup (fun n => knownSpectrumValue n (m n) p) atTop ≤ orbitalValue g p := by
  obtain ⟨b,hb⟩ := exists_whitening_frame (by simp : Fintype.card (Fin (k+1)) = k+1)
    p.eigenvalue (fun a => (p.positive a).le) p.normalized
  let e := (Fintype.equivFin (PairIndex (k+1))).symm
  exact limsup_knownSpectrumValue_le_of_compactWindowLAN p b e
    (physicalCompactWindowLAN p b hb e) m g hg hratio

/-- The unknown-spectrum upper bound at every interior base spectrum. -/
theorem limsup_unknownSpectrumValue_le
    (S : Set (SimpleSpectrum (k+1))) (p : SimpleSpectrum (k+1)) (hp : p ∈ interior S)
    (m : ℕ → ℕ) (g : ℝ) (hg : 1 < g)
    (hratio : Tendsto (fun n => (m n : ℝ)/(n : ℝ)) atTop (𝓝 g)) :
    limsup (fun n => unknownSpectrumValue n (m n) S) atTop ≤ universalValue g p := by
  obtain ⟨b,hb⟩ := exists_whitening_frame (by simp : Fintype.card (Fin (k+1)) = k+1)
    p.eigenvalue (fun a => (p.positive a).le) p.normalized
  let e := (Fintype.equivFin (PairIndex (k+1))).symm
  exact limsup_unknownSpectrumValue_le_of_compactWindowLAN S p hp b hb e
    (physicalCompactWindowLAN p b hb e) m g hg hratio

/-- Regular-closure sets include their boundary spectra. No compactness or
LAN hypothesis is needed in the actual physical upper bound. -/
theorem limsup_unknownSpectrumValue_infimum
    (S : Set (SimpleSpectrum (k+1))) (hSne : S.Nonempty)
    (hS : closure (interior S) = S)
    (m : ℕ → ℕ) (g : ℝ) (hg : 1 < g)
    (hratio : Tendsto (fun n => (m n : ℝ)/(n : ℝ)) atTop (𝓝 g)) :
    limsup (fun n => unknownSpectrumValue n (m n) S) atTop ≤
      ⨅ p : S, universalValue g p.val := by
  apply universal_infimum_regularClosure (by linarith) S hSne hS
  intro p hp
  exact limsup_unknownSpectrumValue_le S p hp m g hg hratio

end Cloning.PhysicalCloningConverse
