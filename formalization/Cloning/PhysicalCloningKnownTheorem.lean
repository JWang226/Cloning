import Cloning.TensorLANEmbeddingCompactLAN
import Cloning.PhysicalCloningConverseKnown
import Cloning.TensorCloningAchievability

/-! The unconditional asymptotic known-spectrum cloning theorem for the actual
optimization over all physical CPTP maps. -/
noncomputable section
open scoped BigOperators Topology Classical InnerProductSpace
open Filter
namespace Cloning.TensorCloning
open Cloning.PCT Cloning.InfiniteTraceClass Cloning.TensorLAN
open Cloning.PCTJointGaussianWhitening Cloning.PhysicalCloningConverse
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
variable {k : ℕ}

theorem knownSpectrumValue_le_one (n m : ℕ) (p : SimpleSpectrum (k+1)) :
    knownSpectrumValue n m p ≤ 1 := by
  letI : Nonempty (QuantumChannel (Register (Fin n → Fin (k+1)))
      (Register (Fin m → Fin (k+1)))) :=
    ⟨knownSpectrumChannel n m (k+1) p.eigenvalue (fun a => (p.positive a).le) p.normalized⟩
  unfold knownSpectrumValue LAN.minimaxValue
  apply ciSup_le
  intro Φ
  have hb : BddBelow (Set.range (spectrumPayoff n m Φ p)) := by
    refine ⟨0,?_⟩
    rintro x ⟨U,rfl⟩
    exact spectrumPayoff_nonneg n m Φ p U
  exact (ciInf_le hb 1).trans (spectrumPayoff_le_one n m Φ p 1)

/-- The actual physical upper bound, with the whitening frame, root enumeration
and both LAN channels constructed internally. -/
theorem limsup_knownSpectrumValue_le (p : SimpleSpectrum (k+1))
    (m : ℕ → ℕ) (g : ℝ) (hg : 1 < g)
    (hratio : Tendsto (fun n => (m n : ℝ)/(n : ℝ)) atTop (𝓝 g)) :
    limsup (fun n => knownSpectrumValue n (m n) p) atTop ≤ orbitalValue g p := by
  obtain ⟨b,hb⟩ := exists_whitening_frame (by simp : Fintype.card (Fin (k+1)) = k+1)
    p.eigenvalue (fun a => (p.positive a).le) p.normalized
  let e := (Fintype.equivFin (PairIndex (k+1))).symm
  exact limsup_knownSpectrumValue_le_of_compactWindowLAN p b e
    (physicalCompactWindowLAN p b hb e) m g hg hratio

/-- Exact asymptotic optimal root fidelity on the complete fixed-spectrum
unitary orbit, optimized over every genuine physical channel. -/
theorem knownSpectrumValue_tendsto (p : SimpleSpectrum (k+1))
    (m : ℕ → ℕ) (g : ℝ) (hg : 1 < g)
    (hratio : Tendsto (fun n => (m n : ℝ)/(n : ℝ)) atTop (𝓝 g)) :
    Tendsto (fun n => knownSpectrumValue n (m n) p) atTop (𝓝 (orbitalValue g p)) := by
  have hm := output_size_tendsto m g (by linarith) hratio
  have hu := limsup_knownSpectrumValue_le p m g hg hratio
  have hb : atTop.IsBoundedUnder (· ≤ ·) (fun n => knownSpectrumValue n (m n) p) := by
    exact isBoundedUnder_of_eventually_le (Eventually.of_forall
      (fun n : ℕ => knownSpectrumValue_le_one n (m n) p))
  apply tendsto_order.mpr
  constructor
  · intro a ha
    have h := eventually_knownSpectrumValue_lower (fun n => n) m tendsto_id hm p g hg hratio
      (orbitalValue g p-a) (sub_pos.mpr ha)
    simpa only [sub_sub_cancel] using h
  · intro a ha
    exact eventually_lt_of_limsup_lt (hu.trans_lt ha) hb

end Cloning.TensorCloning
