import Cloning.PhysicalCloningConverseChart

/-! The actual topology of simple normalized spectra and the regular-closure
step for the unknown-spectrum physical converse. -/
noncomputable section
open scoped Topology BigOperators
open Filter
namespace Cloning
set_option backward.isDefEq.respectTransparency false
variable {d : ℕ}

instance SimpleSpectrum.instTopologicalSpace : TopologicalSpace (SimpleSpectrum d) :=
  TopologicalSpace.induced SimpleSpectrum.eigenvalue inferInstance

theorem SimpleSpectrum.eigenvalue_injective :
    Function.Injective (SimpleSpectrum.eigenvalue : SimpleSpectrum d → Fin d → ℝ) := by
  intro p q h
  cases p
  cases q
  cases h
  rfl

theorem SimpleSpectrum.isEmbedding_eigenvalue :
    Topology.IsEmbedding (SimpleSpectrum.eigenvalue : SimpleSpectrum d → Fin d → ℝ) :=
  ⟨⟨rfl⟩, SimpleSpectrum.eigenvalue_injective⟩

instance SimpleSpectrum.instT2Space : T2Space (SimpleSpectrum d) :=
  SimpleSpectrum.isEmbedding_eigenvalue.t2Space

theorem SimpleSpectrum.continuous_eigenvalue :
    Continuous (SimpleSpectrum.eigenvalue : SimpleSpectrum d → Fin d → ℝ) :=
  SimpleSpectrum.isEmbedding_eigenvalue.continuous

theorem SimpleSpectrum.continuous_ratio (ij : PairIndex d) :
    Continuous (fun p : SimpleSpectrum d => p.ratio ij) := by
  unfold SimpleSpectrum.ratio
  exact ((continuous_apply ij.val.2).comp SimpleSpectrum.continuous_eigenvalue).div
    ((continuous_apply ij.val.1).comp SimpleSpectrum.continuous_eigenvalue)
    (fun p => (p.positive ij.val.1).ne')

theorem continuous_orbitalValue {g : ℝ} (hg : 0 < g) :
    Continuous (orbitalValue g : SimpleSpectrum d → ℝ) := by
  unfold orbitalValue
  apply continuous_finset_prod
  intro ij _
  apply continuous_iff_continuousAt.mpr
  intro p
  exact (Thermal.modeFactor_continuousAt (add_pos hg (p.ratio_pos ij)).ne').comp
    (f := fun q : SimpleSpectrum d => (g, q.ratio ij)) (x := p)
    (continuousAt_const.prodMk (SimpleSpectrum.continuous_ratio ij).continuousAt)

theorem continuous_universalValue {g : ℝ} (hg : 0 < g) :
    Continuous (universalValue g : SimpleSpectrum d → ℝ) :=
  continuous_const.mul (continuous_orbitalValue hg)

namespace PhysicalCloningConverse

/-- A bound proved on interior base spectra extends to every point of a
regular closed spectral set through the concrete spectral topology. -/
theorem universal_bound_regularClosure {g a : ℝ} (hg : 0 < g)
    (K : Set (SimpleSpectrum d)) (hK : closure (interior K) = K)
    (hbound : ∀ p ∈ interior K, a ≤ universalValue g p) :
    ∀ p ∈ K, a ≤ universalValue g p := by
  have hc : IsClosed {p : SimpleSpectrum d | a ≤ universalValue g p} :=
    isClosed_le continuous_const (continuous_universalValue hg)
  have hs : closure (interior K) ⊆ {p : SimpleSpectrum d | a ≤ universalValue g p} :=
    closure_minimal hbound hc
  rw [hK] at hs
  exact hs

theorem universal_infimum_regularClosure {g a : ℝ} (hg : 0 < g)
    (K : Set (SimpleSpectrum d)) (hKne : K.Nonempty)
    (hK : closure (interior K) = K)
    (hbound : ∀ p ∈ interior K, a ≤ universalValue g p) :
    a ≤ ⨅ p : K, universalValue g p.val := by
  letI : Nonempty K := hKne.to_subtype
  apply le_ciInf
  intro p
  exact universal_bound_regularClosure hg K hK hbound p.val p.property

end PhysicalCloningConverse
end Cloning
