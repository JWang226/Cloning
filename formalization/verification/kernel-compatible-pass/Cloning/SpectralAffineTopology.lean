import Cloning.PhysicalCloningConverseSpectrum

/-! The spectral topology is the open positive ordered chamber of the full
trace-one affine hyperplane. In particular the manuscript's ambient relative
interior condition transfers to the physical unknown-spectrum theorem. -/
noncomputable section
open scoped Topology BigOperators
namespace Cloning
set_option backward.isDefEq.respectTransparency false
variable {d : ℕ}

/-- The full trace-one affine hyperplane, without positivity or ordering. -/
def SpectralAffine (d : ℕ) := {p : Fin d → ℝ // ∑ i, p i = 1}

instance SpectralAffine.instTopologicalSpace : TopologicalSpace (SpectralAffine d) :=
  inferInstanceAs (TopologicalSpace {p : Fin d → ℝ // ∑ i, p i = 1})

instance SpectralAffine.instT2Space : T2Space (SpectralAffine d) :=
  inferInstanceAs (T2Space {p : Fin d → ℝ // ∑ i, p i = 1})

def SimpleSpectrum.toAffine (p : SimpleSpectrum d) : SpectralAffine d :=
  ⟨p.eigenvalue,p.normalized⟩

theorem SimpleSpectrum.isEmbedding_toAffine :
    Topology.IsEmbedding (SimpleSpectrum.toAffine : SimpleSpectrum d → SpectralAffine d) := by
  exact Topology.IsEmbedding.subtypeVal.of_comp_iff.mp SimpleSpectrum.isEmbedding_eigenvalue

theorem SimpleSpectrum.range_toAffine :
    Set.range (SimpleSpectrum.toAffine : SimpleSpectrum d → SpectralAffine d) =
      {p | (∀ i, 0 < p.val i) ∧ StrictAnti p.val} := by
  ext p
  constructor
  · rintro ⟨q,rfl⟩
    exact ⟨q.positive,q.strictAnti⟩
  · rintro ⟨hp,ha⟩
    exact ⟨⟨p.val,hp,ha,p.property⟩,rfl⟩

theorem SimpleSpectrum.isOpenEmbedding_toAffine :
    Topology.IsOpenEmbedding (SimpleSpectrum.toAffine : SimpleSpectrum d → SpectralAffine d) := by
  refine ⟨SimpleSpectrum.isEmbedding_toAffine, ?_⟩
  rw [SimpleSpectrum.range_toAffine]
  have hp : IsOpen {p : SpectralAffine d | ∀ i, 0 < p.val i} := by
    simp only [Set.setOf_forall]
    exact isOpen_iInter_of_finite (fun i => isOpen_lt continuous_const
      ((continuous_apply i).comp continuous_subtype_val))
  have ha : IsOpen {p : SpectralAffine d | StrictAnti p.val} := by
    have hcoord (i : Fin d) : Continuous (fun p : SpectralAffine d => p.val i) :=
      (continuous_apply i).comp continuous_subtype_val
    have he : {p : SpectralAffine d | StrictAnti p.val} =
        {p | ∀ ij : PairIndex d, p.val ij.val.2 < p.val ij.val.1} := by
      ext p
      exact ⟨fun h ij => h ij.property, fun h i j hij => h ⟨(i,j),hij⟩⟩
    rw [he]
    simp only [Set.setOf_forall]
    exact isOpen_iInter_of_finite (fun ij => isOpen_lt (hcoord ij.val.2) (hcoord ij.val.1))
  exact hp.inter ha

/-- No spectral direction is lost: regular closure in the full trace-one
hyperplane implies regular closure in the concrete spectral topology. -/
theorem SimpleSpectrum.regularClosure_of_affine (K : Set (SimpleSpectrum d))
    (hK : closure (interior (SimpleSpectrum.toAffine '' K)) =
      SimpleSpectrum.toAffine '' K) : closure (interior K) = K := by
  let f : SimpleSpectrum d → SpectralAffine d := SimpleSpectrum.toAffine
  have hf := SimpleSpectrum.isOpenEmbedding_toAffine (d := d)
  have h := congrArg (fun S : Set (SpectralAffine d) => f ⁻¹' S) hK
  change SimpleSpectrum.toAffine ⁻¹' closure (interior (SimpleSpectrum.toAffine '' K)) =
    SimpleSpectrum.toAffine ⁻¹' (SimpleSpectrum.toAffine '' K) at h
  rw [hf.isOpenMap.preimage_closure_eq_closure_preimage hf.continuous,
    hf.isOpenMap.preimage_interior_eq_interior_preimage hf.continuous,
    Set.preimage_image_eq K hf.injective] at h
  exact h

theorem SimpleSpectrum.toAffine_image_interior (K : Set (SimpleSpectrum d)) :
    SimpleSpectrum.toAffine '' interior K = interior (SimpleSpectrum.toAffine '' K) := by
  have hf := SimpleSpectrum.isOpenEmbedding_toAffine (d := d)
  refine Set.Subset.antisymm (hf.isOpenMap.image_interior_subset K) ?_
  intro y hy
  obtain ⟨p,hp,rfl⟩ := interior_subset hy
  refine ⟨p, ?_, rfl⟩
  have hm : p ∈ SimpleSpectrum.toAffine ⁻¹' interior (SimpleSpectrum.toAffine '' K) := hy
  rw [hf.isOpenMap.preimage_interior_eq_interior_preimage hf.continuous,
    Set.preimage_image_eq K hf.injective] at hm
  exact hm

/-- For compact sets the two regular-closure conditions are equivalent. -/
theorem SimpleSpectrum.regularClosure_affine_iff (K : Set (SimpleSpectrum d))
    (hcompact : IsCompact K) :
    closure (interior (SimpleSpectrum.toAffine '' K)) = SimpleSpectrum.toAffine '' K ↔
      closure (interior K) = K := by
  refine ⟨SimpleSpectrum.regularClosure_of_affine K, ?_⟩
  intro hK
  have hf := SimpleSpectrum.isOpenEmbedding_toAffine (d := d)
  refine Set.Subset.antisymm
    (closure_minimal interior_subset (hcompact.image hf.continuous).isClosed) ?_
  rintro _ ⟨p,hp,rfl⟩
  have hm : SimpleSpectrum.toAffine p ∈
      closure (SimpleSpectrum.toAffine '' interior K) :=
    image_closure_subset_closure_image hf.continuous ⟨p,hK.symm ▸ hp,rfl⟩
  rw [SimpleSpectrum.toAffine_image_interior] at hm
  exact hm

end Cloning
