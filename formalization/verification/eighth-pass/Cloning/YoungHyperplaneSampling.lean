import Cloning.YoungHyperplaneVolume

/-!
# The manuscript's rescaled cells in the root hyperplane

This specializes the geometric transport to `(μ-Np+C)/sqrt N`, proves its
Euclidean cell volume and density prefactor, and gives exact normalization,
`ℓ¹` preservation, and affinity preservation on the full affine lattice.
-/

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators Topology Classical
open MeasureTheory

namespace Cloning.YoungHyperplane

/-- The actual center `(μ-Np)/sqrt N` represented in the sum-zero subspace.
The full-coordinate formula is proved from the two mass constraints below. -/
def sampleCenter (d : ℕ) (N : ℤ) (p : Fin (d + 1) → ℝ) (μ : Lattice d N) : rootSpace d :=
  coordinates d (fun i ↦ ((μ.1 i.castSucc : ℝ) - (N : ℝ) * p i.castSucc) / Real.sqrt (N : ℝ))

theorem sampleCenter_apply (d : ℕ) (N : ℤ) (p : Fin (d + 1) → ℝ)
    (hp : ∑ i, p i = 1) (μ : Lattice d N) (i : Fin (d + 1)) :
    (sampleCenter d N p μ).1 i = ((μ.1 i : ℝ) - (N : ℝ) * p i) / Real.sqrt (N : ℝ) := by
  refine Fin.lastCases ?_ (fun j ↦ ?_) i
  · simp only [sampleCenter, coordinates_last, ← Finset.sum_div, Finset.sum_sub_distrib,
      ← Finset.mul_sum]
    have hμ : (∑ j : Fin d, (μ.1 j.castSucc : ℝ)) + (μ.1 (Fin.last d) : ℝ) = N := by
      exact_mod_cast (show (∑ j : Fin d, μ.1 j.castSucc) + μ.1 (Fin.last d) = N by
        simpa only [Fin.sum_univ_castSucc] using μ.2)
    rw [Fin.sum_univ_castSucc] at hp
    rw [← neg_div]
    congr 1
    have hpn := congrArg (fun t : ℝ ↦ (N : ℝ) * t) hp
    nlinarith only [hμ, hpn]
  · simp [sampleCenter]

/-- Membership in the rescaled half-open affine-lattice cell. -/
def sampleCell (d : ℕ) (N : ℤ) (p : Fin (d + 1) → ℝ) (μ : Lattice d N) : Set (rootSpace d) :=
  {x | (fun i : Fin d ↦ Real.sqrt (N : ℝ) * x.1 i.castSucc + (N : ℝ) * p i.castSucc) ∈
    YoungRounding.cell ((latticeCoordinates d N).symm μ)}

theorem measurableSet_sampleCell (d : ℕ) (N : ℤ) (p : Fin (d + 1) → ℝ) (μ : Lattice d N) :
    MeasurableSet (sampleCell d N p μ) := by
  apply (measurable_pi_lambda _ fun i ↦ ?_) (YoungRounding.measurableSet_cell _)
  exact measurable_const.mul
    ((measurable_pi_apply i).comp (coordinatesContinuous d).symm.continuous.measurable) |>.add_const _

/-- The sample cells tile the actual root hyperplane. -/
theorem sampleCells_cover (d : ℕ) (N : ℤ) (p : Fin (d + 1) → ℝ) :
    (⋃ μ : Lattice d N, sampleCell d N p μ) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  let y : Fin d → ℝ := fun i ↦ Real.sqrt (N : ℝ) * x.1 i.castSucc + (N : ℝ) * p i.castSucc
  refine Set.mem_iUnion.mpr ⟨latticeCoordinates d N (YoungRounding.round y), ?_⟩
  change y ∈ YoungRounding.cell ((latticeCoordinates d N).symm (latticeCoordinates d N (YoungRounding.round y)))
  rw [Equiv.symm_apply_apply]
  exact (YoungRounding.round_eq_iff _ _).mp rfl

theorem sampleCells_disjoint (d : ℕ) (N : ℤ) (p : Fin (d + 1) → ℝ) :
    Pairwise fun μ ν : Lattice d N ↦ Disjoint (sampleCell d N p μ) (sampleCell d N p ν) := by
  intro μ ν h
  apply (YoungRounding.cells_disjoint (fun heq ↦ h ((latticeCoordinates d N).symm.injective heq))).preimage

/-- The exact induced Euclidean volume of each sample cell, including the
root-hyperplane Jacobian. -/
theorem volume_sampleCell (d : ℕ) (N : ℤ) (hN : 0 < (N : ℝ))
    (p : Fin (d + 1) → ℝ) (μ : Lattice d N) :
    volume (sampleCell d N p μ) = ENNReal.ofReal (Real.sqrt ((d : ℝ) + 1)) *
      ENNReal.ofReal ((Real.sqrt (N : ℝ)) ^ d)⁻¹ := by
  have hs : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.2 hN
  rw [volume_eq_sqrt_smul_coordinateMeasure, Measure.smul_apply,
    coordinateMeasure, Measure.map_apply (coordinatesContinuous d).continuous.measurable
      (measurableSet_sampleCell d N p μ)]
  have heq : (coordinatesContinuous d) ⁻¹' sampleCell d N p μ =
      (fun x : Fin d → ℝ ↦ Real.sqrt (N : ℝ) • x) ⁻¹'
        ((fun x : Fin d → ℝ ↦ (fun i ↦ (N : ℝ) * p i.castSucc) + x) ⁻¹'
          YoungRounding.cell ((latticeCoordinates d N).symm μ)) := by
    ext x
    simp only [Set.mem_preimage, sampleCell, Set.mem_setOf_eq]
    apply Iff.of_eq
    congr 1
    ext i
    change Real.sqrt (N : ℝ) * (coordinates d x).1 i.castSucc + (N : ℝ) * p i.castSucc =
      (N : ℝ) * p i.castSucc + Real.sqrt (N : ℝ) * x i
    rw [coordinates_head]
    ring
  rw [heq, Measure.addHaar_preimage_smul volume hs.ne', measure_preimage_add,
    YoungRounding.volume_cell, mul_one]
  simp only [Module.finrank_pi, Fintype.card_fin,
    abs_of_nonneg (inv_nonneg.mpr (pow_nonneg hs.le d)), ENNReal.ofReal_inv_of_pos (pow_pos hs d), smul_eq_mul]

/-- The anchor used to express the manuscript's recentering as a translated
root-space density. -/
def sampleAnchor (d : ℕ) (N : ℤ) (p : Fin (d + 1) → ℝ) : rootSpace d :=
  coordinates d (fun i ↦ -Real.sqrt (N : ℝ) * p i.castSucc)

def sampleInterpolate (d : ℕ) (N : ℤ) (p : Fin (d + 1) → ℝ)
    (P : Lattice d N → ℝ) : rootSpace d → ℝ :=
  euclideanInterpolate d N (Real.sqrt (N : ℝ))⁻¹ (sampleAnchor d N p) P

/-- On the cell indexed by `μ`, the interpolation has precisely the density
prefactor `sqrt(N)^d / sqrt(d+1)`, with the last coordinate retained. -/
theorem sampleInterpolate_eq_on_cell (d : ℕ) (N : ℤ) (hN : 0 < (N : ℝ))
    (p : Fin (d + 1) → ℝ) (P : Lattice d N → ℝ) (μ : Lattice d N)
    (x : rootSpace d) (hx : x ∈ sampleCell d N p μ) :
    sampleInterpolate d N p P x =
      ((Real.sqrt (N : ℝ)) ^ d / Real.sqrt ((d : ℝ) + 1)) * P μ := by
  have hs : (Real.sqrt (N : ℝ)) ^ 2 = N := Real.sq_sqrt hN.le
  unfold sampleInterpolate euclideanInterpolate interpolate YoungRounding.affineDensity
  simp only [inv_inv, inv_pow, Fintype.card_fin]
  have harg : Real.sqrt (N : ℝ) • ((coordinates d).symm x -
      (coordinates d).symm (sampleAnchor d N p)) =
      fun i : Fin d ↦ Real.sqrt (N : ℝ) * x.1 i.castSucc + (N : ℝ) * p i.castSucc := by
    ext i
    simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, coordinates_symm_apply,
      sampleAnchor, coordinates_head]
    have hsi := congrArg (fun t : ℝ ↦ t * p i.castSucc) hs
    nlinarith only [hsi]
  rw [harg, YoungRounding.interpolate_eq_on_cell _ _ hx, Equiv.apply_symm_apply]
  ring

theorem sampleInterpolate_integral (d : ℕ) (N : ℤ) (hN : 0 < (N : ℝ))
    (p : Fin (d + 1) → ℝ) (P : Lattice d N → ℝ) (hP : Summable P) :
    (∫ x, sampleInterpolate d N p P x) = ∑' μ, P μ :=
  euclideanInterpolate_integral d N _ (inv_pos.mpr (Real.sqrt_pos.2 hN)) _ P hP

theorem sampleInterpolate_l1_isometry (d : ℕ) (N : ℤ) (hN : 0 < (N : ℝ))
    (p : Fin (d + 1) → ℝ) (P Q : Lattice d N → ℝ) (hP : Summable P) (hQ : Summable Q) :
    (∫ x, |sampleInterpolate d N p P x - sampleInterpolate d N p Q x|) =
      ∑' μ, |P μ - Q μ| :=
  euclideanInterpolate_l1_isometry d N _ (inv_pos.mpr (Real.sqrt_pos.2 hN)) _ P Q hP hQ

theorem sampleInterpolate_affinity (d : ℕ) (N : ℤ) (hN : 0 < (N : ℝ))
    (p : Fin (d + 1) → ℝ) (P Q : Lattice d N → ℝ)
    (hP0 : ∀ μ, 0 ≤ P μ) (hQ0 : ∀ μ, 0 ≤ Q μ) (hP : Summable P) (hQ : Summable Q) :
    (∫ x, Real.sqrt (sampleInterpolate d N p P x) * Real.sqrt (sampleInterpolate d N p Q x)) =
      ∑' μ, Real.sqrt (P μ) * Real.sqrt (Q μ) :=
  euclideanInterpolate_affinity d N _ (inv_pos.mpr (Real.sqrt_pos.2 hN)) _ P Q hP0 hQ0 hP hQ

/-- Transport a law on the full affine input lattice by the actual completed
rounding kernel. -/
def latticeTransport (d : ℕ) (n m : ℤ) (γ : ℝ) (P : PMF (Lattice d n)) : PMF (Lattice d m) :=
  P.bind (latticeRoundingPMF d n m γ)

/-- Full affine-lattice transport commutes exactly with the coordinate PMF
transport already used in the local-limit analysis. -/
theorem latticeTransport_eq_coordinate_transport (d : ℕ) (n m : ℤ) (γ : ℝ)
    (P : PMF (Fin d → ℤ)) :
    latticeTransport d n m γ (latticePMF d n P) =
      latticePMF d m (YoungRounding.transport γ P) := by
  unfold latticeTransport latticePMF YoungRounding.transport
  rw [PMF.bind_map, PMF.map_bind]
  congr 1
  funext z
  simp only [Function.comp_apply, latticeRoundingPMF, latticePMF, latticeCoordinates_head]

end Cloning.YoungHyperplane
