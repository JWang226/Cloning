import Cloning.TensorGibbsCutoffState

/-! The actual Fock product thermal state and its weighted-height cutoffs. -/
noncomputable section
open scoped BigOperators InnerProductSpace ComplexOrder Topology
open Filter
namespace Cloning.TensorLie
open Cloning.TensorLAN Cloning.InfiniteTraceClass
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {d : ℕ}

def bosonicOccupationWeight (p : Fin d → ℝ) (k : PositiveRoot d → ℕ) : ℝ :=
  (∏ r : PositiveRoot d, (1 - rootBoltzmann p r)) * wordBoltzmann p (canonicalWord k)

theorem bosonicOccupationWeight_hasSum (p : Fin d → ℝ) (hp : ∀ a, 0 < p a)
    (hord : StrictAnti p) : HasSum (bosonicOccupationWeight p) 1 := by
  have hc : (∏ r : PositiveRoot d, (1 - rootBoltzmann p r)) ≠ 0 :=
    (Finset.prod_pos (fun r _ => sub_pos.mpr (rootBoltzmann_lt_one p hp hord r))).ne'
  have hs := (rootPowerProduct_hasSum p hp hord).mul_left (∏ r : PositiveRoot d, (1 - rootBoltzmann p r))
  simpa only [← wordBoltzmann_canonicalWord, bosonicOccupationWeight,
    Finset.prod_inv_distrib, mul_inv_cancel₀ hc] using hs

theorem bosonicOccupationWeight_nonneg (p : Fin d → ℝ) (hp : ∀ a, 0 < p a)
    (hord : StrictAnti p) (k : PositiveRoot d → ℕ) : 0 ≤ bosonicOccupationWeight p k :=
  mul_nonneg (Finset.prod_nonneg (fun r _ => (sub_pos.mpr (rootBoltzmann_lt_one p hp hord r)).le))
    (wordBoltzmann_pos p hp _).le

def occupationCutoffFinset (d R : ℕ) : Finset (PositiveRoot d → ℕ) :=
  (Finset.univ : Finset (HeightOccupation d R)).map ⟨Subtype.val, Subtype.val_injective⟩

@[simp] theorem mem_occupationCutoffFinset (R : ℕ) (k : PositiveRoot d → ℕ) :
    k ∈ occupationCutoffFinset d R ↔ occupationHeight k ≤ R := by
  classical
  simp only [occupationCutoffFinset, Finset.mem_map, Finset.mem_univ, true_and,
    Function.Embedding.coeFn_mk]
  exact ⟨fun ⟨i,hi⟩ => hi ▸ i.property, fun hk => ⟨⟨k,hk⟩,rfl⟩⟩

theorem occupationCutoffFinset_tendsto (d : ℕ) :
    Tendsto (occupationCutoffFinset d) atTop atTop := by
  classical
  apply tendsto_atTop.mpr
  intro s
  filter_upwards [eventually_ge_atTop (s.sup occupationHeight)] with R hR
  intro k hk
  exact (mem_occupationCutoffFinset R k).mpr ((Finset.le_sup hk).trans hR)

theorem heightOccupation_sum_tendsto (f : (PositiveRoot d → ℕ) → ℝ) (hf : Summable f) :
    Tendsto (fun R => ∑ k : HeightOccupation d R, f k.val) atTop (𝓝 (∑' k, f k)) := by
  have ht := hf.hasSum.comp (occupationCutoffFinset_tendsto d)
  simpa only [Function.comp_def, occupationCutoffFinset, Finset.sum_map, Function.Embedding.coeFn_mk] using ht

def rootNumberFrame (d : ℕ) (k : PositiveRoot d → ℕ) : RootFock d :=
  MultimodeCoherentGaussianMixture.numberBasis _ (fockOccupation d k)

theorem rootNumberFrame_orthonormal (d : ℕ) : Orthonormal ℂ (rootNumberFrame d) :=
  (MultimodeCoherentGaussianMixture.numberBasis _).orthonormal.comp _ (fockOccupation_injective d)

def rootThermalState (p : Fin d → ℝ) : TraceClass (RootFock d) :=
  vectorMixture (rootNumberFrame d) (bosonicOccupationWeight p)

theorem rootThermalState_nonneg (p : Fin d → ℝ) (hp : ∀ a, 0 < p a) (hord : StrictAnti p) :
    0 ≤ (rootThermalState p).1 :=
  vectorMixture_nonneg _ (rootNumberFrame_orthonormal d).norm_eq_one _
    (bosonicOccupationWeight_hasSum p hp hord).summable (bosonicOccupationWeight_nonneg p hp hord)

theorem rootThermalState_trace (p : Fin d → ℝ) (hp : ∀ a, 0 < p a) (hord : StrictAnti p) :
    traceCLM (rootThermalState p) = 1 := by
  rw [rootThermalState, traceCLM_vectorMixture _ (rootNumberFrame_orthonormal d).norm_eq_one _
    (bosonicOccupationWeight_hasSum p hp hord).summable, (bosonicOccupationWeight_hasSum p hp hord).tsum_eq]
  rfl

theorem rootThermalState_eigen (p : Fin d → ℝ) (hp : ∀ a, 0 < p a) (hord : StrictAnti p)
    (k : PositiveRoot d → ℕ) :
    (rootThermalState p).1 (rootNumberFrame d k) =
      (bosonicOccupationWeight p k : ℂ) • rootNumberFrame d k := by
  classical
  let L : TraceClass (RootFock d) →L[ℂ] RootFock d :=
    (ContinuousLinearMap.apply ℂ (RootFock d) (rootNumberFrame d k)).comp inclusionCLM
  change L (vectorMixture _ _) = _
  rw [vectorMixture, L.map_tsum (summable_weighted_projectors _
    (rootNumberFrame_orthonormal d).norm_eq_one _ (bosonicOccupationWeight_hasSum p hp hord).summable)]
  have he (j : PositiveRoot d → ℕ) : L (vectorProjector (rootNumberFrame d j)) =
      if j = k then rootNumberFrame d k else 0 := by
    change InnerProductSpace.rankOne ℂ (rootNumberFrame d j) (rootNumberFrame d j) (rootNumberFrame d k) = _
    rw [InnerProductSpace.rankOne_apply, orthonormal_iff_ite.mp (rootNumberFrame_orthonormal d) j k]
    split_ifs with hj
    · simp [hj]
    · simp
  simp only [map_smul, he]
  simp

def rootThermalCutoff (p : Fin d → ℝ) (R : ℕ) : TraceClass (RootFock d) :=
  frameMatrix (cutoffNumberFrame d R)
    (Matrix.diagonal (fun i => (bosonicOccupationWeight p (cutoffOccupation d R i).val : ℂ)))

theorem rootThermalCutoff_error (p : Fin d → ℝ) (hp : ∀ a, 0 < p a) (hord : StrictAnti p) (R : ℕ) :
    ‖rootThermalState p - rootThermalCutoff p R‖ =
      1 - ∑ k : HeightOccupation d R, bosonicOccupationWeight p k.val := by
  rw [rootThermalCutoff, spectralFrame_residual_norm _ (rootThermalState_nonneg p hp hord) _
    (cutoffNumberFrame_orthonormal d R) _ (fun i => rootThermalState_eigen p hp hord _),
    rootThermalState_trace p hp hord, Complex.one_re]
  congr 1
  exact (cutoffOccupation d R).sum_comp (fun k => bosonicOccupationWeight p k.val)

theorem rootThermalCutoff_error_tendsto_zero (p : Fin d → ℝ) (hp : ∀ a, 0 < p a)
    (hord : StrictAnti p) : Tendsto (fun R => ‖rootThermalState p - rootThermalCutoff p R‖) atTop (𝓝 0) := by
  simp_rw [rootThermalCutoff_error p hp hord]
  have ht := heightOccupation_sum_tendsto _ (bosonicOccupationWeight_hasSum p hp hord).summable
  rw [(bosonicOccupationWeight_hasSum p hp hord).tsum_eq] at ht
  simpa only [sub_self] using (tendsto_const_nhds (x := (1 : ℝ))).sub ht

end Cloning.TensorLie
