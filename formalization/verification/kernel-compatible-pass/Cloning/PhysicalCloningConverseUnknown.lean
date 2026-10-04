import Cloning.PhysicalCloningConverseWindows
import Cloning.PhysicalCloningConverseTransfer
import Cloning.HybridFlatBox

/-! Physical unknown-spectrum converse at interior base points. The LAN
premise is the explicit compact-window property for literal tensor states. -/
noncomputable section
open scoped BigOperators Topology Classical
open Filter MeasureTheory
namespace Cloning.PhysicalCloningConverse
open Cloning.PCT Cloning.PCTLocalChart Cloning.PCTPhysicalFidelity
open Cloning.PCTJointGaussianWhitening Cloning.PCTPhysicalState Cloning.TensorCloning
open Cloning.Hybrid
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
variable {k s : ℕ}

theorem output_size_tendsto (m : ℕ → ℕ) (g : ℝ) (hg : 0 < g)
    (hratio : Tendsto (fun n => (m n : ℝ)/(n : ℝ)) atTop (𝓝 g)) :
    Tendsto m atTop atTop := by
  apply (tendsto_natCast_atTop_iff (R := ℝ)).mp
  have h := hratio.pos_mul_atTop hg (tendsto_natCast_atTop_atTop (R := ℝ))
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  exact div_mul_cancel₀ (m n : ℝ) (Nat.cast_ne_zero.mpr hn.ne')

theorem ae_flatBox_mem (L : ℕ) :
    ∀ᵐ ξ ∂(flatBoxDensity k s).expandingPrior L,
      ξ ∈ phaseSpaceBox k s ((L : ℝ)+1) := by
  rw [PhaseDensity.expandingPrior]
  apply (ae_map_iff (by fun_prop)
    (show MeasurableSet {ξ : PhaseSpace k s | ξ ∈ phaseSpaceBox k s ((L : ℝ)+1)}
      from (phaseSpaceBox_closed k s _).measurableSet)).mpr
  simp_rw [smul_mem_phaseSpaceBox_iff (by positivity : 0 < (L : ℝ)+1)]
  rw [PhaseDensity.prior, ae_withDensity_iff (flatBoxDensity k s).measurable.ennreal_ofReal]
  apply Eventually.of_forall
  intro ξ hξ
  by_contra hnot
  simp [flatBoxDensity, hnot] at hξ

def spectrumInSet (S : Set (SimpleSpectrum (k+1))) (p : SimpleSpectrum (k+1)) (hp : p ∈ S)
    (h : Fin (k+1) → ℝ) (n : ℕ) : S :=
  if hm : localSimpleSpectrum p h n ∈ S then ⟨localSimpleSpectrum p h n,hm⟩ else ⟨p,hp⟩

def unknownLocalChart (S : Set (SimpleSpectrum (k+1))) (p : SimpleSpectrum (k+1)) (hp : p ∈ S)
    (b : Fin (k+1) → EuclideanSpace ℝ (Fin (k+1))) (e : Fin s ≃ PairIndex (k+1))
    (n : ℕ) (ξ : PhaseSpace k s) : S × unitary (Matrix (Fin (k+1)) (Fin (k+1)) ℂ) :=
  (spectrumInSet S p hp (phaseParameters p b e ξ).1 n,
    localUnitary p (phaseParameters p b e ξ) n)

theorem model_phaseParameters (p : SimpleSpectrum (k+1))
    (b : OrthonormalBasis (Fin (k+1)) ℝ (EuclideanSpace ℝ (Fin (k+1))))
    (e : Fin s ≃ PairIndex (k+1)) (ξ : PhaseSpace k s) :
    model p b e (phaseParameters p b e ξ) = translatedPositive ξ (reference p e) := by
  unfold model
  rw [parameterTranslation_phaseParameters]
  rfl

theorem model_smul_phaseParameters (p : SimpleSpectrum (k+1))
    (b : OrthonormalBasis (Fin (k+1)) ℝ (EuclideanSpace ℝ (Fin (k+1))))
    (e : Fin s ≃ PairIndex (k+1)) (c : ℝ) (ξ : PhaseSpace k s) :
    model p b e (c • phaseParameters p b e ξ) = translatedPositive (c • ξ) (reference p e) := by
  unfold model
  rw [parameterTranslation_smul, parameterTranslation_phaseParameters]
  rfl

/-- Every fixed physical phase box has genuine input/output LAN errors
tending to zero, uniformly on the box and independently of the competitor. -/
theorem unknown_fixedWindow_errors
    (S : Set (SimpleSpectrum (k+1))) (p : SimpleSpectrum (k+1)) (hp : p ∈ interior S)
    (b : OrthonormalBasis (Fin (k+1)) ℝ (EuclideanSpace ℝ (Fin (k+1))))
    (hb : b 0 = sqrtSpectrum p.eigenvalue) (e : Fin s ≃ PairIndex (k+1))
    (lan : CompactWindowLAN p b e) (m : ℕ → ℕ) (g : ℝ) (hg : 0 < g)
    (hratio : Tendsto (fun n => (m n : ℝ)/(n : ℝ)) atTop (𝓝 g)) (L : ℕ) :
    ∃ δ η : ℕ → ℝ, Tendsto δ atTop (𝓝 0) ∧ Tendsto η atTop (𝓝 0) ∧
      ∀ᶠ n in atTop, ∀ ξ ∈ phaseSpaceBox k s ((L : ℝ)+1),
        let u := unknownLocalChart S p (interior_subset hp) b e n ξ
        (‖(lan.reverse n).map (translatedPositive ξ (reference p e)).1 -
          (tensorState (orbitState u.1.val u.2) n).1‖ ≤ δ n) ∧
        (‖(lan.forward (m n)).map (tensorState (orbitState u.1.val u.2) (m n)).1 -
          (translatedPositive (Real.sqrt g • ξ) (reference p e)).1‖ ≤ η n) := by
  let K := phaseParameters p b e '' phaseSpaceBox k s ((L : ℝ)+1)
  have hK : IsCompact K := compact_phaseParameters p b e _ (phaseSpaceBox_compact k s _)
  have hz : ∀ θ ∈ K, ∑ i, θ.1 i = 0 := by
    rintro θ ⟨ξ,hξ,rfl⟩
    exact phaseParameters_sum_zero p b hb e ξ
  have hm := output_size_tendsto m g hg hratio
  obtain ⟨δ,η,hδ,hη,hbound⟩ := scaled_window_approximations p b e lan m hm
    (fun n => sampleRatio n (m n)) (Real.sqrt g) (sampleRatio_tendsto m g hratio) K hK hz
  have hKscore : Bornology.IsBounded (Prod.fst '' K) := (hK.image continuous_fst).isBounded
  have hzscore : ∀ h ∈ Prod.fst '' K, ∑ i, h i = 0 := by
    rintro h ⟨θ,hθ,rfl⟩
    exact hz θ hθ
  refine ⟨δ,η,hδ,hη,?_⟩
  filter_upwards [hbound,eventually_orbitState_localSimpleSpectrum p K hK hz,
    eventually_localSimpleSpectrum_mem_of_interior S p hp (Prod.fst '' K) hKscore hzscore,
    hm.eventually (eventually_gt_atTop 0)] with n hn he hmem hmn ξ hξ
  let θ := phaseParameters p b e ξ
  have hθ : θ ∈ K := ⟨ξ,hξ,rfl⟩
  have hS := hmem θ.1 ⟨θ,hθ,rfl⟩
  have hmatrix : (orbitState (unknownLocalChart S p (interior_subset hp) b e n ξ).1.val
      (unknownLocalChart S p (interior_subset hp) b e n ξ).2).matrix = chartMatrix p θ n := by
    change (orbitState (spectrumInSet S p (interior_subset hp) θ.1 n).val
      (localUnitary p θ n)).matrix = _
    rw [spectrumInSet, dif_pos hS]
    exact he θ hθ
  have hinput : (tensorState (orbitState (unknownLocalChart S p (interior_subset hp) b e n ξ).1.val
      (unknownLocalChart S p (interior_subset hp) b e n ξ).2) n).1 = chartTensor p θ n := by
    change matrixTensorPower _ n = _
    rw [hmatrix]
    rfl
  have houtput : (tensorState (orbitState (unknownLocalChart S p (interior_subset hp) b e n ξ).1.val
      (unknownLocalChart S p (interior_subset hp) b e n ξ).2) (m n)).1 =
      chartTensor p (sampleRatio n (m n) • θ) (m n) := by
    change matrixTensorPower _ (m n) = matrixTensorPower _ (m n)
    rw [hmatrix, chartMatrix_rescale p θ n (m n) hmn]
  have hh := hn θ hθ
  simpa only [hinput,houtput,θ,model_phaseParameters,model_smul_phaseParameters] using hh


/-- The physical unknown-spectrum minimax converse at an interior base. The
only analytic premise is the genuine compact-window mixed-LAN property. -/
theorem limsup_unknownSpectrumValue_le_of_compactWindowLAN
    (S : Set (SimpleSpectrum (k+1))) (p : SimpleSpectrum (k+1)) (hp : p ∈ interior S)
    (b : OrthonormalBasis (Fin (k+1)) ℝ (EuclideanSpace ℝ (Fin (k+1))))
    (hb : b 0 = sqrtSpectrum p.eigenvalue) (e : Fin s ≃ PairIndex (k+1))
    (lan : CompactWindowLAN p b e) (m : ℕ → ℕ) (g : ℝ) (hg : 1 < g)
    (hratio : Tendsto (fun n => (m n : ℝ)/(n : ℝ)) atTop (𝓝 g)) :
    limsup (fun n => unknownSpectrumValue n (m n) S) atTop ≤ universalValue g p := by
  letI : Nonempty S := ⟨⟨p,interior_subset hp⟩⟩
  choose δ η hδ hη hbound using fun L =>
    unknown_fixedWindow_errors S p hp b hb e lan m g (by linarith) hratio L
  have hd : ∀ L, ∀ᶠ n in atTop, ∀ᵐ ξ ∂(flatBoxDensity k s).expandingPrior L,
      ‖(lan.reverse n).map (translatedPositive ξ (reference p e)).1 -
        (tensorState (orbitState
          (unknownLocalChart S p (interior_subset hp) b e n ξ).1.val
          (unknownLocalChart S p (interior_subset hp) b e n ξ).2) n).1‖ ≤ δ L n := by
    intro L
    filter_upwards [hbound L] with n hn
    exact (ae_flatBox_mem L).mono fun ξ hξ => (hn ξ hξ).1
  have he : ∀ L, ∀ᶠ n in atTop, ∀ᵐ ξ ∂(flatBoxDensity k s).expandingPrior L,
      ‖(lan.forward (m n)).map (tensorState (orbitState
          (unknownLocalChart S p (interior_subset hp) b e n ξ).1.val
          (unknownLocalChart S p (interior_subset hp) b e n ξ).2) (m n)).1 -
        (translatedPositive (Real.sqrt g • ξ) (reference p e)).1‖ ≤ η L n := by
    intro L
    filter_upwards [hbound L] with n hn
    exact (ae_flatBox_mem L).mono fun ξ hξ => (hn ξ hξ).2
  have h := limsup_statePayoff_le_modeFactor_of_approximations
    (fun u : S × unitary (Matrix (Fin (k+1)) (Fin (k+1)) ℂ) => orbitState u.1.val u.2)
    m (flatBoxDensity k s) (fun _ => 1/2) (fun _ => by norm_num) g hg
    (fun i => p.ratio (e i)) (fun i => (p.ratio_pos (e i)).le) (fun i => p.ratio_lt_one (e i))
    lan.reverse (fun n => lan.forward (m n))
    (unknownLocalChart S p (interior_subset hp) b e) δ η hd he hδ hη
  have hprod := e.prod_comp (fun ij => Thermal.modeFactor g (p.ratio ij))
  simpa only [unknownSpectrumValue, spectrumPayoff, universalValue, classicalValue, orbitalValue,
    Nat.cast_add, Nat.cast_one, add_sub_cancel_right, hprod] using h

/-- Boundary spectra are included by the proved concrete continuity of the
Gaussian value. Compactness of S is unnecessary for the upper bound itself. -/
theorem limsup_unknownSpectrumValue_infimum_of_compactWindowLAN
    (S : Set (SimpleSpectrum (k+1))) (hSne : S.Nonempty)
    (hS : closure (interior S) = S) (e : Fin s ≃ PairIndex (k+1))
    (hLAN : ∀ p ∈ interior S,
      ∃ b : OrthonormalBasis (Fin (k+1)) ℝ (EuclideanSpace ℝ (Fin (k+1))),
        b 0 = sqrtSpectrum p.eigenvalue ∧ Nonempty (CompactWindowLAN p b e))
    (m : ℕ → ℕ) (g : ℝ) (hg : 1 < g)
    (hratio : Tendsto (fun n => (m n : ℝ)/(n : ℝ)) atTop (𝓝 g)) :
    limsup (fun n => unknownSpectrumValue n (m n) S) atTop ≤
      ⨅ p : S, universalValue g p.val := by
  apply universal_infimum_regularClosure (by linarith) S hSne hS
  intro p hp
  obtain ⟨b,hb,⟨lan⟩⟩ := hLAN p hp
  exact limsup_unknownSpectrumValue_le_of_compactWindowLAN S p hp b hb e lan m g hg hratio

end Cloning.PhysicalCloningConverse
