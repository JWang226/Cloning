import Cloning.WeylDiagonalMultiplier
import Cloning.WeylQuantumBochnerReflection
import Cloning.WeylThermalCharacteristic

/-! Antilinear displacement covariance determines the actual complementary
channel characteristic. The scalar is fixed by its actual vacuum output. -/
noncomputable section
open scoped BigOperators Topology InnerProductSpace ComplexOrder
namespace Cloning.MultimodeCoherent
open InfiniteTraceClass MultimodeCoherentGaussianMixture ThermalWitness
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
variable {d : ℕ}

theorem weylCharacter_conjugateScale (s : Fin d → ℝ) (a b : Fin d → ℂ) :
    weylCharacter (diagonalScale s (star a)) b=
      weylCharacter a (-(diagonalScale s (star b))) := by
  simp only [weylCharacter, displacementPhase, ← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro i _
  simp only [diagonalScale, Pi.star_apply, Pi.neg_apply, Complex.star_def,
    ComplexCoherent.displacementPhase, ← Complex.exp_sub, map_mul, map_neg,
    Complex.conj_ofReal, starRingEnd_self_apply]
  congr 1
  ring

theorem heisenbergDual_conjugateScale_covariance
    (Φ : TraceClass (Fock d) →L[ℂ] TraceClass (Fock d)) (s : Fin d → ℝ)
    (hΦ : ∀ a T, Φ (displacementTraceMap a T)=
      displacementTraceMap (diagonalScale s (star a)) (Φ T))
    (a : Fin d → ℂ) (A : Fock d →L[ℂ] Fock d) :
    ((displacement a).comp (heisenbergDual Φ A)).comp (displacement (-a))=
      heisenbergDual Φ (((displacement (diagonalScale s (star a))).comp A).comp
        (displacement (-(diagonalScale s (star a))))) := by
  have hcov : ∀ T, Φ (sandwichCLM (displacement (-a)) (star (displacement (-a))) T)=
      sandwichCLM (displacement (diagonalScale s (star (-a))))
        (star (displacement (diagonalScale s (star (-a))))) (Φ T) := by
    intro T
    simpa only [displacementTraceMap, ContinuousLinearMap.star_eq_adjoint,
      displacement_adjoint] using hΦ (-a) T
  have h := heisenbergDual_covariance Φ (displacement (-a))
    (displacement (diagonalScale s (star (-a)))) hcov A
  simpa only [ContinuousLinearMap.star_eq_adjoint, displacement_adjoint,
    star_neg, diagonalScale_neg, neg_neg, ContinuousLinearMap.mul_def] using h

private theorem reflected_covariance_eigenoperator
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (W : (Fin d → ℂ) → H →L[ℂ] H) (χ : (Fin d → ℂ) → (Fin d → ℂ) → ℂ)
    (S R : (Fin d → ℂ) → (Fin d → ℂ))
    (hconj : ∀ a b, ((W a).comp (W b)).comp (W (-a)) = χ a b • W b)
    (hinv : ∀ a v, W (-a) (W a v) = v)
    (hscale : ∀ a b, χ (S a) b = χ a (R b))
    (Ψ : (H →L[ℂ] H) →ₗ[ℂ] (H →L[ℂ] H))
    (hΨ : ∀ a A, ((W a).comp (Ψ A)).comp (W (-a)) =
      Ψ (((W (S a)).comp A).comp (W (-(S a))))) (b : Fin d → ℂ) :
    ∀ a, (W a).comp (Ψ (W b)) = χ a (R b) • (Ψ (W b)).comp (W a) := by
  intro a
  have ha := hΨ a (W b)
  have hright := hconj (S a) b
  have hmap := Ψ.map_smul (χ (S a) b) (W b)
  have hchar := congrArg (fun c : ℂ => c • Ψ (W b)) (hscale a b)
  have ha' := ha.trans ((congrArg Ψ hright).trans (hmap.trans hchar))
  apply ContinuousLinearMap.ext
  intro v
  have hv := congrArg (fun L : H →L[ℂ] H => L (W a v)) ha'
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply, hinv] using hv

/-- The reflected frequency is forced by the genuine Weyl commutation phase. -/
theorem quantumChannel_conjugateScale_multiplier
    (Φ : QuantumChannel (Fock d) (Fock d)) (s : Fin d → ℝ)
    (hΦ : ∀ a T, Φ.toLinearMap (displacementTraceMap a T)=
      displacementTraceMap (diagonalScale s (star a)) (Φ.toLinearMap T)) (b : Fin d → ℂ) :
    ∃ c : ℂ, Φ.heisenberg (displacement b)=
      c • displacement (-(diagonalScale s (star b))) := by
  apply exists_scalar_eigenoperator
  exact reflected_covariance_eigenoperator displacement weylCharacter
    (fun a => diagonalScale s (star a)) (fun b => -(diagonalScale s (star b)))
    displacement_conjugation displacement_neg_cancel (weylCharacter_conjugateScale s)
    Φ.heisenberg (heisenbergDual_conjugateScale_covariance
      Φ.toPositiveTracePreservingMap.toContinuousLinearMap s hΦ) b

/-- Covariance and the literal thermal vacuum output determine the full
all-complex-input characteristic law of the phase-conjugating channel. -/
theorem quantumChannel_conjugateScale_characteristic
    (Φ : QuantumChannel (Fock d) (Fock d)) (q s : Fin d → ℝ)
    (hq0 : ∀ i,0<q i) (hq1 : ∀ i,q i<1)
    (hs : ∀ i,s i^2=q i/(1-q i))
    (hΦ : ∀ a T, Φ.toLinearMap (displacementTraceMap a T)=
      displacementTraceMap (diagonalScale s (star a)) (Φ.toLinearMap T))
    (hvac : Φ.toLinearMap (coherentProjector (0 : Fin d → ℂ))=
      vectorMixture (numberBasis d) (productGeometric q))
    (A : TraceClass (Fock d)) (a : Fin d → ℂ) :
    tracePairing (Φ.toLinearMap A) (displacement a)=
      (∏ i, (Real.exp (-‖a i‖^2/(2*(1-q i))) : ℂ)) *
        tracePairing A (displacement (-(diagonalScale s (star a)))) := by
  obtain ⟨c,hc⟩ := quantumChannel_conjugateScale_multiplier Φ s hΦ a
  let b := -(diagonalScale s (star a))
  let G : ℂ := ∏ i, (Real.exp (-‖a i‖^2/(2*(1-q i))) : ℂ)
  have hchar (T : TraceClass (Fock d)) :
      tracePairing (Φ.toLinearMap T) (displacement a)=c*tracePairing T (displacement b) := by
    rw [← Φ.heisenberg_pairing, hc, map_smul, smul_eq_mul]
  have h0 := hchar (coherentProjector (0 : Fin d → ℂ))
  rw [hvac, productThermal_characteristic hq0 hq1] at h0
  have hgauss : (∏ i, Complex.exp (-(((1+q i)/(2*(1-q i))*‖a i‖^2 : ℝ) : ℂ)))=
      G * tracePairing (coherentProjector (0 : Fin d → ℂ)) (displacement b) := by
    change _=G * tracePairing (rankOneOperator (coherentVector 0) (coherentVector 0)) _
    rw [tracePairing_rankOneOperator, vacuum_characteristic]
    dsimp only [G]
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    have hn : ‖b i‖^2=s i^2*‖a i‖^2 := by
      simp [b, diagonalScale, norm_mul, mul_pow, Complex.norm_real]
    rw [hn, hs i, ← Complex.ofReal_mul, ← Real.exp_add, Complex.ofReal_exp]
    congr 1
    push_cast
    congr 1
    field_simp [ne_of_gt (sub_pos.mpr (hq1 i))]
    ring
  have hn : tracePairing (coherentProjector (0 : Fin d → ℂ)) (displacement b)≠0 := by
    change tracePairing (rankOneOperator (coherentVector 0) (coherentVector 0)) _≠0
    rw [tracePairing_rankOneOperator]
    exact vacuum_characteristic_ne_zero b
  have hcG : c=G := mul_right_cancel₀ hn (h0.symm.trans hgauss)
  rw [hchar, hcG]

end Cloning.MultimodeCoherent
