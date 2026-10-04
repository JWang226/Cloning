import Cloning.MultimodeIdler
import Cloning.ThermalWitness
import Cloning.AmplifierWeylCoherent
import Cloning.WeylMultimodeChannel

/-! The multimode quantum-limited amplifier is the other partial trace of
the already constructed multimode isometry. It acts on the entire occupation
trace class, including arbitrary correlations and coherences. -/
noncomputable section
open scoped ComplexOrder InnerProductSpace Topology BigOperators
namespace Cloning.MultimodeAmplifier
open Cloning.InfiniteTraceClass Cloning.MultimodeCoherent
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

abbrev Occupation (d : ℕ) := Fin d → ℕ
abbrev JointFock (d : ℕ) := Cloning.MultimodeIdler.JointFock d
variable {d : ℕ}

/-- Fix the idler output occupation and retain the signal. -/
def sliceVector (k : Occupation d) (x : JointFock d) : Fock d := by
  refine ⟨fun n => x (n, k), memℓp_gen ?_⟩
  exact ((lp.memℓp x).summable (by norm_num)).comp_injective
    (fun i j h => congrArg Prod.fst h)

lemma sliceVector_norm_le (k : Occupation d) (x : JointFock d) : ‖sliceVector k x‖ ≤ ‖x‖ := by
  apply lp.norm_le_of_tsum_le (by norm_num) (norm_nonneg x)
  rw [lp.norm_rpow_eq_tsum (by norm_num) x]
  exact Summable.tsum_le_tsum_of_inj (fun n : Occupation d => (n, k))
    (fun i j h => congrArg Prod.fst h)
    (fun p _ => Real.rpow_nonneg (norm_nonneg _) _) (fun _ => le_rfl)
    ((lp.memℓp (sliceVector k x)).summable (by norm_num))
    ((lp.memℓp x).summable (by norm_num))

def slice (k : Occupation d) : JointFock d →L[ℂ] Fock d :=
  LinearMap.mkContinuous
    { toFun := sliceVector k
      map_add' := by intro x y; ext n; rfl
      map_smul' := by intro c x; ext n; rfl }
    1 (fun x => by simpa only [one_mul] using sliceVector_norm_le k x)

@[simp] lemma slice_apply (k : Occupation d) (x : JointFock d) (n : Occupation d) :
    slice k x n = x (n, k) := rfl

lemma slice_norm_sq_hasSum (x : JointFock d) :
    HasSum (fun k => ‖slice k x‖ ^ 2) (‖x‖ ^ 2) := by
  have hfull : HasSum (fun p : Occupation d × Occupation d => ‖x p‖ ^ (2 : ℕ)) (‖x‖ ^ 2) := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      lp.hasSum_norm (show 0 < (2 : ENNReal).toReal by norm_num) x
  have hswap : HasSum (fun p : Occupation d × Occupation d => ‖x (p.2, p.1)‖ ^ (2 : ℕ))
      (‖x‖ ^ 2) := (Equiv.prodComm (Occupation d) (Occupation d)).hasSum_iff.mpr hfull
  apply hswap.prod_fiberwise
  intro k
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, slice_apply] using
    lp.hasSum_norm (show 0 < (2 : ENNReal).toReal by norm_num) (slice k x)

def kraus (q : Fin d → ℝ) (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i < 1)
    (k : Occupation d) : Fock d →L[ℂ] Fock d :=
  (slice k).comp (Cloning.MultimodeIdler.isometry q hq0 hq1).toContinuousLinearMap

lemma kraus_norm_sq_hasSum (q : Fin d → ℝ) (hq0 : ∀ i, 0 ≤ q i)
    (hq1 : ∀ i, q i < 1) (x : Fock d) :
    HasSum (fun k => ‖kraus q hq0 hq1 k x‖ ^ 2) (‖x‖ ^ 2) := by
  simpa only [kraus, ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
    LinearIsometry.norm_map] using
    slice_norm_sq_hasSum (Cloning.MultimodeIdler.isometry q hq0 hq1 x)

/-- Genuine CPTP multimode amplifier with potentially distinct mode gains. -/
def channel (q : Fin d → ℝ) (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i < 1) :
    QuantumChannel (Fock d) (Fock d) :=
  QuantumChannel.ofKraus (kraus q hq0 hq1) (kraus_norm_sq_hasSum q hq0 hq1)

lemma channel_hasSum (q : Fin d → ℝ) (hq0 : ∀ i, 0 ≤ q i)
    (hq1 : ∀ i, q i < 1) (A : TraceClass (Fock d)) :
    HasSum (fun k => krausTerm (kraus q hq0 hq1 k) A) ((channel q hq0 hq1).toLinearMap A) :=
  QuantumChannel.ofKraus_hasSum _ _ A

lemma kraus_numberBasis (q : Fin d → ℝ) (hq0 : ∀ i, 0 ≤ q i)
    (hq1 : ∀ i, q i < 1) (k n : Occupation d) :
    kraus q hq0 hq1 k (Cloning.MultimodeIdler.numberBasis d n) =
      (Real.sqrt (Cloning.BosonicNumberLaw.productLaw q n k) : ℂ) •
        Cloning.MultimodeIdler.numberBasis d (n + k) := by
  ext m
  simp only [Cloning.MultimodeIdler.numberBasis_eq_single, kraus,
    ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
    Cloning.MultimodeIdler.isometry_single, slice_apply, Cloning.MultimodeIdler.column_apply,
    lp.coeFn_smul, Pi.smul_apply, lp.single_apply, Pi.single_apply, smul_eq_mul]
  by_cases h : m = n + k <;> simp [h]

def coherentKrausAmplitude (q : Fin d → ℝ) (k : Occupation d) (z : Fin d → ℂ) : ℂ :=
  ∏ i, Cloning.BosonicAmplifier.coherentKrausAmplitude (q i) (k i) (z i)

/-- All modes retain their exact coherent Kraus phases. -/
theorem kraus_adjoint_coherentVector (q : Fin d → ℝ) (hq0 : ∀ i, 0 ≤ q i)
    (hq1 : ∀ i, q i < 1) (k : Occupation d) (z : Fin d → ℂ) :
    (kraus q hq0 hq1 k).adjoint (coherentVector z) =
      coherentKrausAmplitude q k z •
        coherentVector (fun i => (Real.sqrt (1 - q i) : ℂ) * z i) := by
  ext n
  rw [← Cloning.MultimodeIdler.inner_numberBasis, ContinuousLinearMap.adjoint_inner_right,
    kraus_numberBasis, inner_smul_left, Cloning.MultimodeIdler.inner_numberBasis]
  simp only [Complex.conj_ofReal, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  unfold Cloning.BosonicNumberLaw.productLaw
  rw [Real.sqrt_prod _ (fun i _ => Cloning.BosonicNumberLaw.seededLaw_nonneg (hq0 i) (hq1 i) _ _),
    Complex.ofReal_prod]
  simp only [coherentVector_apply, coherentKrausAmplitude, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  exact Cloning.BosonicAmplifier.coherent_kraus_coefficient (hq0 i) (hq1 i) (k i) (n i) (z i)

lemma coherentKrausAmplitude_inner_hasSum (q : Fin d → ℝ)
    (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i < 1) (v w : Fin d → ℂ) :
    HasSum (fun k => star (coherentKrausAmplitude q k v) * coherentKrausAmplitude q k w)
      (((∏ i, (1 - q i) : ℝ) : ℂ) *
        ⟪coherentVector (fun i => (Real.sqrt (q i) : ℂ) * v i),
          coherentVector (fun i => (Real.sqrt (q i) : ℂ) * w i)⟫_ℂ) := by
  have h := hasSum_fin_product_complex d _ _
    (fun i => Cloning.BosonicAmplifier.coherentKrausAmplitude_inner_hasSum (hq0 i) (hq1 i) (v i) (w i))
  simpa only [coherentKrausAmplitude, star_prod, ← Finset.prod_mul_distrib,
    coherentVector, inner_tensorVector, Complex.ofReal_prod, Complex.ofReal_sub,
    Complex.ofReal_one, Finset.prod_mul_distrib] using h

/-- The complete coherent matrix kernel of the actual multimode amplifier. -/
theorem channel_coherent_matrixCoefficient (q : Fin d → ℝ)
    (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i < 1) (A : TraceClass (Fock d)) (v w : Fin d → ℂ) :
    ⟪coherentVector v, ((channel q hq0 hq1).toLinearMap A).1 (coherentVector w)⟫_ℂ =
      (((∏ i, (1 - q i) : ℝ) : ℂ) *
        ⟪coherentVector (fun i => (Real.sqrt (q i) : ℂ) * v i),
          coherentVector (fun i => (Real.sqrt (q i) : ℂ) * w i)⟫_ℂ) *
      ⟪coherentVector (fun i => (Real.sqrt (1 - q i) : ℂ) * v i),
        A.1 (coherentVector (fun i => (Real.sqrt (1 - q i) : ℂ) * w i))⟫_ℂ := by
  have hs := (channel_hasSum q hq0 hq1 A).mapL
    (traceClassMatrixCoefficient (coherentVector v) (coherentVector w))
  have ht := (coherentKrausAmplitude_inner_hasSum q hq0 hq1 v w).mul_right
    ⟪coherentVector (fun i => (Real.sqrt (1 - q i) : ℂ) * v i),
      A.1 (coherentVector (fun i => (Real.sqrt (1 - q i) : ℂ) * w i))⟫_ℂ
  apply hs.unique
  convert ht using 1
  funext k
  simp only [traceClassMatrixCoefficient_apply, krausTerm, inner_sandwichCLM,
    ContinuousLinearMap.star_eq_adjoint, kraus_adjoint_coherentVector,
    map_smul, inner_smul_left, inner_smul_right, Complex.star_def]
  ring

lemma coherentVector_zero_eq_numberBasis :
    coherentVector (0 : Fin d → ℂ) = Cloning.MultimodeIdler.numberBasis d 0 := by
  classical
  ext n
  simp only [Cloning.MultimodeIdler.numberBasis_eq_single, lp.single_apply, Pi.single_apply]
  by_cases hn : n = 0
  · subst n
    simp [coherentVector_apply, Cloning.ComplexCoherent.coherentVector_apply]
  · rw [if_neg hn]
    rw [coherentVector_apply]
    obtain ⟨i, hi⟩ : ∃ i, n i ≠ 0 := by
      by_contra h
      push_neg at h
      exact hn (funext h)
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [Cloning.ComplexCoherent.coherentVector_apply, hi]

lemma productLaw_zero (q : Fin d → ℝ) (k : Occupation d) :
    Cloning.BosonicNumberLaw.productLaw q 0 k = Cloning.ThermalWitness.productGeometric q k := by
  simp [Cloning.BosonicNumberLaw.productLaw, Cloning.BosonicNumberLaw.seededLaw,
    Cloning.ThermalWitness.productGeometric, Cloning.Thermal.geometric]

/-- The actual amplifier sends joint vacuum to the product thermal density. -/
theorem channel_vacuum (q : Fin d → ℝ)
    (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i < 1) :
    (channel q hq0 hq1).toLinearMap (coherentProjector (0 : Fin d → ℂ)) =
      vectorMixture (Cloning.MultimodeCoherentGaussianMixture.numberBasis d)
        (Cloning.ThermalWitness.productGeometric q) := by
  have h := channel_hasSum q hq0 hq1
    (vectorProjector (Cloning.MultimodeIdler.numberBasis d 0))
  simp only [krausTerm_vectorProjector, kraus_numberBasis, zero_add, productLaw_zero] at h
  have he (k : Occupation d) : vectorProjector
      ((Real.sqrt (Cloning.ThermalWitness.productGeometric q k) : ℂ) •
        Cloning.MultimodeIdler.numberBasis d k) =
      (Cloning.ThermalWitness.productGeometric q k : ℂ) •
        vectorProjector (Cloning.MultimodeIdler.numberBasis d k) :=
    Cloning.BosonicAmplifier.vectorProjector_sqrt_smul _
      (Cloning.ThermalWitness.productGeometric_nonneg hq0 hq1 k) _
  simp only [he] at h
  change (channel q hq0 hq1).toLinearMap (vectorProjector (coherentVector 0)) = _
  rw [coherentVector_zero_eq_numberBasis]
  exact h.tsum_eq.symm

end Cloning.MultimodeAmplifier
