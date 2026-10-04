import Cloning.AmplifierWeylMultimode
import Cloning.WeylSqueezerProduct

/-! The actual negative-binomial isometry has an exact joint coherent kernel.
This retains all coherent phases and determines the complementary covariance. -/
noncomputable section
open scoped ComplexOrder InnerProductSpace Topology BigOperators
namespace Cloning.MultimodeIdler
open Cloning.InfiniteTraceClass Cloning.MultimodeCoherent
open Cloning.WeylSqueezerProduct
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 100000
variable {d : ℕ}

lemma coherent_star_apply (z : Fin d → ℂ) (n : Occupation d) :
    coherentVector (star z) n = star (coherentVector z n) := by
  simp only [coherentVector_apply, star_prod]
  apply Finset.prod_congr rfl
  intro i _
  simp only [Cloning.ComplexCoherent.coherentVector_apply, Pi.star_apply, Complex.star_def,
    Complex.norm_conj]
  rw [map_div₀, map_mul, map_pow, Complex.conj_ofReal, Complex.conj_ofReal]

lemma coherentKrausAmplitude_eq_star (q : Fin d → ℝ) (hq0 : ∀ i, 0 ≤ q i)
    (k : Occupation d) (v : Fin d → ℂ) :
    Cloning.MultimodeAmplifier.coherentKrausAmplitude q k v =
      (∏ i, (Real.sqrt (1-q i) : ℂ)) *
        star (coherentVector (fun i => (Real.sqrt (q i) : ℂ) * star (v i)) k) := by
  unfold Cloning.MultimodeAmplifier.coherentKrausAmplitude
  simp_rw [Cloning.BosonicAmplifier.coherentKrausAmplitude_eq _ (hq0 _)]
  rw [Finset.prod_mul_distrib]
  congr 1
  have he : (fun i => (Real.sqrt (q i) : ℂ) * star (v i)) =
      star (fun i => (Real.sqrt (q i) : ℂ) * v i) := by ext i; simp
  rw [he, coherent_star_apply, star_star]
  rfl

lemma coherent_column_coefficient (q : Fin d → ℝ)
    (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i < 1)
    (n k : Occupation d) (v : Fin d → ℂ) :
    (Real.sqrt (BosonicNumberLaw.productLaw q n k) : ℂ) * coherentVector v (n+k) =
      Cloning.MultimodeAmplifier.coherentKrausAmplitude q k v *
        coherentVector (fun i => (Real.sqrt (1-q i) : ℂ) * v i) n := by
  unfold BosonicNumberLaw.productLaw
  rw [Real.sqrt_prod _ (fun i _ => BosonicNumberLaw.seededLaw_nonneg (hq0 i) (hq1 i) _ _),
    Complex.ofReal_prod]
  simp only [coherentVector_apply, Cloning.MultimodeAmplifier.coherentKrausAmplitude,
    ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  exact Cloning.BosonicAmplifier.coherent_kraus_coefficient (hq0 i) (hq1 i) (k i) (n i) (v i)

/-- The exact coefficient multiplying the retained input coherent vector. -/
def coherentKernel (q : Fin d → ℝ) (v w : Fin d → ℂ) : ℂ :=
  (∏ i, (Real.sqrt (1-q i) : ℂ)) *
    ⟪coherentVector (fun i => (Real.sqrt (q i) : ℂ) * star (v i)), coherentVector w⟫_ℂ

lemma coherent_column_inner (q : Fin d → ℝ)
    (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i < 1)
    (n : Occupation d) (v w : Fin d → ℂ) :
    ⟪column q hq0 hq1 n, jointTensor (coherentVector v) (coherentVector w)⟫_ℂ =
      coherentKernel q v w * coherentVector (fun i => (Real.sqrt (1-q i) : ℂ) * v i) n := by
  let f : Occupation d × Occupation d → ℂ := fun p =>
    ⟪column q hq0 hq1 n p, jointTensor (coherentVector v) (coherentVector w) p⟫_ℂ
  have hf : HasSum f
      ⟪column q hq0 hq1 n, jointTensor (coherentVector v) (coherentVector w)⟫_ℂ :=
    lp.hasSum_inner _ _
  have hinj : Function.Injective (fun k : Occupation d => (n+k,k)) :=
    fun _ _ h => congrArg Prod.snd h
  have hzero : ∀ p ∉ Set.range (fun k : Occupation d => (n+k,k)), f p=0 := by
    intro p hp
    have hn : p.1 ≠ n+p.2 := fun h => hp ⟨p.2,Prod.ext h.symm rfl⟩
    simp [f, column_apply, hn]
  have hs := (hinj.hasSum_iff hzero).mpr hf
  have ht := ((lp.hasSum_inner
    (coherentVector (fun i => (Real.sqrt (q i) : ℂ) * star (v i))) (coherentVector w)).mul_left
      (∏ i, (Real.sqrt (1-q i) : ℂ))).mul_right
        (coherentVector (fun i => (Real.sqrt (1-q i) : ℂ) * v i) n)
  apply hs.unique
  convert ht using 1
  funext k
  change f (n+k,k) = _
  simp only [f, column_apply, jointTensor_apply, RCLike.inner_apply,
    ite_true, Complex.conj_ofReal]
  have hh := coherent_column_coefficient q hq0 hq1 n k v
  rw [coherentKrausAmplitude_eq_star q hq0] at hh
  simp only [Complex.star_def] at hh ⊢
  linear_combination (coherentVector w k)*hh

/-- The adjoint of the genuine occupation isometry on every joint coherent
vector, including its complete complex scalar phase. -/
theorem isometry_adjoint_jointTensor_coherent (q : Fin d → ℝ)
    (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i < 1) (v w : Fin d → ℂ) :
    (isometry q hq0 hq1).toContinuousLinearMap.adjoint
      (jointTensor (coherentVector v) (coherentVector w)) =
        coherentKernel q v w • coherentVector (fun i => (Real.sqrt (1-q i) : ℂ) * v i) := by
  ext n
  rw [← inner_numberBasis, ContinuousLinearMap.adjoint_inner_right]
  simp only [LinearIsometry.coe_toContinuousLinearMap, numberBasis_eq_single,
    isometry_single, coherent_column_inner, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]

end Cloning.MultimodeIdler
