import Cloning.PCTGaussianCovariance
import Cloning.PCTPurificationFrame

/-! Actual Hermitian Hilbert--Schmidt frames. The real Hermitian subspace
complexifies to the entire coefficient space, so its real orthonormal bases
are complex orthonormal bases as well. -/
noncomputable section
open scoped ComplexOrder InnerProductSpace Topology BigOperators
namespace Cloning.PCTFlatGaussianCross
open Cloning.PCT Cloning.PCTReducedGaussian
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {A : Type*} [Fintype A] [DecidableEq A]

/-- Hermitian matrices viewed in the actual purification coefficient Hilbert space. -/
def hermitianSpace (A : Type*) [Fintype A] [DecidableEq A] : Submodule ℝ (Register (A×A)) where
  carrier := {x | ∀ a b, star (x (b,a))=x (a,b)}
  zero_mem' := by simp
  add_mem' := by intro x y hx hy a b; simp [hx a b,hy a b]
  smul_mem' := by intro c x hx a b; simp [Complex.real_smul,hx a b]

lemma hermitianSpace_inner_real (x y : hermitianSpace A) :
    ⟪(x : Register (A×A)),(y : Register (A×A))⟫_ℂ=
      (⟪x,y⟫_ℝ : ℂ) := by
  have hs : star ⟪(x : Register (A×A)),(y : Register (A×A))⟫_ℂ=
      ⟪(x : Register (A×A)),(y : Register (A×A))⟫_ℂ := by
    rw [lp.inner_eq_tsum]
    simp only [tsum_fintype,Fintype.sum_prod_type,RCLike.inner_apply,
      star_sum,star_mul,starRingEnd_apply,star_star]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    rw [y.2 a b,← x.2 b a]
    ring
  change _=(⟪(x : Register (A×A)),(y : Register (A×A))⟫_ℝ : ℂ)
  have hr : ⟪(x : Register (A×A)),(y : Register (A×A))⟫_ℝ=
      (⟪(x : Register (A×A)),(y : Register (A×A))⟫_ℂ).re := by
    rw [lp.inner_eq_tsum,lp.inner_eq_tsum]
    simp only [tsum_fintype,Complex.re_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact real_inner_eq_re_inner (𝕜 := ℂ) (x.val i) (y.val i)
  rw [hr]
  exact (Complex.conj_eq_iff_re.mp hs).symm

/-- Every Hermitian real ONB is complex orthonormal in the ambient space. -/
lemma hermitianBasis_orthonormal {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ (hermitianSpace A)) :
    Orthonormal ℂ (fun i => (b i : Register (A×A))) := by
  classical
  rw [orthonormal_iff_ite]
  intro i j
  rw [hermitianSpace_inner_real,orthonormal_iff_ite.mp b.orthonormal]
  split_ifs <;> norm_num

private def hermitianPart (x : Register (A×A)) : hermitianSpace A :=
  ⟨coefficientVector (fun a b => (x (a,b)+star (x (b,a)))/2),by
    intro a b
    simp [coefficientVector_apply,map_div₀,map_add,add_comm]⟩

private def imaginaryPart (x : Register (A×A)) : hermitianSpace A :=
  ⟨coefficientVector (fun a b => -(Complex.I/2)*(x (a,b)-star (x (b,a)))),by
    intro a b
    simp only [coefficientVector_apply,map_mul,map_neg,map_div₀,map_sub,star_star,
      Complex.star_def,Complex.conj_I,map_ofNat,Complex.conj_conj]
    ring⟩

private lemma hermitian_decomposition (x : Register (A×A)) :
    x=(hermitianPart x : Register (A×A))+Complex.I • (imaginaryPart x : Register (A×A)) := by
  ext ab
  rcases ab with ⟨a,b⟩
  simp only [hermitianPart,imaginaryPart,lp.coeFn_add,Pi.add_apply,lp.coeFn_smul,
    Pi.smul_apply,smul_eq_mul,coefficientVector_apply]
  ring_nf
  simp
  ring

lemma hermitianBasis_complex_span {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ (hermitianSpace A)) :
    ⊤≤Submodule.span ℂ (Set.range (fun i => (b i : Register (A×A)))) := by
  let S := Submodule.span ℂ (Set.range (fun i => (b i : Register (A×A))))
  have hx (x : hermitianSpace A) : (x : Register (A×A))∈S := by
    have he := b.sum_repr x
    have he' := congrArg (fun z : hermitianSpace A => (z : Register (A×A))) he
    dsimp only at he'
    simp only [Submodule.coe_sum,Submodule.coe_smul_of_tower] at he'
    rw [← he']
    apply Submodule.sum_mem
    intro i _
    change ((b.repr x i : ℝ) : ℂ) • (b i : Register (A×A))∈S
    exact S.smul_mem _ (Submodule.subset_span ⟨i,rfl⟩)
  intro x _
  rw [hermitian_decomposition x]
  exact S.add_mem (hx _) (S.smul_mem _ (hx _))

/-- The same vectors, as a genuine complex orthonormal basis. -/
def complexHermitianBasis {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ (hermitianSpace A)) :
    OrthonormalBasis ι ℂ (Register (A×A)) :=
  OrthonormalBasis.mk (hermitianBasis_orthonormal b) (hermitianBasis_complex_span b)

@[simp] lemma complexHermitianBasis_apply {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ (hermitianSpace A)) (i : ι) :
    complexHermitianBasis b i=(b i : Register (A×A)) := by
  simp [complexHermitianBasis,OrthonormalBasis.coe_mk]

end Cloning.PCTFlatGaussianCross
