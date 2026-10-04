import Cloning.PCTRankPurificationMoment
import Cloning.PCTRankPurificationBlockAlgebra
import Cloning.TensorSchurHaarOrthogonality

/-! Finite coefficient tests for equality of rectangular Haar moments. -/
noncomputable section
open scoped BigOperators Classical Matrix Kronecker Matrix.Norms.L2Operator
open Matrix MeasureTheory
namespace Cloning.PCTRankPurification
open Cloning.PCTPurificationChannel Cloning.TensorLie
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
variable {A B I J : Type*} [Fintype A] [Fintype B] [Fintype I] [Fintype J]
  [DecidableEq A] [DecidableEq B] [DecidableEq I] [DecidableEq J]

def matrixVector (T : Matrix A B ℂ) : A×B → ℂ := fun ab => T ab.1 ab.2

def matrixMoment (T : Matrix A B ℂ) : Matrix (A×B) (A×B) ℂ :=
  Matrix.vecMulVec (matrixVector T) (star (matrixVector T))

@[simp] theorem matrixMoment_apply (T : Matrix A B ℂ) (a c : A) (b d : B) :
    matrixMoment T (a,b) (c,d)=T a b*star (T c d) := rfl

theorem matrixVector_mul (L : Matrix I A ℂ) (T : Matrix A B ℂ) (R : Matrix B J ℂ) :
    matrixVector (L*T*R)=(L⊗ₖRᵀ)*ᵥmatrixVector T := by
  funext ⟨i,j⟩
  simp only [matrixVector,Matrix.mul_apply,Matrix.mulVec,dotProduct,
    Matrix.kronecker_apply,Matrix.transpose_apply,Fintype.sum_prod_type]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem matrixMoment_mul (L : Matrix I A ℂ) (T : Matrix A B ℂ) (R : Matrix B J ℂ) :
    matrixMoment (L*T*R)=(L⊗ₖRᵀ)*matrixMoment T*(L⊗ₖRᵀ)ᴴ := by
  unfold matrixMoment
  rw [matrixVector_mul,Matrix.mul_vecMulVec,Matrix.vecMulVec_mul,
    Matrix.vecMul_conjTranspose,star_star]

variable {S T : Type*} [MeasurableSpace S] [MeasurableSpace T]

def matrixMomentIntegral (μ : Measure S) (f : S → Matrix A B ℂ) :=
  ∫ u, matrixMoment (f u) ∂μ

theorem matrixMomentIntegral_apply (μ : Measure S) (f : S → Matrix A B ℂ)
    (hf : Integrable (fun u => matrixMoment (f u)) μ) (a c : A) (b d : B) :
    matrixMomentIntegral μ f (a,b) (c,d)=∫u,f u a b*star (f u c d) ∂μ := by
  exact ((matrixEntryCLM (a,b) (c,d)).integral_comp_comm hf).symm

theorem matrixMomentIntegral_mul (μ : Measure S) (f : S → Matrix A B ℂ)
    (hf : Integrable (fun u => matrixMoment (f u)) μ)
    (L : Matrix I A ℂ) (R : Matrix B J ℂ) :
    matrixMomentIntegral μ (fun u => L*f u*R)=
      (L⊗ₖRᵀ)*matrixMomentIntegral μ f*(L⊗ₖRᵀ)ᴴ := by
  simpa only [matrixMomentIntegral,matrixMoment_mul] using
    (rectangularSandwichCLM (L⊗ₖRᵀ)).integral_comp_comm hf

theorem integrable_matrixMoment_mul (μ : Measure S) (f : S → Matrix A B ℂ)
    (hf : Integrable (fun u => matrixMoment (f u)) μ)
    (L : Matrix I A ℂ) (R : Matrix B J ℂ) :
    Integrable (fun u => matrixMoment (L*f u*R)) μ := by
  simpa only [matrixMoment_mul] using
    (rectangularSandwichCLM (L⊗ₖRᵀ)).integrable_comp hf

/-- Equality of second moments in any complete pair of coordinate frames
implies literal equality of the original bipartite matrices. -/
theorem matrixMomentIntegral_eq_of_frame_coefficients
    (μ : Measure S) (ν : Measure T) (f : S → Matrix A B ℂ) (g : T → Matrix A B ℂ)
    (hf : Integrable (fun u => matrixMoment (f u)) μ)
    (hg : Integrable (fun u => matrixMoment (g u)) ν)
    (F : Matrix A I ℂ) (G : Matrix B J ℂ) (hF : F*Fᴴ=1) (hG : G*Gᴴ=1)
    (hcoeff : ∀ i k j l,
      (∫u,(Fᴴ*f u*G) i j*star ((Fᴴ*f u*G) k l) ∂μ)=
      ∫v,(Fᴴ*g v*G) i j*star ((Fᴴ*g v*G) k l) ∂ν) :
    matrixMomentIntegral μ f=matrixMomentIntegral ν g := by
  have he : matrixMomentIntegral μ (fun u => Fᴴ*f u*G)=
      matrixMomentIntegral ν (fun v => Fᴴ*g v*G) := by
    ext ⟨i,j⟩ ⟨k,l⟩
    rw [matrixMomentIntegral_apply _ _ (integrable_matrixMoment_mul _ _ hf _ _),
      matrixMomentIntegral_apply _ _ (integrable_matrixMoment_mul _ _ hg _ _)]
    exact hcoeff i k j l
  have he' := congrArg (fun X => (F⊗ₖGᴴᵀ)*X*(F⊗ₖGᴴᵀ)ᴴ) he
  dsimp only at he'
  rw [← matrixMomentIntegral_mul μ (fun u => Fᴴ*f u*G) (integrable_matrixMoment_mul _ _ hf _ _) F Gᴴ,
    ← matrixMomentIntegral_mul ν (fun u => Fᴴ*g u*G) (integrable_matrixMoment_mul _ _ hg _ _) F Gᴴ] at he'
  have hrec (X : Matrix A B ℂ) : F*(Fᴴ*X*G)*Gᴴ=X := by
    calc
      _=(F*Fᴴ)*X*(G*Gᴴ) := by simp only [Matrix.mul_assoc]
      _=X := by rw [hF,hG,Matrix.one_mul,Matrix.mul_one]
  simpa only [hrec] using he'

@[simp] theorem rectangularMoment_eq_matrixMoment (n : ℕ) (X : Matrix A B ℂ) :
    rectangularMoment n X=matrixMoment (tensorPower n X) := rfl

end Cloning.PCTRankPurification
