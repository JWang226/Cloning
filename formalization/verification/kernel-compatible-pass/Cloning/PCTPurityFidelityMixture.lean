import Cloning.PCTPhysicalState
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! Exact coefficient-integral formulas for the purity of tensor mixtures.
These finite identities hold before any limiting estimate. -/
noncomputable section
open scoped BigOperators Matrix InnerProductSpace ComplexOrder
open MeasureTheory
namespace Cloning.PCTPurity
open Cloning.PCTPurificationChannel Cloning.PCTPhysicalState
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
variable {X ι : Type*} [MeasurableSpace X] [Fintype ι] [DecidableEq ι]

def matrixMixture (μ : Measure X) (M : X→Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  fun i j => ∫ z,M z i j ∂μ

theorem integrable_trace_mul_left (μ : Measure X) (M : X→Matrix ι ι ℂ)
    (hM : ∀i j,Integrable (fun z => M z i j) μ) (B : Matrix ι ι ℂ) :
    Integrable (fun z => Matrix.trace (B*M z)) μ := by
  simp only [Matrix.trace,Matrix.diag,Matrix.mul_apply]
  exact integrable_finset_sum _ (fun i _ => integrable_finset_sum _
    (fun j _ => (hM j i).const_mul (B i j)))

theorem integrable_trace_mul_right (μ : Measure X) (M : X→Matrix ι ι ℂ)
    (hM : ∀i j,Integrable (fun z => M z i j) μ) (B : Matrix ι ι ℂ) :
    Integrable (fun z => Matrix.trace (M z*B)) μ := by
  simp only [Matrix.trace,Matrix.diag,Matrix.mul_apply]
  exact integrable_finset_sum _ (fun i _ => integrable_finset_sum _
    (fun j _ => (hM i j).mul_const (B j i)))

theorem trace_mul_matrixMixture_left (μ : Measure X) (M : X→Matrix ι ι ℂ)
    (hM : ∀i j,Integrable (fun z => M z i j) μ) (B : Matrix ι ι ℂ) :
    Matrix.trace (B*matrixMixture μ M)=∫ z,Matrix.trace (B*M z) ∂μ := by
  simp only [Matrix.trace,Matrix.diag,Matrix.mul_apply,matrixMixture]
  rw [integral_finset_sum _ (fun i _ => integrable_finset_sum _
    (fun j _ => (hM j i).const_mul (B i j)))]
  apply Finset.sum_congr rfl
  intro i hi
  rw [integral_finset_sum _ (fun j _ => (hM j i).const_mul (B i j))]
  simp only [integral_const_mul]

theorem trace_mul_matrixMixture_right (μ : Measure X) (M : X→Matrix ι ι ℂ)
    (hM : ∀i j,Integrable (fun z => M z i j) μ) (B : Matrix ι ι ℂ) :
    Matrix.trace (matrixMixture μ M*B)=∫ z,Matrix.trace (M z*B) ∂μ := by
  simp only [Matrix.trace,Matrix.diag,Matrix.mul_apply,matrixMixture]
  rw [integral_finset_sum _ (fun i _ => integrable_finset_sum _
    (fun j _ => (hM i j).mul_const (B j i)))]
  apply Finset.sum_congr rfl
  intro i hi
  rw [integral_finset_sum _ (fun j _ => (hM i j).mul_const (B j i))]
  simp only [integral_mul_const]

theorem matrixMixture_purity (μ : Measure X) (M : X→Matrix ι ι ℂ)
    (hM : ∀i j,Integrable (fun z => M z i j) μ) :
    Matrix.trace (matrixMixture μ M*matrixMixture μ M)=
      ∫ z,∫ w,Matrix.trace (M z*M w) ∂μ ∂μ := by
  rw [trace_mul_matrixMixture_right μ M hM]
  exact integral_congr_ae (Filter.Eventually.of_forall (fun z => trace_mul_matrixMixture_left μ M hM (M z)))

theorem matrixMixture_purity_re (μ : Measure X) (M : X→Matrix ι ι ℂ)
    (hM : ∀i j,Integrable (fun z => M z i j) μ) :
    (Matrix.trace (matrixMixture μ M*matrixMixture μ M)).re=
      ∫ z,∫ w,(Matrix.trace (M z*M w)).re ∂μ ∂μ := by
  have hi : Integrable (fun z => ∫ w,Matrix.trace (M z*M w) ∂μ) μ := by
    simp_rw [←trace_mul_matrixMixture_left μ M hM]
    exact integrable_trace_mul_right μ M hM _
  rw [matrixMixture_purity μ M hM]
  have hre : (∫ z,∫ w,Matrix.trace (M z*M w) ∂μ ∂μ).re=
      ∫ z,(∫ w,Matrix.trace (M z*M w) ∂μ).re ∂μ :=
    (Complex.reCLM.integral_comp_comm hi).symm
  rw [hre]
  apply integral_congr_ae
  filter_upwards [] with z
  exact (Complex.reCLM.integral_comp_comm (integrable_trace_mul_left μ M hM (M z))).symm

variable {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]

def tensorMixtureMatrix (μ : Measure X) (ρ : X→Matrix A A ℂ) (L : ℕ) :
    Matrix (Fin L→A) (Fin L→A) ℂ := matrixMixture μ (fun z => tensorPower L (ρ z))

theorem tensorMixtureMatrix_purity (μ : Measure X) (ρ : X→Matrix A A ℂ) (L : ℕ)
    (hρ : ∀i j,Integrable (fun z => tensorPower L (ρ z) i j) μ) :
    Matrix.trace (tensorMixtureMatrix μ ρ L*tensorMixtureMatrix μ ρ L)=
      ∫ z,∫ w,(Matrix.trace (ρ z*ρ w))^L ∂μ ∂μ := by
  rw [tensorMixtureMatrix,matrixMixture_purity μ _ hρ]
  simp only [←tensorPower_mul,trace_tensorPower]

theorem tensorMixtureMatrix_purity_re (μ : Measure X) (ρ : X→Matrix A A ℂ) (L : ℕ)
    (hρ : ∀i j,Integrable (fun z => tensorPower L (ρ z) i j) μ)
    (hreal : ∀z w,(Matrix.trace (ρ z*ρ w)).im=0) :
    (Matrix.trace (tensorMixtureMatrix μ ρ L*tensorMixtureMatrix μ ρ L)).re=
      ∫ z,∫ w,((Matrix.trace (ρ z*ρ w)).re)^L ∂μ ∂μ := by
  rw [tensorMixtureMatrix,matrixMixture_purity_re μ _ hρ]
  simp only [←tensorPower_mul,trace_tensorPower]
  apply integral_congr_ae
  filter_upwards [] with z
  apply integral_congr_ae
  filter_upwards [] with w
  have he : Matrix.trace (ρ z*ρ w)=((Matrix.trace (ρ z*ρ w)).re : ℂ) := by
    exact Complex.ext rfl (by simpa using hreal z w)
  rw [he,←Complex.ofReal_pow,Complex.ofReal_re]
  simp only [Complex.ofReal_re]

end Cloning.PCTPurity
