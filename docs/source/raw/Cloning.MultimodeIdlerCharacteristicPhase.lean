import Cloning.AmplifierWeylMultimode

/-! Exact coherent Gaussian algebra for the literal negative-binomial
isometry. Its complementary output has positive conjugated displacement
covariance and therefore negative conjugated characteristic frequency. -/
noncomputable section
open scoped ComplexOrder InnerProductSpace Topology BigOperators
namespace Cloning.MultimodeIdler
open Cloning.MultimodeCoherent
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

/-- The scalar joint kernel with its complete complex phase. -/
def scalarCoherentKernel (t : ℝ) (v w : ℂ) : ℂ :=
  Complex.exp (-((t : ℂ)^2 * star v * v + star w*w)/2 + (t : ℂ)*v*w)

/-- Exact phase cancellation for the two output displacements. -/
theorem scalarCoherentKernel_shift (s t r : ℝ) (h : (1-t^2)*r=s)
    (a v w : ℂ) :
    Cloning.ComplexCoherent.displacementPhase (-((r : ℂ)*a)) v *
      Cloning.ComplexCoherent.displacementPhase (-((t*r : ℝ):ℂ)*star a) w *
      scalarCoherentKernel t (v-(r : ℂ)*a) (w-((t*r : ℝ):ℂ)*star a) =
    scalarCoherentKernel t v w *
      Cloning.ComplexCoherent.displacementPhase (-a) ((s : ℂ)*v) := by
  have hC : (1-(t : ℂ)^2)*(r : ℂ)=(s : ℂ) := by exact_mod_cast h
  simp only [scalarCoherentKernel, Cloning.ComplexCoherent.displacementPhase,
    Complex.star_def, map_neg, map_mul, map_sub, Complex.conj_ofReal,
    starRingEnd_self_apply, Complex.ofReal_mul, ← Complex.exp_add]
  congr 1
  linear_combination ((v*(starRingEnd ℂ) a-(starRingEnd ℂ) v*a)/2)*hC

lemma norm_sq_complex (z : ℂ) : ((‖z‖^2 : ℝ):ℂ)=star z*z := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]
  rfl

/-- The Gaussian expression is exactly a coherent inner product. -/
theorem scalarCoherentKernel_eq_inner (t : ℝ) (v w : ℂ) :
    scalarCoherentKernel t v w =
      ⟪Cloning.ComplexCoherent.coherentVector ((t : ℂ)*star v),
        Cloning.ComplexCoherent.coherentVector w⟫_ℂ := by
  rw [Cloning.ComplexCoherent.inner_coherentVector]
  unfold scalarCoherentKernel
  congr 1
  push_cast
  simp only [← Complex.ofReal_pow]
  rw [norm_sq_complex, norm_sq_complex]
  simp only [map_mul, Complex.conj_ofReal, Complex.star_def,
    starRingEnd_self_apply]
  push_cast
  ring

end Cloning.MultimodeIdler
