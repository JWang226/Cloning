import Cloning.WeylGNSRegular
import Mathlib.Algebra.BigOperators.Fin

/-! The actual real-linear symplectic Bogoliubov transformation on the doubled
signal/idler phase space. All modes may have different gains. -/
noncomputable section
open scoped BigOperators Topology
namespace Cloning.WeylSqueezer
open Cloning.MultimodeCoherent Cloning.WeylGNS
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 250000
variable {d : ℕ}

/-- The first and second blocks are the signal and idler amplitudes. -/
def transform (c s : Fin d → ℝ) (z : Fin (d+d) → ℂ) : Fin (d+d) → ℂ :=
  Fin.append (fun i => (c i : ℂ)*z (Fin.castAdd d i)+(s i : ℂ)*(starRingEnd ℂ) (z (Fin.natAdd d i)))
    (fun i => (c i : ℂ)*z (Fin.natAdd d i)+(s i : ℂ)*(starRingEnd ℂ) (z (Fin.castAdd d i)))

@[simp] theorem transform_left (c s : Fin d → ℝ) (z : Fin (d+d) → ℂ) (i : Fin d) :
    transform c s z (Fin.castAdd d i)=
      (c i : ℂ)*z (Fin.castAdd d i)+(s i : ℂ)*(starRingEnd ℂ) (z (Fin.natAdd d i)) := by
  simp only [transform, Fin.append_left, Fin.append_right]

@[simp] theorem transform_right (c s : Fin d → ℝ) (z : Fin (d+d) → ℂ) (i : Fin d) :
    transform c s z (Fin.natAdd d i)=
      (c i : ℂ)*z (Fin.natAdd d i)+(s i : ℂ)*(starRingEnd ℂ) (z (Fin.castAdd d i)) := by
  simp only [transform, Fin.append_left, Fin.append_right]

@[simp] theorem transform_zero (c s : Fin d → ℝ) : transform c s 0=0 := by
  ext i
  refine Fin.addCases ?_ ?_ i <;> intro j <;>
    simp only [transform_left, transform_right, Pi.zero_apply, map_zero, mul_zero, add_zero]

@[simp] theorem transform_add (c s : Fin d → ℝ) (a b : Fin (d+d) → ℂ) :
    transform c s (a+b)=transform c s a+transform c s b := by
  ext i
  refine Fin.addCases ?_ ?_ i <;> intro j <;>
    simp only [transform_left, transform_right, Pi.add_apply, map_add] <;> ring

@[simp] theorem transform_smul (c s : Fin d → ℝ) (t : ℝ) (a : Fin (d+d) → ℂ) :
    transform c s (t • a)=t • transform c s a := by
  ext i
  refine Fin.addCases ?_ ?_ i <;> intro j <;>
    simp only [transform_left, transform_right, Pi.smul_apply, Complex.real_smul,
      map_mul, Complex.conj_ofReal] <;> ring

theorem continuous_transform (c s : Fin d → ℝ) : Continuous (transform c s) := by
  apply continuous_pi
  intro i
  refine Fin.addCases ?_ ?_ i <;> intro j
  · simp only [transform_left]
    fun_prop
  · simp only [transform_right]
    fun_prop

private theorem inverse_pair (c s : ℝ) (hcs : c^2-s^2=1) (a b : ℂ) :
    (c : ℂ)*((c : ℂ)*a+(s : ℂ)*(starRingEnd ℂ) b)+(-s : ℝ)*(starRingEnd ℂ) ((c : ℂ)*b+(s : ℂ)*(starRingEnd ℂ) a)=a := by
  have hh : (c : ℂ)^2-(s : ℂ)^2=1 := by exact_mod_cast hcs
  simp only [map_add, map_mul, Complex.conj_ofReal, starRingEnd_self_apply, Complex.ofReal_neg]
  linear_combination a*hh

theorem transform_inverse (c s : Fin d → ℝ) (hcs : ∀i,c i^2-s i^2=1)
    (z : Fin (d+d) → ℂ) : transform c (-s) (transform c s z)=z := by
  ext i
  refine Fin.addCases ?_ ?_ i <;> intro j <;>
    simp only [transform_left, transform_right, Pi.neg_apply]
  · exact inverse_pair (c j) (s j) (hcs j) _ _
  · exact inverse_pair (c j) (s j) (hcs j) _ _

theorem transform_append (c s : Fin d → ℝ) (a b : Fin d → ℂ) :
    transform c s (Fin.append a b)=
      Fin.append (fun i => (c i : ℂ)*a i+(s i : ℂ)*(starRingEnd ℂ) (b i))
        (fun i => (c i : ℂ)*b i+(s i : ℂ)*(starRingEnd ℂ) (a i)) := by
  ext i
  refine Fin.addCases ?_ ?_ i <;> intro j <;>
    simp only [transform_left, transform_right, Fin.append_left, Fin.append_right]

theorem transform_signal (c s : Fin d → ℝ) (a : Fin d → ℂ) :
    transform c s (Fin.append a 0)=
      Fin.append (fun i => (c i : ℂ)*a i)
        (fun i => (s i : ℂ)*(starRingEnd ℂ) (a i)) := by
  rw [transform_append]
  simp only [Pi.zero_apply, map_zero, mul_zero, add_zero, zero_add]

/-- A genuine real-linear automorphism, with inverse obtained by reversing the
squeezing sign. -/
def phaseEquiv (c s : Fin d → ℝ) (hcs : ∀i,c i^2-s i^2=1) :
    (Fin (d+d) → ℂ) ≃L[ℝ] (Fin (d+d) → ℂ) where
  toFun := transform c s
  invFun := transform c (-s)
  left_inv := transform_inverse c s hcs
  right_inv := by
    intro z
    have hh : ∀i,c i^2-(-s i)^2=1 := by simpa using hcs
    simpa only [neg_neg] using transform_inverse c (-s) hh z
  map_add' := transform_add c s
  map_smul' := transform_smul c s
  continuous_toFun := continuous_transform c s
  continuous_invFun := continuous_transform c (-s)

private theorem phase_pair (c s : ℝ) (hcs : c^2-s^2=1) (a b u v : ℂ) :
    ComplexCoherent.displacementPhase ((c : ℂ)*a+(s : ℂ)*(starRingEnd ℂ) b)
        ((c : ℂ)*u+(s : ℂ)*(starRingEnd ℂ) v)*
      ComplexCoherent.displacementPhase ((c : ℂ)*b+(s : ℂ)*(starRingEnd ℂ) a)
        ((c : ℂ)*v+(s : ℂ)*(starRingEnd ℂ) u)=
      ComplexCoherent.displacementPhase a u*ComplexCoherent.displacementPhase b v := by
  have hh : (c : ℂ)^2-(s : ℂ)^2=1 := by exact_mod_cast hcs
  unfold ComplexCoherent.displacementPhase
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  simp only [map_add, map_mul, Complex.conj_ofReal, starRingEnd_self_apply]
  linear_combination ((a*(starRingEnd ℂ) u-(starRingEnd ℂ) a*u+b*(starRingEnd ℂ) v-(starRingEnd ℂ) b*v)/2)*hh

/-- The Weyl cocycle is exactly preserved, including the complex phase. -/
theorem displacementPhase_transform (c s : Fin d → ℝ) (hcs : ∀i,c i^2-s i^2=1)
    (a b : Fin (d+d) → ℂ) :
    displacementPhase (transform c s a) (transform c s b)=displacementPhase a b := by
  unfold displacementPhase
  rw [Fin.prod_univ_add, Fin.prod_univ_add, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  simp only [transform_left, transform_right]
  exact phase_pair (c i) (s i) (hcs i) _ _ _ _

/-- The pulled-back action is an actual regular Weyl representation on doubled
Fock space; its implementing isometry is not assumed. -/
def regularWeyl (c s : Fin d → ℝ) (hcs : ∀i,c i^2-s i^2=1) :
    RegularWeyl (d+d) (Fock (d+d)) where
  toIsometry z := weylUnitary (transform c s z)
  zero_apply := by intro v; simp
  mul_apply := by
    intro a b v
    have hh := (fockRegularWeyl (d+d)).mul_apply (transform c s a) (transform c s b) v
    rw [displacementPhase_transform c s hcs, ← transform_add] at hh
    exact hh
  continuous_apply := by
    intro v
    exact (continuous_displacement v).comp (continuous_transform c s)

@[simp] theorem regularWeyl_operator (c s : Fin d → ℝ) (hcs : ∀i,c i^2-s i^2=1)
    (z : Fin (d+d) → ℂ) :
    (regularWeyl c s hcs).operator z=displacement (transform c s z) := rfl

/-- Physical modewise gains give the hyperbolic identity required above. -/
theorem gain_hyperbolic (g : Fin d → ℝ) (hg : ∀i,1≤g i) :
    ∀i,(Real.sqrt (g i))^2-(Real.sqrt (g i-1))^2=1 := by
  intro i
  rw [Real.sq_sqrt (by linarith [hg i]), Real.sq_sqrt (by linarith [hg i])]
  ring

end Cloning.WeylSqueezer
