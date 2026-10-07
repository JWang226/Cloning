import Cloning.WeylSqueezerProduct

/-! Displacements factor on literal Fock product vectors, first on coherent
vectors and then on the whole Hilbert spaces by continuity. -/
noncomputable section
open scoped BigOperators InnerProductSpace Topology
namespace Cloning.WeylSqueezerProduct
open Cloning.MultimodeCoherent
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
variable {a b : ℕ}

theorem coherent_ext {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {T S : Fock a →L[ℂ] E}
    (h : ∀z, T (coherentVector z)=S (coherentVector z)) : T=S := by
  have he : (fun v => T v)=(fun v => S v) := by
    apply coherentCombination_dense.equalizer T.continuous S.continuous
    funext c
    simp only [Function.comp_apply,coherentCombination,Finsupp.linearCombination_apply,
      Finsupp.sum,map_sum,map_smul,h]
  exact DFunLike.ext _ _ (congrFun he)

@[simp] theorem tensorVector_smul_left (c : ℂ) (x : Fock a) (y : Fock b) :
    tensorVector (c • x) y=c • tensorVector x y := (tensorRight y).map_smul c x

@[simp] theorem tensorVector_smul_right (c : ℂ) (x : Fock a) (y : Fock b) :
    tensorVector x (c • y)=c • tensorVector x y := (tensorLeft x).map_smul c y

@[simp] theorem tensorVector_coherent (z : Fin a → ℂ) (w : Fin b → ℂ) :
    tensorVector (coherentVector z) (coherentVector w)=coherentVector (Fin.append z w) := by
  ext k
  simp only [tensorVector_apply,coherentVector_apply,Fin.prod_univ_add,
    Fin.append_left,Fin.append_right]

theorem displacementPhase_append (z u : Fin a → ℂ) (w v : Fin b → ℂ) :
    displacementPhase (Fin.append z w) (Fin.append u v)=
      displacementPhase z u*displacementPhase w v := by
  simp only [displacementPhase,Fin.prod_univ_add,Fin.append_left,Fin.append_right]

theorem append_add (z u : Fin a → ℂ) (w v : Fin b → ℂ) :
    Fin.append z w+Fin.append u v=Fin.append (z+u) (w+v) := by
  ext i
  refine Fin.addCases ?_ ?_ i <;> intro j <;> simp only [Pi.add_apply,Fin.append_left,Fin.append_right]

theorem displacement_append_coherent (z : Fin a → ℂ) (w : Fin b → ℂ)
    (u : Fin a → ℂ) (v : Fin b → ℂ) :
    displacement (Fin.append z w) (tensorVector (coherentVector u) (coherentVector v))=
      tensorVector (displacement z (coherentVector u)) (displacement w (coherentVector v)) := by
  rw [tensorVector_coherent,displacement_coherentVector,displacement_coherentVector,
    displacement_coherentVector,tensorVector_smul_left,tensorVector_smul_right,
    tensorVector_coherent,smul_smul,displacementPhase_append,append_add]

theorem displacement_append_tensor (z : Fin a → ℂ) (w : Fin b → ℂ)
    (x : Fock a) (y : Fock b) :
    displacement (Fin.append z w) (tensorVector x y)=
      tensorVector (displacement z x) (displacement w y) := by
  have hc (u : Fin a → ℂ) :
      (displacement (Fin.append z w)).comp (tensorLeft (coherentVector u))=
        (tensorLeft (displacement z (coherentVector u))).comp (displacement w) := by
    apply coherent_ext
    intro v
    exact displacement_append_coherent z w u v
  have he : (displacement (Fin.append z w)).comp (tensorRight y)=
      (tensorRight (displacement w y)).comp (displacement z) := by
    apply coherent_ext
    intro u
    exact congrArg (fun T : Fock b →L[ℂ] Fock (a+b) => T y) (hc u)
  exact congrArg (fun T : Fock a →L[ℂ] Fock (a+b) => T x) he

end Cloning.WeylSqueezerProduct
