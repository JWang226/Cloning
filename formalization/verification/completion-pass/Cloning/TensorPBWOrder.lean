import Cloning.TensorCyclicFiltration
import Mathlib.Data.List.Sort
import Mathlib.Data.Finset.Sort

/-! A concrete total order and termination measure for physical lowering words. -/
noncomputable section
namespace Cloning.TensorLie
set_option maxHeartbeats 1000000
variable {d : ℕ}

/-- Lexicographic order of positive roots, encoded without changing the ambient
product order on pairs of finite indices. -/
def rootKey (a : PositiveRoot d) : ℕ := d * a.val.1.val + a.val.2.val

theorem rootKey_injective : Function.Injective (@rootKey d) := by
  intro a b h
  apply Subtype.ext
  apply Prod.ext <;> apply Fin.ext
  · have ha := a.val.2.isLt
    have hb := b.val.2.isLt
    simp only [rootKey] at h
    have hdiv := congrArg (fun x => x / d) h
    have hd : 0 < d := by omega
    simpa [Nat.add_comm, Nat.add_mul_div_left _ _ hd, Nat.div_eq_of_lt ha,
      Nat.div_eq_of_lt hb] using hdiv
  · have ha := a.val.2.isLt
    have hb := b.val.2.isLt
    have hmod := congrArg (fun x => x % d) h
    simpa [rootKey, Nat.add_mod, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] using hmod

def RootOrdered (w : List (PositiveRoot d)) : Prop :=
  w.Pairwise (fun a b => rootKey a ≤ rootKey b)

def rootInversions : List (PositiveRoot d) → ℕ
  | [] => 0
  | a :: w => rootInversions w + w.countP (fun b => rootKey b < rootKey a)

theorem rootInversions_swap (p w : List (PositiveRoot d)) (a b : PositiveRoot d)
    (h : rootKey b < rootKey a) :
    rootInversions (p ++ b :: a :: w) + 1 = rootInversions (p ++ a :: b :: w) := by
  induction p with
  | nil =>
    simp only [List.nil_append, rootInversions, List.countP_cons]
    simp only [h, Nat.not_lt.mpr (Nat.le_of_lt h), decide_true, decide_false,
      Bool.false_eq_true, ↓reduceIte]
    omega
  | cons c p ih =>
    simp only [List.cons_append, rootInversions, List.countP_append, List.countP_cons]
    omega

theorem exists_adjacent_rootInversion (w : List (PositiveRoot d)) (h : ¬ RootOrdered w) :
    ∃ p a b t, w = p ++ a :: b :: t ∧ rootKey b < rootKey a := by
  induction w with
  | nil => exact (h (by simp [RootOrdered])).elim
  | cons a w ih =>
    cases w with
    | nil => exact (h (by simp [RootOrdered])).elim
    | cons b t =>
      by_cases hab : rootKey a ≤ rootKey b
      · have ht : ¬ RootOrdered (b :: t) := by
          intro ht
          apply h
          rw [RootOrdered, List.pairwise_cons] at ht ⊢
          refine ⟨?_, List.pairwise_cons.mpr ht⟩
          intro c hc
          rcases List.mem_cons.mp hc with rfl | hc
          · exact hab
          · exact hab.trans (ht.1 c hc)
        obtain ⟨p, c, e, u, hp, hce⟩ := ih ht
        exact ⟨a :: p, c, e, u, by simp [hp], hce⟩
      · exact ⟨[], a, b, t, rfl, Nat.lt_of_not_ge hab⟩

theorem loweringHeight_append (p w : List (PositiveRoot d)) :
    loweringHeight (p ++ w) = loweringHeight p + loweringHeight w := by
  induction p with
  | nil => simp [loweringHeight]
  | cons a p ih => simp [loweringHeight, ih, Nat.add_assoc]

theorem loweringWord_append {n : ℕ} (Ω : TensorRegister n (Fin d))
    (p w : List (PositiveRoot d)) :
    loweringWord Ω (p ++ w) = loweringWord (loweringWord Ω w) p := by
  induction p with
  | nil => rfl
  | cons a p ih => simp only [List.cons_append, loweringWord, ih]

def loweringOperator (n : ℕ) : List (PositiveRoot d) →
    (TensorRegister n (Fin d) →L[ℂ] TensorRegister n (Fin d))
  | [] => ContinuousLinearMap.id ℂ _
  | a :: w => collectiveGenerator n a.val.2 a.val.1 * loweringOperator n w

@[simp] theorem loweringOperator_apply {n : ℕ} (w : List (PositiveRoot d))
    (Ω : TensorRegister n (Fin d)) : loweringOperator n w Ω = loweringWord Ω w := by
  induction w with
  | nil => rfl
  | cons a w ih => simp only [loweringOperator, ContinuousLinearMap.mul_apply, ih, loweringWord]

end Cloning.TensorLie
