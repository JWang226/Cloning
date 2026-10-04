import Cloning.TensorLocalUnitaryTail
import Cloning.TensorCartanCutoffMatrixLimit

/-! Physical normalized root matrix elements converge to the oscillator ladder
matrix elements in the common complete cutoff frame. -/
noncomputable section
open scoped BigOperators InnerProductSpace Topology
open Filter
namespace Cloning.TensorLocalUnitary
open Cloning.TensorLie
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

/-- Exact coefficient of one additional creator in a normalized PBW word. -/
theorem creator_normalizedWord {ι H : Type*} [DecidableEq ι]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (F : ι → H →L[ℂ] H) (Ω : H) (a : ι) (w : List ι) :
    F a (PBW.normalizedWord F w Ω) =
      (Real.sqrt ((w.count a : ℝ)+1) : ℂ) • PBW.normalizedWord F (a::w) Ω := by
  simp only [PBW.normalizedWord, map_smul, PBW.word_cons, smul_smul]
  congr 1
  have hs : Real.sqrt ((w.count a : ℝ)+1) ≠ 0 := by positivity
  have hf : Real.sqrt (PBW.occupationFactorial w : ℝ) ≠ 0 := by
    exact ne_of_gt (Real.sqrt_pos.mpr (Nat.cast_pos.mpr (PBW.occupationFactorial_pos w)))
  have he : (Real.sqrt (PBW.occupationFactorial w : ℝ))⁻¹ =
      Real.sqrt ((w.count a : ℝ)+1) *
        (Real.sqrt (PBW.occupationFactorial (a::w) : ℝ))⁻¹ := by
    simp only [PBW.occupationFactorial, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    rw [Real.sqrt_mul (by positivity)]
    field_simp
  exact_mod_cast he

variable {d : ℕ}

theorem normalizedCreator_normalizedLoweringWord {n : ℕ}
    (Ω : TensorRegister n (Fin d)) (mu : Fin d → ℕ)
    (a : PositiveRoot d) (w : List (PositiveRoot d)) :
    normalizedCreator n mu a.val.1 a.val.2 (normalizedLoweringWord Ω mu w) =
      (Real.sqrt ((w.count a : ℝ)+1) : ℂ) • normalizedLoweringWord Ω mu (a::w) :=
  by
    simpa only [normalizedLoweringWord, List.count_eq_countP, Bool.beq_eq_decide_eq] using
      creator_normalizedWord (fun b : PositiveRoot d => normalizedCreator n mu b.val.1 b.val.2) Ω a w


def creationEntry (a : PositiveRoot d) (u v : List (PositiveRoot d)) : ℂ :=
  (Real.sqrt ((v.count a : ℝ)+1) : ℂ) * (if u.Perm (a::v) then 1 else 0)

def annihilationEntry (a : PositiveRoot d) (u v : List (PositiveRoot d)) : ℂ :=
  star (creationEntry a v u)

def oscillatorEntry (z : PositiveRoot d → ℂ) (u v : List (PositiveRoot d)) : ℂ :=
  ∑ a, (z a * creationEntry a u v - star (z a) * annihilationEntry a u v)

variable (mu : ℕ → Fin d → ℕ) (hmu : ∀ N, Antitone (mu N))
    (δ : ℕ → ℝ) (hδ : Tendsto δ atTop atTop)
    (hgap : ∀ᶠ N in atTop, ∀ a : PositiveRoot d, δ N ≤ rootGap (mu N) a)
include hδ hgap

theorem partition_creator_word_tendsto (a : PositiveRoot d) (u v : List (PositiveRoot d)) :
    Tendsto (fun N =>
      ⟪normalizedLoweringWord (partitionHighestTensor (mu N) (hmu N)) (mu N) u,
        normalizedCreator (∑ j, mu N j) (mu N) a.val.1 a.val.2
          (normalizedLoweringWord (partitionHighestTensor (mu N) (hmu N)) (mu N) v)⟫_ℂ)
      atTop (𝓝 (creationEntry a u v)) := by
  have hg := partition_normalized_gram_tendsto (fun a : PositiveRoot d => a)
    Function.injective_id mu hmu δ hδ hgap u (a::v)
  have hh := hg.const_mul (Real.sqrt ((v.count a : ℝ)+1) : ℂ)
  simp_rw [normalizedCreator_normalizedLoweringWord, inner_smul_right]
  exact hh

theorem partition_annihilator_word_tendsto (a : PositiveRoot d) (u v : List (PositiveRoot d)) :
    Tendsto (fun N =>
      ⟪normalizedLoweringWord (partitionHighestTensor (mu N) (hmu N)) (mu N) u,
        normalizedAnnihilator (∑ j, mu N j) (mu N) a.val.1 a.val.2
          (normalizedLoweringWord (partitionHighestTensor (mu N) (hmu N)) (mu N) v)⟫_ℂ)
      atTop (𝓝 (annihilationEntry a u v)) := by
  have hh := (partition_creator_word_tendsto mu hmu δ hδ hgap a v u).star
  convert hh using 1
  ext N
  rw [← normalized_inner_adjoint]
  exact (inner_conj_symm _ _).symm

end Cloning.TensorLocalUnitary
