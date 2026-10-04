import Cloning.TensorSchurDecompositionConcentration
import Cloning.YoungGeneralSharpConcentration

/-! The exact exponential rate in the manuscript's uniform Young concentration
lemma. The finite physical Schur law first receives exponent -N epsilon^2/2;
the spare quarter absorbs every dimension-dependent polynomial prefactor. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace Cloning.TensorLie
open Cloning.YoungGeneral
set_option maxHeartbeats 800000
attribute [local instance] Classical.propDecidable
variable {d n : ℕ}

theorem tensorYoungPMF_tail_half_le (p : Fin d→ℝ) (hp : ∀a,0≤p a)
    (hs : ∑a,p a=1) (horder : Antitone p)
    (ε : ℝ) (hε : 0≤ε) (hε1 : ε≤1) :
    tailProbability (tensorYoungPMF n d p hp hs) p ε≤
      ((n*d+1:ℕ):ℝ)^Fintype.card (PositiveRoot d)*
        (2*d*Real.exp (-(n:ℝ)*ε^2/2)) := by
  have he := tensorYoungPMF_sum_mul (n:=n) p hp hs (fun mu=>
    if ∃i,(n:ℝ)*ε≤|((mu i).val:ℝ)-n*p i| then 1 else 0)
  simp only [mul_ite,mul_one,mul_zero,wordShape_val] at he
  change (∑mu : Shape d n,
    if ∃i,(n:ℝ)*ε≤|((mu i).val:ℝ)-n*p i| then
      (tensorYoungPMF n d p hp hs mu).toReal else 0)≤_
  rw [he]
  calc
    _≤∑w : Fin n→Fin d,
        ((n*d+1:ℕ):ℝ)^Fintype.card (PositiveRoot d)*
          (if ∃i,(n:ℝ)*ε≤|(rowCount w i:ℝ)-n*p i| then wordWeight p w else 0) := by
      apply Finset.sum_le_sum
      intro w _
      split_ifs
      · exact physicalStandardWordWeight_le p hp horder w
      · simp
    _=_ := (Finset.mul_sum ..).symm
    _≤_ := mul_le_mul_of_nonneg_left
      (max_rowCount_tail_half_le p hp hs ε hε hε1) (by positivity)

/-- A polynomial envelope with a whole additional exp(-N^(1/3)/4) factor
left available. This is stronger than the old vanishing-tail envelope. -/
theorem tensorYoungPMF_tail_shrinking_half_le (n : ℕ) (hn : 1≤n)
    (p : Fin d→ℝ) (hp : ∀a,0≤p a) (hs : ∑a,p a=1) (horder : Antitone p) :
    tailProbability (tensorYoungPMF n d p hp hs) p (shrinkingRadius n)≤
      (((d:ℝ)+1)^Fintype.card (PositiveRoot d)*
        (((n:ℝ)+1)^Fintype.card (PositiveRoot d)*concentrationEnvelope d n))*
      Real.exp (-((n:ℝ)^(1/3:ℝ))/4) := by
  have ht := tensorYoungPMF_tail_half_le (n:=n) p hp hs horder (shrinkingRadius n)
    (shrinkingRadius_nonneg n) (shrinkingRadius_le_one n hn)
  have he : -(n:ℝ)*shrinkingRadius n^2/2=-((n:ℝ)^(1/3:ℝ))/2 := by
    rw [neg_mul,sample_mul_radius_sq n (by omega)]
  rw [he] at ht
  let s := Fintype.card (PositiveRoot d)
  let e := Real.exp (-((n:ℝ)^(1/3:ℝ))/4)
  have hsplit : Real.exp (-((n:ℝ)^(1/3:ℝ))/2)=e*e := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hpoly : ((n*d+1:ℕ):ℝ)^s≤((d:ℝ)+1)^s*((n:ℝ)+1)^s := by
    rw [← mul_pow]
    apply pow_le_pow_left₀ (by positivity)
    push_cast
    nlinarith [(Nat.cast_nonneg n : (0:ℝ)≤n),(Nat.cast_nonneg d : (0:ℝ)≤d)]
  have hone : (1:ℝ)≤((n:ℝ)+1)^(d*d) :=
    one_le_pow₀ (by linarith [(Nat.cast_nonneg n : (0:ℝ)≤n)])
  have hepos : 0≤e := (Real.exp_pos _).le
  have hbase : ((n*d+1:ℕ):ℝ)^s*(2*d*e)≤
      ((d:ℝ)+1)^s*((n:ℝ)+1)^s*(((n:ℝ)+1)^(d*d)*(2*d*e)) := by
    calc
      _≤(((d:ℝ)+1)^s*((n:ℝ)+1)^s)*(2*d*e) :=
        mul_le_mul_of_nonneg_right hpoly (by positivity)
      _≤_ := by
        have h := mul_le_mul_of_nonneg_left hone
          (show 0≤(((d:ℝ)+1)^s*((n:ℝ)+1)^s)*(2*d*e) by positivity)
        nlinarith
  have hmul := mul_le_mul_of_nonneg_right hbase hepos
  rw [hsplit] at ht
  apply ht.trans
  convert hmul using 1 <;> dsimp [s,e,concentrationEnvelope] <;> ring

/-- Exact manuscript rate, uniformly over the closed ordered probability
simplex. Its sample threshold depends only on the ambient dimension d. -/
theorem tensorYoungPMF_tail_shrinking_uniform_exp (d : ℕ) :
    ∀ᶠ n in atTop,∀(p : Fin d→ℝ) (hp : ∀a,0≤p a) (hs : ∑a,p a=1),
      Antitone p →
      tailProbability (tensorYoungPMF n d p hp hs) p (shrinkingRadius n)≤
        Real.exp (-((n:ℝ)^(1/3:ℝ))/4) := by
  have ht := (polynomial_concentrationEnvelope_tendsto_zero d
    (Fintype.card (PositiveRoot d))).const_mul (((d:ℝ)+1)^Fintype.card (PositiveRoot d))
  simp only [mul_zero] at ht
  have hsmall := ht.eventually (Iio_mem_nhds (by norm_num : (0:ℝ)<1))
  filter_upwards [hsmall,eventually_ge_atTop 1] with n hsmall hn p hp hs horder
  have h := tensorYoungPMF_tail_shrinking_half_le n hn p hp hs horder
  exact h.trans (by
    have hmul := mul_le_mul_of_nonneg_right hsmall.le
      (Real.exp_pos (-((n:ℝ)^(1/3:ℝ))/4)).le
    simpa only [one_mul] using hmul)

/-- A natural-number threshold expresses explicitly the dimension-only
quantifier before every spectrum, including repeated and zero eigenvalues. -/
theorem exists_tensorYoungPMF_uniform_exp_threshold (d : ℕ) :
    ∃N₀ : ℕ,∀n≥N₀,∀(p : Fin d→ℝ) (hp : ∀a,0≤p a) (hs : ∑a,p a=1),
      Antitone p →
      tailProbability (tensorYoungPMF n d p hp hs) p (shrinkingRadius n)≤
        Real.exp (-((n:ℝ)^(1/3:ℝ))/4) :=
  eventually_atTop.mp (tensorYoungPMF_tail_shrinking_uniform_exp d)

end Cloning.TensorLie
