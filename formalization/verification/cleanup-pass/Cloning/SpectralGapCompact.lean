import Cloning.SpectralAffineTheorem

/-! The manuscript's concrete compact spectral sets with a positive lower
bound on the smallest eigenvalue and each adjacent gap. -/
noncomputable section
open scoped Topology BigOperators
open Filter
namespace Cloning.SpectralGap
variable {d : ℕ}
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

def gapSet (d : ℕ) (κ : ℝ) : Set (SimpleSpectrum (d+1)) :=
  {p | κ ≤ p.eigenvalue (Fin.last d) ∧
    ∀ i : Fin d, κ ≤ p.eigenvalue i.castSucc - p.eigenvalue i.succ}

def strictGapSet (d : ℕ) (κ : ℝ) : Set (SimpleSpectrum (d+1)) :=
  {p | κ < p.eigenvalue (Fin.last d) ∧
    ∀ i : Fin d, κ < p.eigenvalue i.castSucc - p.eigenvalue i.succ}

theorem strictGapSet_open (d : ℕ) (κ : ℝ) : IsOpen (strictGapSet d κ) := by
  have hc (i : Fin (d+1)) : Continuous (fun p : SimpleSpectrum (d+1) => p.eigenvalue i) :=
    (continuous_apply i).comp SimpleSpectrum.continuous_eigenvalue
  unfold strictGapSet
  simp only [Set.setOf_and, Set.setOf_forall]
  exact (isOpen_lt continuous_const (hc _)).inter
    (isOpen_iInter_of_finite fun i : Fin d =>
      isOpen_lt continuous_const ((hc i.castSucc).sub (hc i.succ)))

theorem gapSet_closed (d : ℕ) (κ : ℝ) : IsClosed (gapSet d κ) := by
  have hc (i : Fin (d+1)) : Continuous (fun p : SimpleSpectrum (d+1) => p.eigenvalue i) :=
    (continuous_apply i).comp SimpleSpectrum.continuous_eigenvalue
  unfold gapSet
  simp only [Set.setOf_and, Set.setOf_forall]
  exact (isClosed_le continuous_const (hc _)).inter
    (isClosed_iInter fun i : Fin d =>
      isClosed_le continuous_const ((hc i.castSucc).sub (hc i.succ)))

theorem strictGapSet_subset_interior (d : ℕ) (κ : ℝ) :
    strictGapSet d κ ⊆ interior (gapSet d κ) :=
  interior_maximal (fun _ h => ⟨h.1.le,fun i => (h.2 i).le⟩)
    (strictGapSet_open d κ)

private theorem sum_fin_cast (d : ℕ) :
    (∑ i : Fin (d+1), (i.val : ℝ)) = (d:ℝ)*(d+1)/2 := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last, ih, Nat.cast_add, Nat.cast_one]
    ring

def arithmeticVector (d : ℕ) (κ : ℝ) (i : Fin (d+1)) : ℝ :=
  1/(d+1) + ((d:ℝ)/2-i.val)*κ

theorem arithmeticVector_sum (d : ℕ) (κ : ℝ) :
    ∑ i, arithmeticVector d κ i = 1 := by
  have hd : (d:ℝ)+1 ≠ 0 := by positivity
  simp only [arithmeticVector, sub_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul,
    Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_add, Nat.cast_one, sum_fin_cast]
  field_simp
  ring

theorem arithmeticVector_gap (d : ℕ) (κ : ℝ) (i : Fin d) :
    arithmeticVector d κ i.castSucc - arithmeticVector d κ i.succ = κ := by
  simp only [arithmeticVector, Fin.val_castSucc, Fin.val_succ, Nat.cast_add, Nat.cast_one]
  ring

theorem arithmeticVector_last_gt (d : ℕ) {κ : ℝ}
    (hκ : κ < 2/(((d:ℝ)+1)*(d+2))) :
    κ < arithmeticVector d κ (Fin.last d) := by
  have hd : 0 < (d:ℝ)+1 := by positivity
  have hd2 : 0 < ((d:ℝ)+1)*(d+2) := by positivity
  have h := (lt_div_iff₀ hd2).mp hκ
  simp only [arithmeticVector, Fin.val_last]
  have hinv : (1/((d:ℝ)+1))*((d:ℝ)+1)=1 := div_mul_cancel₀ 1 hd.ne'
  nlinarith

def arithmeticSpectrum (d : ℕ) (κ : ℝ) (hκ : 0 < κ)
    (hupper : κ < 2/(((d:ℝ)+1)*(d+2))) : SimpleSpectrum (d+1) where
  eigenvalue := arithmeticVector d κ
  positive := by
    intro i
    have hl := arithmeticVector_last_gt d hupper
    have hi : (i.val:ℝ) ≤ d := by exact_mod_cast Nat.le_of_lt_succ i.isLt
    simp only [arithmeticVector, Fin.val_last] at *
    nlinarith
  strictAnti := Fin.strictAnti_iff_succ_lt.mpr (fun i => by
    have h := arithmeticVector_gap d κ i
    linarith)
  normalized := arithmeticVector_sum d κ

theorem strictGapSet_nonempty (d : ℕ) {κ : ℝ} (hκ : 0 < κ)
    (hupper : κ < 2/(((d:ℝ)+1)*(d+2))) : (strictGapSet d κ).Nonempty := by
  obtain ⟨t,hκt,ht⟩ := exists_between hupper
  refine ⟨arithmeticSpectrum d t (hκ.trans hκt) ht, ?_⟩
  exact ⟨hκt.trans (arithmeticVector_last_gt d ht),fun i => by
    change κ < arithmeticVector d t i.castSucc - arithmeticVector d t i.succ
    rw [arithmeticVector_gap]
    exact hκt⟩

theorem gapSet_compact (d : ℕ) {κ : ℝ} (hκ : 0 < κ) :
    IsCompact (gapSet d κ) := by
  let S : Set (Fin (d+1) → ℝ) := {p | (∑ i, p i)=1 ∧ κ≤p (Fin.last d) ∧
    ∀ i : Fin d, κ≤p i.castSucc-p i.succ}
  have he : SimpleSpectrum.eigenvalue '' gapSet d κ = S := by
    ext p
    constructor
    · rintro ⟨q,hq,rfl⟩
      exact ⟨q.normalized,hq⟩
    · rintro ⟨hsum,hl,hgap⟩
      have ha : StrictAnti p := Fin.strictAnti_iff_succ_lt.mpr fun i => by
        have h := hgap i
        linarith
      have hp (i) : 0<p i := (hκ.trans_le hl).trans_le (ha.antitone (Fin.le_last i))
      exact ⟨⟨p,hp,ha,hsum⟩,⟨hl,hgap⟩,rfl⟩
  have hc : IsClosed S := by
    have hsum : Continuous (fun p : Fin (d+1)→ℝ => ∑ i, p i) :=
      continuous_finset_sum _ (fun i _ => continuous_apply i)
    dsimp [S]
    simp only [Set.setOf_and, Set.setOf_forall]
    exact (isClosed_eq hsum continuous_const).inter
      ((isClosed_le continuous_const (continuous_apply _)).inter
        (isClosed_iInter fun i : Fin d => isClosed_le continuous_const
          ((continuous_apply i.castSucc).sub (continuous_apply i.succ))))
  have hb : S ⊆ Set.Icc (0 : Fin (d+1)→ℝ) 1 := by
    intro p hp
    obtain ⟨q,hq,rfl⟩ := he.symm ▸ hp
    refine ⟨fun i => (q.positive i).le,fun i => ?_⟩
    calc
      q.eigenvalue i ≤ ∑ j, q.eigenvalue j :=
        Finset.single_le_sum (fun j _ => (q.positive j).le) (Finset.mem_univ i)
      _ = 1 := q.normalized
  apply SimpleSpectrum.isEmbedding_eigenvalue.isCompact_iff.mpr
  rw [he]
  exact isCompact_Icc.of_isClosed_subset hc hb

def mix (p q : SimpleSpectrum (d+1)) (t : ℝ) (ht : 0≤t) (ht1 : t≤1) :
    SimpleSpectrum (d+1) where
  eigenvalue i := (1-t)*p.eigenvalue i+t*q.eigenvalue i
  positive := by
    intro i
    by_cases h : t=0
    · simp [h,p.positive i]
    · exact add_pos_of_nonneg_of_pos (mul_nonneg (by linarith) (p.positive i).le)
        (mul_pos (lt_of_le_of_ne ht (Ne.symm h)) (q.positive i))
  strictAnti := by
    intro i j hij
    have hp := p.strictAnti hij
    have hq := q.strictAnti hij
    by_cases h : t=0
    · simpa [h] using hp
    · have htp : 0<t := lt_of_le_of_ne ht (Ne.symm h)
      nlinarith [mul_nonneg (show 0≤1-t by linarith) (sub_pos.mpr hp).le,
        mul_pos htp (sub_pos.mpr hq)]
  normalized := by
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum,p.normalized,q.normalized]
    ring

theorem mix_mem_strictGapSet {κ t : ℝ} {p q : SimpleSpectrum (d+1)}
    (hp : p∈gapSet d κ) (hq : q∈strictGapSet d κ) (ht : 0<t) (ht1 : t≤1) :
    mix p q t ht.le ht1 ∈ strictGapSet d κ := by
  have hl : 0≤1-t := by linarith
  constructor
  · change κ < (1-t)*p.eigenvalue _+t*q.eigenvalue _
    nlinarith [mul_nonneg hl (sub_nonneg.mpr hp.1),mul_pos ht (sub_pos.mpr hq.1)]
  · intro i
    change κ < ((1-t)*p.eigenvalue i.castSucc+t*q.eigenvalue i.castSucc)-
      ((1-t)*p.eigenvalue i.succ+t*q.eigenvalue i.succ)
    nlinarith [mul_nonneg hl (sub_nonneg.mpr (hp.2 i)),mul_pos ht (sub_pos.mpr (hq.2 i))]

theorem gapSet_regularClosure (d : ℕ) {κ : ℝ} (hκ : 0<κ)
    (hupper : κ < 2/(((d:ℝ)+1)*(d+2))) :
    closure (interior (gapSet d κ)) = gapSet d κ := by
  refine Set.Subset.antisymm (closure_minimal interior_subset (gapSet_closed d κ)) ?_
  intro p hp
  obtain ⟨q,hq⟩ := strictGapSet_nonempty d hκ hupper
  have ht (n : ℕ) : 0 < 1/((n:ℝ)+1) := by positivity
  have ht1 (n : ℕ) : 1/((n:ℝ)+1) ≤ 1 := (div_le_one (by positivity)).mpr (by have hn : (0:ℝ)≤n := Nat.cast_nonneg n; linarith)
  let u (n : ℕ) := mix p q (1/((n:ℝ)+1)) (ht n).le (ht1 n)
  have hu (n) : u n ∈ interior (gapSet d κ) :=
    strictGapSet_subset_interior d κ (mix_mem_strictGapSet hp hq (ht n) (ht1 n))
  have hc : Tendsto u atTop (𝓝 p) := by
    apply SimpleSpectrum.isEmbedding_eigenvalue.tendsto_nhds_iff.mpr
    apply tendsto_pi_nhds.mpr
    intro i
    have hz := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    simpa [u,mix] using (((tendsto_const_nhds (x := (1:ℝ))).sub hz).mul_const (p.eigenvalue i)).add
      (hz.mul_const (q.eigenvalue i))
  exact mem_closure_of_tendsto hc (Eventually.of_forall hu)

/-- The displayed concrete spectral family satisfies every compact-set
hypothesis of the unknown-spectrum minimax theorem. -/
theorem gapSet_hypotheses (d : ℕ) {κ : ℝ} (hκ : 0<κ)
    (hupper : κ < 2/(((d:ℝ)+1)*(d+2))) :
    IsCompact (gapSet d κ) ∧ (gapSet d κ).Nonempty ∧
      closure (interior (SimpleSpectrum.toAffine '' gapSet d κ)) =
        SimpleSpectrum.toAffine '' gapSet d κ := by
  have hc := gapSet_compact d hκ
  obtain ⟨p,hp⟩ := strictGapSet_nonempty d hκ hupper
  exact ⟨hc,⟨p,interior_subset (strictGapSet_subset_interior d κ hp)⟩,
    (SimpleSpectrum.regularClosure_affine_iff _ hc).mpr (gapSet_regularClosure d hκ hupper)⟩

end Cloning.SpectralGap
